//
// ::formally - the open-source formal methods toolchain
//
// Copyright (c) 2026 Nicola Gigante
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//

mod utils;
use utils::*;

use crate::formally;

use formally::{
    io::print::*,
    smt::{
        self, Config, Env, Function, FunctionRef, Quantified, Solver, Sort, Term, TermKind,
        TermManager, TermPool, ToTerm, Variable,
        backends::Backend,
        theories::{Core, CoreAtom},
    },
    support::{Diagnosable, DiagnosticEmitted, Located, Span},
};

use oxidd::{
    BooleanFunction as _, BooleanFunctionQuant, Function as _, HasLevel, HasWorkers, LevelNo,
    Manager as _, ManagerRef, Node, VarNo, WorkerPool,
    bcdd::{BCDDFunction, BCDDManagerRef},
    error::OutOfMemory,
};

use oxidd_reorder::set_var_order_seq;
use oxidd_rules_bdd::complement_edge::EdgeTag;

use dashmap::DashMap;
use itertools::Itertools;
use parking_lot::RwLock;
use thiserror::Error;
use transitive::Transitive;

use std::{
    collections::HashMap,
    fmt::Debug,
    num::NonZero,
    sync::{
        Arc,
        atomic::{AtomicU32, AtomicUsize, Ordering},
    },
};

#[derive(Debug, Error, Located, Transitive)]
#[allow(clippy::duplicated_attributes)]
#[transitive(from(OutOfMemory, ErrorKind))]
#[transitive(from(DiagnosticEmitted, ErrorKind))]
#[error("{kind}")]
pub struct Error {
    pub kind: ErrorKind,
    pub span: Option<Span>,
}

impl From<ErrorKind> for Error {
    fn from(kind: ErrorKind) -> Self {
        Error { kind, span: None }
    }
}

#[derive(Debug, Error)]
pub enum ErrorKind {
    #[error("maximum memory usage limit reached for BDD nodes")]
    OutOfMemory(#[from] OutOfMemory),
    #[error("unable to instantiate a new SMT backend")]
    BackendError(#[from] DiagnosticEmitted),
}

impl Diagnosable for Error {}

pub fn qe(
    term: &Term,
    pool: Arc<dyn TermPool + Send + Sync>,
    env: Env,
    backend: &'static dyn Backend,
    jobs: Option<NonZero<u32>>,
) -> Result<Term, Error> {
    qe_in(term, pool, env, backend, jobs, &HashMap::new())
}

#[allow(clippy::mutable_key_type)]
fn qe_in(
    term: &Term,
    pool: Arc<dyn TermPool + Send + Sync>,
    env: Env,
    backend: &'static dyn Backend,
    jobs: Option<NonZero<u32>>,
    bindings: &HashMap<Variable, Term>,
) -> Result<Term, Error> {
    match term.kind() {
        TermKind::Constant(_) => Ok(term.clone()),
        TermKind::Atom(atom) => {
            if let FunctionRef::Bound(bound) = &atom.head
                && let Function::Variable(var) = &bound.function
                && let Some(term) = bindings.get(var)
            {
                qe_in(term, pool, env, backend, jobs, bindings)
            } else {
                Ok(smt::Atom {
                    head: atom.head.clone(),
                    arguments: atom
                        .arguments
                        .iter()
                        .map(|arg| qe_in(arg, pool.clone(), env.clone(), backend, jobs, bindings))
                        .try_collect()?,
                    span: atom.span(),
                }
                .into_term_in(&*pool))
            }
        }
        TermKind::Quantified(_) => {
            let mut quantifiers = Vec::new();
            let mut body = term.clone();

            while let TermKind::Quantified(quant) = body.kind() {
                for variable in &*quant.variables {
                    quantifiers.push(Quantifier {
                        quantifier: quant.quantifier,
                        target: variable.clone(),
                    })
                }
                body = quant.body.clone();
            }
            quantifiers.reverse();

            let body = qe_in(&body, pool.clone(), env.clone(), backend, jobs, bindings)?;
            QE::new(pool, env, backend, jobs).qe(&quantifiers, &body)
        }
        TermKind::Let(let_) => {
            let mut nested = bindings.clone();
            for bind in &*let_.bindings {
                nested.insert(
                    bind.variable.clone(),
                    qe_in(
                        &bind.def,
                        pool.clone(),
                        env.clone(),
                        backend,
                        jobs,
                        bindings,
                    )?,
                );
            }
            qe_in(&let_.body, pool, env, backend, jobs, &nested)
        }
    }
}

struct Quantifier {
    quantifier: smt::Quantifier,
    target: Variable,
}

struct OrderBlock {
    target: Option<Variable>,
    start: VarNo,
    len: AtomicU32,
    capacity: RwLock<u32>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BddConstruction {
    Coarse,
    Fine,
}

struct QE {
    manager: BCDDManagerRef,
    top: BCDDFunction,
    bottom: BCDDFunction,
    pool: Arc<dyn TermPool + Send + Sync>,
    env: Env,
    backend: &'static dyn Backend,
    atoms: SyncBiMap<Term, VarNo>,
    free: DashMap<Term, BitSet>,
    variables: BiMap<Variable, usize>,
    order: Vec<OrderBlock>,
    booleans: BitSet,
}

impl QE {
    pub fn new(
        pool: Arc<dyn TermPool + Send + Sync>,
        env: Env,
        backend: &'static dyn Backend,
        jobs: Option<NonZero<u32>>,
    ) -> QE {
        let jobs = jobs.map(NonZero::get).unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(NonZero::get)
                .unwrap_or(1) as u32
        });
        let manager = oxidd::bcdd::new_manager(1_073_741_824, 1_048_576, jobs);
        manager.workers().set_split_depth(Some(0));
        QE {
            top: manager.with_manager_shared(|m| BCDDFunction::t(m)),
            bottom: manager.with_manager_shared(|m| BCDDFunction::f(m)),
            manager,
            pool,
            env,
            backend,
            atoms: SyncBiMap::new(),
            free: DashMap::new(),
            variables: BiMap::new(),
            order: Vec::new(),
            booleans: BitSet::new(),
        }
    }

    fn setup(&mut self, quantifiers: &[Quantifier]) {
        const BLOCK: u32 = 10;

        self.manager.with_manager_exclusive(|m| {
            // initial block for atoms not mentioning any eliminated variables
            let vars = m.add_vars(BLOCK);
            self.order.push(OrderBlock {
                target: None,
                start: vars.start,
                len: AtomicU32::new(0),
                capacity: RwLock::new(BLOCK),
            });

            // with rev(), variables to be eliminated *earlier* have *higher* indexes,
            // which conceptually similar to how also levels in the BDD are higher.
            for (index, q) in quantifiers.iter().rev().enumerate() {
                self.variables.insert(q.target.clone(), index);
                if *q.target.sort() == Core::Bool() {
                    self.booleans.set(index, true);
                }

                let vars = m.add_vars(BLOCK);
                self.order.push(OrderBlock {
                    target: Some(q.target.clone()),
                    start: vars.start,
                    len: AtomicU32::new(0),
                    capacity: RwLock::new(BLOCK),
                })
            }
        })
    }

    fn cutoff(&self, variable: &Variable) -> Option<LevelNo> {
        let index = self.variables.by_key(variable)?;
        let var = self.order[index + 1].start;
        let level = self.manager.with_manager_shared(|m| m.var_to_level(var));

        Some(level)
    }

    fn qe(&mut self, quantifiers: &[Quantifier], body: &Term) -> Result<Term, Error> {
        let mut prevq = smt::Quantifier::Exists;

        self.setup(quantifiers);

        let mut body = self.bdd(body, BddConstruction::Fine)?;
        for Quantifier { quantifier, target } in quantifiers {
            // match quantifier {
            //     smt::Quantifier::Forall => eprint!("eliminating forall {}... ", target.name()),
            //     smt::Quantifier::Exists => eprint!("eliminating exists {}... ", target.name()),
            // }

            if prevq != *quantifier {
                body = body.not()?;
            }
            prevq = *quantifier;

            if *target.sort() == Core::Bool() {
                body = self.project(target, body)?;
                // eprintln!("eliminated with Boolean projection!");
            } else {
                let calls = AtomicUsize::new(0);
                body = self.eliminate(target, body, &calls)?;

                // eprintln!(
                //     "eliminated with {} QE calls!",
                //     calls.load(Ordering::Relaxed)
                // );
            }
        }

        if prevq == smt::Quantifier::Forall {
            body = body.not()?;
        }

        Ok(self.term(&body))
    }

    #[allow(unused)]
    fn print_atoms(&self) {
        self.manager.with_manager_exclusive(|m| {
            eprintln!("atoms:");
            for block in &self.order {
                match &block.target {
                    Some(target) => eprint!("- `{}` ", target.name()),
                    None => eprint!("- irrelevant variables "),
                }
                let len = block.len.load(Ordering::Relaxed);
                let capacity = *block.capacity.read();
                eprintln!("(len: {len}, capacity: {capacity}):");
                let level = m.var_to_level(block.start);
                for level in level..level + capacity {
                    let var = m.level_to_var(level);

                    eprint!("  - level {level:4} -> var {var:4}: ");
                    match self.atoms.by_index(&var) {
                        Some(atom) => {
                            if let Some(target) = &block.target
                                && let Some(index) = self.variables.by_key(target)
                                && !self.free(&atom).get(index)
                            {
                                eprint!("!! ")
                            } else {
                                eprint!("   ")
                            }
                            let mut printed = Vec::new();
                            atom.print(&mut printed).ok();
                            let mut printed = String::from_utf8(printed).unwrap();
                            if printed.len() > 60 {
                                printed.truncate(60);
                                printed.push_str("...");
                            }
                            eprintln!("{printed}");
                        }
                        None => {
                            eprintln!();
                        }
                    }
                }
            }
        })
    }

    fn top(&self) -> BCDDFunction {
        self.top.clone()
    }

    fn bottom(&self) -> BCDDFunction {
        self.bottom.clone()
    }

    fn project(&self, target: &Variable, body: BCDDFunction) -> Result<BCDDFunction, Error> {
        debug_assert_eq!(*target.sort(), Core::Bool());

        let target = target.into_term_in(&*self.pool);
        let var = self.atoms.by_key(&target).unwrap();
        let var = self
            .manager
            .with_manager_shared(|m| BCDDFunction::var(m, var))?;

        Ok(body.exists(&var)?)
    }

    fn eliminate(
        &mut self,
        target: &Variable,
        body: BCDDFunction,
        calls: &AtomicUsize,
    ) -> Result<BCDDFunction, Error> {
        self.eliminate_in(target, body, &DashMap::new(), calls)
    }

    fn eliminate_in(
        &self,
        target: &Variable,
        body: BCDDFunction,
        cache: &DashMap<BCDDFunction, BCDDFunction>,
        calls: &AtomicUsize,
    ) -> Result<BCDDFunction, Error> {
        if let Some(result) = cache.get(&body) {
            return Ok(result.clone());
        }

        let result = match body.cofactors() {
            Some((high, low)) => {
                let (level, guard) = body.with_manager_shared(|m, edge| -> Result<_, Error> {
                    let Node::Inner(node) = m.get_node(edge) else {
                        unreachable!()
                    };
                    let level = node.level();
                    let var = m.level_to_var(level);

                    Ok((level, BCDDFunction::var(m, var)?))
                })?;

                let cutoff = self.cutoff(target).unwrap();
                if level < cutoff {
                    let (high, low) = self.manager.workers().join(
                        || self.eliminate_in(target, high, cache, calls),
                        || self.eliminate_in(target, low, cache, calls),
                    );

                    guard.ite(&high?, &low?)?
                } else {
                    let quant = Quantified {
                        quantifier: smt::Quantifier::Exists,
                        variables: Arc::new([target.clone()]),
                        body: self.term(&body),
                        span: None,
                    }
                    .into_term_in(&*self.pool);

                    let manager = TermManager::with_pool(self.backend, self.pool.clone())?;
                    let mut solver = Solver::with_manager(&Config::default(), manager)?;
                    solver.import(self.env.clone())?;

                    let _calls = calls.fetch_add(1, Ordering::Relaxed);
                    // eprint!("{calls}th QE call: ");
                    // quant.println(&mut std::io::stderr()).ok();
                    let eliminated = solver.qe(quant)?;
                    // eprint!("{calls}th QE result: ");
                    // eliminated.println(&mut std::io::stderr()).ok();

                    self.bdd(&eliminated, BddConstruction::Coarse)?
                }
            }
            None => body.clone(),
        };

        cache.insert(body, result.clone());

        Ok(result)
    }

    // How to concurrently insert new atoms efficiently.
    //
    // Requirements:
    // 1. maintain a pool of free vars to only allocate new ones every once in a while
    // 2. hold the write lock on the manager only for the new vars allocation
    // 3. maintain the vars order based on the appearance of variables in the corresponding atoms
    //    - maintain "blocks" of vars with the same earliest occurring variable
    //    - maintain the cutoffs and insertion points of each block (possibly at the bottom)
    // We need basically the same logic of a vector for each block: cutoff, len, capacity.
    // For the initial configuration see setup()
    fn atom(&self, term: Term) -> VarNo {
        let size = self.atoms.size();
        self.atoms.by_key_or_insert(term, |term| {
            // block zero is for atoms mentioning no variables to be eliminated.
            // other blocks are at variable's index + 1
            let earliest = match self.earliest(term) {
                Some(variable) => self.variables.by_key(&variable).unwrap() + 1,
                None => 0,
            };

            let block = &self.order[earliest];

            // we reserve our place by incrementing `len` atomically.
            // nobody will reuse that spot
            let len = block.len.fetch_add(1, Ordering::Relaxed);

            // we check if len >= capacity
            // not `==` because some other thread may have incremented `len` concurrently
            if len >= *block.capacity.read() {
                // Here len *was* equal to capacity at some point.
                // Some other thread may have increased it already, but we don't care about
                // double increases.
                // For the allocation we lock both `capacity` and the manager.
                self.manager.with_manager_exclusive(|m| {
                    let mut capacity = block.capacity.write();

                    // to double the capacity we add the same amount of variables
                    let vars = m.add_vars(*capacity);

                    // the insertion level is the end of the block
                    let level = (m.var_to_level(block.start) + *capacity) as usize;

                    // we set up the vector of vars in the right order and call `set_var_order_seq`
                    let mut order = (0..m.num_levels()).map(|l| m.level_to_var(l)).collect_vec();

                    // the variables were added at the end of the order so to move them after
                    // `level` we rotate everything to the right of the right amount
                    order[level..].rotate_right(vars.len());

                    // The new variables are not yet mentioned by any BDD so this should be cheap
                    set_var_order_seq(m, &order);

                    // double the capacity
                    *capacity *= 2;
                });
            }

            self.manager
                .workers()
                .set_split_depth(Some(std::cmp::max(15, (size / 4 * 3) as u32)));

            // here we have the old `len` we reserved before, and we know *at least* one
            // reallocation happened if needed at all.
            self.manager
                .with_manager_shared(|m| m.level_to_var(m.var_to_level(block.start) + len))
        })
    }

    fn earliest(&self, term: &Term) -> Option<Variable> {
        let free = self.free(term);
        free.last_one()
            .map(|index| self.variables.by_index(&index).unwrap())
    }

    fn free(&self, term: &Term) -> BitSet {
        if let Some(bits) = self.free.get(term) {
            return bits.clone();
        }

        let bits = match term.kind() {
            TermKind::Constant(_) => BitSet::new(),
            TermKind::Atom(atom) => {
                let mut bits = BitSet::new();
                if let FunctionRef::Bound(bound) = &atom.head
                    && let Function::Variable(variable) = &bound.function
                    && let Some(index) = self.variables.by_key(variable)
                {
                    bits.set(index, true);
                }

                for arg in &*atom.arguments {
                    bits |= self.free(arg)
                }

                bits
            }
            _ => unreachable!(),
        };

        self.free.insert(term.clone(), bits.clone());

        bits
    }

    fn has_booleans(&self, term: &Term) -> bool {
        (self.free(term) & &self.booleans).any()
    }

    fn bdd(&self, term: &Term, construction: BddConstruction) -> Result<BCDDFunction, Error> {
        self.bdd_in(term, construction, &mut HashMap::new())
    }

    #[allow(clippy::mutable_key_type)]
    fn bdd_in(
        &self,
        term: &Term,
        construction: BddConstruction,
        cache: &mut HashMap<Term, BCDDFunction>,
    ) -> Result<BCDDFunction, Error> {
        if let Some(bdd) = cache.get(term) {
            return Ok(bdd.clone());
        }

        if construction == BddConstruction::Coarse && !self.has_booleans(term) {
            if *term == true {
                return Ok(self.top());
            }
            if *term == false {
                return Ok(self.bottom());
            }

            let var = self.atom(term.simplified(&*self.pool));
            let bdd = self
                .manager
                .with_manager_shared(|m| BCDDFunction::var(m, var))?;
            cache.insert(term.clone(), bdd.clone());
            return Ok(bdd);
        }

        let bdd = match term.kind() {
            TermKind::Atom(atom) => {
                if let Ok(atom) = CoreAtom::try_from(atom) {
                    match atom {
                        CoreAtom::True => self.top(),
                        CoreAtom::False => self.bottom(),
                        CoreAtom::Not(arg) => self.bdd_in(arg, construction, cache)?.not()?,
                        CoreAtom::Implies(args) => args
                            .iter()
                            .enumerate()
                            .map(|(i, arg)| {
                                if i == args.len() - 1 {
                                    self.bdd_in(arg, construction, cache)
                                } else {
                                    Ok(self.bdd_in(arg, construction, cache)?.not()?)
                                }
                            })
                            .try_fold(self.bottom(), |acc, arg| Ok::<_, Error>(acc.or(&arg?)?))?,
                        CoreAtom::And(args) => args
                            .iter()
                            .map(|arg| self.bdd_in(arg, construction, cache))
                            .try_fold(self.top(), |acc, arg| Ok::<_, Error>(acc.and(&arg?)?))?,
                        CoreAtom::Or(args) => args
                            .iter()
                            .map(|arg| self.bdd_in(arg, construction, cache))
                            .try_fold(self.bottom(), |acc, arg| Ok::<_, Error>(acc.or(&arg?)?))?,
                        CoreAtom::Xor(args) => args
                            .iter()
                            .map(|arg| self.bdd_in(arg, construction, cache))
                            .try_fold(self.bottom(), |acc, arg| Ok::<_, Error>(acc.xor(&arg?)?))?,
                        CoreAtom::Ite(guard, high, low) => {
                            let guard = self.bdd_in(guard, construction, cache)?;
                            let high = self.bdd_in(high, construction, cache)?;
                            let low = self.bdd_in(low, construction, cache)?;

                            guard.ite(&high, &low)?
                        }
                        CoreAtom::Equals(args) | CoreAtom::Distinct(args) => {
                            if args
                                .iter()
                                .any(|arg| Sort::of(arg).unwrap() == Core::Bool())
                            {
                                args.iter()
                                    .map(|arg| self.bdd_in(arg, construction, cache))
                                    .try_fold(self.top(), |acc, arg| {
                                        let arg = arg?;
                                        Ok::<_, Error>(acc.imp(&arg)?.and(&arg.imp(&acc)?)?)
                                    })?
                            } else {
                                let var = self.atom(term.simplified(&*self.pool));
                                self.manager
                                    .with_manager_shared(|m| BCDDFunction::var(m, var))?
                            }
                        }
                    }
                } else {
                    let var = self.atom(term.simplified(&*self.pool));
                    self.manager
                        .with_manager_shared(|m| BCDDFunction::var(m, var))?
                }
            }
            _ => unreachable!(),
        };

        cache.insert(term.clone(), bdd.clone());

        Ok(bdd)
    }

    #[allow(clippy::mutable_key_type)]
    fn term(&self, bdd: &BCDDFunction) -> Term {
        self.term_in(bdd, &mut HashMap::new())
            .simplified(&*self.pool)
    }

    #[allow(clippy::mutable_key_type)]
    fn term_in(&self, bdd: &BCDDFunction, cache: &mut HashMap<BCDDFunction, Term>) -> Term {
        if let Some(term) = cache.get(bdd) {
            return term.clone();
        }

        let term = match bdd.cofactors() {
            Some((high, low)) => {
                let guard = self.manager.with_manager_shared(|m| {
                    let edge = bdd.as_edge(m);
                    let Node::Inner(node) = m.get_node(edge) else {
                        unreachable!()
                    };
                    self.atoms
                        .by_index(&m.level_to_var(node.level()))
                        .unwrap()
                        .clone()
                });

                let high = self.term_in(&high, cache);
                let low = self.term_in(&low, cache);

                Core::ite()
                    .call([guard, high, low])
                    .into_term_in(&*self.pool)
            }
            None => bdd.with_manager_shared(|_, edge| match edge.tag() {
                EdgeTag::None => Core::True().into_term_in(&*self.pool),
                EdgeTag::Complemented => Core::False().into_term_in(&*self.pool),
            }),
        };

        cache.insert(bdd.clone(), term.clone());
        term
    }
}
