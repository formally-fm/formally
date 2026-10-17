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

mod executor;
mod utils;

use executor::*;
use utils::*;

use crate::formally;

use formally::{
    smt::{
        self, Atom, Config, Env, Function, FunctionRef, Quantified, Solver, Sort, Term, TermKind,
        TermManager, TermPool, ToTerm, Variable,
        backends::Backend,
        theories::{Core, CoreAtom},
    },
    support::{Diagnosable, DiagnosticEmitted, Located, Span},
};

use oxidd::{
    BooleanFunction as _, BooleanFunctionQuant, Function as _, HasLevel, HasWorkers, LevelNo,
    Manager as _, ManagerRef as _, Node, VarNo, WorkerPool,
    bcdd::{BCDDFunction as BDD, BCDDManagerRef as ManagerRef},
    error::OutOfMemory,
};

use oxidd_reorder::set_var_order_seq;
use oxidd_rules_bdd::complement_edge::EdgeTag;

use itertools::Itertools;
use parking_lot::RwLock;
use thiserror::Error;
use transitive::Transitive;

#[allow(unused)]
use rand::prelude::*;

use async_recursion::async_recursion;
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    num::NonZero,
    ops::Range,
    pin::Pin,
    sync::{
        Arc, Weak,
        atomic::{AtomicU32, Ordering},
    },
};

#[derive(Debug, Clone, Error, Located, Transitive)]
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

#[derive(Debug, Clone, Error)]
pub enum ErrorKind {
    #[error("maximum memory usage limit reached for BDD nodes")]
    OutOfMemory(#[from] OutOfMemory),
    #[error("unable to instantiate a new SMT backend")]
    BackendError(#[from] DiagnosticEmitted),
}

impl Diagnosable for Error {}

type Result<T, E = Error> = std::result::Result<T, E>;

pub fn qe(
    term: &Term,
    pool: Arc<dyn TermPool + Send + Sync>,
    env: Env,
    backend: &'static dyn Backend,
    jobs: Option<NonZero<u32>>,
) -> Result<Term> {
    let term = expand_let(term, &*pool, &HashMap::new());
    let term = hoist_ite(&term, &*pool, &mut HashMap::new());
    qe_in(&term, pool, env, backend, jobs)
}

// (f (ite b x y) z w) -> (ite b (f x z w) (f y z w))
#[allow(clippy::mutable_key_type)]
fn hoist_ite_in(
    head: &FunctionRef,
    arguments: &[Term],
    pool: &dyn TermPool,
    cache: &mut HashMap<Term, Term>,
) -> Term {
    for (i, arg) in arguments.iter().enumerate() {
        if let Ok(CoreAtom::Ite(guard, high, low)) = CoreAtom::try_from(arg)
            && Sort::of(arg).unwrap() != Core::Bool()
        {
            let mut argshigh = arguments.to_vec();
            argshigh[i] = high.clone();

            let mut argslow = arguments.to_vec();
            argslow[i] = low.clone();

            let high = Atom {
                head: head.clone(),
                arguments: Arc::from(argshigh.into_boxed_slice()),
                span: None,
            }
            .into_term_in(pool);

            let low = Atom {
                head: head.clone(),
                arguments: Arc::from(argslow.into_boxed_slice()),
                span: None,
            }
            .into_term_in(pool);

            let high = hoist_ite(&high, pool, cache);
            let low = hoist_ite(&low, pool, cache);

            return Core::ite()
                .call([guard.clone(), high, low])
                .into_term_in(pool);
        }
    }

    Atom {
        head: head.clone(),
        arguments: arguments.iter().cloned().collect(),
        span: None,
    }
    .into_term_in(pool)
}

#[allow(clippy::mutable_key_type)]
fn hoist_ite(term: &Term, pool: &dyn TermPool, cache: &mut HashMap<Term, Term>) -> Term {
    if let Some(term) = cache.get(term) {
        return term.clone();
    }

    let result = match term.kind() {
        TermKind::Constant(_) => term.clone(),
        TermKind::Atom(atom) => {
            if let Ok(CoreAtom::Ite(guard, high, low)) = CoreAtom::try_from(atom) {
                Core::ite()
                    .call([
                        hoist_ite(guard, pool, cache),
                        hoist_ite(high, pool, cache),
                        hoist_ite(low, pool, cache),
                    ])
                    .into_term_in(pool)
            } else {
                let mut arguments = Vec::with_capacity(atom.arguments.len());
                for arg in &*atom.arguments {
                    arguments.push(hoist_ite(arg, pool, cache));
                }

                hoist_ite_in(&atom.head, &arguments, pool, cache)
            }
        }
        TermKind::Quantified(quant) => Quantified {
            quantifier: quant.quantifier,
            variables: quant.variables.clone(),
            body: hoist_ite(&quant.body, pool, cache),
            span: None,
        }
        .into_term_in(pool),
        TermKind::Let(_) => unreachable!(),
    };

    cache.insert(term.clone(), result.clone());

    result
}

#[allow(clippy::mutable_key_type)]
fn expand_let(term: &Term, pool: &dyn TermPool, scope: &HashMap<Variable, Term>) -> Term {
    match term.kind() {
        TermKind::Constant(_) => term.clone(),
        TermKind::Atom(atom) => {
            if let FunctionRef::Bound(bound) = &atom.head
                && let Function::Variable(var) = &bound.function
                && let Some(term) = scope.get(var)
            {
                expand_let(term, pool, scope)
            } else {
                Atom {
                    head: atom.head.clone(),
                    arguments: atom
                        .arguments
                        .iter()
                        .map(|arg| expand_let(arg, pool, scope))
                        .collect(),
                    span: atom.span(),
                }
                .into_term_in(pool)
            }
        }
        TermKind::Quantified(quant) => Quantified {
            quantifier: quant.quantifier,
            variables: quant.variables.clone(),
            body: expand_let(&quant.body, pool, scope),
            span: None,
        }
        .into_term_in(pool),
        TermKind::Let(let_) => {
            let mut nested = scope.clone();
            for bind in &*let_.bindings {
                nested.insert(bind.variable.clone(), expand_let(&bind.def, pool, scope));
            }
            expand_let(&let_.body, pool, &nested)
        }
    }
}

#[allow(clippy::mutable_key_type)]
fn qe_in(
    term: &Term,
    pool: Arc<dyn TermPool + Send + Sync>,
    env: Env,
    backend: &'static dyn Backend,
    jobs: Option<NonZero<u32>>,
) -> Result<Term> {
    match term.kind() {
        TermKind::Constant(_) => Ok(term.clone()),
        TermKind::Atom(atom) => Ok(Atom {
            head: atom.head.clone(),
            arguments: atom
                .arguments
                .iter()
                .map(|arg| qe_in(arg, pool.clone(), env.clone(), backend, jobs))
                .try_collect()?,
            span: atom.span(),
        }
        .into_term_in(&*pool)),
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

            let body = qe_in(&body, pool.clone(), env.clone(), backend, jobs)?;
            QE::new(pool, env, backend, jobs).qe(quantifiers, body, Strategy::Immediate)
        }
        TermKind::Let(_) => unreachable!(),
    }
}

#[derive(Clone)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Insertion {
    Earliest,
    Bottom,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BddMode {
    Coarse,
    Fine,
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[allow(unused)]
enum Strategy {
    Immediate,
    Delayed,
}

struct QE {
    this: Weak<QE>,
    manager: ManagerRef,
    top: BDD,
    bottom: BDD,
    pool: Arc<dyn TermPool + Send + Sync>,
    env: Env,
    backend: &'static dyn Backend,
    atoms: SyncBiMap<Term, VarNo>,
    partials: MemoMap<VarNo, Result<Term>>,
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
        let jobs = match jobs {
            Some(jobs) => jobs.get(),
            None => match std::thread::available_parallelism() {
                Ok(jobs) => jobs.get() as u32,
                Err(_) => 1u32,
            },
        };
        let manager = oxidd::bcdd::new_manager(2usize.pow(30), 2usize.pow(20), jobs);
        manager.workers().set_split_depth(Some(0));
        QE {
            this: Weak::new(),
            top: manager.with_manager_shared(|m| BDD::t(m)),
            bottom: manager.with_manager_shared(|m| BDD::f(m)),
            manager: manager.clone(),
            pool,
            env,
            backend,
            atoms: SyncBiMap::new(),
            partials: MemoMap::new(manager),
            variables: BiMap::new(),
            order: Vec::new(),
            booleans: BitSet::new(),
        }
    }

    fn arc(&self) -> Arc<Self> {
        self.this.upgrade().unwrap()
    }

    fn setup(
        &mut self,
        quantifiers: Vec<Quantifier>,
        body: &Term,
    ) -> (Vec<Quantifier>, Vec<Range<usize>>, Term) {
        let body = body.simplified(&*self.pool);

        self.setup_indexes(&quantifiers);
        let (quantifiers, ranges) = self.elimination_order(quantifiers, &body);

        self.setup_indexes(&quantifiers);
        self.init_order(&quantifiers);

        (quantifiers, ranges, body)
    }

    fn setup_indexes(&mut self, quantifiers: &[Quantifier]) {
        self.variables = BiMap::new();
        self.booleans = BitSet::new();

        for (index, q) in quantifiers.iter().rev().enumerate() {
            self.variables.insert(q.target.clone(), index);
            if *q.target.sort() == Core::Bool() {
                self.booleans.set(index, true);
            }
        }
    }

    //
    // New elimination order heuristic.
    //
    // Main observation:
    // - if a subtree mentions a subset of the variables which is not mentioned above, eliminating
    //   all those variables from the subtree at once reduces the problem to satisfiability.
    // Conceptually:
    // - Make an undirected graph with the variables as nodes and an edge between two variables iff
    //   they appear together in an atom.
    // - Find the connected components.
    // - Push down together in the var order the atoms of the same connected components
    // - Eliminate at once all the variables of the lower connected component, repeat.
    // In practice:
    // - we don't need the graph
    // - start from a variable and collect all the atoms that mention it
    // - take another variable mentioned by those atoms and collect atoms mentioning it, repeat
    // - when there are no uncovered variables, you have your component
    // Problem:
    // - This can only be done precisely for a single quantifier block.
    // - Atoms mentioning variables in later blocks prevent the reduction to satisfiability.
    // - Still it can be useful to eliminate all the variables of the component at once.
    // - Doing that will generate new atoms mentioning variables in later blocks.
    // - Where do we put those atoms in the var order?
    // Observation:
    // - The new atoms can only mention variables that were already mentioned in the eliminated
    //   formula.
    // - Those atoms will either:
    //   - fit into an existing connected component from a single later block (best case), or
    //   - connect together existing components from later blocks (bad case), maybe even not
    //     contiguous in the order (worst case).
    // Idea:
    // - New atoms are placed according to their earliest mention. So:
    //   - If the atom fits an existing component, by construction its position will belong to the
    //     component
    //   - If the atom does not fit an existing component, the position does not matter
    fn elimination_order(
        &self,
        mut quantifiers: Vec<Quantifier>,
        body: &Term,
    ) -> (Vec<Quantifier>, Vec<Range<usize>>) {
        let atoms = self.collect_atoms(&quantifiers, body);
        let mut quants = Vec::with_capacity(quantifiers.len());
        let mut ranges = Vec::with_capacity(quantifiers.len());
        let mut start = 0;
        for block in quantifiers.chunk_by_mut(|q, r| q.quantifier == r.quantifier) {
            let quant = block[0].quantifier;
            let targets = block.iter().map(|q| q.target.clone()).collect_vec();
            let (q, r) = self.elimination_order_block(start, quant, targets, &atoms);
            quants.extend(q);
            ranges.extend(r);
            start += block.len();
        }

        (quants, ranges)
    }

    #[allow(clippy::mutable_key_type)]
    fn elimination_order_block(
        &self,
        start: usize,
        quantifier: smt::Quantifier,
        targets: Vec<Variable>,
        atoms: &HashMap<Variable, HashSet<Term>>,
    ) -> (Vec<Quantifier>, Vec<Range<usize>>) {
        let mut quants = Vec::with_capacity(targets.len());
        let mut ranges = Vec::with_capacity(targets.len());

        let mut block = BitSet::new();
        for target in &targets {
            block.set(self.variables.by_key(target).unwrap(), true);
        }
        let mut remaining = block.clone();

        while let Some(index) = remaining.first_one() {
            let mut component = BitSet::new();
            let mut mentioned = BitSet::new();
            mentioned.set(index, true);

            while let Some(index) = mentioned.first_one() {
                mentioned.set(index, false);
                component.set(index, true);
                remaining.set(index, false);

                let target = self.variables.by_index(&index).unwrap();

                let mut free = BitSet::new();
                for atom in atoms.get(&target).unwrap() {
                    free |= self.free(atom);
                }
                for index in component.iter_ones() {
                    free.set(index, false);
                }
                mentioned |= free & &block;
            }

            let len = component.count_ones();
            let component = component
                .iter_ones()
                .map(|i| self.variables.by_index(&i).unwrap().clone())
                .map(|target| Quantifier { quantifier, target });
            let begin = start + quants.len();
            quants.extend(component);
            let end = begin + len;
            ranges.push(begin..end);
        }

        (quants, ranges)
    }

    fn collect_atoms(
        &self,
        quantifiers: &[Quantifier],
        term: &Term,
    ) -> HashMap<Variable, HashSet<Term>> {
        let mut variables = HashMap::new();
        for q in quantifiers {
            variables.insert(q.target.clone(), HashSet::new());
        }
        self.collect_atoms_in(term, &mut variables);

        variables
    }

    #[allow(clippy::mutable_key_type)]
    fn collect_atom(&self, term: &Term, atoms: &mut HashMap<Variable, HashSet<Term>>) {
        let free = self.free(term);
        for index in free.iter_ones() {
            if let Some(variable) = self.variables.by_index(&index) {
                atoms.get_mut(&variable).unwrap().insert(term.clone());
            }
        }
    }

    #[allow(clippy::mutable_key_type)]
    fn collect_atoms_in(&self, term: &Term, variables: &mut HashMap<Variable, HashSet<Term>>) {
        match term.kind() {
            TermKind::Constant(_) => {}
            TermKind::Atom(atom) => {
                if let Ok(atom) = CoreAtom::try_from(atom) {
                    match atom {
                        CoreAtom::True | CoreAtom::False => {}
                        CoreAtom::Not(arg) => self.collect_atoms_in(arg, variables),
                        CoreAtom::Implies(args)
                        | CoreAtom::And(args)
                        | CoreAtom::Or(args)
                        | CoreAtom::Xor(args) => {
                            for arg in args {
                                self.collect_atoms_in(arg, variables);
                            }
                        }
                        CoreAtom::Ite(guard, high, low) => {
                            self.collect_atoms_in(guard, variables);
                            self.collect_atoms_in(high, variables);
                            self.collect_atoms_in(low, variables);
                        }
                        CoreAtom::Equals(args) | CoreAtom::Distinct(args) => {
                            if Sort::of(&args[0]).unwrap() == Core::Bool() {
                                for arg in args {
                                    self.collect_atoms_in(arg, variables);
                                }
                            } else {
                                self.collect_atom(term, variables);
                            }
                        }
                    }
                } else {
                    self.collect_atom(term, variables);
                }
            }
            TermKind::Quantified(quant) => self.collect_atoms_in(&quant.body, variables),
            TermKind::Let(_) => unreachable!(),
        }
    }

    fn init_order(&mut self, quantifiers: &[Quantifier]) {
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
            // which is conceptually similar to how also levels in the BDD are higher.
            for q in quantifiers.iter().rev() {
                let vars = m.add_vars(BLOCK);
                self.order.push(OrderBlock {
                    target: Some(q.target.clone()),
                    start: vars.start,
                    len: AtomicU32::new(0),
                    capacity: RwLock::new(BLOCK),
                })
            }

            // last block for atoms corresponding to QE calls
            let vars = m.add_vars(BLOCK);
            self.order.push(OrderBlock {
                target: None,
                start: vars.start,
                len: AtomicU32::new(0),
                capacity: RwLock::new(BLOCK),
            });
        })
    }

    fn cutoff(&self, variable: &Variable) -> Option<LevelNo> {
        let index = self.variables.by_key(variable)?;
        let var = self.order[index + 1].start;
        let level = self.manager.with_manager_shared(|m| m.var_to_level(var));

        Some(level)
    }

    fn qe(mut self, quantifiers: Vec<Quantifier>, body: Term, strategy: Strategy) -> Result<Term> {
        let (quantifiers, ranges, body) = self.setup(quantifiers, &body);

        let manager = self.manager.clone();
        let this = Arc::new_cyclic(|weak| QE {
            this: weak.clone(),
            ..self
        });
        let main =
            manager.spawn(async move { this.qe_in(quantifiers, ranges, body, strategy).await });

        futures::executor::block_on(main)
    }

    async fn qe_in(
        &self,
        quantifiers: Vec<Quantifier>,
        ranges: Vec<Range<usize>>,
        body: Term,
        strategy: Strategy,
    ) -> Result<Term> {
        let mut prevq = smt::Quantifier::Exists;
        eprint!("compiling initial bdd...");
        let mut body = self.bdd(&body, BddMode::Fine, Insertion::Earliest)?;
        eprintln!(
            "compiled (size {})!",
            body.with_manager_shared(|m, _| m.num_inner_nodes())
        );
        self.print_atoms();
        for range in ranges {
            let quantifier = quantifiers[range.clone()][0].quantifier;
            let variables = quantifiers[range]
                .iter()
                .map(|q| q.target.clone())
                .collect_vec();

            eprint!("eliminating",);
            for variable in &variables {
                eprint!(" {}", variable.name());
            }
            eprint!(" ...");

            if prevq != quantifier {
                body = body.not()?;
            }
            prevq = quantifier;

            if strategy == Strategy::Immediate
                && variables.iter().all(|v| *v.sort() == Core::Bool())
            {
                body = self.project(&variables, body)?;
                eprintln!(" eliminated with Boolean projection!")
            } else {
                body = self.eliminate(variables, body, strategy).await?;
                eprintln!(" eliminated!");
            }
        }

        if prevq == smt::Quantifier::Forall {
            body = body.not()?;
        }

        self.term(&body).await
    }

    #[allow(unused)]
    fn print_atoms(&self) {
        self.manager.with_manager_exclusive(|m| {
            eprintln!("atoms:");
            for (i, block) in self.order.iter().enumerate() {
                match &block.target {
                    Some(target) => eprint!("- `{}` ", target.name()),
                    None if i == 0 => eprint!("- irrelevant variables "),
                    None => eprint!("- local QE surrogates "),
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
                            eprintln!("{atom}");
                        }
                        None => {
                            eprintln!();
                        }
                    }
                }
            }
        })
    }

    fn top(&self) -> BDD {
        self.top.clone()
    }

    fn bottom(&self) -> BDD {
        self.bottom.clone()
    }

    #[allow(unused)]
    fn project(&self, targets: &[Variable], body: BDD) -> Result<BDD> {
        let targets = targets.iter().map(|v| v.to_term_in(&*self.pool));
        let vars = targets
            .into_iter()
            .map(|v| self.atom(v, Insertion::Earliest))
            .collect_vec();
        let bdds: Vec<_> = self
            .manager
            .with_manager_shared(|m| vars.into_iter().map(|v| BDD::var(m, v)).try_collect())?;
        let all = bdds
            .into_iter()
            .try_fold(self.top(), |acc, arg| acc.and(&arg))?;

        Ok(body.exists(&all)?)
    }

    async fn eliminate(
        &self,
        targets: Vec<Variable>,
        body: BDD,
        strategy: Strategy,
    ) -> Result<BDD> {
        let cache = Arc::new(MemoMap::new(self.manager.clone()));
        self.arc()
            .eliminate_in(targets, body, strategy, cache)
            .await
    }

    #[async_recursion]
    async fn eliminate_in(
        self: Arc<Self>,
        targets: Vec<Variable>,
        body: BDD,
        strategy: Strategy,
        cache: Arc<MemoMap<BDD, Result<BDD>>>,
    ) -> Result<BDD> {
        cache
            .clone()
            .get_or_insert(body, async move |body| match body.cofactors() {
                Some((high, low)) => {
                    let (level, guard) = body.with_manager_shared(|m, edge| -> Result<_> {
                        let Node::Inner(node) = m.get_node(edge) else {
                            unreachable!()
                        };
                        let level = node.level();
                        let var = m.level_to_var(level);

                        Ok((level, BDD::var(m, var)?))
                    })?;

                    let cutoff = self.cutoff(targets.last().unwrap()).unwrap();
                    if level < cutoff {
                        let m = self.manager.clone();
                        let self2 = self.clone();
                        let targets2 = targets.clone();
                        let cache2 = cache.clone();
                        let high = m.spawn(self.eliminate_in(targets, high, strategy, cache));
                        let low = m.spawn(self2.eliminate_in(targets2, low, strategy, cache2));

                        Ok(guard.ite(&high.await?, &low.await?)?)
                    } else {
                        let env = self.env.clone();
                        let pool = self.pool.clone();
                        let backend = self.backend;
                        let this = self.clone();
                        let qe = async move || -> Result<Term> {
                            let quant = Quantified {
                                quantifier: smt::Quantifier::Exists,
                                variables: Arc::from(targets.into_boxed_slice()),
                                body: this.clone().term(&body).await?,
                                span: None,
                            }
                            .into_term_in(&*pool);

                            let manager = TermManager::with_pool(backend, pool.clone())?;
                            let mut solver = Solver::with_manager(&Config::default(), manager)?;
                            solver.import(env)?;

                            let eliminated = solver.qe(quant)?;

                            Ok(eliminated)
                        };

                        match strategy {
                            Strategy::Immediate => {
                                let eliminated = qe().await?;
                                self.bdd(&eliminated, BddMode::Coarse, Insertion::Bottom)
                            }
                            Strategy::Delayed => {
                                let var = self.new_var(None);
                                self.partials.provide(var, async move |_| qe().await);
                                Ok(self.manager.with_manager_shared(|m| BDD::var(m, var))?)
                            }
                        }
                    }
                }
                None => Ok(body),
            })
            .await
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
    fn new_var(&self, index: Option<usize>) -> VarNo {
        let block = match index {
            Some(index) => &self.order[index],
            None => &self.order[self.order.len() - 1],
        };

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

        // here we have the old `len` we reserved before, and we know *at least* one
        // reallocation happened if needed at all.
        self.manager
            .with_manager_shared(|m| m.level_to_var(m.var_to_level(block.start) + len))
    }

    fn atom(&self, term: Term, insertion: Insertion) -> VarNo {
        let size = self.atoms.size();
        self.atoms.by_key_or_insert(term, |term| {
            // block zero is for atoms mentioning no variables to be eliminated.
            // other blocks are at variable's index + 1. The last block is the "bottom" block.
            let index = match insertion {
                Insertion::Earliest => match self.earliest(term) {
                    Some(variable) => Some(self.variables.by_key(&variable).unwrap() + 1),
                    None => Some(0),
                },
                Insertion::Bottom => None,
            };

            let var = self.new_var(index);

            self.manager
                .workers()
                .set_split_depth(Some(std::cmp::max(15, (size / 4 * 3) as u32)));

            var
        })
    }

    fn earliest(&self, term: &Term) -> Option<Variable> {
        let free = self.free(term);
        free.last_one()
            .map(|index| self.variables.by_index(&index).unwrap())
    }

    fn free(&self, term: &Term) -> BitSet {
        self.free_in(term, &mut HashMap::new())
    }

    #[allow(clippy::mutable_key_type)]
    fn free_in(&self, term: &Term, cache: &mut HashMap<Term, BitSet>) -> BitSet {
        if let Some(bits) = cache.get(term) {
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

        cache.insert(term.clone(), bits.clone());

        bits
    }

    fn has_booleans(&self, term: &Term) -> bool {
        (self.free(term) & &self.booleans).any()
    }

    fn bdd(&self, term: &Term, construction: BddMode, insertion: Insertion) -> Result<BDD> {
        self.bdd_in(term, construction, insertion, &mut HashMap::new())
    }

    #[allow(clippy::mutable_key_type)]
    fn bdd_in(
        &self,
        term: &Term,
        mode: BddMode,
        insertion: Insertion,
        cache: &mut HashMap<Term, BDD>,
    ) -> Result<BDD> {
        if let Some(bdd) = cache.get(term) {
            return Ok(bdd.clone());
        }

        let term = term.simplified(&*self.pool);

        if mode == BddMode::Coarse && !self.has_booleans(&term) {
            if term == true {
                return Ok(self.top());
            }
            if term == false {
                return Ok(self.bottom());
            }

            let var = self.atom(term.clone(), Insertion::Bottom);
            let bdd = self.manager.with_manager_shared(|m| BDD::var(m, var))?;
            cache.insert(term, bdd.clone());
            return Ok(bdd);
        }

        let bdd = match term.kind() {
            TermKind::Atom(atom) => {
                if let Ok(atom) = CoreAtom::try_from(atom) {
                    match atom {
                        CoreAtom::True => self.top(),
                        CoreAtom::False => self.bottom(),
                        CoreAtom::Not(arg) => self.bdd_in(arg, mode, insertion, cache)?.not()?,
                        CoreAtom::Implies(args) => args
                            .iter()
                            .enumerate()
                            .map(|(i, arg)| {
                                if i == args.len() - 1 {
                                    self.bdd_in(arg, mode, insertion, cache)
                                } else {
                                    Ok(self.bdd_in(arg, mode, insertion, cache)?.not()?)
                                }
                            })
                            .try_fold(self.bottom(), |acc, arg| Ok::<_, Error>(acc.or(&arg?)?))?,
                        CoreAtom::And(args) => args
                            .iter()
                            .map(|arg| self.bdd_in(arg, mode, insertion, cache))
                            .try_fold(self.top(), |acc, arg| Ok::<_, Error>(acc.and(&arg?)?))?,
                        CoreAtom::Or(args) => args
                            .iter()
                            .map(|arg| self.bdd_in(arg, mode, insertion, cache))
                            .try_fold(self.bottom(), |acc, arg| Ok::<_, Error>(acc.or(&arg?)?))?,
                        CoreAtom::Xor(args) => args
                            .iter()
                            .map(|arg| self.bdd_in(arg, mode, insertion, cache))
                            .try_fold(self.bottom(), |acc, arg| Ok::<_, Error>(acc.xor(&arg?)?))?,
                        CoreAtom::Ite(guard, high, low) => {
                            let guard = self.bdd_in(guard, mode, insertion, cache)?;
                            let high = self.bdd_in(high, mode, insertion, cache)?;
                            let low = self.bdd_in(low, mode, insertion, cache)?;

                            guard.ite(&high, &low)?
                        }
                        CoreAtom::Equals(args) | CoreAtom::Distinct(args) => {
                            if Sort::of(&args[0]).unwrap() == Core::Bool() {
                                let bdds: Vec<_> = args
                                    .iter()
                                    .map(|t| self.bdd_in(t, mode, insertion, cache))
                                    .try_collect()?;

                                if let CoreAtom::Equals(_) = atom {
                                    let mut acc = self.top();
                                    for (a, b) in bdds.into_iter().tuple_windows() {
                                        acc = acc.and(&a.imp(&b)?.and(&b.imp(&a)?)?)?;
                                    }
                                    acc
                                } else {
                                    let mut acc = self.bottom();
                                    for (a, b) in bdds.into_iter().tuple_windows() {
                                        acc =
                                            acc.or(&a.and(&b.not()?)?.or(&b.and(&a.not()?)?)?)?;
                                    }
                                    acc
                                }
                            } else {
                                let var = self.atom(term.simplified(&*self.pool), insertion);
                                self.manager.with_manager_shared(|m| BDD::var(m, var))?
                            }
                        }
                    }
                } else {
                    let var = self.atom(term.simplified(&*self.pool), insertion);
                    self.manager.with_manager_shared(|m| BDD::var(m, var))?
                }
            }
            _ => unreachable!(),
        };

        cache.insert(term.clone(), bdd.clone());

        Ok(bdd)
    }

    #[allow(clippy::mutable_key_type)]
    async fn term(&self, bdd: &BDD) -> Result<Term> {
        Ok(self
            .term_in(bdd.clone(), &mut HashMap::new())
            .await?
            .simplified(&*self.pool))
    }

    #[allow(clippy::mutable_key_type)]
    fn term_in<'s>(
        &'s self,
        bdd: BDD,
        cache: &'s mut HashMap<BDD, Term>,
    ) -> Pin<Box<dyn 's + Send + Future<Output = Result<Term>>>> {
        Box::pin(async move {
            if let Some(term) = cache.get(&bdd) {
                return Ok(term.clone());
            }

            let term = match bdd.cofactors() {
                Some((high, low)) => {
                    let guard = self.manager.with_manager_shared(|m| {
                        let edge = bdd.as_edge(m);
                        let Node::Inner(node) = m.get_node(edge) else {
                            unreachable!()
                        };
                        m.level_to_var(node.level())
                    });

                    let guard = match self.atoms.by_index(&guard) {
                        Some(guard) => guard,
                        None => self.partials.get(&guard).unwrap().get().await.clone()?,
                    };

                    let high = self.term_in(high, cache).await?;
                    let low = self.term_in(low, cache).await?;

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
            Ok(term)
        })
    }
}
