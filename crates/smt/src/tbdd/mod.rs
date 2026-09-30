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
    smt::{
        self, Config, Env, Function, FunctionRef, Quantified, Quantifier, Solver, Sort, Term,
        TermKind, TermPool, ToTerm, Variable,
        backends::Backend,
        theories::{Core, CoreAtom},
    },
    support::{Diagnosable, DiagnosticEmitted, Located, Span},
};

use oxidd::{
    BooleanFunction as _, Function as _, HasLevel, HasWorkers, LevelNo, Manager as _, ManagerRef,
    Node, VarNo, WorkerPool,
    bcdd::{BCDDFunction, BCDDManagerRef},
    error::OutOfMemory,
};

use oxidd_reorder::set_var_order_seq;
use oxidd_rules_bdd::complement_edge::EdgeTag;

use dashmap::{DashMap, Entry};
use itertools::Itertools;
use thiserror::Error;
use transitive::Transitive;

use std::{collections::HashMap, fmt::Debug, hash::Hash, num::NonZero, ops::Deref, sync::Arc};
//
// Given an SMT formula and a set of variables to be existentially eliminated, things to do:
// 1. ✓ collect the atoms to form the set of BDD variables
//    - ✓ collect free variables for each atom/term
// 2. ✓ build the BDD
// 3. ✓ reorder according to the next variable to eliminate
// 4. ✓ traverse to make the local QE calls
// 5. ✓ rebuild (with possibly the new variables corresponding to new atoms)
// 6. go to point 3
// 7. ✓ build a Term out of the BDD
//
// when to make the BDD T-reduced?
//

// type Manager<'m> = <BCDDFunction as oxidd::Function>::Manager<'m>;
// type Edge<'m> = <<BCDDFunction as oxidd::Function>::Manager<'m> as oxidd::Manager>::Edge;

#[derive(Clone, Hash, PartialEq, Eq)]
struct Atom(Term);

impl Deref for Atom {
    type Target = Term;

    fn deref(&self) -> &Term {
        &self.0
    }
}

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
    pool: &(dyn TermPool + Send + Sync),
    env: Env,
    backend: &'static dyn Backend,
    jobs: Option<NonZero<u32>>,
) -> Result<Term, Error> {
    qe_in(term, pool, env, backend, jobs, &HashMap::new())
}

#[allow(clippy::mutable_key_type)]
fn qe_in(
    term: &Term,
    pool: &(dyn TermPool + Send + Sync),
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
                        .map(|arg| qe_in(arg, pool, env.clone(), backend, jobs, bindings))
                        .try_collect()?,
                    span: atom.span(),
                }
                .into_term_in(pool))
            }
        }
        TermKind::Quantified(Quantified { quantifier, .. }) => {
            let mut variables = Vec::new();
            let mut body = term.clone();

            while let TermKind::Quantified(quant) = body.kind()
                && quant.quantifier == *quantifier
            {
                variables.extend(quant.variables.iter().cloned());
                body = quant.body.clone();
            }

            let quant = Quantified {
                quantifier: *quantifier,
                variables: Arc::from(variables.into_boxed_slice()),
                body: qe_in(&body, pool, env.clone(), backend, jobs, bindings)?,
                span: term.span(),
            };

            QE::new(pool, env, backend, jobs).qe(quant)
        }
        TermKind::Let(let_) => {
            let mut nested = bindings.clone();
            for bind in &*let_.bindings {
                nested.insert(
                    bind.variable.clone(),
                    qe_in(&bind.def, pool, env.clone(), backend, jobs, bindings)?,
                );
            }
            qe_in(&let_.body, pool, env, backend, jobs, &nested)
        }
    }
}

struct QE<'p> {
    manager: BCDDManagerRef,
    pool: &'p (dyn TermPool + Send + Sync),
    env: Env,
    backend: &'static dyn Backend,
    atoms: SyncBiMap<Atom, VarNo>,
    variables: SyncBiMap<Variable, usize>,
    free: DashMap<Term, BitSet>,
    mentions: DashMap<(Atom, Variable), bool>,
    bdds: DashMap<Term, BCDDFunction>,
}

impl<'p> QE<'p> {
    pub fn new(
        pool: &'p (dyn TermPool + Send + Sync),
        env: Env,
        backend: &'static dyn Backend,
        jobs: Option<NonZero<u32>>,
    ) -> QE<'p> {
        let jobs = jobs.map(NonZero::get).unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(NonZero::get)
                .unwrap_or(1) as u32
        });
        QE {
            manager: oxidd::bcdd::new_manager(268_435_456, 1_048_576, jobs),
            pool,
            env,
            backend,
            atoms: SyncBiMap::new(),
            variables: SyncBiMap::new(),
            free: DashMap::new(),
            mentions: DashMap::new(),
            bdds: DashMap::new(),
        }
    }

    fn qe(self, quant: Quantified) -> Result<Term, Error> {
        for (index, var) in quant.variables.iter().cloned().enumerate() {
            self.variables.insert(var, index)
        }

        eprintln!("building initial BDD...");
        let bdd = self.bdd(&quant.body)?;
        eprintln!("initial BDD built!");

        self.stats();

        let result = match quant.quantifier {
            Quantifier::Exists => self.qe_exists(&quant.variables, bdd)?,
            Quantifier::Forall => self.qe_forall(&quant.variables, bdd)?,
        };

        eprintln!("exporting result...");
        let term = self.term(&result);
        eprintln!("result exported!");

        let size = term.size();

        eprintln!("QE finished ({size} nodes), collecting shared subterms...");

        let term = smt::Let::collect(&term, self.pool)?;

        let size_after = term.size();
        eprintln!("shared subterms collected! (size {size_after})");

        Ok(term)
    }

    fn qe_exists(
        &self,
        variables: &[Variable],
        mut body: BCDDFunction,
    ) -> Result<BCDDFunction, Error> {
        self.manager.workers().install(|| {
            for variable in variables {
                // eprintln!("reordering...");
                // let cutoff = self.reorder(var.clone());
                let cutoff = self.cutoff(variable);
                eprintln!(
                    "eliminating variable {} (cutoff {})",
                    variable.name(),
                    cutoff
                );
                body = self.eliminate(variable.clone(), cutoff, &body)?;
                eprintln!("variable {} eliminated!", variable.name());
            }
            Ok(body)
        })
    }

    #[allow(unused)]
    fn qe_forall(&self, variables: &[Variable], body: BCDDFunction) -> Result<BCDDFunction, Error> {
        Ok(self.qe_exists(variables, body.not()?)?.not()?)
    }

    fn earliest_mention(&self, atom: &Atom) -> Option<Variable> {
        let index = self.free(&atom.0).first_one()?;
        Some(self.variables.by_index(&index).unwrap())
    }

    fn insertion_level(&self, atom: &Atom, vars: &[VarNo]) -> LevelNo {
        match self.earliest_mention(atom) {
            Some(earliest) => {
                for (level, var) in vars.iter().enumerate() {
                    let atom = self.atoms.by_index(var).unwrap();
                    if self.mentions(atom, &earliest) {
                        return level as LevelNo;
                    }
                }
                vars.len() as LevelNo
            }
            None => 0,
        }
    }

    fn mentions(&self, atom: Atom, variable: &Variable) -> bool {
        match self.mentions.entry((atom.clone(), variable.clone())) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let free = self.free(atom.clone());
                let index = self.variables.by_key(variable).unwrap();
                let mentions = free.get(index);

                entry.insert(mentions);

                mentions
            }
        }
    }

    fn atom(&self, atom: Atom) -> VarNo {
        self.manager.with_manager_exclusive(|m| {
            self.atoms.by_key_or_insert(atom, |atom| {
                let mut vars: Vec<_> = (0..m.num_levels())
                    .into_iter()
                    .map(|l| m.level_to_var(l))
                    .collect();
                let var = m.add_vars(1).start;
                let level = self.insertion_level(atom, &vars);
                vars.insert(level as usize, var);

                set_var_order_seq(m, &vars);

                var
            })
        })
    }

    fn cutoff(&self, variable: &Variable) -> LevelNo {
        self.manager.with_manager_shared(|m| {
            let levels = m.num_levels();
            for level in 0..levels {
                let var = m.level_to_var(level);
                let atom = self.atoms.by_index(&var).unwrap();
                if self.mentions(atom, variable) {
                    return level;
                }
            }
            m.num_levels()
        })
    }

    fn top(&self) -> BCDDFunction {
        self.manager.with_manager_shared(|m| BCDDFunction::t(m))
    }

    fn bottom(&self) -> BCDDFunction {
        self.manager.with_manager_shared(|m| BCDDFunction::f(m))
    }

    fn stats(&self) {
        eprintln!("stats:");
        eprintln!(" - variables: ");
        eprint!("   -");
        for index in 0..self.variables.size() {
            let var = self.variables.by_index(&index).unwrap();
            print!(" {}", var.name());
        }
        println!();
        eprintln!(" - atoms ({}):", self.atoms.size());
        self.manager.with_manager_shared(|m| {
            for level in 0..m.num_levels() {
                eprint!("   {}.", level);
                let var = m.level_to_var(level);
                let atom = self.atoms.by_index(&var).unwrap();

                let free = self.free(atom.clone());
                for index in 0..free.len() {
                    if free.get(index) {
                        let variable = self.variables.by_index(&index).unwrap();
                        eprint!(" {} ", variable.name());
                    }
                }
                eprintln!()
            }
        })
    }

    #[allow(clippy::mutable_key_type)]
    fn eliminate(
        &self,
        var: Variable,
        cutoff: LevelNo,
        bdd: &BCDDFunction,
    ) -> Result<BCDDFunction, Error> {
        let cache = DashMap::new();
        self.eliminate_in(var, cutoff, bdd, &cache)
    }

    #[allow(clippy::mutable_key_type)]
    fn eliminate_in(
        &self,
        var: Variable,
        cutoff: LevelNo,
        bdd: &BCDDFunction,
        cache: &DashMap<BCDDFunction, BCDDFunction>,
    ) -> Result<BCDDFunction, Error> {
        if let Some(result) = cache.get(bdd) {
            return Ok(result.clone());
        }

        let result = match bdd.cofactors() {
            Some((high, low)) => {
                let (level, guard) = bdd.with_manager_shared(|m, edge| -> Result<_, Error> {
                    let Node::Inner(node) = m.get_node(edge) else {
                        unreachable!()
                    };
                    let level = node.level();
                    let var = m.level_to_var(level);

                    Ok((level, BCDDFunction::var(m, var)?))
                })?;

                if level <= cutoff {
                    let (high, low) = self.manager.workers().join(
                        || self.eliminate_in(var.clone(), cutoff, &high, cache),
                        || self.eliminate_in(var.clone(), cutoff, &low, cache),
                    );
                    let high = high?;
                    let low = low?;

                    guard.ite(&high, &low)?
                } else {
                    let quant = Quantified {
                        quantifier: Quantifier::Exists,
                        variables: Arc::new([var]),
                        body: self.term(bdd),
                        span: None,
                    }
                    .into_term_in(self.pool);

                    let mut solver = Solver::with_backend(&Config::default(), self.backend)?;
                    solver.import(self.env.clone())?;

                    eprintln!("invoking QE backend...");
                    let eliminated = solver.qe(quant)?;
                    eprintln!("QE backend invoked!");

                    self.bdd(&eliminated)?
                }
            }
            None => bdd.clone(),
        };

        cache.insert(bdd.clone(), result.clone());

        Ok(result)
    }

    fn bdd(&self, term: &Term) -> Result<BCDDFunction, Error> {
        if let Some(bdd) = self.bdds.get(term) {
            return Ok(bdd.clone());
        }

        let bdd = match term.kind() {
            TermKind::Atom(atom) => {
                if let Ok(atom) = CoreAtom::try_from(atom) {
                    match atom {
                        CoreAtom::True => self.top(),
                        CoreAtom::False => self.bottom(),
                        CoreAtom::Not(arg) => self.bdd(arg)?.not()?,
                        CoreAtom::Implies(args) => {
                            let bdds: Vec<_> =
                                args.iter().map(|arg| self.bdd(arg)).try_collect()?;
                            bdds.into_iter()
                                .rev()
                                .try_fold(self.bottom(), |acc, arg| acc.imp(&arg))?
                        }
                        CoreAtom::And(args) => {
                            let bdds: Vec<_> =
                                args.iter().map(|arg| self.bdd(arg)).try_collect()?;
                            bdds.into_iter()
                                .try_fold(self.top(), |acc, arg| acc.and(&arg))?
                        }
                        CoreAtom::Or(args) => {
                            let bdds: Vec<_> =
                                args.iter().map(|arg| self.bdd(arg)).try_collect()?;
                            bdds.into_iter()
                                .try_fold(self.bottom(), |acc, arg| acc.or(&arg))?
                        }
                        CoreAtom::Xor(args) => {
                            let bdds: Vec<_> =
                                args.iter().map(|arg| self.bdd(arg)).try_collect()?;
                            bdds.into_iter()
                                .try_fold(self.bottom(), |acc, arg| acc.xor(&arg))?
                        }
                        CoreAtom::Ite(guard, then, else_) => {
                            let guard = self.bdd(guard)?;
                            let then = self.bdd(then)?;
                            let else_ = self.bdd(else_)?;

                            guard.ite(&then, &else_)?
                        }
                        CoreAtom::Equals(_) | CoreAtom::Distinct(_) => {
                            let var = self.atom(Atom(term.clone()));
                            self.manager
                                .with_manager_shared(|m| BCDDFunction::var(m, var))?
                        }
                    }
                } else if let Ok(sort) = Sort::of(term)
                    && sort == Core::Bool()
                {
                    let var = self.atom(Atom(term.clone()));
                    self.manager
                        .with_manager_shared(|m| BCDDFunction::var(m, var))?
                } else {
                    unreachable!();
                }
            }
            TermKind::Constant(_) => unreachable!(),
            TermKind::Quantified(_) => unreachable!(),
            TermKind::Let(_) => unreachable!(),
        };

        self.bdds.insert(term.clone(), bdd.clone());

        Ok(bdd)
    }

    #[allow(clippy::mutable_key_type)]
    fn term(&self, bdd: &BCDDFunction) -> Term {
        let mut cache = HashMap::new();
        self.term_in(bdd, &mut cache)
    }

    #[allow(clippy::mutable_key_type)]
    fn term_in<'m>(&self, bdd: &BCDDFunction, cache: &mut HashMap<BCDDFunction, Term>) -> Term {
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
                        .0
                });

                let high = self.term_in(&high, cache);
                let low = self.term_in(&low, cache);

                if high == true && low == false {
                    guard
                } else if high == false && low == true {
                    Core::not().call([guard]).into_term_in(&*self.pool)
                } else if low == true {
                    Core::implies()
                        .call([guard, high])
                        .into_term_in(&*self.pool)
                } else if low == false {
                    Core::and().call([guard, high]).into_term_in(&*self.pool)
                } else if high == true {
                    Core::or().call([guard, low]).into_term_in(&*self.pool)
                } else {
                    Core::ite()
                        .call([guard, high, low])
                        .into_term_in(&*self.pool)
                }
            }
            None => bdd.with_manager_shared(|_, edge| match edge.tag() {
                EdgeTag::None => Core::True().into_term_in(&*self.pool),
                EdgeTag::Complemented => Core::False().into_term_in(&*self.pool),
            }),
        };

        cache.insert(bdd.clone(), term.clone());
        term
    }

    fn free(&self, term: impl Deref<Target = Term>) -> BitSet {
        if let Some(bits) = self.free.get(&term) {
            return bits.clone();
        }

        let bits = match term.kind() {
            TermKind::Constant(_) => BitSet::new(),
            TermKind::Atom(atom) => {
                let mut bits = BitSet::new();
                if let FunctionRef::Bound(bound) = &atom.head
                    && let Function::Variable(var) = &bound.function
                    && let Some(index) = self.variables.by_key(var)
                {
                    bits.set(index, true);
                }
                for arg in &*atom.arguments {
                    bits |= self.free(arg);
                }

                bits
            }
            TermKind::Quantified(_) => unreachable!(),
            TermKind::Let(let_) => {
                let mut bits = self.free(&let_.body);
                for bind in &*let_.bindings {
                    if let Some(index) = self.variables.by_key(&bind.variable) {
                        bits.set(index, false)
                    }
                }
                bits
            }
        };
        self.free.insert(term.clone(), bits.clone());

        bits
    }
}
