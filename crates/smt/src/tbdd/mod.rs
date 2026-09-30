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

use oxidd_reorder::set_var_order;
use oxidd_rules_bdd::complement_edge::EdgeTag;

use dashmap::DashMap;
use itertools::{Itertools, partition};
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
struct Error {
    pub kind: ErrorKind,
    pub span: Option<Span>,
}

impl From<ErrorKind> for Error {
    fn from(kind: ErrorKind) -> Self {
        Error { kind, span: None }
    }
}

#[derive(Debug, Error)]
enum ErrorKind {
    #[error("maximum memory usage limit reached for BDD nodes")]
    OutOfMemory(#[from] OutOfMemory),
    #[error("unable to instantiate a new SMT backend")]
    BackendError(#[from] DiagnosticEmitted),
}

impl Diagnosable for Error {}

pub struct QE {
    manager: BCDDManagerRef,
    pool: Arc<dyn TermPool + Send + Sync>,
    env: Env,
    backend: &'static dyn Backend,
    atoms: SyncBiMap<Atom, VarNo>,
    vars: SyncBiMap<Variable, usize>,
    free: DashMap<Term, BitSet>,
    bdds: DashMap<Term, BCDDFunction>,
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
        QE {
            manager: oxidd::bcdd::new_manager(268_435_456, 1_048_576, jobs),
            pool: pool.clone(),
            env,
            backend,
            atoms: SyncBiMap::new(),
            vars: SyncBiMap::new(),
            free: DashMap::new(),
            bdds: DashMap::new(),
        }
    }

    pub fn qe(&self, term: &Term) -> Result<Term, DiagnosticEmitted> {
        self.qe_in(term, &HashMap::new())
    }

    #[allow(clippy::mutable_key_type)]
    fn qe_in(
        &self,
        term: &Term,
        bindings: &HashMap<Variable, Term>,
    ) -> Result<Term, DiagnosticEmitted> {
        match term.kind() {
            TermKind::Constant(_) => Ok(term.clone()),
            TermKind::Atom(atom) => {
                if let FunctionRef::Bound(bound) = &atom.head
                    && let Function::Variable(var) = &bound.function
                    && let Some(term) = bindings.get(var)
                {
                    self.qe_in(term, bindings)
                } else {
                    Ok(smt::Atom {
                        head: atom.head.clone(),
                        arguments: atom
                            .arguments
                            .iter()
                            .map(|arg| self.qe_in(arg, bindings))
                            .try_collect()?,
                        span: atom.span(),
                    }
                    .into_term_in(&*self.pool))
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
                    body: self.qe_in(&body, bindings)?,
                    span: term.span(),
                };

                Ok(self.qe_quant(quant)?)
            }
            TermKind::Let(let_) => {
                let mut nested = bindings.clone();
                for bind in &*let_.bindings {
                    nested.insert(bind.variable.clone(), self.qe_in(&bind.def, bindings)?);
                }
                self.qe_in(&let_.body, &nested)
            }
        }
    }

    fn qe_quant(&self, quant: Quantified) -> Result<Term, Error> {
        match quant.quantifier {
            Quantifier::Exists => self.qe_exists(&quant.variables, &quant.body),
            Quantifier::Forall => self.qe_forall(&quant.variables, &quant.body),
        }
    }

    fn qe_exists(&self, variables: &[Variable], body: &Term) -> Result<Term, Error> {
        let result = self.manager.workers().install(|| -> Result<_, Error> {
            eprintln!("building initial BDD...");
            let mut result = self.bdd(body)?;
            eprintln!("initial BDD built!");
            for var in variables {
                eprintln!("reordering...");
                let cutoff = self.reorder(var.clone());
                eprintln!("eliminating variable {}", var.name());
                result = self.eliminate(var.clone(), cutoff, &result)?;
                eprintln!("variable {} eliminated!", var.name());
            }
            Ok(result)
        })?;

        eprintln!("exporting result...");
        let term = self.term(&result);
        eprintln!("result exported!");

        let size = term.size();

        eprintln!("QE finished ({size} nodes), collecting shared subterms...");

        let term = smt::Let::collect(&term, &*self.pool)?;

        let size_after = term.size();
        eprintln!("shared subterms collected! (size {size_after})");

        Ok(term)
    }

    #[allow(unused)]
    fn qe_forall(&self, variables: &[Variable], body: &Term) -> Result<Term, Error> {
        let neg = Core::not().call([body.clone()]).into_term_in(&*self.pool);
        let elim = self.qe_exists(variables, &neg)?;
        let result = Core::not().call([elim.clone()]).into_term_in(&*self.pool);

        Ok(result)
    }

    fn atom(&self, atom: Atom) -> VarNo {
        self.manager
            .with_manager_exclusive(|m| self.atoms.by_key_or_insert(atom, |_| m.add_vars(1).start))
    }

    fn variable(&self, var: Variable) -> usize {
        self.vars.by_key_or_insert(var, |_| self.vars.size())
    }

    fn top(&self) -> BCDDFunction {
        self.manager.with_manager_shared(|m| BCDDFunction::t(m))
    }

    fn bottom(&self) -> BCDDFunction {
        self.manager.with_manager_shared(|m| BCDDFunction::f(m))
    }

    fn reorder(&self, eliminate: Variable) -> LevelNo {
        let eliminate = self.variable(eliminate);
        let mut bddvars = self.atoms.indexes().collect_vec();

        let cutoff = partition(&mut bddvars, |var| {
            !self.free(self.atoms.by_index(var).unwrap()).get(eliminate)
        });

        self.manager.with_manager_exclusive(|m| {
            set_var_order(m, &bddvars);
            m.var_to_level(bddvars[cutoff])
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

                if level < cutoff {
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
                    .into_term_in(&*self.pool);

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
                {
                    bits.set(self.variable(var.clone()), true);
                }
                for arg in &*atom.arguments {
                    bits |= self.free(arg);
                }

                bits
            }
            TermKind::Quantified(quant) => {
                let mut bits = self.free(&quant.body);
                for var in &*quant.variables {
                    bits.set(self.variable(var.clone()), false)
                }
                bits
            }
            TermKind::Let(let_) => {
                let mut bits = self.free(&let_.body);
                for bind in &*let_.bindings {
                    bits.set(self.variable(bind.variable.clone()), false)
                }
                bits
            }
        };
        self.free.insert(term.clone(), bits.clone());

        bits
    }
}
