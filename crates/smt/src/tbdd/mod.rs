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
        Config, Function, FunctionRef, Quantified, Quantifier, Solver, Sort, Term, TermKind,
        TermManager, TermPool, ToTerm, Variable,
        backends::{Backend, cvc5::Cvc5},
        qe,
        theories::{Core, CoreAtom},
    },
    support::{Diagnosable, DiagnosticEmitted, Level, Located, Span},
};

use oxidd::{
    BooleanFunction as _, Function as _, HasLevel, LevelNo, Manager as _, ManagerRef, Node, VarNo,
    bdd::{BDDFunction, BDDManagerRef},
    error::OutOfMemory,
};

use oxidd_reorder::set_var_order;
use oxidd_rules_bdd::simple::BDDTerminal;

use dashmap::DashMap;
use itertools::{Itertools, partition};
use thiserror::Error;
use transitive::Transitive;

use std::{collections::HashMap, fmt::Debug, hash::Hash, ops::Deref, sync::Arc};
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

type Manager<'m> = <BDDFunction as oxidd::Function>::Manager<'m>;
type Edge<'m> = <<BDDFunction as oxidd::Function>::Manager<'m> as oxidd::Manager>::Edge;

#[derive(Clone, Hash, PartialEq, Eq)]
struct Atom(Term);

impl Deref for Atom {
    type Target = Term;

    fn deref(&self) -> &Term {
        &self.0
    }
}

#[derive(Debug, Error, Located, Transitive)]
#[transitive(from(OutOfMemory, ErrorKind))]
#[transitive(from(Box<dyn Diagnosable>, ErrorKind))]
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
    #[error("building T-BDDs for let expressions is not (yet) supported")]
    UnsupportedLet,
    #[error(transparent)]
    Backend(#[from] Box<dyn Diagnosable>),
}

impl Diagnosable for Error {
    fn level(&self) -> Level {
        match &self.kind {
            ErrorKind::Backend(err) => err.level(),
            _ => Level::Error,
        }
    }

    fn notes(&self) -> DiagnosticEmitted {
        match &self.kind {
            ErrorKind::Backend(err) => err.notes(),
            _ => DiagnosticEmitted,
        }
    }
}

pub struct QE {
    manager: BDDManagerRef,
    pool: Arc<dyn TermPool + Send + Sync>,
    solver: Solver,
    atoms: SyncBiMap<Atom, VarNo>,
    vars: SyncBiMap<Variable, usize>,
    free: DashMap<Term, BitSet>,
    bdds: DashMap<Term, BDDFunction>,
}

impl qe::Backend for QE {
    fn qe(&self, quant: Quantified) -> Result<Term, Box<dyn Diagnosable>> {
        match quant.quantifier {
            Quantifier::Exists => {
                let mut result = self
                    .bdd(&quant.body)
                    .map_err(|err| Box::new(err) as Box<dyn Diagnosable>)?;
                for var in &*quant.variables {
                    let cutoff = self.reorder(var.clone());
                    result = self
                        .eliminate(var.clone(), cutoff, &result)
                        .map_err(|err| Box::new(err) as Box<dyn Diagnosable>)?;
                }

                Ok(result.with_manager_shared(|m, edge| self.term(m, edge)))
            }
            Quantifier::Forall => todo!(),
        }
    }

    fn pool(&self) -> Arc<dyn TermPool> {
        self.pool.clone()
    }
}

impl QE {
    pub fn new(pool: Arc<dyn TermPool + Send + Sync>) -> QE {
        QE {
            manager: oxidd::bdd::new_manager(65_536, 65_536, 1),
            pool: pool.clone(),
            solver: Solver::with_manager(
                &Config::default(),
                TermManager::with_pool(Cvc5, pool).unwrap(),
            )
            .unwrap(),
            atoms: SyncBiMap::new(),
            vars: SyncBiMap::new(),
            free: DashMap::new(),
            bdds: DashMap::new(),
        }
    }

    fn atom(&self, atom: Atom) -> VarNo {
        self.manager
            .with_manager_exclusive(|m| self.atoms.by_key_or_insert(atom, || m.add_vars(1).start))
    }

    fn variable(&self, var: Variable) -> usize {
        self.vars.by_key_or_insert(var, || self.vars.size())
    }

    fn top(&self) -> BDDFunction {
        self.manager.with_manager_shared(|m| BDDFunction::t(m))
    }

    fn bottom(&self) -> BDDFunction {
        self.manager.with_manager_shared(|m| BDDFunction::f(m))
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

    fn eliminate<'m>(
        &self,
        var: Variable,
        cutoff: LevelNo,
        bdd: &BDDFunction,
    ) -> Result<BDDFunction, Error> {
        bdd.with_manager_shared(|m, edge| self.eliminate_(m, var, cutoff, edge))
    }

    fn eliminate_<'m>(
        &self,
        m: &Manager<'m>,
        var: Variable,
        cutoff: LevelNo,
        edge: &Edge<'m>,
    ) -> Result<BDDFunction, Error> {
        match m.get_node(edge) {
            Node::Inner(node) if node.level() < cutoff => {
                let guard = BDDFunction::var(m, m.level_to_var(node.level()))?;
                let (high, low) = BDDFunction::cofactors_edge(m, edge).unwrap();
                let high = self.eliminate_(m, var.clone(), cutoff, &high)?;
                let low = self.eliminate_(m, var, cutoff, &low)?;

                Ok(guard.ite(&high, &low)?)
            }
            Node::Inner(_) => {
                let quant = Quantified {
                    quantifier: Quantifier::Exists,
                    variables: Arc::new([var]),
                    body: self.term(m, edge),
                    span: None,
                };

                let cvc5 = Cvc5
                    .solver(&Config::default(), Cvc5.manager().unwrap().into())
                    .unwrap();
                let qe = cvc5.as_qe(self.pool.clone()).unwrap();
                let eliminated = qe.qe(quant)?;

                Ok(self.bdd(&eliminated)?)
            }
            Node::Terminal(t) => match t {
                BDDTerminal::False => Ok(BDDFunction::f(m)),
                BDDTerminal::True => Ok(BDDFunction::t(m)),
            },
        }
    }

    fn bdd(&self, term: &Term) -> Result<BDDFunction, Error> {
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
                                .with_manager_shared(|m| BDDFunction::var(m, var))?
                        }
                    }
                } else if let Ok(sort) = Sort::of(term)
                    && sort == Core::Bool()
                {
                    let var = self.atom(Atom(term.clone()));
                    self.manager
                        .with_manager_shared(|m| BDDFunction::var(m, var))?
                } else {
                    unreachable!();
                }
            }
            TermKind::Constant(_) => unreachable!(),
            TermKind::Quantified(_) => unreachable!(),
            TermKind::Let(_) => {
                return Err(Error {
                    kind: ErrorKind::UnsupportedLet,
                    span: None,
                });
            }
        };

        self.bdds.insert(term.clone(), bdd.clone());

        Ok(bdd)
    }

    fn term<'m>(&self, m: &Manager<'m>, bdd: &Edge<'m>) -> Term {
        let mut cache = HashMap::new();
        self.term_in(m, &BDDFunction::from_edge_ref(m, bdd), &mut cache)
    }

    fn term_in<'m>(
        &self,
        m: &Manager<'m>,
        bdd: &BDDFunction,
        cache: &mut HashMap<BDDFunction, Term>,
    ) -> Term {
        if let Some(term) = cache.get(bdd) {
            return term.clone();
        }

        let edge = bdd.as_edge(m);
        let term = match m.get_node(edge) {
            Node::Inner(node) => {
                let guard = self
                    .atoms
                    .by_index(&m.level_to_var(node.level()))
                    .unwrap()
                    .0;
                let (high, low) = BDDFunction::cofactors_edge(m, edge).unwrap();
                let high = self.term_in(m, &BDDFunction::from_edge_ref(m, &high), cache);
                let low = self.term_in(m, &BDDFunction::from_edge_ref(m, &low), cache);

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
            Node::Terminal(t) => match t {
                BDDTerminal::False => Core::False().into_term_in(&*self.pool),
                BDDTerminal::True => Core::True().into_term_in(&*self.pool),
            },
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
