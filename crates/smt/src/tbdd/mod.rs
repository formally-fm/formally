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

mod intbimap;
use intbimap::*;

use crate::{Config, Function, FunctionRef, formally};

use formally::smt::{
    Solver, Sort, Term, TermKind, Variable,
    backends::cvc5::Cvc5,
    theories::{Core, CoreAtom},
};

use oxidd::{
    BooleanFunction as _, Manager as _, ManagerRef, VarNo,
    bdd::{BDDFunction, BDDManagerRef},
    error::OutOfMemory,
};

use bitvec::vec::BitVec;
use dashmap::DashMap;
use itertools::Itertools;
use parking_lot::RwLock;
use thiserror::Error;

use std::{fmt::Debug, hash::Hash, ops::Deref};
//
// Given an SMT formula and a set of variables to existentially eliminate, things to do:
// 1. ✓ collect the atoms to form the set of BDD variables
//    - ✓ collect free variables for each atom/term
// 2. ✓ build the BDD
// 3. reorder according to the next variable to eliminate
// 4. traverse to make the local QE calls
// 5. rebuild (with possibly the new variables corresponding to new atoms)
// 6. go to point 3
//
// when to make the BDD T-reduced?
//

#[derive(Clone, Hash, PartialEq, Eq)]
struct Atom(Term);

impl Deref for Atom {
    type Target = Term;

    fn deref(&self) -> &Term {
        &self.0
    }
}

impl Atom {
    pub fn into_term(self) -> Term {
        self.0
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("tried to build a T-BDD for a non-Boolean term")]
    NotBoolean,
    #[error("tried to build a T-BDD for a quantified term")]
    Quantified,
    #[error("maximum memory usage limit reached for BDD nodes")]
    OutOfMemory(#[from] OutOfMemory),
    #[error("building T-BDDs for let expressions is not (yet) supported")]
    UnsupportedLet,
}

type Result<T, E = Error> = std::result::Result<T, E>;

#[derive(Default)]
pub struct Manager {
    inner: RwLock<Inner>,
}

impl Manager {
    pub fn new() -> Manager {
        Manager::default()
    }
}

struct Inner {
    manager: BDDManagerRef,
    solver: Solver,
    atoms: IntBiMap<Atom, VarNo>,
    vars: IntBiMap<Variable, usize>,
    free: DashMap<Term, BitVec>,
    bdds: DashMap<Term, BDDFunction>,
}

impl Default for Inner {
    fn default() -> Self {
        Inner {
            manager: oxidd::bdd::new_manager(65_536, 65_536, 1),
            solver: Solver::with_backend(&Config::default(), Cvc5).unwrap(),
            atoms: IntBiMap::new(),
            vars: IntBiMap::new(),
            free: DashMap::new(),
            bdds: DashMap::new(),
        }
    }
}

impl Inner {
    fn atom(&self, atom: Atom) -> VarNo {
        self.manager.with_manager_exclusive(|m| {
            let var = self.atoms.by_key_or_insert(atom);
            if var >= m.num_vars() {
                let added = m.add_vars(1).start;
                assert_eq!(var, added);
            }

            var
        })
    }

    fn top(&self) -> BDDFunction {
        self.manager.with_manager_shared(|m| BDDFunction::t(m))
    }

    fn bottom(&self) -> BDDFunction {
        self.manager.with_manager_shared(|m| BDDFunction::f(m))
    }

    fn bdd(&self, term: &Term) -> Result<BDDFunction> {
        if let Some(bdd) = self.bdds.get(term) {
            return Ok(bdd.clone());
        }

        let bdd = match term.kind() {
            TermKind::Constant(_) => return Err(Error::NotBoolean),
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
                    return Err(Error::NotBoolean);
                }
            }
            TermKind::Quantified(_) => return Err(Error::Quantified),
            TermKind::Let(_) => return Err(Error::UnsupportedLet),
        };

        self.bdds.insert(term.clone(), bdd.clone());

        Ok(bdd)
    }

    fn free(&self, term: impl Deref<Target = Term>) -> BitVec {
        if let Some(bits) = self.free.get(&term) {
            return bits.clone();
        }

        let bits = match term.kind() {
            TermKind::Constant(_) => BitVec::repeat(false, self.vars.size()),
            TermKind::Atom(atom) => {
                let mut bits = BitVec::repeat(false, self.vars.size());
                if let FunctionRef::Bound(bound) = &atom.head
                    && let Function::Variable(var) = &bound.function
                {
                    bits.set(self.vars.by_key(var).unwrap(), true);
                }
                for arg in &*atom.arguments {
                    let argbits = self.free(arg);
                    bits |= argbits;
                }

                bits
            }
            TermKind::Quantified(quant) => {
                let mut bits = self.free(&quant.body);
                for var in &*quant.variables {
                    bits.set(self.vars.by_key(var).unwrap(), false)
                }
                bits
            }
            TermKind::Let(let_) => {
                let mut bits = self.free(&let_.body);
                for bind in &*let_.bindings {
                    bits.set(self.vars.by_key(&bind.variable).unwrap(), false)
                }
                bits
            }
        };
        self.free.insert(term.clone(), bits.clone());

        bits
    }
}
