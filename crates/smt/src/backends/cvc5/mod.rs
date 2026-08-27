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

mod bindings;

use crate::formally;
use bindings as cvc5;
use formally::smt::{
    self, ToTerm as _,
    backends::{self, Backend, api},
    logic,
    logics::{Logic, LogicEx},
    theories,
};
use std::rc::Rc;

type Result<T, E = backends::Error> = std::result::Result<T, E>;

#[smt::backend]
#[derive(Clone, Copy, Default)]
pub struct Cvc5;

#[derive(Default)]
struct Manager {
    cvc5manager: Rc<cvc5::TermManager>,
}

struct Solver {
    cvc5solver: Rc<cvc5::Solver>,
    logic: &'static dyn Logic,
}

struct Model<'s> {
    solver: &'s Solver,
}

logic! {
    name: ALL,
    theories: [
        theories::Core,
        theories::Ints,
        theories::Reals,
        theories::RealsInts,
        theories::Arrays
    ],
    requirements: [ ]
}

impl Backend for Cvc5 {
    fn name(&self) -> &str {
        "cvc5"
    }

    fn manager(&self) -> Box<dyn backends::Manager> {
        Box::new(api::ManagerFacade::new(Manager::default()))
    }

    fn solver(
        &self,
        config: &smt::Config,
        manager: Rc<dyn backends::Manager>,
    ) -> Result<Box<dyn backends::Solver>> {
        Ok(Box::new(api::SolverFacade::<Solver>::new(
            self, config, manager,
        )?))
    }
}

impl api::Solver for Solver {
    type Manager = Manager;
    type Result = cvc5::Result;
    type Model<'s>
        = Model<'s>
    where
        Self: 's;

    fn new(
        config: &smt::Config,
        logic: Result<Option<&'static dyn Logic>>,
        manager: Rc<Self::Manager>,
    ) -> Result<Self> {
        let cvc5solver = Rc::new(cvc5::Solver::new(manager.cvc5manager.clone()));

        let logic = match logic? {
            Some(logic) => {
                cvc5solver.set_logic(logic.name());
                logic
            }
            None => &ALL,
        };

        let solver = Solver { cvc5solver, logic };

        solver.config(config)?;

        Ok(solver)
    }

    fn logic(&self) -> &dyn Logic {
        self.logic
    }

    fn solver(&self) -> &<Self::Manager as api::Manager>::Solver {
        &self.cvc5solver
    }

    fn config(&self, config: &smt::Config) -> Result<()> {
        if config.produce_models {
            self.cvc5solver.set_option("produce-models", "true")
        } else {
            self.cvc5solver.set_option("produce-models", "false")
        }
        Ok(())
    }

    fn push(&mut self) -> Result<()> {
        self.cvc5solver.push();

        Ok(())
    }

    fn pop(&mut self, n: usize) -> Result<()> {
        self.cvc5solver.pop(n as u32);

        Ok(())
    }

    fn require(&mut self, term: <Self::Manager as api::Manager>::Term) -> Result<()> {
        self.cvc5solver.assert_formula(term);

        Ok(())
    }

    fn check(&self) -> Result<Self::Result> {
        Ok(self.cvc5solver.check_sat())
    }

    fn model(&self) -> Result<Self::Model<'_>> {
        Ok(Model { solver: self })
    }
}

impl api::Model for Model<'_> {
    type Term = cvc5::Term;

    fn value(&self, term: Self::Term) -> Option<Self::Term> {
        Some(self.solver.cvc5solver.get_value(term))
    }
}

impl api::Manager for Manager {
    type ALL = ALL;
    type Backend = Cvc5;
    type Solver = cvc5::Solver;
    type FuncDecl = cvc5::Term;
    type Sort = cvc5::Sort;
    type Term = cvc5::Term;
    const FUNC_DEF_SUPPORTED: bool = true;

    fn backend(&self) -> &Self::Backend {
        &Cvc5
    }

    fn uninterpreted_sort(&self, name: &str) -> Result<cvc5::Sort> {
        Ok(self.cvc5manager.mk_uninterpreted_sort(name))
    }

    fn func_decl(
        &self,
        _solver: &cvc5::Solver,
        name: &str,
        sorts: &[cvc5::Sort],
        range: cvc5::Sort,
    ) -> Result<cvc5::Term> {
        if sorts.is_empty() {
            Ok(self.cvc5manager.mk_const(range, name))
        } else {
            Ok(self
                .cvc5manager
                .mk_const(self.cvc5manager.mk_fun_sort(sorts, range), name))
        }
    }

    fn func_def(
        &self,
        solver: &cvc5::Solver,
        name: &str,
        _sorts: &[cvc5::Sort],
        range: cvc5::Sort,
        variables: &[cvc5::Term],
        body: cvc5::Term,
    ) -> Result<cvc5::Term> {
        Ok(solver.define_fun(name, variables, range, body, false))
    }

    fn variable(&self, name: &str, sort: cvc5::Sort) -> Result<cvc5::Term> {
        Ok(self.cvc5manager.mk_var(sort, name))
    }

    fn application(&self, func: &cvc5::Term, arguments: &[cvc5::Term]) -> Result<cvc5::Term> {
        if arguments.is_empty() {
            return Ok(*func);
        }

        let mut args = Vec::new();
        args.push(*func);
        args.extend(arguments.iter().cloned());

        Ok(self.cvc5manager.mk_term(cvc5::Kind::ApplyUf, &args))
    }

    fn constant(&self, cnst: &smt::Constant) -> Result<cvc5::Term> {
        match cnst {
            smt::Constant::Integer { value, .. } => {
                Ok(self.cvc5manager.mk_integer(&value.to_string()))
            }
            smt::Constant::Rational { value, .. } => {
                Ok(self.cvc5manager.mk_real(&value.to_string()))
            }
        }
    }

    fn quantified(
        &self,
        quantifier: smt::Quantifier,
        variables: &[cvc5::Term],
        body: cvc5::Term,
    ) -> Result<cvc5::Term> {
        let varlist = self
            .cvc5manager
            .mk_term(cvc5::Kind::VariableList, variables);
        let kind = match quantifier {
            smt::Quantifier::Forall => cvc5::Kind::Forall,
            smt::Quantifier::Exists => cvc5::Kind::Exists,
        };

        Ok(self.cvc5manager.mk_term(kind, &[varlist, body]))
    }

    fn sort(
        &self,
        sort: <Self::ALL as LogicEx>::Sort<'_>,
        to_sort: impl Fn(&smt::SortArgument) -> Result<cvc5::Sort>,
        _to_value: impl Fn(&smt::SortArgument) -> Result<&smt::Integer>,
    ) -> Result<cvc5::Sort> {
        Ok(match sort {
            ALL_Sort::Core(sort) => match sort {
                theories::CoreSort::Bool => self.cvc5manager.get_boolean_sort(),
            },
            ALL_Sort::Ints(sort) => match sort {
                theories::IntsSort::Int => self.cvc5manager.get_integer_sort(),
            },
            ALL_Sort::Reals(sort) => match sort {
                theories::RealsSort::Real => self.cvc5manager.get_real_sort(),
            },
            ALL_Sort::RealsInts(_) => unreachable!(),
            ALL_Sort::Arrays(sort) => match sort {
                theories::ArraysSort::Array(index, range) => {
                    let index = to_sort(index)?;
                    let range = to_sort(range)?;

                    self.cvc5manager.mk_array_sort(index, range)
                }
            },
        })
    }

    fn atom(
        &self,
        atom: <Self::ALL as LogicEx>::Atom<'_>,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<cvc5::Term>>,
    ) -> Result<cvc5::Term> {
        match atom {
            ALL_Atom::Core(atom) => self.core_atom_to_cvc5(atom, to_term, to_terms),
            ALL_Atom::Ints(atom) => self.ints_atom_to_cvc5(atom, to_term, to_terms),
            ALL_Atom::Reals(atom) => self.reals_atom_to_cvc5(atom, to_term, to_terms),
            ALL_Atom::RealsInts(atom) => self.reals_ints_atom_to_cvc5(atom, to_term),
            ALL_Atom::Arrays(atom) => self.arrays_atom_to_cvc5(atom, to_term),
        }
    }

    fn export(
        &self,
        term: Self::Term,
        pool: &dyn smt::TermPool,
        _to_func: impl Clone + Fn(Self::FuncDecl) -> Option<smt::UserFunction>,
        _to_sort: impl Clone + Fn(Self::Sort) -> Option<smt::Sort>,
    ) -> Option<smt::Term> {
        use smt::theories::*;

        if let Some(value) = self.cvc5manager.get_boolean_value(term) {
            return if value {
                Some(Core::True().into_term_in(pool))
            } else {
                Some(Core::False().into_term_in(pool))
            };
        } else if let Some(value) = self.cvc5manager.get_integer_value(term) {
            return Some(smt::Constant::from(value).into_term_in(pool));
        } else if let Some(value) = self.cvc5manager.get_real_value(term) {
            return Some(smt::Constant::from(value).into_term_in(pool));
        }

        None
    }
}

impl Manager {
    fn core_atom_to_cvc5(
        &self,
        atom: theories::CoreAtom,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<cvc5::Term>>,
    ) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::CoreAtom::True => self.cvc5manager.mk_boolean(true),
            theories::CoreAtom::False => self.cvc5manager.mk_boolean(false),
            theories::CoreAtom::Not(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Not, &[arg])
            }
            theories::CoreAtom::Implies(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Implies, &args)
            }
            theories::CoreAtom::And(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::And, &args)
            }
            theories::CoreAtom::Or(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Or, &args)
            }
            theories::CoreAtom::Xor(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Xor, &args)
            }
            theories::CoreAtom::Equals(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Equal, &args)
            }
            theories::CoreAtom::Distinct(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Distinct, &args)
            }
            theories::CoreAtom::Ite(cond, then, else_) => {
                let cond = to_term(cond)?;
                let then = to_term(then)?;
                let else_ = to_term(else_)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::Ite, &[cond, then, else_])
            }
        })
    }

    fn ints_atom_to_cvc5(
        &self,
        atom: theories::IntsAtom,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<cvc5::Term>>,
    ) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::IntsAtom::Unary_minus(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Neg, &[arg])
            }
            theories::IntsAtom::Minus(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Sub, &args)
            }
            theories::IntsAtom::Plus(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Add, &args)
            }
            theories::IntsAtom::Mult(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Mult, &args)
            }
            theories::IntsAtom::Div(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Distinct, &args)
            }
            theories::IntsAtom::Mod_(left, right) => {
                let left = to_term(left)?;
                let right = to_term(right)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::IntsModulus, &[left, right])
            }
            theories::IntsAtom::Abs(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Abs, &[arg])
            }
            theories::IntsAtom::Le(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Leq, &args)
            }
            theories::IntsAtom::Lt(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Lt, &args)
            }
            theories::IntsAtom::Ge(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Geq, &args)
            }
            theories::IntsAtom::Gt(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Gt, &args)
            }
        })
    }

    fn reals_atom_to_cvc5(
        &self,
        atom: theories::RealsAtom,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<cvc5::Term>>,
    ) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::RealsAtom::Unary_minus(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Neg, &[arg])
            }
            theories::RealsAtom::Minus(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Sub, &args)
            }
            theories::RealsAtom::Plus(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Add, &args)
            }
            theories::RealsAtom::Mult(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Mult, &args)
            }
            theories::RealsAtom::Div(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Distinct, &args)
            }
            theories::RealsAtom::Le(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Leq, &args)
            }
            theories::RealsAtom::Lt(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Lt, &args)
            }
            theories::RealsAtom::Ge(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Geq, &args)
            }
            theories::RealsAtom::Gt(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Gt, &args)
            }
        })
    }

    fn reals_ints_atom_to_cvc5(
        &self,
        atom: theories::RealsIntsAtom,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
    ) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::RealsIntsAtom::To_real(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::ToReal, &[arg])
            }
            theories::RealsIntsAtom::To_int(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::ToInteger, &[arg])
            }
            theories::RealsIntsAtom::Is_int(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::IsInteger, &[arg])
            }
        })
    }

    fn arrays_atom_to_cvc5(
        &self,
        atom: theories::ArraysAtom,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
    ) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::ArraysAtom::Select(array, index) => {
                let array = to_term(array)?;
                let index = to_term(index)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::Select, &[array, index])
            }
            theories::ArraysAtom::Store(array, index, elem) => {
                let array = to_term(array)?;
                let index = to_term(index)?;
                let elem = to_term(elem)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::Store, &[array, index, elem])
            }
        })
    }
}
