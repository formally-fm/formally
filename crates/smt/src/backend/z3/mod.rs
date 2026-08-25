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

use crate::{Config, formally};
use bindings as z3;
use formally::smt::{
    self,
    backend::{self, Backend, standard},
    logic,
    logics::{Logic, LogicEx},
    theories,
};
use std::rc::Rc;

type Result<T, E = backend::Error> = std::result::Result<T, E>;

#[derive(Clone, Copy, Default)]
pub struct Z3;

struct Manager {
    z3context: Rc<z3::Context>,
}

struct Solver {
    z3context: Rc<z3::Context>,
    z3solver: Rc<z3::Solver>,
    logic: &'static dyn Logic,
}

struct Model<'s> {
    solver: &'s Solver,
    model: z3::Model,
}

logic! {
    name: ALL,
    theories: [
        theories::Core,
        theories::Ints,
        theories::Reals,
        theories::Reals_Ints,
        theories::Arrays
    ],
    requirements: [ ]
}

impl Backend for Z3 {
    fn name(&self) -> &str {
        "cvc5"
    }

    fn manager(&self) -> Box<dyn backend::Manager> {
        Box::new(standard::ManagerFacade::new(Manager::default()))
    }

    fn solver(
        &self,
        config: &Config,
        manager: Rc<dyn backend::Manager>,
    ) -> Result<Box<dyn backend::Solver>> {
        Ok(Box::new(standard::SolverFacade::<Solver>::new(
            self, config, manager,
        )?))
    }
}

impl standard::Solver for Solver {
    type Manager = Manager;
    type Result = z3::LBool;
    type Model<'s>
        = Model<'s>
    where
        Self: 's;

    fn new(
        config: &Config,
        logic: Result<Option<&'static dyn Logic>>,
        context: Rc<Self::Manager>,
    ) -> Result<Self> {
        let solver = match logic? {
            Some(logic) => {
                let z3solver = Rc::new(z3::Solver::new_for_logic(
                    context.z3context.clone(),
                    logic.name(),
                ));
                Solver {
                    z3context: context.z3context.clone(),
                    z3solver,
                    logic,
                }
            }
            None => {
                let z3solver = Rc::new(z3::Solver::new(context.z3context.clone()));
                Solver {
                    z3context: context.z3context.clone(),
                    z3solver,
                    logic: &ALL,
                }
            }
        };

        solver.config(config)?;

        Ok(solver)
    }

    fn logic(&self) -> &dyn Logic {
        self.logic
    }

    fn solver(&self) -> &<Self::Manager as standard::Manager>::Solver {
        &self.z3solver
    }

    fn config(&self, config: &Config) -> Result<()> {
        let params = z3::Params::new(self.z3solver.ctx.clone());

        params.set_bool("model", config.produce_models);

        self.z3solver.set_params(params);

        Ok(())
    }

    fn push(&mut self) -> Result<()> {
        self.z3solver.push();

        Ok(())
    }

    fn pop(&mut self, n: usize) -> Result<()> {
        self.z3solver.pop(n);

        Ok(())
    }

    fn require(&mut self, term: <Self::Manager as standard::Manager>::Term) -> Result<()> {
        self.z3solver.assert(term);

        Ok(())
    }

    fn check(&self) -> Result<Self::Result> {
        Ok(self.z3solver.check())
    }

    fn model(&self) -> Result<Self::Model<'_>> {
        Ok(Model {
            solver: self,
            model: self.z3solver.get_model(),
        })
    }
}

impl standard::Model for Model<'_> {
    type Term = z3::Ast;

    fn value(&self, term: Self::Term) -> Option<smt::ModelValue> {
        let result = self.solver.z3context.simplify(self.model.eval(&term)?);

        match self.solver.z3context.get_bool_value(result.clone()) {
            z3::Z3_L_FALSE => {
                return Some(smt::ModelValue::from(false));
            }
            z3::Z3_L_TRUE => {
                return Some(smt::ModelValue::from(true));
            }
            _ => {}
        }

        match result.kind() {
            z3::AstKind::Numeral => {
                let string = result.get_numeral_string();

                match rug::Integer::from_str_radix(&string, 10) {
                    Ok(int) => Some(smt::ModelValue::from(smt::Constant::from(int))),
                    Err(_) => match rug::Rational::from_str_radix(&string, 10) {
                        Ok(rat) => Some(smt::ModelValue::from(smt::Constant::from(rat))),
                        Err(_) => None,
                    },
                }
            }
            _ => None,
        }
    }
}

impl Default for Manager {
    fn default() -> Self {
        Manager {
            z3context: z3::Context::new(),
        }
    }
}

impl standard::Manager for Manager {
    type ALL = ALL;
    type Backend = Z3;
    type Solver = z3::Solver;
    type FuncDecl = z3::FuncDecl;
    type Sort = z3::Sort;
    type Term = z3::Ast;

    fn backend(&self) -> &Self::Backend {
        &Z3
    }

    fn uninterpreted_sort(&self, name: &str) -> Result<z3::Sort> {
        Ok(self.z3context.mk_uninterpreted_sort(name))
    }

    fn func_decl(
        &self,
        _solver: &z3::Solver,
        name: &str,
        sorts: &[z3::Sort],
        range: z3::Sort,
    ) -> Result<z3::FuncDecl> {
        Ok(self.z3context.mk_func_decl(name, sorts, range))
    }

    fn variable(&self, name: &str, sort: z3::Sort) -> Result<z3::Ast> {
        Ok(self.z3context.mk_const(name, sort))
    }

    fn application(&self, func: &z3::FuncDecl, arguments: &[z3::Ast]) -> Result<z3::Ast> {
        Ok(self.z3context.mk_app(func, arguments))
    }

    fn constant(&self, cnst: &smt::Constant) -> Result<z3::Ast> {
        match cnst {
            smt::Constant::Integer { value, .. } => {
                Ok(self.z3context.mk_numeral(&value.to_string()))
            }
            smt::Constant::Rational { value, .. } => {
                Ok(self.z3context.mk_numeral(&value.to_string()))
            }
        }
    }

    fn quantified(
        &self,
        quantifier: smt::Quantifier,
        variables: &[z3::Ast],
        body: z3::Ast,
    ) -> Result<z3::Ast> {
        match quantifier {
            smt::Quantifier::Forall => Ok(self.z3context.mk_forall_const(variables, body)),
            smt::Quantifier::Exists => Ok(self.z3context.mk_exists_const(variables, body)),
        }
    }

    fn sort(
        &self,
        sort: <Self::ALL as LogicEx>::Sort<'_>,
        to_sort: impl Fn(&smt::SortArgument) -> Result<z3::Sort>,
        _to_value: impl Fn(&smt::SortArgument) -> Result<&smt::Integer>,
    ) -> Result<z3::Sort> {
        Ok(match sort {
            ALLSort::Core(sort) => match sort {
                theories::CoreSort::Bool => self.z3context.mk_bool_sort(),
            },
            ALLSort::Ints(sort) => match sort {
                theories::IntsSort::Int => self.z3context.mk_int_sort(),
            },
            ALLSort::Reals(sort) => match sort {
                theories::RealsSort::Real => self.z3context.mk_real_sort(),
            },
            ALLSort::Reals_Ints(_) => unreachable!(),
            ALLSort::Arrays(sort) => match sort {
                theories::ArraysSort::Array(index, range) => {
                    let index = to_sort(index)?;
                    let range = to_sort(range)?;

                    self.z3context.mk_array_sort(&[index], range)
                }
            },
        })
    }

    fn atom(
        &self,
        atom: <Self::ALL as LogicEx>::Atom<'_>,
        to_term: impl Fn(&smt::Term) -> Result<z3::Ast>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<z3::Ast>>,
    ) -> Result<z3::Ast> {
        match atom {
            ALLAtom::Core(atom) => self.core_atom_to_z3(atom, to_term, to_terms),
            ALLAtom::Ints(atom) => self.ints_atom_to_z3(atom, to_term, to_terms),
            ALLAtom::Reals(atom) => self.reals_atom_to_z3(atom, to_term, to_terms),
            ALLAtom::Reals_Ints(atom) => self.reals_int_atom_to_z3(atom, to_term),
            ALLAtom::Arrays(atom) => self.arrays_atom_to_z3(atom, to_term),
        }
    }
}

impl Manager {
    fn core_atom_to_z3(
        &self,
        atom: theories::CoreAtom,
        to_term: impl Fn(&smt::Term) -> Result<z3::Ast>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<z3::Ast>>,
    ) -> Result<z3::Ast> {
        Ok(match atom {
            theories::CoreAtom::True => self.z3context.mk_true(),
            theories::CoreAtom::False => self.z3context.mk_false(),
            theories::CoreAtom::Not(arg) => self.z3context.mk_not(to_term(arg)?),
            theories::CoreAtom::Implies(args) => to_terms(args)?
                .into_iter()
                .rev()
                .reduce(|acc, arg| self.z3context.mk_implies(arg, acc))
                .unwrap_or(self.z3context.mk_false()),
            theories::CoreAtom::And(args) => self.z3context.mk_and(to_terms(args)?),
            theories::CoreAtom::Or(args) => self.z3context.mk_or(to_terms(args)?),
            theories::CoreAtom::Xor(args) => to_terms(args)?
                .into_iter()
                .reduce(|acc, arg| self.z3context.mk_xor(acc, arg))
                .unwrap_or(self.z3context.mk_false()),
            theories::CoreAtom::Equals(args) => {
                let args = to_terms(args)?;

                let mut partials = Vec::new();
                for i in 0..args.len() - 1 {
                    partials.push(self.z3context.mk_eq(args[i].clone(), args[i + 1].clone()));
                }
                self.z3context.mk_and(partials)
            }
            theories::CoreAtom::Distinct(args) => self.z3context.mk_distinct(to_terms(args)?),
            theories::CoreAtom::Ite(cond, then, else_) => {
                let cond = to_term(cond)?;
                let then = to_term(then)?;
                let else_ = to_term(else_)?;

                self.z3context.mk_ite(cond, then, else_)
            }
        })
    }

    fn ints_atom_to_z3(
        &self,
        atom: theories::IntsAtom,
        to_term: impl Fn(&smt::Term) -> Result<z3::Ast>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<z3::Ast>>,
    ) -> Result<z3::Ast> {
        Ok(match atom {
            theories::IntsAtom::Unary_minus(arg) => self.z3context.mk_unary_minus(to_term(arg)?),
            theories::IntsAtom::Minus(args) => self.z3context.mk_sub(to_terms(args)?),
            theories::IntsAtom::Plus(args) => self.z3context.mk_add(to_terms(args)?),
            theories::IntsAtom::Mult(args) => self.z3context.mk_mul(to_terms(args)?),
            theories::IntsAtom::Div(args) => to_terms(args)?
                .into_iter()
                .reduce(|acc, arg| self.z3context.mk_div(acc, arg))
                .unwrap_or(self.z3context.mk_int(1)),
            theories::IntsAtom::Mod_(left, right) => {
                self.z3context.mk_mod(to_term(left)?, to_term(right)?)
            }
            theories::IntsAtom::Abs(arg) => {
                let arg = to_term(arg)?;
                self.z3context.mk_ite(
                    self.z3context.mk_ge(arg.clone(), self.z3context.mk_int(0)),
                    arg.clone(),
                    self.z3context.mk_unary_minus(arg),
                )
            }
            theories::IntsAtom::Le(args) => {
                let args = to_terms(args)?;
                let mut partials = Vec::new();
                for i in 0..args.len() - 1 {
                    partials.push(self.z3context.mk_le(args[i].clone(), args[i + 1].clone()));
                }
                self.z3context.mk_and(partials)
            }
            theories::IntsAtom::Lt(args) => {
                let args = to_terms(args)?;
                let mut partials = Vec::new();
                for i in 0..args.len() - 1 {
                    partials.push(self.z3context.mk_lt(args[i].clone(), args[i + 1].clone()));
                }
                self.z3context.mk_and(partials)
            }
            theories::IntsAtom::Ge(args) => {
                let args = to_terms(args)?;
                let mut partials = Vec::new();
                for i in 0..args.len() - 1 {
                    partials.push(self.z3context.mk_ge(args[i].clone(), args[i + 1].clone()));
                }
                self.z3context.mk_and(partials)
            }
            theories::IntsAtom::Gt(args) => {
                let args = to_terms(args)?;
                let mut partials = Vec::new();
                for i in 0..args.len() - 1 {
                    partials.push(self.z3context.mk_gt(args[i].clone(), args[i + 1].clone()));
                }
                self.z3context.mk_and(partials)
            }
        })
    }

    fn reals_atom_to_z3(
        &self,
        atom: theories::RealsAtom,
        to_term: impl Fn(&smt::Term) -> Result<z3::Ast>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<z3::Ast>>,
    ) -> Result<z3::Ast> {
        Ok(match atom {
            theories::RealsAtom::Unary_minus(arg) => self.z3context.mk_unary_minus(to_term(arg)?),
            theories::RealsAtom::Minus(args) => self.z3context.mk_sub(to_terms(args)?),
            theories::RealsAtom::Plus(args) => self.z3context.mk_add(to_terms(args)?),
            theories::RealsAtom::Mult(args) => self.z3context.mk_mul(to_terms(args)?),
            theories::RealsAtom::Div(args) => to_terms(args)?
                .into_iter()
                .reduce(|acc, arg| self.z3context.mk_div(acc, arg))
                .unwrap_or(self.z3context.mk_int(1)),
            theories::RealsAtom::Le(args) => {
                let args = to_terms(args)?;
                let mut partials = Vec::new();
                for i in 0..args.len() - 1 {
                    partials.push(self.z3context.mk_le(args[i].clone(), args[i + 1].clone()));
                }
                self.z3context.mk_and(partials)
            }
            theories::RealsAtom::Lt(args) => {
                let args = to_terms(args)?;
                let mut partials = Vec::new();
                for i in 0..args.len() - 1 {
                    partials.push(self.z3context.mk_lt(args[i].clone(), args[i + 1].clone()));
                }
                self.z3context.mk_and(partials)
            }
            theories::RealsAtom::Ge(args) => {
                let args = to_terms(args)?;
                let mut partials = Vec::new();
                for i in 0..args.len() - 1 {
                    partials.push(self.z3context.mk_ge(args[i].clone(), args[i + 1].clone()));
                }
                self.z3context.mk_and(partials)
            }
            theories::RealsAtom::Gt(args) => {
                let args = to_terms(args)?;
                let mut partials = Vec::new();
                for i in 0..args.len() - 1 {
                    partials.push(self.z3context.mk_gt(args[i].clone(), args[i + 1].clone()));
                }
                self.z3context.mk_and(partials)
            }
        })
    }

    fn reals_int_atom_to_z3(
        &self,
        atom: theories::Reals_IntsAtom,
        to_term: impl Fn(&smt::Term) -> Result<z3::Ast>,
    ) -> Result<z3::Ast> {
        Ok(match atom {
            theories::Reals_IntsAtom::To_real(arg) => self.z3context.mk_int2real(to_term(arg)?),
            theories::Reals_IntsAtom::To_int(arg) => self.z3context.mk_real2int(to_term(arg)?),
            theories::Reals_IntsAtom::Is_int(arg) => self.z3context.mk_is_int(to_term(arg)?),
        })
    }

    fn arrays_atom_to_z3(
        &self,
        atom: theories::ArraysAtom,
        to_term: impl Fn(&smt::Term) -> Result<z3::Ast>,
    ) -> Result<z3::Ast> {
        Ok(match atom {
            theories::ArraysAtom::Select(array, index) => {
                let array = to_term(array)?;
                let index = to_term(index)?;
                self.z3context.mk_select_n(array, vec![index])
            }
            theories::ArraysAtom::Store(array, index, value) => {
                let array = to_term(array)?;
                let index = to_term(index)?;
                let value = to_term(value)?;
                self.z3context.mk_store_n(array, vec![index], value)
            }
        })
    }
}
