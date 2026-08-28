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
use bindings as z3;
use formally::smt::{
    self, ToTerm as _,
    backends::{
        self, Backend,
        api::{self},
    },
    logic,
    logics::{Logic, LogicEx},
    theories,
};
use itertools::Itertools;
use std::rc::Rc;

type Result<T, E = backends::Error> = std::result::Result<T, E>;

#[smt::backend]
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
        theories::RealsInts,
        theories::Arrays
    ],
    requirements: [ ]
}

impl Backend for Z3 {
    fn name(&self) -> Result<&str> {
        Ok("z3")
    }

    fn manager(&self) -> Result<Box<dyn backends::Manager>> {
        Ok(Box::new(api::ManagerFacade::new(Manager::default())))
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
    type Result = z3::LBool;
    type Model<'s>
        = Model<'s>
    where
        Self: 's;

    fn new(
        config: &smt::Config,
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

    fn solver(&self) -> &<Self::Manager as api::Manager>::Solver {
        &self.z3solver
    }

    fn config(&self, config: &smt::Config) -> Result<()> {
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

    fn require(&mut self, term: <Self::Manager as api::Manager>::Term) -> Result<()> {
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

impl api::Model for Model<'_> {
    type Term = z3::Ast;

    fn value(&self, term: Self::Term) -> Option<Self::Term> {
        Some(self.solver.z3context.simplify(self.model.eval(&term)?))
    }
}

impl Default for Manager {
    fn default() -> Self {
        Manager {
            z3context: z3::Context::new(),
        }
    }
}

impl api::Manager for Manager {
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
            ALL_Sort::Core(sort) => match sort {
                theories::CoreSort::Bool => self.z3context.mk_bool_sort(),
            },
            ALL_Sort::Ints(sort) => match sort {
                theories::IntsSort::Int => self.z3context.mk_int_sort(),
            },
            ALL_Sort::Reals(sort) => match sort {
                theories::RealsSort::Real => self.z3context.mk_real_sort(),
            },
            ALL_Sort::RealsInts(_) => unreachable!(),
            ALL_Sort::Arrays(sort) => match sort {
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
            ALL_Atom::Core(atom) => self.core_atom_to_z3(atom, to_term, to_terms),
            ALL_Atom::Ints(atom) => self.ints_atom_to_z3(atom, to_term, to_terms),
            ALL_Atom::Reals(atom) => self.reals_atom_to_z3(atom, to_term, to_terms),
            ALL_Atom::RealsInts(atom) => self.reals_int_atom_to_z3(atom, to_term),
            ALL_Atom::Arrays(atom) => self.arrays_atom_to_z3(atom, to_term),
        }
    }

    fn export(
        &self,
        term: z3::Ast,
        pool: &dyn smt::TermPool,
        to_func: impl Clone + Fn(z3::FuncDecl) -> Option<smt::UserFunction>,
        to_sort: impl Clone + Fn(z3::Sort) -> Option<smt::Sort>,
    ) -> Option<smt::Term> {
        self.export(term, &[], pool, to_func, to_sort)
    }
}

impl Manager {
    fn export_sort(
        &self,
        sort: z3::Sort,
        to_sort: impl Clone + Fn(z3::Sort) -> Option<smt::Sort>,
    ) -> Option<smt::Sort> {
        use smt::theories::*;

        match sort.kind() {
            z3::SortKind::Uninterpreted => to_sort(sort),
            z3::SortKind::Bool => Some(Core::Bool()),
            z3::SortKind::Int => Some(Ints::Int()),
            z3::SortKind::Real => Some(Reals::Real()),
            z3::SortKind::Array => {
                let index = self.export_sort(sort.get_array_sort_domain(), to_sort.clone())?;
                let element = self.export_sort(sort.get_array_sort_range(), to_sort.clone())?;

                Some(Arrays::Array(&index, &element))
            }
            _ => None,
        }
    }

    fn export(
        &self,
        term: z3::Ast,
        vars: &[smt::Variable],
        pool: &dyn smt::TermPool,
        to_func: impl Clone + Fn(z3::FuncDecl) -> Option<smt::UserFunction>,
        to_sort: impl Clone + Fn(z3::Sort) -> Option<smt::Sort>,
    ) -> Option<smt::Term> {
        match term.kind() {
            z3::AstKind::Numeral => self.export_numeral(term, pool),
            z3::AstKind::App => {
                self.export_app(term.to_app().unwrap(), vars, pool, to_func, to_sort)
            }
            z3::AstKind::Var => Some(vars[term.var_index().unwrap()].clone().into_term_in(pool)),
            z3::AstKind::Quantifier => self.export_quant(term, vars, pool, to_func, to_sort),
            _ => None,
        }
    }

    fn export_numeral(&self, term: z3::Ast, pool: &dyn smt::TermPool) -> Option<smt::Term> {
        assert!(term.is_numeral());

        let string = term.get_numeral_string();

        match rug::Integer::from_str_radix(&string, 10) {
            Ok(int) => Some(smt::Constant::from(int).into_term_in(pool)),
            Err(_) => match rug::Rational::from_str_radix(&string, 10) {
                Ok(rat) => Some(smt::Constant::from(rat).into_term_in(pool)),
                Err(_) => None,
            },
        }
    }

    fn export_quant(
        &self,
        term: z3::Ast,
        vars: &[smt::Variable],
        pool: &dyn smt::TermPool,
        to_func: impl Clone + Fn(z3::FuncDecl) -> Option<smt::UserFunction>,
        to_sort: impl Clone + Fn(z3::Sort) -> Option<smt::Sort>,
    ) -> Option<smt::Term> {
        let mut vars = vars.iter().cloned().collect_vec();

        for i in 0..term.get_quantifier_num_bound() {
            let name = term.get_quantifier_bound_name(i);
            let sort = self.export_sort(term.get_quantifier_bound_sort(i), to_sort.clone())?;
            vars.push(smt::Variable::new(name, sort))
        }

        let body = self.export(term.get_quantifier_body(), &vars, pool, to_func, to_sort)?;

        if term.is_quantifier_forall() {
            Some(smt::term!(forall #(#vars)* #body).into_term_in(pool))
        } else if term.is_quantifier_exists() {
            Some(smt::term!(exists #(#vars)* #body).into_term_in(pool))
        } else {
            None
        }
    }

    fn export_app(
        &self,
        app: z3::App,
        vars: &[smt::Variable],
        pool: &dyn smt::TermPool,
        to_func: impl Clone + Fn(z3::FuncDecl) -> Option<smt::UserFunction>,
        to_sort: impl Clone + Fn(z3::Sort) -> Option<smt::Sort>,
    ) -> Option<smt::Term> {
        let mut intargs = true;
        let mut realargs = true;

        let mut args = Vec::with_capacity(app.len());
        for i in 0..app.len() {
            let arg = app.arg(i);
            intargs = intargs && arg.sort().kind() == z3::SortKind::Int;
            realargs = realargs && arg.sort().kind() == z3::SortKind::Real;

            args.push(self.export(app.arg(i), vars, pool, to_func.clone(), to_sort.clone())?)
        }

        let decl = app.decl();
        if let Some(decl) = to_func(decl.clone()) {
            return Some(smt::term!(#decl #(#args)*).into_term_in(pool));
        }

        use smt::theories::*;

        let head = match decl.kind() {
            z3::DeclKind::True => Core::True(),
            z3::DeclKind::False => Core::False(),
            z3::DeclKind::Eq => Core::equals(),
            z3::DeclKind::Distinct => Core::distinct(),
            z3::DeclKind::Ite => Core::ite(),
            z3::DeclKind::And => Core::and(),
            z3::DeclKind::Or => Core::or(),
            z3::DeclKind::Iff => Core::equals(),
            z3::DeclKind::Xor => Core::xor(),
            z3::DeclKind::Not => Core::not(),
            z3::DeclKind::Implies => Core::implies(),
            z3::DeclKind::Le if intargs => Ints::le(),
            z3::DeclKind::Le if realargs => Reals::le(),
            z3::DeclKind::Ge if intargs => Ints::ge(),
            z3::DeclKind::Ge if realargs => Reals::ge(),
            z3::DeclKind::Lt if intargs => Ints::lt(),
            z3::DeclKind::Lt if realargs => Reals::lt(),
            z3::DeclKind::Gt if intargs => Ints::gt(),
            z3::DeclKind::Gt if realargs => Reals::gt(),
            z3::DeclKind::Add if intargs => Ints::plus(),
            z3::DeclKind::Add if realargs => Reals::plus(),
            z3::DeclKind::Sub if intargs => Ints::minus(),
            z3::DeclKind::Sub if realargs => Reals::minus(),
            z3::DeclKind::Uminus if intargs => Ints::unary_minus(),
            z3::DeclKind::Uminus if realargs => Reals::unary_minus(),
            z3::DeclKind::Mul if intargs => Ints::mult(),
            z3::DeclKind::Mul if realargs => Reals::mult(),
            z3::DeclKind::Div => Reals::div(),
            z3::DeclKind::Idiv => Ints::div(),
            z3::DeclKind::Mod => Ints::mod_(),
            z3::DeclKind::ToReal => RealsInts::to_real(),
            z3::DeclKind::ToInt => RealsInts::to_int(),
            z3::DeclKind::IsInt => RealsInts::is_int(),
            z3::DeclKind::Abs if intargs => Ints::abs(),
            z3::DeclKind::Store => Arrays::store(),
            z3::DeclKind::Select => Arrays::select(),
            _ => return None,
        };

        Some(smt::term!(#head #(#args)*).into_term_in(pool))
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
        atom: theories::RealsIntsAtom,
        to_term: impl Fn(&smt::Term) -> Result<z3::Ast>,
    ) -> Result<z3::Ast> {
        Ok(match atom {
            theories::RealsIntsAtom::To_real(arg) => self.z3context.mk_int2real(to_term(arg)?),
            theories::RealsIntsAtom::To_int(arg) => self.z3context.mk_real2int(to_term(arg)?),
            theories::RealsIntsAtom::Is_int(arg) => self.z3context.mk_is_int(to_term(arg)?),
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
