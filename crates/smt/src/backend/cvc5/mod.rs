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

pub mod bindings;

use crate::formally;
use formally::smt::{
    self,
    backend::{self, Backend as _},
    logic, logics, theories,
};
use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use bindings as cvc5;

type Result<T, E = backend::Error> = std::result::Result<T, E>;

#[derive(Clone, Copy, Default)]
pub struct Cvc5;

pub struct Cvc5Manager {
    pub manager: Rc<cvc5::TermManager>,
}

pub struct Cvc5Solver {
    manager: Rc<Cvc5Manager>,
    cvc5manager: Rc<cvc5::TermManager>,
    logic: &'static dyn logics::Logic,
    cvc5solver: Rc<cvc5::Solver>,
    decls: RefCell<HashMap<smt::Declared, cvc5::Term>>,
    defs: RefCell<HashMap<smt::Defined, cvc5::Term>>,
    sorts: RefCell<HashMap<smt::Declared, cvc5::Sort>>,
    terms: RefCell<HashMap<smt::Term, cvc5::Term>>,
    bindings: RefCell<HashMap<smt::Binding, cvc5::Term>>,
    result: Option<bool>,
}

logic! {
    name: Cvc5ALL,
    theories: [
        theories::Core,
        theories::Ints,
        theories::Reals,
        theories::Reals_Ints,
        theories::Arrays
    ],
    requirements: [ ]
}

impl backend::Backend for Cvc5 {
    fn name(&self) -> &str {
        "cvc5"
    }

    fn manager(&self) -> Box<dyn backend::Manager> {
        Box::new(Cvc5Manager::new())
    }

    fn solver(
        &self,
        config: &smt::Config,
        manager: Rc<dyn backend::Manager>,
    ) -> Result<Box<dyn backend::Solver>, backend::Error> {
        let manager =
            match Rc::downcast::<Cvc5Manager>(manager as Rc<dyn Any>) {
                Ok(manager) => manager,
                Err(_) => return Err(backend::Error::new(
                    Cvc5.name(),
                    backend::ErrorKind::Internal(
                        "Z3 backend method called with a `dyn Manager` which is not `Cvc5Manager`"
                            .into(),
                    ),
                )),
            };

        let solver = Cvc5Solver::new(config, manager)?;

        Ok(Box::new(solver) as Box<dyn backend::Solver>)
    }
}

impl backend::Manager for Cvc5Manager {
    fn backend(&self) -> &dyn backend::Backend {
        &Cvc5
    }
}

impl backend::Solver for Cvc5Solver {
    fn manager(&self) -> &dyn backend::Manager {
        &*self.manager
    }

    fn backend(&self) -> &dyn backend::Backend {
        &Cvc5
    }

    fn logic(&self) -> &'_ dyn logics::Logic {
        self.logic
    }

    fn declare(&mut self, decl: smt::Declared) -> Result<()> {
        if decl.range == smt::Sort::sort() {
            self.declare_sort(decl)
        } else {
            self.declare_fun(decl)
        }
    }

    fn define(&mut self, def: smt::Defined) -> Result<()> {
        if self.defs.borrow().contains_key(&def) {
            return Ok(());
        }

        let mut args = Vec::new();
        for bind in &def.domain {
            args.push(self.binding_to_cvc5(bind)?)
        }
        let range = self.sort_to_cvc5(&def.range)?;
        let body = self.term_to_cvc5(&def.body)?;

        let func = self
            .cvc5solver
            .define_fun(def.name.name(), &args, range, body, false);

        self.defs.borrow_mut().insert(def, func);

        Ok(())
    }

    fn push(&mut self) -> Result<()> {
        self.cvc5solver.push();

        Ok(())
    }

    fn pop_n(&mut self, n: usize) -> Result<()> {
        self.cvc5solver.pop(n as u32);

        Ok(())
    }

    fn require(&mut self, term: &smt::Term) -> Result<()> {
        self.cvc5solver.assert_formula(self.term_to_cvc5(term)?);

        Ok(())
    }

    fn check(&mut self) -> Result<Option<bool>> {
        let result = self.cvc5solver.check_sat();

        if result.is_sat() {
            self.result = Some(true);
        } else if result.is_unsat() {
            self.result = Some(false);
        } else {
            assert!(result.is_unknown());
            self.result = None;
        }

        Ok(self.result)
    }

    fn model(&self) -> Result<Option<Box<dyn '_ + smt::ModelProvider>>> {
        todo!()
    }
}

impl Cvc5Manager {
    pub fn new() -> Cvc5Manager {
        Cvc5Manager {
            manager: Rc::new(cvc5::TermManager::new()),
        }
    }
}

impl Default for Cvc5Manager {
    fn default() -> Self {
        Cvc5Manager::new()
    }
}

impl Cvc5Solver {
    pub fn new(
        config: &smt::Config,
        manager: Rc<Cvc5Manager>,
    ) -> Result<Cvc5Solver, backend::Error> {
        let cvc5manager = manager.manager.clone();
        let cvc5solver = Rc::new(cvc5::Solver::new(manager.manager.clone()));

        let logic: &dyn logics::Logic;
        match &config.logic {
            Some(name) => match logics::standard_logic(name, &Cvc5ALL) {
                Some(found) => {
                    cvc5solver.set_logic(name.name());
                    logic = found;
                }
                None => {
                    return Err(backend::Error {
                        kind: Box::new(backend::ErrorKind::UnsupportedLogic(
                            name.clone().into_owned(),
                        )),
                        backend: Cvc5.name().to_string(),
                    });
                }
            },
            None => {
                logic = &Cvc5ALL;
            }
        }

        if config.produce_models {
            cvc5solver.set_option("produce-models", "true")
        } else {
            cvc5solver.set_option("produce-models", "false")
        }

        Ok(Cvc5Solver {
            manager,
            cvc5manager,
            logic,
            cvc5solver,
            decls: RefCell::default(),
            defs: RefCell::default(),
            sorts: RefCell::default(),
            terms: RefCell::default(),
            bindings: RefCell::default(),
            result: None,
        })
    }

    fn declare_sort(&self, decl: smt::Declared) -> Result<()> {
        if self.sorts.borrow().contains_key(&decl) {
            return Ok(());
        }

        let sort = if decl.domain.is_empty() {
            self.cvc5manager.mk_uninterpreted_sort(decl.name.name())
        } else {
            todo!()
        };

        self.sorts.borrow_mut().insert(decl, sort);

        Ok(())
    }

    fn declare_fun(&self, decl: smt::Declared) -> Result<()> {
        if self.decls.borrow().contains_key(&decl) {
            return Ok(());
        }

        let range = self.sort_to_cvc5(&decl.range)?;
        let mut sorts = Vec::new();
        for sort in &decl.domain {
            sorts.push(self.sort_to_cvc5(sort)?);
        }

        let cvc5decl = self
            .cvc5solver
            .declare_fun(decl.name.name(), &sorts, range, true);

        self.decls.borrow_mut().insert(decl, cvc5decl);

        Ok(())
    }

    fn sort_to_cvc5(&self, sort: &smt::Sort) -> Result<cvc5::Sort> {
        match &sort.head {
            smt::Function::Binding(_) => unreachable!(),
            smt::Function::Primitive(_) => self.prim_sort_to_cvc5(sort),
            smt::Function::User(user) => self.user_sort_to_cvc5(sort, user),
        }
    }

    fn prim_sort_to_cvc5(&self, sort: &smt::Sort) -> Result<cvc5::Sort> {
        match Cvc5ALLSort::try_from(sort) {
            Ok(sort) => self.cvc5sort_to_cvc5(sort),
            Err(_) => Err(backend::Error::new(
                Cvc5.name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unknown primitive sort or mismatching arguments: `{}`",
                    sort.head.name()
                )),
            )),
        }
    }

    fn user_sort_to_cvc5(&self, sort: &smt::Sort, user: &smt::UserFunction) -> Result<cvc5::Sort> {
        match user {
            smt::UserFunction::Declared(decl) => match self.sorts.borrow().get(decl) {
                Some(sort) => Ok(*sort),
                None => Err(backend::Error::new(
                    Cvc5.name(),
                    backend::ErrorKind::ViolatedPrecondition(format!(
                        "unknown sort or mismatching arguments: `{}`",
                        sort.head.name()
                    )),
                )),
            },
            smt::UserFunction::Defined(_) => todo!(),
        }
    }

    fn sort_argument_to_sort<'s>(&self, arg: &'s smt::SortArgument) -> Result<&'s smt::Sort> {
        match arg {
            smt::SortArgument::Sort(sort) => Ok(sort),
            smt::SortArgument::Value(_) => Err(backend::Error::new(
                Cvc5.name(),
                backend::ErrorKind::ViolatedPrecondition("expected sort, found a value".into()),
            )),
        }
    }

    fn cvc5sort_to_cvc5(&self, sort: Cvc5ALLSort) -> Result<cvc5::Sort> {
        Ok(match sort {
            Cvc5ALLSort::Core(sort) => match sort {
                theories::CoreSort::Bool => self.cvc5manager.get_boolean_sort(),
            },
            Cvc5ALLSort::Ints(sort) => match sort {
                theories::IntsSort::Int => self.cvc5manager.get_integer_sort(),
            },
            Cvc5ALLSort::Reals(sort) => match sort {
                theories::RealsSort::Real => self.cvc5manager.get_real_sort(),
            },
            Cvc5ALLSort::Reals_Ints(_) => unreachable!(),
            Cvc5ALLSort::Arrays(sort) => match sort {
                theories::ArraysSort::Array(index, range) => {
                    let index = self.sort_to_cvc5(self.sort_argument_to_sort(index)?)?;
                    let range = self.sort_to_cvc5(self.sort_argument_to_sort(range)?)?;

                    self.cvc5manager.mk_array_sort(index, range)
                }
            },
        })
    }

    fn term_to_cvc5(&self, term: &smt::Term) -> Result<cvc5::Term> {
        match term.kind() {
            smt::TermKind::Constant(cnst) => self.constant_to_cvc5(cnst),
            smt::TermKind::Atom(atom) => self.atom_to_cvc5(atom),
            smt::TermKind::Quantified(quant) => self.quant_to_cvc5(quant),
        }
    }

    fn terms_to_cvc5(&self, terms: &[smt::Term]) -> Result<Vec<cvc5::Term>> {
        let mut cvc5terms = Vec::new();
        for term in terms {
            cvc5terms.push(self.term_to_cvc5(term)?)
        }

        Ok(cvc5terms)
    }

    fn constant_to_cvc5(&self, cnst: &smt::Constant) -> Result<cvc5::Term> {
        match cnst {
            smt::Constant::Integer { value, .. } => {
                Ok(self.cvc5manager.mk_integer(&value.to_string()))
            }
            smt::Constant::Rational { value, .. } => {
                Ok(self.cvc5manager.mk_real(&value.to_string()))
            }
        }
    }

    fn quant_to_cvc5(&self, quant: &smt::Quantified) -> Result<cvc5::Term> {
        todo!()
    }

    fn atom_to_cvc5(&self, atom: &smt::Atom) -> Result<cvc5::Term> {
        match atom {
            smt::Atom::Bound(atom) => match &atom.head.function {
                smt::Function::Binding(bind) => self.binding_to_cvc5(bind),
                smt::Function::Primitive(_) => self.prim_to_cvc5(atom),
                smt::Function::User(user) => self.userfunc_to_cvc5(user, &atom.arguments),
            },
            smt::Atom::Unbound(smt::UnboundAtom { head, .. }) => Err(backend::Error::new(
                Cvc5.name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unbound variable in term: `{head}`"
                )),
            )),
        }
    }

    fn binding_to_cvc5(&self, binding: &smt::Binding) -> Result<cvc5::Term> {
        todo!()
    }

    fn prim_to_cvc5(&self, atom: &smt::BoundAtom) -> Result<cvc5::Term> {
        match Cvc5ALLAtom::try_from(atom) {
            Ok(atom) => self.cvc5atom_to_cvc5(&atom),
            Err(_) => Err(backend::Error::new(
                Cvc5.name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unknown primitive symbol or mismatching arguments: `{}`",
                    atom.head.function.name()
                )),
            )),
        }
    }

    fn cvc5atom_to_cvc5(&self, atom: &Cvc5ALLAtom) -> Result<cvc5::Term> {
        match atom {
            Cvc5ALLAtom::Core(atom) => self.core_atom_to_cvc5(atom),
            Cvc5ALLAtom::Ints(atom) => self.ints_atom_to_cvc5(atom),
            Cvc5ALLAtom::Reals(atom) => self.reals_atom_to_cvc5(atom),
            Cvc5ALLAtom::Reals_Ints(atom) => self.reals_ints_atom_to_cvc5(atom),
            Cvc5ALLAtom::Arrays(atom) => self.arrays_atom_to_cvc5(atom),
        }
    }

    fn core_atom_to_cvc5(&self, atom: &theories::CoreAtom) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::CoreAtom::True => self.cvc5manager.mk_boolean(true),
            theories::CoreAtom::False => self.cvc5manager.mk_boolean(false),
            theories::CoreAtom::Not(arg) => {
                let arg = self.term_to_cvc5(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Not, &[arg])
            }
            theories::CoreAtom::Implies(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Implies, &args)
            }
            theories::CoreAtom::And(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::And, &args)
            }
            theories::CoreAtom::Or(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Or, &args)
            }
            theories::CoreAtom::Xor(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Xor, &args)
            }
            theories::CoreAtom::Equals(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Equal, &args)
            }
            theories::CoreAtom::Distinct(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Distinct, &args)
            }
            theories::CoreAtom::Ite(cond, then, else_) => {
                let cond = self.term_to_cvc5(cond)?;
                let then = self.term_to_cvc5(then)?;
                let else_ = self.term_to_cvc5(else_)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::Ite, &[cond, then, else_])
            }
        })
    }

    fn ints_atom_to_cvc5(&self, atom: &theories::IntsAtom) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::IntsAtom::Unary_minus(arg) => {
                let arg = self.term_to_cvc5(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Neg, &[arg])
            }
            theories::IntsAtom::Minus(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Sub, &args)
            }
            theories::IntsAtom::Plus(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Add, &args)
            }
            theories::IntsAtom::Mult(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Mult, &args)
            }
            theories::IntsAtom::Div(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Distinct, &args)
            }
            theories::IntsAtom::Mod_(left, right) => {
                let left = self.term_to_cvc5(left)?;
                let right = self.term_to_cvc5(right)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::IntsModulus, &[left, right])
            }
            theories::IntsAtom::Abs(arg) => {
                let arg = self.term_to_cvc5(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Abs, &[arg])
            }
            theories::IntsAtom::Le(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Leq, &args)
            }
            theories::IntsAtom::Lt(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Lt, &args)
            }
            theories::IntsAtom::Ge(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Geq, &args)
            }
            theories::IntsAtom::Gt(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Gt, &args)
            }
        })
    }

    fn reals_atom_to_cvc5(&self, atom: &theories::RealsAtom) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::RealsAtom::Unary_minus(arg) => {
                let arg = self.term_to_cvc5(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Neg, &[arg])
            }
            theories::RealsAtom::Minus(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Sub, &args)
            }
            theories::RealsAtom::Plus(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Add, &args)
            }
            theories::RealsAtom::Mult(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Mult, &args)
            }
            theories::RealsAtom::Div(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Distinct, &args)
            }
            theories::RealsAtom::Le(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Leq, &args)
            }
            theories::RealsAtom::Lt(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Lt, &args)
            }
            theories::RealsAtom::Ge(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Geq, &args)
            }
            theories::RealsAtom::Gt(args) => {
                let args = self.terms_to_cvc5(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Gt, &args)
            }
        })
    }

    fn reals_ints_atom_to_cvc5(&self, atom: &theories::Reals_IntsAtom) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::Reals_IntsAtom::To_real(arg) => {
                let arg = self.term_to_cvc5(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::ToReal, &[arg])
            }
            theories::Reals_IntsAtom::To_int(arg) => {
                let arg = self.term_to_cvc5(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::ToInteger, &[arg])
            }
            theories::Reals_IntsAtom::Is_int(arg) => {
                let arg = self.term_to_cvc5(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::IsInteger, &[arg])
            }
        })
    }

    fn arrays_atom_to_cvc5(&self, atom: &theories::ArraysAtom) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::ArraysAtom::Select(array, index) => {
                let array = self.term_to_cvc5(array)?;
                let index = self.term_to_cvc5(index)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::Select, &[array, index])
            }
            theories::ArraysAtom::Store(array, index, elem) => {
                let array = self.term_to_cvc5(array)?;
                let index = self.term_to_cvc5(index)?;
                let elem = self.term_to_cvc5(elem)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::Store, &[array, index, elem])
            }
        })
    }

    fn userfunc_to_cvc5(
        &self,
        user: &smt::UserFunction,
        arguments: &[smt::Term],
    ) -> Result<cvc5::Term> {
        todo!()
    }
}
