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

use crate::formally;
use formally::smt::{
    self,
    backend::{
        self, Backend,
        standard::{Manager, Model, Solver},
    },
    logics::{Logic, LogicEx, standard_logic},
};
use std::{any::Any, cell::RefCell, collections::HashMap, rc::Rc};

type Result<T, E = backend::Error> = std::result::Result<T, E>;

pub struct ManagerFacade<M: Manager> {
    manager: Rc<M>,
    decls: RefCell<HashMap<smt::Declared, M::FuncDecl>>,
    defs: RefCell<HashMap<smt::Defined, M::FuncDecl>>,
    sorts: RefCell<HashMap<smt::Declared, M::Sort>>,
    terms: RefCell<HashMap<smt::Term, M::Term>>,
    bindings: RefCell<HashMap<smt::Binding, M::Term>>,
}

pub struct SolverFacade<S: Solver> {
    manager: Rc<ManagerFacade<<S as Solver>::Manager>>,
    solver: S,
    result: Option<bool>,
    config: RefCell<smt::Config>,
}

struct ModelFacade<'s, S: 's + Solver> {
    solver: &'s SolverFacade<S>,
    model: S::Model<'s>,
}

impl<S: Solver> backend::Solver for SolverFacade<S> {
    fn manager(&self) -> &dyn backend::Manager {
        &*self.manager
    }

    fn backend(&self) -> &dyn Backend {
        self.manager().backend()
    }

    fn config(&self, config: &smt::Config) -> Result<()> {
        *self.config.borrow_mut() = config.clone();
        self.solver.config(config)
    }

    fn logic(&self) -> &dyn Logic {
        self.solver.logic()
    }

    fn declare(&mut self, decl: smt::Declared) -> Result<()> {
        self.manager.declare(self.solver.solver(), decl)
    }

    fn define(&mut self, def: smt::Defined) -> Result<()> {
        self.manager.define(self.solver.solver(), def)
    }

    fn push(&mut self) -> Result<()> {
        self.solver.push()
    }

    fn pop_n(&mut self, n: usize) -> Result<()> {
        self.solver.pop(n)
    }

    fn require(&mut self, term: &smt::Term) -> Result<()> {
        self.solver.require(self.manager.term(term)?)
    }

    fn check(&mut self) -> Result<Option<bool>> {
        self.result = self.solver.check().map(Into::into)?;

        Ok(self.result)
    }

    fn model(&self) -> Result<Option<Box<dyn '_ + smt::ModelProvider>>> {
        if !self.config.borrow().produce_models {
            return Err(backend::Error::new(
                self.backend().name(),
                backend::ErrorKind::ViolatedPrecondition(
                    "no model can be produced if the `:produce-models` option is not set to true"
                        .into(),
                ),
            ));
        }

        if self.result.is_none() {
            return Ok(None);
        }

        Ok(Some(Box::new(ModelFacade {
            solver: self,
            model: self.solver.model()?,
        })))
    }
}

impl<S: Solver> SolverFacade<S> {
    pub fn new(
        backend: &<<S as Solver>::Manager as Manager>::Backend,
        config: &smt::Config,
        manager: Rc<dyn backend::Manager>,
    ) -> Result<Self> {
        let manager =
            match Rc::downcast::<ManagerFacade<<S as Solver>::Manager>>(manager as Rc<dyn Any>) {
                Ok(manager) => manager,
                Err(_) => return Err(backend::Error::new(
                    backend.name(),
                    backend::ErrorKind::Internal(
                        "`SolverFacade` method called with a `dyn Manager` which is not `ManagerFacade`"
                            .into(),
                    ),
                )),
            };

        let logic = match &config.logic {
            Some(name) => match standard_logic(name) {
                Some(found) => Ok(Some(found)),
                None => Err(backend::Error {
                    kind: Box::new(backend::ErrorKind::UnsupportedLogic(
                        name.clone().into_owned(),
                    )),
                    backend: backend.name().to_string(),
                }),
            },
            None => Ok(None),
        };

        Ok(SolverFacade {
            manager: manager.clone(),
            solver: <S as Solver>::new(config, logic, manager.manager.clone())?,
            result: None,
            config: RefCell::new(config.clone()),
        })
    }
}

impl<'s, S: 's + Solver> backend::ModelProvider for ModelFacade<'s, S> {
    fn value(&self, term: &smt::Term) -> Option<smt::ModelValue> {
        let term = self.solver.manager.term(term).map(Some).unwrap_or(None)?;

        self.model.value(term)
    }
}

impl<M: 'static + Manager> backend::Manager for ManagerFacade<M> {
    fn backend(&self) -> &dyn Backend {
        self.manager.backend()
    }
}

impl<M: Manager> ManagerFacade<M> {
    pub fn new(manager: M) -> Self {
        ManagerFacade {
            manager: Rc::new(manager),
            decls: RefCell::default(),
            defs: RefCell::default(),
            sorts: RefCell::default(),
            terms: RefCell::default(),
            bindings: RefCell::default(),
        }
    }

    pub fn sort(&self, sort: &smt::Sort) -> Result<M::Sort> {
        match &sort.head {
            smt::Function::Binding(_) => unreachable!(),
            smt::Function::Primitive(_) => self.prim_sort(sort),
            smt::Function::User(user) => self.user_sort(sort, user),
        }
    }

    pub fn sorts(&self, sorts: &[smt::Sort]) -> Result<Vec<M::Sort>> {
        let mut vec = Vec::new();
        for sort in sorts {
            vec.push(self.sort(sort)?)
        }
        Ok(vec)
    }

    pub fn term(&self, term: &smt::Term) -> Result<M::Term> {
        if let Some(term) = self.terms.borrow().get(term) {
            return Ok(term.clone());
        }

        let t = match term.kind() {
            smt::TermKind::Constant(cnst) => self.manager.constant(cnst)?,
            smt::TermKind::Atom(atom) => self.atom(atom)?,
            smt::TermKind::Quantified(quant) => self.quant(quant)?,
        };

        self.terms.borrow_mut().insert(term.clone(), t.clone());

        Ok(t)
    }

    pub fn terms(&self, terms: &[smt::Term]) -> Result<Vec<M::Term>> {
        let mut vec = Vec::new();
        for sort in terms {
            vec.push(self.term(sort)?)
        }
        Ok(vec)
    }

    pub fn declare(&self, solver: &M::Solver, decl: smt::Declared) -> Result<()> {
        if decl.range == smt::Sort::sort() {
            self.declare_sort(decl)
        } else {
            self.declare_fun(solver, decl)
        }
    }

    pub fn define(&self, solver: &M::Solver, def: smt::Defined) -> Result<()> {
        if self.defs.borrow().contains_key(&def) {
            return Ok(());
        }

        let mut sorts = Vec::new();
        let mut args = Vec::new();
        for bind in &def.domain {
            sorts.push(self.sort(bind.sort())?);
            args.push(self.binding(bind)?)
        }
        let range = self.sort(&def.range)?;
        let body = self.term(&def.body)?;

        let func = self
            .manager
            .func_def(solver, def.name.name(), &sorts, range, &args, body)?;

        self.defs.borrow_mut().insert(def, func);

        Ok(())
    }

    fn sort_argument_to_sort(&self, arg: &smt::SortArgument) -> Result<M::Sort> {
        match arg {
            smt::SortArgument::Sort(sort) => self.sort(sort),
            smt::SortArgument::Value(_) => Err(backend::Error::new(
                self.manager.backend().name(),
                backend::ErrorKind::ViolatedPrecondition("expected sort, found a value".into()),
            )),
        }
    }

    fn sort_argument_to_value<'a>(&self, arg: &'a smt::SortArgument) -> Result<&'a smt::Constant> {
        match arg {
            smt::SortArgument::Value(value) => Ok(value),
            smt::SortArgument::Sort(_) => Err(backend::Error::new(
                self.manager.backend().name(),
                backend::ErrorKind::ViolatedPrecondition("expected value, found a sort".into()),
            )),
        }
    }

    fn prim_sort(&self, sort: &smt::Sort) -> Result<M::Sort> {
        match <M::ALL as LogicEx>::Sort::try_from(sort) {
            Ok(sort) => self.manager.sort(
                sort,
                |arg| self.sort_argument_to_sort(arg),
                |arg| self.sort_argument_to_value(arg),
            ),
            Err(_) => Err(backend::Error::new(
                self.manager.backend().name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unknown primitive sort or mismatching arguments: `{}`",
                    sort.head.name()
                )),
            )),
        }
    }

    fn user_sort(&self, sort: &smt::Sort, user: &smt::UserFunction) -> Result<M::Sort> {
        match user {
            smt::UserFunction::Declared(decl) => match self.sorts.borrow().get(decl) {
                Some(sort) => Ok(sort.clone()),
                None => Err(backend::Error::new(
                    self.manager.backend().name(),
                    backend::ErrorKind::ViolatedPrecondition(format!(
                        "unknown sort or mismatching arguments: `{}`",
                        sort.head.name()
                    )),
                )),
            },
            smt::UserFunction::Defined(_) => todo!(),
        }
    }

    fn atom(&self, atom: &smt::Atom) -> Result<M::Term> {
        match atom {
            smt::Atom::Bound(atom) => match &atom.head.function {
                smt::Function::Binding(bind) => self.binding(bind),
                smt::Function::Primitive(_) => self.primitive(atom),
                smt::Function::User(user) => self.user_func(user, &atom.arguments),
            },
            smt::Atom::Unbound(smt::UnboundAtom { head, .. }) => Err(backend::Error::new(
                self.manager.backend().name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unbound variable in term: `{head}`"
                )),
            )),
        }
    }

    fn binding(&self, binding: &smt::Binding) -> Result<M::Term> {
        if let Some(bind) = self.bindings.borrow().get(binding) {
            return Ok(bind.clone());
        }

        let t = self
            .manager
            .binding(binding.name().name(), self.sort(binding.sort())?)?;

        self.bindings
            .borrow_mut()
            .insert(binding.clone(), t.clone());

        Ok(t)
    }

    fn primitive(&self, atom: &smt::BoundAtom) -> Result<M::Term> {
        match <M::ALL as LogicEx>::Atom::try_from(atom) {
            Ok(atom) => self.manager.atom(atom, |t| self.term(t), |t| self.terms(t)),
            Err(_) => Err(backend::Error::new(
                self.manager.backend().name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unknown primitive symbol or mismatching arguments: `{}`",
                    atom.head.function.name()
                )),
            )),
        }
    }

    fn user_func(&self, user: &smt::UserFunction, arguments: &[smt::Term]) -> Result<M::Term> {
        match user {
            smt::UserFunction::Declared(decl) => self.declared(decl, arguments),
            smt::UserFunction::Defined(def) => self.defined(def, arguments),
        }
    }

    fn declared(&self, decl: &smt::Declared, arguments: &[smt::Term]) -> Result<M::Term> {
        let arguments = self.terms(arguments)?;

        if let Some(func) = self.decls.borrow().get(decl) {
            return self.manager.application(func, &arguments);
        }

        Err(backend::Error::new(
            self.manager.backend().name(),
            backend::ErrorKind::ViolatedPrecondition(format!(
                "use of unknown function declaration: `{}`",
                decl.name
            )),
        ))
    }

    fn defined(&self, def: &smt::Defined, arguments: &[smt::Term]) -> Result<M::Term> {
        let arguments = self.terms(arguments)?;

        if let Some(func) = self.defs.borrow().get(def) {
            return self.manager.application(func, &arguments);
        }

        Err(backend::Error::new(
            self.manager.backend().name(),
            backend::ErrorKind::ViolatedPrecondition(format!(
                "use of unknown function declaration: `{}`",
                def.name
            )),
        ))
    }

    fn quant(&self, quant: &smt::Quantified) -> Result<M::Term> {
        let mut bindings = Vec::new();
        for bind in &*quant.bindings {
            bindings.push(self.binding(bind)?);
        }

        let body = self.term(&quant.body)?;

        self.manager.quantified(quant.quantifier, &bindings, body)
    }

    fn declare_sort(&self, decl: smt::Declared) -> Result<()> {
        if self.sorts.borrow().contains_key(&decl) {
            return Ok(());
        }

        let sort = if decl.domain.is_empty() {
            self.manager.uninterpreted_sort(decl.name.name())?
        } else {
            todo!()
        };

        self.sorts.borrow_mut().insert(decl, sort);

        Ok(())
    }

    fn declare_fun(&self, solver: &M::Solver, decl: smt::Declared) -> Result<()> {
        if self.decls.borrow().contains_key(&decl) {
            return Ok(());
        }

        let range = self.sort(&decl.range)?;
        let mut sorts = Vec::new();
        for sort in &decl.domain {
            sorts.push(self.sort(sort)?);
        }

        let func = self
            .manager
            .func_decl(solver, decl.name.name(), &sorts, range)?;

        self.decls.borrow_mut().insert(decl, func);

        Ok(())
    }
}
