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
        api::{Manager, Model, Solver},
    },
    logics::{Logic, LogicEx, standard_logic},
};
use std::{any::Any, cell::RefCell, collections::HashMap, iter::zip, rc::Rc};

type Result<T, E = backend::Error> = std::result::Result<T, E>;

/// A type that helps to implement instances of the [backend::Manager] trait.
///
/// Given a type `M: api::Manager`, `ManagerFacade<M>` implements [backend::Manager].
/// See the documentation of [api::Manager](Manager) for how to implement it properly.
pub struct ManagerFacade<M: Manager> {
    manager: Rc<M>,
    decls: RefCell<HashMap<smt::Declared, M::FuncDecl>>,
    defs: RefCell<HashMap<smt::Defined, M::FuncDecl>>,
    funcs: RefCell<HashMap<M::FuncDecl, smt::UserFunction>>,
    sorts: RefCell<HashMap<smt::Declared, M::Sort>>,
    sorts_rev: RefCell<HashMap<M::Sort, smt::Sort>>,
    terms: RefCell<HashMap<smt::Term, M::Term>>,
    variables: RefCell<HashMap<smt::Variable, M::Term>>,
}

/// A type that helps to implement instances of the [backend::Solver] trait.
///
/// Given a type `M: api::Solver`, `SolverFacade<M>` implements [backend::Solver].
/// See the documentation of [api::Solver](Solver) for how to implement it properly.
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
        self.solver
            .require(self.manager.term(term, &BindMap::new())?)
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
    /// Construct a new [SolverFacade].
    ///
    /// The method expects a reference to the backend, a [Config](smt::Config) and a
    /// [backend::Manager]. The latter two can come directly from the arguments of
    /// [backend::Backend::solver()] which therefore is quite easy to implement.
    ///
    /// For example, supposing your [api::Solver](Solver) type is called `MySolver`:
    ///
    /// ```text
    /// fn solver(&self, config: &Config, manager: Rc<dyn Manager>) -> Result<Box<dyn Solver>, Error> {
    ///     Ok(Box::new(api::SolverFacade::<MySolver>::new(self, config, manager)?))
    /// }
    /// ```
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
    fn value(&self, term: &smt::Term, pool: &dyn smt::TermPool) -> Option<smt::Term> {
        if let smt::TermKind::Atom(atom) = term.kind()
            && let smt::FunctionRef::Bound(bound) = &atom.head
            && let smt::BoundRef { function, .. } = bound
            && let smt::Function::User(smt::UserFunction::Defined(def)) = function
        {
            return self.value(&def.body, pool);
        }

        let term = self.solver.manager.term(term, &BindMap::new()).ok()?;

        self.solver
            .manager
            .export(self.model.value(term)?, pool)
            .ok()
    }
}

impl<M: 'static + Manager> backend::Manager for ManagerFacade<M> {
    fn backend(&self) -> &dyn Backend {
        self.manager.backend()
    }
}

type BindMap<Term> = rpds::HashTrieMap<smt::Variable, Term>;

impl<M: Manager> ManagerFacade<M> {
    /// Create a new [ManagerFacade].
    ///
    /// This method accepts any instance of the underlying [api::Manager](Manager) type `M`.
    /// The resulting object can be returned directly from [backend::Backend::manager()].
    ///
    /// ```text
    /// fn manager(&self) -> Box<dyn backend::Manager> {
    ///     Box::new(api::ManagerFacade::new(MyManager::default()))
    /// }
    /// ```
    pub fn new(manager: M) -> Self {
        ManagerFacade {
            manager: Rc::new(manager),
            decls: RefCell::default(),
            defs: RefCell::default(),
            funcs: RefCell::default(),
            sorts: RefCell::default(),
            sorts_rev: RefCell::default(),
            terms: RefCell::default(),
            variables: RefCell::default(),
        }
    }

    pub(crate) fn sort(&self, sort: &smt::Sort) -> Result<M::Sort> {
        match &sort.head {
            smt::SortHead::Bound(func) => match func {
                smt::Function::Variable(_) => unreachable!(),
                smt::Function::Primitive(_) => self.prim_sort(sort),
                smt::Function::User(user) => self.user_sort(sort, user),
            },
            smt::SortHead::Unbound(name) => Err(backend::Error::new(
                self.manager.backend().name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "an unresolved symbol reached the backend: `{name}`"
                )),
            )),
        }
    }

    pub(crate) fn term(&self, term: &smt::Term, bindmap: &BindMap<M::Term>) -> Result<M::Term> {
        if let Some(term) = self.terms.borrow().get(term) {
            return Ok(term.clone());
        }

        let t = match term.kind() {
            smt::TermKind::Constant(cnst) => self.manager.constant(cnst)?,
            smt::TermKind::Atom(atom) => self.atom(atom, bindmap)?,
            smt::TermKind::Quantified(quant) => self.quant(quant, bindmap)?,
            smt::TermKind::Let(let_) => self.let_(let_, bindmap)?,
        };

        self.terms.borrow_mut().insert(term.clone(), t.clone());

        Ok(t)
    }

    pub(crate) fn terms(
        &self,
        terms: &[smt::Term],
        bindmap: &BindMap<M::Term>,
    ) -> Result<Vec<M::Term>> {
        let mut vec = Vec::new();
        for sort in terms {
            vec.push(self.term(sort, bindmap)?)
        }
        Ok(vec)
    }

    pub(crate) fn declare(&self, solver: &M::Solver, decl: smt::Declared) -> Result<()> {
        if decl.range == smt::Sort::sort() {
            self.declare_sort(decl)
        } else {
            self.declare_fun(solver, decl)
        }
    }

    pub(crate) fn define(&self, solver: &M::Solver, def: smt::Defined) -> Result<()> {
        if !M::FUNC_DEF_SUPPORTED {
            return Ok(());
        }

        if self.defs.borrow().contains_key(&def) {
            return Ok(());
        }

        let mut sorts = Vec::new();
        let mut args = Vec::new();
        for var in &def.domain {
            sorts.push(self.sort(var.sort())?);
            args.push(self.variable(var)?)
        }
        let range = self.sort(&def.range)?;
        let body = self.term(&def.body, &BindMap::new())?;

        let func = self
            .manager
            .func_def(solver, def.name.name(), &sorts, range, &args, body)?;
        self.defs.borrow_mut().insert(def.clone(), func.clone());
        self.funcs
            .borrow_mut()
            .insert(func, smt::UserFunction::from(def));

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

    fn sort_argument_to_value<'a>(&self, arg: &'a smt::SortArgument) -> Result<&'a smt::Integer> {
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

    fn atom(&self, atom: &smt::Atom, bindmap: &BindMap<M::Term>) -> Result<M::Term> {
        match &atom.head {
            smt::FunctionRef::Bound(bound) => match &bound.function {
                smt::Function::Variable(var) => {
                    if let Some(t) = bindmap.get(var) {
                        Ok(t.clone())
                    } else {
                        self.variable(var)
                    }
                }
                smt::Function::Primitive(_) => self.primitive(atom, bindmap),
                smt::Function::User(user) => self.user_func(user, &atom.arguments, bindmap),
            },
            smt::FunctionRef::Unbound(unbound) => Err(backend::Error::new(
                self.manager.backend().name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "an unresolved symbol reached the backend: `{unbound}`"
                )),
            )),
        }
    }

    fn variable(&self, variable: &smt::Variable) -> Result<M::Term> {
        if let Some(var) = self.variables.borrow().get(variable) {
            return Ok(var.clone());
        }

        let t = self
            .manager
            .variable(variable.name().name(), self.sort(variable.sort())?)?;

        self.variables
            .borrow_mut()
            .insert(variable.clone(), t.clone());

        Ok(t)
    }

    fn primitive(&self, atom: &smt::Atom, bindmap: &BindMap<M::Term>) -> Result<M::Term> {
        match <M::ALL as LogicEx>::Atom::try_from(atom) {
            Ok(atom) => {
                self.manager
                    .atom(atom, |t| self.term(t, bindmap), |t| self.terms(t, bindmap))
            }
            Err(_) => Err(backend::Error::new(
                self.manager.backend().name(),
                backend::ErrorKind::ViolatedPrecondition(format!(
                    "unknown primitive symbol or mismatching arguments: `{}`",
                    atom.head
                )),
            )),
        }
    }

    fn user_func(
        &self,
        user: &smt::UserFunction,
        arguments: &[smt::Term],
        bindmap: &BindMap<M::Term>,
    ) -> Result<M::Term> {
        match user {
            smt::UserFunction::Declared(decl) => self.declared(decl, arguments, bindmap),
            smt::UserFunction::Defined(def) => self.defined(def, arguments, bindmap),
        }
    }

    fn declared(
        &self,
        decl: &smt::Declared,
        arguments: &[smt::Term],
        bindmap: &BindMap<M::Term>,
    ) -> Result<M::Term> {
        let arguments = self.terms(arguments, bindmap)?;

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

    fn defined(
        &self,
        def: &smt::Defined,
        arguments: &[smt::Term],
        bindmap: &BindMap<M::Term>,
    ) -> Result<M::Term> {
        if M::FUNC_DEF_SUPPORTED {
            let arguments = self.terms(arguments, bindmap)?;
            if let Some(func) = self.defs.borrow().get(def) {
                self.manager.application(func, &arguments)
            } else {
                Err(backend::Error::new(
                    self.manager.backend().name(),
                    backend::ErrorKind::ViolatedPrecondition(format!(
                        "use of unknown function declaration: `{}`",
                        def.name
                    )),
                ))
            }
        } else {
            if def.domain.len() != arguments.len() {
                return Err(backend::Error::new(
                    self.manager.backend().name(),
                    backend::ErrorKind::ViolatedPrecondition(format!(
                        "defined function `{}` applied to {} arguments, expected {}",
                        def.name,
                        arguments.len(),
                        def.domain.len()
                    )),
                ));
            }

            let mut nested = BindMap::new();
            for (param, arg) in zip(def.domain.iter(), arguments.iter()) {
                nested.insert_mut(param.clone(), self.term(arg, bindmap)?);
            }
            self.term(&def.body, &nested)
        }
    }

    fn quant(&self, quant: &smt::Quantified, bindmap: &BindMap<M::Term>) -> Result<M::Term> {
        let mut bindmap = bindmap.clone();

        let mut vars = Vec::new();
        for var in &*quant.variables {
            vars.push(self.variable(var)?);
            bindmap.remove_mut(var);
        }

        let body = self.term(&quant.body, &bindmap)?;

        self.manager.quantified(quant.quantifier, &vars, body)
    }

    fn let_(&self, let_: &smt::Let, bindmap: &BindMap<M::Term>) -> Result<M::Term> {
        let mut nested = bindmap.clone();
        for bind in &*let_.bindings {
            nested.insert_mut(bind.variable.clone(), self.term(&bind.def, bindmap)?);
        }

        self.term(&let_.body, &nested)
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

        self.sorts.borrow_mut().insert(decl.clone(), sort.clone());
        self.sorts_rev
            .borrow_mut()
            .insert(sort, smt::Sort::from(decl));

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

        self.decls.borrow_mut().insert(decl.clone(), func.clone());
        self.funcs
            .borrow_mut()
            .insert(func, smt::UserFunction::from(decl));

        Ok(())
    }

    fn export(&self, term: M::Term, pool: &dyn smt::TermPool) -> Result<smt::Term> {
        let to_func = |decl| self.funcs.borrow().get(&decl).cloned();
        let to_sort = |decl| self.sorts_rev.borrow().get(&decl).cloned();
        match self.manager.export(term, pool, to_func, to_sort) {
            Some(t) => Ok(t),
            None => Err(backend::Error::new(
                self.manager.backend().name(),
                backend::ErrorKind::Unsupported {
                    msg: "unsupported Z3_ast in conversion to Term".into(),
                    span: None,
                },
            )),
        }
    }
}
