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
    backend::{self, Backend as _, standard},
    logics::LogicEx,
};
use std::{cell::RefCell, collections::HashMap};

type Result<T, E = backend::Error> = std::result::Result<T, E>;

pub struct Manager<M: standard::Manager> {
    manager: M,
    decls: RefCell<HashMap<smt::Declared, M::FuncDecl>>,
    defs: RefCell<HashMap<smt::Defined, M::FuncDecl>>,
    sorts: RefCell<HashMap<smt::Declared, M::Sort>>,
    terms: RefCell<HashMap<smt::Term, M::Term>>,
    bindings: RefCell<HashMap<smt::Binding, M::Term>>,
}

impl<M: 'static + standard::Manager> backend::Manager for Manager<M> {
    fn backend(&self) -> &dyn backend::Backend {
        self.manager.backend()
    }
}

impl<M: standard::Manager> Default for Manager<M> {
    fn default() -> Self {
        Manager {
            manager: M::default(),
            decls: RefCell::default(),
            defs: RefCell::default(),
            sorts: RefCell::default(),
            terms: RefCell::default(),
            bindings: RefCell::default(),
        }
    }
}

impl<M: standard::Manager> Manager<M> {
    pub fn new() -> Self {
        Manager::default()
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

    fn prim_sort(&self, sort: &smt::Sort) -> Result<M::Sort> {
        match <M::ALL as LogicEx>::Sort::try_from(sort) {
            Ok(sort) => self.manager.sort(sort, |s| self.sort(s), |s| self.sorts(s)),
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
        for bind in &quant.bindings {
            bindings.push(
                self.manager
                    .binding(bind.name().name(), self.sort(bind.sort())?)?,
            );
        }

        let body = self.term(&quant.body)?;

        self.manager.quantified(quant.quantifier, &bindings, body)
    }
}
