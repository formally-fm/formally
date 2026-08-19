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

mod facade;
pub use facade::ManagerFacade;
pub use facade::SolverFacade;

use crate::formally;
use formally::smt::{
    self,
    backend::{Backend, Error},
    logics::{Logic, LogicEx},
};

use std::rc::Rc;

type Result<T, E = Error> = std::result::Result<T, E>;

pub trait Manager: Default + Sized {
    type ALL: LogicEx;
    type Backend: Backend;
    type Solver;
    type FuncDecl: Clone;
    type Sort: Clone;
    type Term: Clone;

    fn backend(&self) -> &Self::Backend;

    fn uninterpreted_sort(&self, name: &str) -> Result<Self::Sort>;

    fn func_decl(
        &self,
        solver: &Self::Solver,
        name: &str,
        sorts: &[Self::Sort],
        range: Self::Sort,
    ) -> Result<Self::FuncDecl>;

    fn func_def(
        &self,
        solver: &Self::Solver,
        name: &str,
        sorts: &[Self::Sort],
        range: Self::Sort,
        bindings: &[Self::Term],
        body: Self::Term,
    ) -> Result<Self::FuncDecl>;

    fn variable(&self, name: &str, sort: Self::Sort) -> Result<Self::Term>;

    fn application(&self, func: &Self::FuncDecl, arguments: &[Self::Term]) -> Result<Self::Term>;

    fn constant(&self, cnst: &smt::Constant) -> Result<Self::Term>;

    fn quantified(
        &self,
        quantifier: smt::Quantifier,
        variables: &[Self::Term],
        body: Self::Term,
    ) -> Result<Self::Term>;

    fn sort(
        &self,
        sort: <Self::ALL as LogicEx>::Sort<'_>,
        to_sort: impl Fn(&smt::SortArgument) -> Result<Self::Sort>,
        to_value: impl Fn(&smt::SortArgument) -> Result<&smt::Constant>,
    ) -> Result<Self::Sort>;

    fn atom(
        &self,
        atom: <Self::ALL as LogicEx>::Atom<'_>,
        to_term: impl Fn(&smt::Term) -> Result<Self::Term>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<Self::Term>>,
    ) -> Result<Self::Term>;
}

pub trait Solver: Sized {
    type Manager: 'static + Manager;
    type Result: Into<Option<bool>>;
    type Model<'s>: Model<Term = <Self::Manager as Manager>::Term>
    where
        Self: 's;

    fn new(
        config: &smt::Config,
        logic: Result<Option<&'static dyn Logic>>,
        manager: Rc<Self::Manager>,
    ) -> Result<Self>;

    fn logic(&self) -> &dyn Logic;

    fn solver(&self) -> &<Self::Manager as Manager>::Solver;

    fn config(&self, config: &smt::Config) -> Result<()>;

    fn push(&mut self) -> Result<()>;

    fn pop(&mut self, n: usize) -> Result<()>;

    fn require(&mut self, term: <Self::Manager as Manager>::Term) -> Result<()>;

    fn check(&self) -> Result<Self::Result>;

    fn model(&self) -> Result<Self::Model<'_>>;
}

pub trait Model: Sized {
    type Term;

    fn value(&self, term: Self::Term) -> Option<smt::ModelValue>;
}
