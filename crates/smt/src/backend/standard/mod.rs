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

pub mod facade;

use crate::formally;
use formally::{
    smt::{self, backend, logics::LogicEx},
    support::Identifier,
};

use std::rc::Rc;

type Result<T, E = backend::Error> = std::result::Result<T, E>;

pub trait Manager: Default + Sized {
    type ALL: LogicEx;
    type Backend: backend::Backend;
    type FuncDecl: Clone;
    type Sort: Clone;
    type Term: Clone;

    fn backend(&self) -> &Self::Backend;

    fn uninterpreted_sort(&self, name: Identifier<'_>) -> Result<Self::Sort>;

    fn func_decl(&self, sorts: &[Self::Sort], range: Self::Sort) -> Result<Self::FuncDecl>;

    fn func_def(
        &self,
        sorts: &[Self::Sort],
        range: Self::Sort,
        bindings: &[Self::Term],
        body: Self::Term,
    ) -> Result<Self::FuncDecl>;

    fn binding(&self, name: &str, sort: Self::Sort) -> Result<Self::Term>;

    fn application(&self, func: &Self::FuncDecl, arguments: &[Self::Term]) -> Result<Self::Term>;

    fn constant(&self, cnst: &smt::Constant) -> Result<Self::Term>;

    fn quantified(
        &self,
        quantifier: smt::Quantifier,
        bindings: &[Self::Term],
        body: Self::Term,
    ) -> Result<Self::Term>;

    fn sort(
        &self,
        sort: <Self::ALL as LogicEx>::Sort<'_>,
        to_sort: impl Fn(&smt::Sort) -> Result<Self::Sort>,
        to_sorts: impl Fn(&[smt::Sort]) -> Result<Vec<Self::Sort>>,
    ) -> Result<Self::Sort>;

    fn atom(
        &self,
        atom: <Self::ALL as LogicEx>::Atom<'_>,
        to_term: impl Fn(&smt::Term) -> Result<Self::Term>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<Self::Term>>,
    ) -> Result<Self::Term>;
}

pub trait Solver: Sized {
    type Manager: Manager;
    type Result: Into<Option<bool>>;

    fn new(config: &smt::Config, manager: Rc<Self::Manager>) -> Self;

    fn push(&mut self) -> Result<()>;

    fn pop(&mut self, n: usize) -> Result<()>;

    fn require(&mut self, term: <Self::Manager as Manager>::Term) -> Result<()>;

    fn check(&self) -> Result<Self::Result>;
}
