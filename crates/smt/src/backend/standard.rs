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
use formally::{
    smt::{self, backend, logics::LogicEx, theories},
    support::Identifier,
};

use std::rc::Rc;

type Result<T, E = backend::Error> = std::result::Result<T, E>;

pub trait Backend {
    type ALL: LogicEx;
    type Manager: Manager<Backend = Self>;
    type Solver;
}

pub trait Manager: Sized {
    type Backend: Backend<Manager = Self>;
    type FuncDecl;
    type FuncDef;
    type Sort;
    type Term;
    type Binding;

    fn new() -> Self;

    fn uninterpreted_sort(&mut self, name: Identifier<'_>) -> Result<Self::Sort>;

    fn func_decl(&mut self, sorts: &[Self::Sort], range: Self::Sort) -> Result<Self::FuncDecl>;

    fn func_def(
        &mut self,
        sorts: &[Self::Sort],
        range: Self::Sort,
        bindings: &[Self::Binding],
        body: Self::Term,
    ) -> Result<Self::FuncDef>;

    fn binding(&mut self, name: Identifier<'_>, sort: Self::Sort) -> Result<Self::Binding>;

    fn application(&mut self, func: Self::FuncDecl, arguments: &[Self::Term])
    -> Result<Self::Term>;

    fn constant(&mut self, cnst: &smt::Constant) -> Result<Self::Term>;

    fn quantified(
        &mut self,
        quantifier: smt::Quantifier,
        bindings: &[Self::Binding],
        body: Self::Term,
    ) -> Result<Self::Term>;

    fn sort(
        &mut self,
        sort: <<Self::Backend as Backend>::ALL as LogicEx>::Sort<'_>,
    ) -> Result<Self::Sort>;

    fn atom(
        &mut self,
        atom: <<Self::Backend as Backend>::ALL as LogicEx>::Atom<'_>,
    ) -> Result<Self::Term>;
}

pub trait Solver: Sized {
    type Backend: Backend<Solver = Self>;
    type Result: Into<Option<bool>>;

    fn new(config: &smt::Config, manager: Rc<<Self::Backend as Backend>::Manager>) -> Self;

    fn push(&mut self) -> Result<()>;

    fn pop(&mut self, n: usize) -> Result<()>;

    fn require(
        &mut self,
        term: <<Self::Backend as Backend>::Manager as Manager>::Term,
    ) -> Result<()>;
    
    fn check(&self) -> Result<Self::Result>;
}
