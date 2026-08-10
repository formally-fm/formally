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
    backend::{
        self,
        z3::{Z3, bindings as z3},
    },
    *,
};

use std::{collections::HashMap, rc::Rc};

pub struct Z3Manager {
    z3context: Rc<z3::Context>,
    functions: HashMap<Declared, z3::FuncDecl>,
    sorts: HashMap<Declared, z3::Sort>,
    terms: HashMap<Term, z3::Ast>,
}

impl backend::Term for z3::Ast {}

impl Z3Manager {
    pub fn new() -> Z3Manager {
        Z3Manager {
            z3context: z3::Context::new(&z3::Config::new()),
            functions: HashMap::new(),
            sorts: HashMap::new(),
            terms: HashMap::new(),
        }
    }
}

impl Default for Z3Manager {
    fn default() -> Self {
        Z3Manager::new()
    }
}

impl backend::Manager for Z3Manager {
    fn backend(&self) -> &dyn backend::Backend {
        &Z3
    }

    fn import(&self, term: &Term) -> Result<&dyn backend::Term, backend::Error> {
        todo!()
    }

    fn export(&self, term: &dyn backend::Term, pool: &TermPool) -> Result<Term, backend::Error> {
        todo!()
    }
}
