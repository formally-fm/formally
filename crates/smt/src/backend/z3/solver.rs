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
        self, Backend as _,
        z3::{Z3, Z3ALL, bindings as z3, manager::Z3Manager},
    },
    logics::{Logic, standard_logic},
    *,
};

use crate::backend::{Backend, Error, Manager};
use std::rc::Rc;

pub struct Z3Solver {
    logic: &'static dyn Logic,
    manager: Rc<Z3Manager>,
    z3solver: z3::Solver,
    result: Option<bool>,
}

impl Z3Solver {
    pub fn new(config: &Config, manager: Rc<Z3Manager>) -> Result<Z3Solver, backend::Error> {
        let z3config = z3::Config::new();

        let z3context = z3::Context::new(&z3config);

        let z3solver;
        let logic: &dyn Logic;
        match &config.logic {
            Some(name) => match standard_logic(name, &Z3ALL) {
                Some(found) => {
                    z3solver = z3::Solver::new_for_logic(z3context.clone(), name);
                    logic = found;
                }
                None => {
                    return Err(backend::Error {
                        kind: Box::new(backend::ErrorKind::UnsupportedLogic(
                            name.clone().into_owned(),
                        )),
                        backend: Z3.name().to_string(),
                    });
                }
            },
            None => {
                z3solver = z3::Solver::new(z3context.clone());
                logic = &Z3ALL;
            }
        }

        Ok(Z3Solver {
            logic,
            manager,
            z3solver,
            result: None,
        })
    }
}

impl backend::Solver for Z3Solver {
    fn manager(&self) -> &dyn Manager {
        &*self.manager
    }

    fn backend(&self) -> &dyn Backend {
        &Z3
    }

    fn logic(&self) -> &'_ dyn Logic {
        self.logic
    }

    fn declare(&mut self, decl: Declared) -> Result<(), Error> {
        todo!()
    }

    fn define(&mut self, def: Defined) -> Result<(), Error> {
        todo!()
    }

    fn push(&mut self) -> Result<(), Error> {
        todo!()
    }

    fn pop_n(&mut self, n: usize) -> Result<(), Error> {
        todo!()
    }

    fn require(&mut self, term: &dyn backend::Term) -> Result<(), Error> {
        todo!()
    }

    fn check(&mut self) -> Result<Option<bool>, Error> {
        todo!()
    }

    fn model(&self) -> Result<Option<Box<dyn '_ + ModelProvider>>, Error> {
        todo!()
    }
}
