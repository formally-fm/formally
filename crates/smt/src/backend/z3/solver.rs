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

use std::rc::Rc;

pub struct Z3Solver {
    logic: &'static dyn Logic,
    manager: Rc<Z3Manager>,
    z3solver: z3::Solver,
    result: Option<bool>,
}

impl Z3Solver {
    pub fn new(config: &Config, manager: Rc<Z3Manager>) -> Result<Z3Solver, backend::Error> {
        let z3solver;
        let logic: &dyn Logic;
        match &config.logic {
            Some(name) => match standard_logic(name) {
                Some(found) => {
                    z3solver = z3::Solver::new_for_logic(manager.z3context.clone(), name);
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
                z3solver = z3::Solver::new(manager.z3context.clone());
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
    fn manager(&self) -> &dyn backend::Manager {
        &*self.manager
    }

    fn backend(&self) -> &dyn backend::Backend {
        &Z3
    }

    fn logic(&self) -> &'_ dyn Logic {
        self.logic
    }

    fn declare(&mut self, decl: Declared) -> Result<(), backend::Error> {
        self.manager.declare(decl)
    }

    fn define(&mut self, def: Defined) -> Result<(), backend::Error> {
        self.manager.define(def)
    }

    fn push(&mut self) -> Result<(), backend::Error> {
        self.z3solver.push();

        Ok(())
    }

    fn pop_n(&mut self, n: usize) -> Result<(), backend::Error> {
        self.z3solver.pop(n);

        Ok(())
    }

    fn require(&mut self, term: &Term) -> Result<(), backend::Error> {
        let ast = self.manager.term_to_z3(term)?;

        self.z3solver.assert(ast);

        Ok(())
    }

    fn check(&mut self) -> Result<Option<bool>, backend::Error> {
        let result = self.z3solver.check();

        self.result = match result {
            z3::Z3_L_TRUE => Some(true),
            z3::Z3_L_FALSE => Some(false),
            _ => None,
        };

        Ok(self.result)
    }

    fn model(&self) -> Result<Option<Box<dyn '_ + ModelProvider>>, backend::Error> {
        match &self.z3solver.model {
            Some(m) => Ok(Some(
                Box::new(Model::new(self, m.clone())) as Box<dyn ModelProvider>
            )),
            None => Ok(None),
        }
    }
}

struct Model<'s> {
    solver: &'s Z3Solver,
    model: z3::Model,
}

impl<'s> Model<'s> {
    fn new(solver: &'s Z3Solver, model: z3::Model) -> Model<'s> {
        Model { solver, model }
    }
}

impl ModelProvider for Model<'_> {
    fn value(&self, decl: &Declared) -> Option<ModelValue> {
        let decls = self.solver.manager.decls.borrow();
        let func = decls.get(decl)?;
        let ast = self.model.get_const_interp(func)?;

        self.solver.manager.z3_const_to_value(ast)
    }
}
