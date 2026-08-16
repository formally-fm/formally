//
// ::formally - the open-source formal methods toolchain
//
// Copyright (c) 2025 Nicola Gigante
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

//! The Z3 backend.

#![allow(clippy::type_complexity)]

mod bindings;
mod manager;
mod solver;

pub use manager::Z3Manager;
pub use solver::Z3Solver;

use crate::formally;
use formally::smt::{self, backend, logic};
use std::{any::Any, rc::Rc};

/// The Z3 backend.
///
/// This backend is based on the C API of [Z3](https://github.com/Z3Prover/z3) from Microsoft
/// Research, accessed via the [z3_sys] crate.
#[derive(Clone, Copy, Default)]
pub struct Z3;

logic! {
    name: Z3ALL,
    theories: [
        smt::theories::Core,
        smt::theories::Ints,
        smt::theories::Reals,
        smt::theories::Reals_Ints,
        smt::theories::Arrays
    ],
    requirements: [ ]
}

impl backend::Backend for Z3 {
    fn name(&self) -> &str {
        "z3"
    }

    fn manager(&self) -> Box<dyn backend::Manager> {
        Box::new(Z3Manager::new())
    }

    fn solver<'m>(
        &self,
        config: &smt::Config,
        manager: Rc<dyn backend::Manager>,
    ) -> Result<Box<dyn backend::Solver>, backend::Error> {
        let manager =
            match Rc::downcast::<Z3Manager>(manager as Rc<dyn Any>) {
                Ok(manager) => manager,
                Err(_) => return Err(backend::Error::new(
                    Z3.name(),
                    backend::ErrorKind::Internal(
                        "Z3 backend method called with a `dyn Manager` which is not `Z3Manager`"
                            .into(),
                    ),
                )),
            };

        let solver = Z3Solver::new(config, manager)?;

        Ok(Box::new(solver) as Box<dyn backend::Solver>)
    }
}