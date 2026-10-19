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

mod formally {
    pub extern crate formally_smt as smt;
    pub extern crate formally_support as support;
}

use formally::{
    smt::{
        backends::{
            api,
            cvc5::{self, Cvc5},
        },
        *,
    },
    support::*,
};

use std::{any::Any, ffi::CStr, rc::Rc};

struct Plugin;

impl cvc5::Plugin for Plugin {
    fn get_name() -> &'static CStr
    where
        Self: Sized,
    {
        c"test"
    }
}

#[test]
fn plugins() -> Result<()> {
    let mut solver = Solver::with_backend(&Config::default(), Cvc5)?;

    let backend = solver.solver() as &dyn Any;
    let cvc5 = backend
        .downcast_ref::<api::ApiSolver<cvc5::Solver>>()
        .unwrap()
        .solver();

    cvc5.add_plugin(Rc::new(Plugin));

    solver.declare(Declaration::constant("x", sort!(Int)))?;
    solver.declare(Declaration::constant("y", sort!(Int)))?;
    solver.require(term!(> x y))?;

    solver.check()?;

    Ok(())
}
