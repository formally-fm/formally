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
    pub extern crate formally_io as io;
    pub extern crate formally_smt as smt;
    pub extern crate formally_support as support;
}

use formally::{
    io::print::*,
    smt::{theories::*, *},
    support::*,
};

#[test]
pub fn simplify() -> Result<()> {
    let mut solver = Solver::new(&Config::default().logic("LRA"))?;
    solver.declare(Declaration::constant("x", sort!(Real)))?;
    solver.declare(Declaration::constant("y", sort!(Real)))?;
    solver.declare(Declaration::constant("z", sort!(Real)))?;

    solver.declare(Declaration::constant("p", sort!(Bool)))?;
    solver.declare(Declaration::constant("q", sort!(Bool)))?;
    solver.declare(Declaration::constant("r", sort!(Bool)))?;

    let top = Core::True().into_term_in(&*solver.pool());
    let bottom = Core::False().into_term_in(&*solver.pool());

    let mut term = solver.lookup(term!(+ x (+ y (* 2.0 y) (* 4.0 2.0 y))), Role::Function)?;
    let mut term2 = solver.lookup(term!(and #top (or q #top) (not #bottom)), Role::Function)?;
    let mut term3 = solver.lookup(term!(+ (- (+ (+ x y) (+ x y))) z), Role::Function)?;

    term = term.simplified(&*solver.pool());
    term2 = term2.simplified(&*solver.pool());
    term3 = term3.simplified(&*solver.pool());

    assert_eq!(term2, true);

    term.println(&mut std::io::stdout()).ok();
    term2.println(&mut std::io::stdout()).ok();
    term3.println(&mut std::io::stdout()).ok();

    Ok(())
}
