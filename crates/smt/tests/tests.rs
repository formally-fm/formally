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

mod formally {
    pub use formally_smt as smt;
    pub use formally_support as support;
}

use formally::{
    smt::{backend::z3::Z3, *},
    support::*,
};

#[test]
fn term_macro() -> Result<()> {
    let manager = TermManager::new(Z3);
    let mut solver = Solver::with_manager(&Config::new(), manager)?;

    let p = solver.declare(Declaration::constant("p", theories::Core::Bool()))?;
    solver.declare(Declaration::constant("q", theories::Core::Bool()))?;

    let and = Identifier::from("and");
    let q = Identifier::from("q");

    let t = term!(not q);

    solver.require(term!(p))?;
    solver.require(term!(#and (=> #p #q) #t))?;

    assert_eq!(solver.check()?, Answer::No);

    Ok(())
}
