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

use formally::smt::backends::z3::Z3;
use formally::{smt::*, support::*};

#[test]
fn solve() -> Result<()> {
    let mut solver = Solver::new(&Config::new().backend(Z3))?;

    let p = solver.declare(Declaration::constant("p", theories::Core::Bool()))?;
    let q = solver.declare(Declaration::constant("q", theories::Core::Bool()))?;

    solver.require(term!(=> #p #q))?;

    solver.require(p)?;

    solver.push()?;

    solver.require(term!(not q))?;

    assert_eq!(solver.check()?, Answer::No);

    solver.pop()?;

    let answer = solver.check()?;

    match answer {
        Answer::Yes => match solver.model()? {
            Some(model) => assert_eq!(model.value(&q), Some(ModelValue::from(true))),
            None => panic!("there is no model!"),
        },
        _ => panic!("wrong answer: {answer:?}"),
    }

    Ok(())
}
