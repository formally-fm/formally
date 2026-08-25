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

use formally::smt::backend::{Backend, cvc5::Cvc5, z3::Z3};
use formally::{smt::*, support::*};

use std::rc::Rc;

use rstest::*;

#[test]
fn manager() -> Result<()> {
    let manager = Rc::new(TermManager::new(Cvc5));
    let config = Config::new();
    let mut slv1 = Solver::with_manager(&config, manager.clone())?;
    let mut slv2 = Solver::with_manager(&config, manager.clone())?;

    let x1 = slv1.declare(Declaration::constant("x", sort!(Int)))?;
    let x2 = slv2.declare(Declaration::constant("x", sort!(Int)))?;

    assert_eq!(x1, x2);

    let t1 = slv1.lookup(term!(* x x), Role::Function)?;
    let t2 = slv2.lookup(term!(* x x), Role::Function)?;

    assert_eq!(t1, t2);

    slv1.require(term!(= x 42))?;

    slv2.require(term!(not (= x 42)))?;

    assert_eq!(slv1.check()?, Answer::Yes);

    assert_eq!(slv2.check()?, Answer::Yes);

    Ok(())
}

#[rstest]
fn solve(#[values(Z3, Cvc5)] backend: impl Backend) -> Result<()> {
    let config = Config::new().produce_models(true);
    let mut solver = Solver::with_backend(&config, backend)?;

    let p = solver.declare(Declaration::constant("p", sort!(Bool)))?;
    let q = solver.declare(Declaration::constant("q", sort!(Bool)))?;

    solver.require(term!(=> #p #q))?;

    solver.require(p)?;

    solver.push()?;

    solver.require(term!(not q))?;

    assert_eq!(solver.check()?, Answer::No);

    solver.pop()?;

    let answer = solver.check()?;

    match answer {
        Answer::Yes => match solver.model()? {
            Some(model) => assert_eq!(model.value(q)?, Some(ModelValue::from(true))),
            None => panic!("there is no model!"),
        },
        _ => panic!("wrong answer: {answer:?}"),
    }

    Ok(())
}

#[rstest]
fn quantified(#[values(Z3, Cvc5)] backend: impl Backend) -> Result<()> {
    let config = Config::new();
    let mut solver = Solver::with_backend(&config, backend)?;

    let density = term!(
        (forall ((x Real) (y Real)) (=> (< x y) (exists ((z Real)) (and (> z x) (< z y)))))
    );
    solver.require(term!(not #density))?;

    assert_eq!(solver.check()?, Answer::No);

    Ok(())
}

#[rstest]
fn definitions(#[values(Z3, Cvc5)] backend: impl Backend) -> Result<()> {
    let config = Config::new().produce_models(true);
    let mut solver = Solver::with_backend(&config, backend)?;

    solver.declare(Declaration::constant("x", sort!(Int)))?;
    solver.declare(Declaration::constant("y", sort!(Int)))?;
    solver.define(Definition::constant("z", sort!(Int), term!(* x 2)))?;

    solver.require(term!(= x 21))?;
    solver.require(term!(= y z))?;

    let result = solver.check()?;

    assert_eq!(result, Answer::Yes);

    let model = solver.model()?.unwrap();

    assert_eq!(
        model.value(term!(y))?,
        Some(ModelValue::from(Integer::from(42)))
    );

    Ok(())
}

#[rstest]
fn variables(#[values(Z3, Cvc5)] backend: impl Backend) -> Result<()> {
    let config = Config::new().produce_models(true);
    let mut solver = Solver::with_backend(&config, backend)?;

    solver.define(Definition::function(
        "f",
        vars!((x Int) (y Int)),
        sort!(Int),
        term!(+ x y),
    ))?;
    let x = solver.declare(Declaration::constant("x", sort!(Int)))?;

    solver.require(term!(= x (f 30 12)))?;

    assert_eq!(solver.check()?, Answer::Yes);

    let value = solver.model()?.unwrap().value(x)?;
    assert_eq!(value, Some(ModelValue::from(Integer::from(42))));

    Ok(())
}

#[rstest]
fn arrays(#[values(Z3, Cvc5)] backend: impl Backend) -> Result<()> {
    let config = Config::new().produce_models(true);
    let mut solver = Solver::with_backend(&config, backend)?;

    solver.declare(Declaration::constant("a1", sort!(Array Int Int)))?;
    solver.declare(Declaration::constant("a2", sort!(Array Int Int)))?;
    let x = solver.declare(Declaration::constant("x", sort!(Int)))?;

    solver.require(term!(= a2 (store a1 0 42)))?;
    solver.require(term!(= #x (select a2 0)))?;

    assert_eq!(solver.check()?, Answer::Yes);

    let model = solver.model()?.unwrap();

    assert_eq!(model.value(x)?, Some(ModelValue::from(Integer::from(42))));

    Ok(())
}
