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

use formally::{
    io::{parse::*, print::Print},
    support::*,
};

use formally::smt::smtlib;
use rstest::*;
use std::{fmt::Debug, io::Cursor};

#[rstest]
#[case("255", smtlib::ast::Numeral::parser())]
#[case("3.14", smtlib::ast::Decimal::parser())]
#[case("#abba", smtlib::ast::Hexadecimal::parser())]
#[case("#b101", smtlib::ast::Binary::parser())]
#[case("\"ciao \"\"mondo\"\"!\"", smtlib::ast::StringLiteral::parser())]
#[case("Array", smtlib::ast::Index::parser())]
#[case("3", smtlib::ast::Index::parser())]
#[case("Array", smtlib::ast::Identifier::parser())]
#[case("|Array LoL|", smtlib::ast::Identifier::parser())]
#[case("(_ Array 3 Int)", smtlib::ast::Identifier::parser())]
#[case("(_ Array 3 Int)", smtlib::ast::Sort::parser())]
#[case(
    "(as pippo (_ Array 3 Int))",
    smtlib::ast::QualifiedIdentifier::parser()
)]
#[case("((as pippo (_ Array 3 Int)) 42)", smtlib::ast::Term::parser())]
#[case("(let ((x 20) (y 22)) (+ x y))", smtlib::ast::Term::parser())]
#[case("(lambda ((x Int) (y Int)) (+ x y))", smtlib::ast::Term::parser())]
#[case("(exists ((x Int) (y Int)) (+ x y))", smtlib::ast::Term::parser())]
#[case("(forall ((x Int) (y Int)) (+ x y))", smtlib::ast::Term::parser())]
// TODO: reimplement the parser for match constructs
//#[case("(match x ((None 0) ((Option _) 1)))", smtlib::ast::Term::parser())]
#[case("(assert (= 42 (+ 20 22)))", smtlib::ast::Command::parser())]
#[case(
    "(check-sat-assuming ((< x 42) (> x 42)))",
    smtlib::ast::Command::parser()
)]
#[case(
    "(declare-fun index ((_ Array 3 Int) Int) Int)",
    smtlib::ast::Command::parser()
)]
#[case("(define-const pi Real 3.14)", smtlib::ast::Command::parser())]
pub fn successes<T: Debug + Print>(
    #[case] input: &str,
    #[case] parser: Parser<'_, T>,
) -> std::io::Result<()> {
    let mut output = Vec::new();
    let mut cursor = Cursor::new(&mut output);

    eprintln!("parsing: {input}...");
    let emitter = StdErrEmitter::new();

    let result = parser.parse(&emitter, input);
    match result {
        Ok(out) => {
            eprintln!(" - parsed!");
            eprintln!("{:?}", out);
            out.render(&mut cursor, 80)?;
            assert_eq!(String::from_utf8(output).unwrap(), input);
        }
        Err(err) => {
            eprintln!(" - parsing error: {err:?}");
            unreachable!()
        }
    }
    Ok(())
}
