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

use crate::smtlib::ast::*;
use formally_io::parse::{combinators::*, parsers::*, *};

use rug::ops::CompleteRound;
use std::str::FromStr as _;

impl<'c> Parsable<'c> for Boolean {
    fn parser() -> Parser<'c, Self> {
        keyword("true")
            .with_value(true)
            .or(keyword("false").with_value(false))
            .map(|value| Boolean { value, span: None })
            .located()
    }
}

impl<'c> Parsable<'c> for Numeral {
    fn parser() -> Parser<'c, Numeral> {
        ascii_digit()
            .many1()
            .skipping(nothing())
            .requires(
                |v: &String| v.len() == 1 || !v.starts_with('0'),
                "numerals cannot start with zero",
            )
            .to_string()
            .map(|s| Numeral {
                value: rug::Integer::from_str(s.as_str()).unwrap(),
                span: None,
            })
            .located()
            .silent()
            .named("integer number", "integer numbers")
    }
}

impl<'c> Parsable<'c> for Decimal {
    fn parser() -> Parser<'c, Decimal> {
        let int = ascii_digit().many1().requires(
            |v: &String| v.len() == 1 || !v.starts_with('0'),
            "numerals cannot start with zero",
        );
        let dot = char('.')
            .named("decimal dot", "decimal dots")
            .once()
            .to_string();
        let frac = ascii_digit()
            .many1()
            .to_string()
            .named("fractional part", "fractional parts");

        int.and(dot)
            .and(frac)
            .map(|((int, _), frac)| format!("{int}.{frac}"))
            .skipping(nothing())
            .map(|s| Decimal {
                value: rug::Float::parse(s)
                    .unwrap()
                    .complete(53)
                    .to_rational()
                    .unwrap(),
                span: None,
            })
            .located()
            .silent()
            .named("decimal number", "decimal numbers")
    }
}

impl<'c> Parsable<'c> for Hexadecimal {
    fn parser() -> Parser<'c, Hexadecimal> {
        char('#')
            .then(ascii_hexdigit().many1().skipping(nothing()).to_string())
            .map(|s: String| Hexadecimal {
                value: rug::Integer::from_str_radix(&s, 16).unwrap(),
                span: None,
            })
            .located()
            .named("hexadecimal number", "hexadecimal numbers")
    }
}

impl<'c> Parsable<'c> for Binary {
    fn parser() -> Parser<'c, Binary> {
        text("#b")
            .then(ascii_binary_digit().many1().skipping(nothing()).to_string())
            .map(|s: String| Binary {
                value: rug::Integer::from_str_radix(&s, 2).unwrap(),
                span: None,
            })
            .located()
            .named("binary number", "binary numbers")
    }
}

impl<'c> Parsable<'c> for StringLiteral {
    fn parser() -> Parser<'c, StringLiteral> {
        any()
            .only_if(|c| *c != '"' && (c.is_ascii_graphic() || c.is_ascii_whitespace()))
            .named("printable character", "printable characters")
            .or(text("\"\"").with_value('"'))
            .many()
            .skipping(nothing())
            .between(char('"'), char('"'))
            .map(|value| StringLiteral { value, span: None })
            .located()
            .silent()
            .named("string literal", "string literals")
    }
}

impl<'c> Parsable<'c> for Constant {
    fn parser() -> Parser<'c, Constant> {
        Decimal::parser()
            .map(Constant::Decimal)
            .or(Numeral::parser().map(Constant::Numeral))
            .or(Hexadecimal::parser().map(Constant::Hexadecimal))
            .or(Binary::parser().map(Constant::Binary))
            .or(StringLiteral::parser().map(Constant::String))
            .named("constant", "constants")
    }
}

impl<'c> Parsable<'c> for SimpleSymbol {
    fn parser() -> Parser<'c, SimpleSymbol> {
        any()
            .only_if(|c| SimpleSymbol::admitted(*c))
            .named(
                "character admitted in simple symbols",
                "characters admitted in simple symbols",
            )
            .many1()
            .skipping(nothing())
            .only_if(|s: &String| !SimpleSymbol::invalid(s))
            .map(|s| SimpleSymbol::new(&s))
            .unwrap()
            .located()
            .named("simple symbol", "simple symbols")
    }
}

impl<'c> Parsable<'c> for QuotedSymbol {
    fn parser() -> Parser<'c, QuotedSymbol> {
        any()
            .only_if(|c| QuotedSymbol::admitted(*c))
            .named(
                "character admitted in quoted symbols",
                "characters admitted in quoted symbols",
            )
            .many()
            .between(char('|'), char('|'))
            .skipping(nothing())
            .map(|s: String| QuotedSymbol::new(&s))
            .unwrap()
            .located()
            .silent()
            .named("quoted symbol", "quoted symbols")
    }
}

impl<'c> Parsable<'c> for Symbol {
    fn parser() -> Parser<'c, Symbol> {
        SimpleSymbol::parser()
            .map(Symbol::Simple)
            .or(QuotedSymbol::parser().map(Symbol::Quoted))
            .map(|sy| sy.simplify())
            .silent()
            .named("symbol", "symbols")
    }
}

impl<'c> Parsable<'c> for Keyword {
    fn parser() -> Parser<'c, Keyword> {
        char(':')
            .then(SimpleSymbol::parser())
            .map(|symbol| Keyword { symbol, span: None })
            .located()
    }
}

impl<'c> Parsable<'c> for Sort {
    fn parser() -> Parser<'c, Sort> {
        Identifier::parser()
            .map(Sort::Simple)
            .or(Identifier::parser()
                .and(lazy(Sort::parser).named("argument", "arguments").many1())
                .parens()
                .map(|(head, args)| SortApplication {
                    head,
                    args,
                    span: None,
                })
                .map(Sort::Application)
                .located())
            .named("sort", "sorts")
    }
}

impl<'c> Parsable<'c> for Index {
    fn parser() -> Parser<'c, Index> {
        Numeral::parser()
            .map(Index::Numeral)
            .or(Symbol::parser().map(Index::Symbol))
            .located()
    }
}

impl<'c> Parsable<'c> for Identifier {
    fn parser() -> Parser<'c, Identifier> {
        Symbol::parser()
            .map(Identifier::Symbol)
            .or(char('_')
                .then(Symbol::parser())
                .and(
                    Index::parser()
                        .named("argument", "arguments")
                        .many1()
                        .named("argument list", "argument lists"),
                )
                .map(|(head, args)| {
                    Identifier::Application(IdApplication {
                        head,
                        args,
                        span: None,
                    })
                })
                .located()
                .parens())
            .silent()
            .named("identifier", "identifiers")
    }
}

impl<'c> Parsable<'c> for QualifiedIdentifier {
    fn parser() -> Parser<'c, QualifiedIdentifier> {
        Identifier::parser()
            .map(QualifiedIdentifier::from)
            .or(keyword("as")
                .then(Identifier::parser())
                .and(Sort::parser())
                .map(|(id, sort)| QualifiedIdentifier {
                    id,
                    sort: Some(sort),
                    span: None,
                })
                .located()
                .parens())
            .silent()
            .located()
            .named("qualified identifier", "qualified identifiers")
    }
}

impl<'c> Parsable<'c> for Application {
    fn parser() -> Parser<'c, Self> {
        QualifiedIdentifier::parser()
            .and(lazy(Term::parser).many1())
            .map(|(head, args)| Application {
                head,
                args,
                span: None,
            })
            .located()
            .named("function application", "function applications")
    }
}

impl<'c> Parsable<'c> for Binding {
    fn parser() -> Parser<'c, Self> {
        Symbol::parser()
            .and(lazy(Term::parser))
            .parens()
            .map(|(name, body)| Binding {
                name,
                body,
                span: None,
            })
            .located()
            .named("variable binding", "variable bindings")
    }
}

impl<'c> Parsable<'c> for Let {
    fn parser() -> Parser<'c, Self> {
        keyword("let")
            .then(
                Binding::parser()
                    .many1()
                    .parens()
                    .named("variable bindings list", "variable bindings lists"),
            )
            .and(recursive(Term::parser))
            .map(|(bindings, body)| Let {
                bindings,
                body,
                span: None,
            })
            .located()
            .named("let expression", "let expressions")
    }
}

impl<'c> Parsable<'c> for SortedVar {
    fn parser() -> Parser<'c, Self> {
        Symbol::parser()
            .and(Sort::parser())
            .parens()
            .map(|(name, sort)| SortedVar {
                name,
                sort,
                span: None,
            })
            .located()
            .named("sorted variable", "sorted variables")
    }
}

impl<'c> Parsable<'c> for FunctionDef {
    fn parser() -> Parser<'c, Self> {
        Symbol::parser()
            .and(SortedVar::parser().many1().parens())
            .and(Sort::parser())
            .and(Term::parser())
            .map(|(((name, domain), range), body)| FunctionDef {
                name,
                domain,
                range,
                body,
                span: None,
            })
            .located()
            .named("function definition", "function definitions")
    }
}

impl<'c> Parsable<'c> for Lambda {
    fn parser() -> Parser<'c, Self> {
        keyword("lambda")
            .then(
                SortedVar::parser()
                    .many1()
                    .parens()
                    .named("sorted variables list", "sorted variables lists"),
            )
            .and(recursive(Term::parser))
            .map(|(bindings, body)| Lambda {
                bindings,
                body,
                span: None,
            })
            .located()
            .named("lambda expression", "lambda expressions")
    }
}

impl<'c> Parsable<'c> for Exists {
    fn parser() -> Parser<'c, Self> {
        keyword("exists")
            .then(
                SortedVar::parser()
                    .many1()
                    .parens()
                    .named("sorted variables list", "sorted variables lists"),
            )
            .and(recursive(Term::parser))
            .map(|(bindings, body)| Exists {
                bindings,
                body,
                span: None,
            })
            .located()
            .named("existential quantification", "existential quantifications")
    }
}

impl<'c> Parsable<'c> for Forall {
    fn parser() -> Parser<'c, Self> {
        keyword("forall")
            .then(
                SortedVar::parser()
                    .many1()
                    .parens()
                    .named("sorted variables list", "sorted variables lists"),
            )
            .and(recursive(Term::parser))
            .map(|(bindings, body)| Forall {
                bindings,
                body,
                span: None,
            })
            .located()
            .named("universal quantification", "universal quantifications")
    }
}

impl<'c> Parsable<'c> for Match {
    fn parser() -> Parser<'c, Self> {
        reject()
    }
}

impl<'c> Parsable<'c> for Term {
    fn parser() -> Parser<'c, Term> {
        Constant::parser()
            .map(Term::Constant)
            .or(QualifiedIdentifier::parser().map(Term::Identifier))
            .or(Application::parser()
                .map(Term::Application)
                .or(Let::parser().map(Term::Let))
                .or(Lambda::parser().map(Term::Lambda))
                .or(Exists::parser().map(Term::Exists))
                .or(Forall::parser().map(Term::Forall))
                .or(Match::parser().map(Term::Match))
                .parens())
            .silent()
            .named("term", "terms")
    }
}

impl<'c> Parsable<'c> for InfoFlag {
    fn parser() -> Parser<'c, Self> {
        keyword(":all-statistics")
            .with_value(InfoFlag::AllStatistics)
            .or(keyword(":assertion-stack-levels").with_value(InfoFlag::AssertionStackLevels))
            .or(keyword(":authors").with_value(InfoFlag::Authors))
            .or(keyword(":error-behavior").with_value(InfoFlag::ErrorBehavior))
            .or(keyword(":name").with_value(InfoFlag::Name))
            .or(keyword(":reason-unknown").with_value(InfoFlag::ReasonUnknown))
            .or(keyword(":version").with_value(InfoFlag::Version))
            .or(Keyword::parser().map(InfoFlag::Keyword))
            .named("info flag", "info flags")
    }
}

impl<'c> Parsable<'c> for Command {
    fn parser() -> Parser<'c, Self> {
        fn command<'a, T: 'a>(name: &'a str, p: Parser<'a, T>) -> Parser<'a, T> {
            keyword(name)
                .then(p)
                .named(format!("{name} command"), format!("{name} commands"))
        }

        command(
            "assert",
            Term::parser().map(|term| Command::Assert(Assert { term, span: None })),
        )
        .or(command(
            "check-sat-assuming",
            Term::parser().many().parens().map(|assumptions| {
                Command::CheckSatAssuming(CheckSatAssuming {
                    assumptions,
                    span: None,
                })
            }),
        ))
        .or(command(
            "check-sat",
            succeed().map(|_| Command::CheckSat(None)),
        ))
        .or(command(
            "declare-const",
            Symbol::parser().and(Sort::parser()).map(|(name, sort)| {
                Command::DeclareConst(DeclareConst {
                    name,
                    sort,
                    span: None,
                })
            }),
        ))
        //.or(keyword("declare-datatype"))
        //.or(keyword("declare-datatypes"))
        .or(command(
            "declare-fun",
            Symbol::parser()
                .and(Sort::parser().many().parens())
                .and(Sort::parser())
                .map(|((name, domain), range)| {
                    Command::DeclareFun(DeclareFun {
                        name,
                        domain,
                        range,
                        span: None,
                    })
                }),
        ))
        .or(command(
            "declare-sort-parameter",
            Symbol::parser().map(Command::DeclareSortParameter),
        ))
        .or(command(
            "declare-sort",
            Symbol::parser()
                .and(Numeral::parser())
                .map(|(name, arity)| {
                    Command::DeclareSort(DeclareSort {
                        name,
                        arity,
                        span: None,
                    })
                }),
        ))
        .or(command(
            "define-const",
            Symbol::parser()
                .and(Sort::parser())
                .and(Term::parser())
                .map(|((name, sort), body)| {
                    Command::DefineConst(DefineConst {
                        name,
                        sort,
                        body,
                        span: None,
                    })
                }),
        ))
        .or(command(
            "define-fun",
            FunctionDef::parser().map(Command::DefineFun),
        ))
        //.or(keyword("define-fun-rec"))
        //.or(keyword("define-funs-rec"))
        .or(command(
            "define-sort",
            Symbol::parser()
                .and(Symbol::parser().many().parens())
                .and(Sort::parser())
                .map(|((name, parameters), body)| {
                    Command::DefineSort(DefineSort {
                        name,
                        parameters,
                        body,
                        span: None,
                    })
                }),
        ))
        .or(command("echo", StringLiteral::parser().map(Command::Echo)))
        .or(command(
            "get-assertions",
            succeed().map(|_| Command::GetAssertions(None)),
        ))
        .or(command(
            "get-info",
            InfoFlag::parser().map(|flag| Command::GetInfo(GetInfo { flag, span: None })),
        ))
        .or(command(
            "get-model",
            succeed().map(|_| Command::GetModel(None)),
        ))
        .or(command(
            "get-option",
            Keyword::parser().map(|keyword| {
                Command::GetOption(GetOption {
                    keyword,
                    span: None,
                })
            }),
        ))
        .or(command(
            "get-proof",
            succeed().map(|_| Command::GetProof(None)),
        ))
        .or(command(
            "get-unsat-assumptions",
            succeed().map(|_| Command::GetUnsatAssumptions(None)),
        ))
        .or(command(
            "get-unsat-core",
            succeed().map(|_| Command::GetUnsatCore(None)),
        ))
        .or(command(
            "get-value",
            Term::parser()
                .many1()
                .map(|terms| Command::GetValue(GetValue { terms, span: None }))
                .parens(),
        ))
        .or(command(
            "pop",
            Numeral::parser().map(|levels| Command::Pop(Pop { levels, span: None })),
        ))
        .or(command(
            "push",
            Numeral::parser().map(|levels| Command::Push(Push { levels, span: None })),
        ))
        .or(command(
            "reset-assertions",
            succeed().map(|_| Command::ResetAssertions(None)),
        ))
        .or(command("reset", succeed().map(|_| Command::Reset(None))))
        // .or(keyword("set-info").then(Attribute::ast()).map(SetInfo))
        .or(command(
            "set-logic",
            Symbol::parser().map(|logic| Command::SetLogic(SetLogic { logic, span: None })),
        ))
        .or(command(
            "set-option",
            AstOption::parser().map(|option| Command::SetOption(SetOption { option, span: None })),
        ))
        .located()
        .named("SMT-LIBv2 command", "SMT-LIBv2 commands")
        .parens()
        .named("SMT-LIBv2 command", "SMT-LIBv2 commands")
    }
}

impl<'c> Parsable<'c> for AttributeValue {
    fn parser() -> Parser<'c, Self> {
        Constant::parser()
            .map(AttributeValue::Constant)
            .or(Symbol::parser().map(AttributeValue::Symbol))
    }
}

impl<'c> Parsable<'c> for Attribute {
    fn parser() -> Parser<'c, Self> {
        Keyword::parser()
            .and(AttributeValue::parser())
            .map(|(keyword, value)| Attribute {
                keyword,
                value,
                span: None,
            })
            .located()
    }
}

impl<'c> Parsable<'c> for AstOption {
    fn parser() -> Parser<'c, Self> {
        Attribute::parser().map(|attr| match AstOption::try_from(attr.clone()) {
            Ok(opt) => opt,
            Err(_) => AstOption::Attribute(Box::new(attr)),
        })
    }
}

impl<'c> Parsable<'c> for Script {
    fn parser() -> Parser<'c, Self> {
        Command::parser()
            .many1()
            .map(|commands| Script {
                commands,
                span: None,
            })
            .whole()
            .located()
            .named("SMT-LIBv2 script", "SMT-LIBv2 scripts")
    }
}

impl<'c> Parsable<'c> for CheckSatResponse {
    fn parser() -> Parser<'c, Self> {
        keyword("sat")
            .with_value(Some(true))
            .or(keyword("unsat").with_value(Some(false)))
            .or(keyword("unknown").with_value(None))
            .map(|response| CheckSatResponse {
                response,
                span: None,
            })
            .located()
            .named("check-sat response", "check-sat responses")
    }
}

impl<'c> Parsable<'c> for ErrorBehavior {
    fn parser() -> Parser<'c, Self> {
        use ErrorBehavior::*;

        keyword("immediate-exit")
            .with_value(ImmediateExit)
            .or(keyword("continued-execution").with_value(ContinuedExecution))
            .named(":error-behavior response", ":error-behavior responses")
    }
}

impl<'c> Parsable<'c> for SExprElement {
    fn parser() -> Parser<'c, Self> {
        Constant::parser()
            .map(SExprElement::Constant)
            .or(Symbol::parser().map(SExprElement::Symbol))
            .or(Keyword::parser().map(SExprElement::Keyword))
    }
}

impl<'c> Parsable<'c> for SExpr {
    fn parser() -> Parser<'c, Self> {
        SExprElement::parser()
            .map(SExpr::Element)
            .or(lazy(SExpr::parser)
                .many()
                .map(|exprs| SExpr::List(SExprList { exprs, span: None }))
                .located())
            .named("s-expression", "s-expressions")
    }
}

impl<'c> Parsable<'c> for ReasonUnknown {
    fn parser() -> Parser<'c, Self> {
        keyword("memout")
            .map(|_| ReasonUnknown::Memout)
            .or(keyword("incomplete").map(|_| ReasonUnknown::Incomplete))
            .or(SExpr::parser().map(ReasonUnknown::SExpr))
    }
}

impl<'c> Parsable<'c> for Info {
    fn parser() -> Parser<'c, Self> {
        keyword(":assertion-stack-levels")
            .then(Numeral::parser())
            .map(Info::AssertionStackLevels)
            .or(keyword(":authors")
                .then(StringLiteral::parser())
                .map(Info::Authors))
            .or(keyword(":error-behavior")
                .then(ErrorBehavior::parser())
                .map(Info::ErrorBehavior))
            .or(keyword(":name")
                .then(StringLiteral::parser())
                .map(Info::Name))
            .or(keyword(":reason-unknown")
                .then(ReasonUnknown::parser())
                .map(Info::ReasonUnknown))
            .or(keyword(":version")
                .then(StringLiteral::parser())
                .map(Info::Version))
            //.or(Attribute::ast().map(InfoResponse::Attribute))
            .named("get-info response", "get-info responses")
    }
}

impl<'c> Parsable<'c> for Model {
    fn parser() -> Parser<'c, Self> {
        todo!()
    }
}

impl<'c> Parsable<'c> for Response {
    fn parser() -> Parser<'c, Self> {
        keyword("success")
            .map(|_| Response::Success)
            .or(keyword("unsupported").map(|_| Response::Unsupported))
            .or(keyword("error")
                .then(StringLiteral::parser())
                .map(Response::Error))
            .or(keyword("sat").map(|_| {
                Response::CheckSat(CheckSatResponse {
                    response: Some(true),
                    span: None,
                })
            }))
            .or(keyword("unsat").map(|_| {
                Response::CheckSat(CheckSatResponse {
                    response: Some(false),
                    span: None,
                })
            }))
            .or(keyword("unknown").map(|_| {
                Response::CheckSat(CheckSatResponse {
                    response: None,
                    span: None,
                })
            }))
            .or(StringLiteral::parser().map(|msg| Response::Echo(EchoResponse { msg, span: None })))
            .or(Term::parser().many().parens().map(|assertions| {
                Response::GetAssertions(GetAssertionsResponse {
                    assertions,
                    span: None,
                })
            }))
            .or(Symbol::parser()
                .and(Boolean::parser())
                .parens()
                .many()
                .parens()
                .map(|assignments| {
                    Response::GetAssignment(GetAssignmentResponse {
                        assignments,
                        span: None,
                    })
                }))
            .or(Info::parser()
                .many1()
                .parens()
                .map(|infos| Response::GetInfo(GetInfoResponse { infos, span: None })))
            .or(Model::parser()
                .many()
                .parens()
                .map(|models| Response::GetModel(GetModelResponse { models, span: None })))
            //.or(AttributeValue::ast().map(Response::GetOption))
            .or(SExpr::parser()
                .map(|proof| Response::GetProof(GetProofResponse { proof, span: None })))
            .or(Term::parser().many().parens().map(|assumption| {
                Response::GetUnsatAssumption(GetUnsatAssumptionResponse {
                    assumption,
                    span: None,
                })
            }))
            .or(Symbol::parser()
                .many()
                .parens()
                .map(|core| Response::GetUnsatCore(GetUnsatCoreResponse { core, span: None })))
            .or(Term::parser()
                .and(Term::parser())
                .parens()
                .many1()
                .parens()
                .map(|values| Response::GetValue(GetValueResponse { values, span: None })))
            .located()
    }
}
