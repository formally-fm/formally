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

use crate::formally;
use formally::io::print::*;

use crate::smtlib::ast::*;

impl Pretty for Numeral {
    fn pretty(&self) -> RcDoc<'static> {
        RcDoc::as_string(&self.value)
    }
}

impl Pretty for Decimal {
    fn pretty(&self) -> RcDoc<'static> {
        RcDoc::text(self.value.to_f64().to_string())
    }
}

impl Pretty for Hexadecimal {
    fn pretty(&self) -> RcDoc<'static> {
        RcDoc::text("#").append(RcDoc::text(self.value.to_string_radix(16)))
    }
}

impl Pretty for Binary {
    fn pretty(&self) -> RcDoc<'static> {
        RcDoc::text("#b").append(RcDoc::text(self.value.to_string_radix(2)))
    }
}

impl Pretty for StringLiteral {
    fn pretty(&self) -> RcDoc<'static> {
        let mut out = String::new();
        for c in self.value.chars() {
            out.push(c);
            if c == '\"' {
                out.push('"');
            }
        }
        quotes(RcDoc::text(out))
    }
}

impl Pretty for Constant {
    fn pretty(&self) -> RcDoc<'static> {
        match self {
            Constant::Numeral(n) => n.pretty(),
            Constant::Decimal(d) => d.pretty(),
            Constant::Hexadecimal(h) => h.pretty(),
            Constant::Binary(b) => b.pretty(),
            Constant::String(s) => s.pretty(),
        }
    }
}

impl Pretty for SimpleSymbol {
    fn pretty(&self) -> RcDoc<'static> {
        RcDoc::text(self.clone().into_inner())
    }
}

impl Pretty for QuotedSymbol {
    fn pretty(&self) -> RcDoc<'static> {
        RcDoc::text("|")
            .append(RcDoc::text(self.clone().into_inner()))
            .append(RcDoc::text("|"))
    }
}

impl Pretty for Symbol {
    fn pretty(&self) -> RcDoc<'static> {
        match self {
            Symbol::Simple(sy) => sy.pretty(),
            Symbol::Quoted(sy) => sy.pretty(),
        }
    }
}

impl Pretty for Keyword {
    fn pretty(&self) -> RcDoc<'static> {
        RcDoc::text(":").append(self.symbol.pretty())
    }
}

impl Pretty for Index {
    fn pretty(&self) -> RcDoc<'static> {
        match self {
            Index::Numeral(n) => n.pretty(),
            Index::Symbol(s) => s.pretty(),
        }
    }
}

impl Pretty for Identifier {
    fn pretty(&self) -> RcDoc<'static> {
        match self {
            Identifier::Symbol(s) => s.pretty(),
            Identifier::Application(IdApplication { head, args, .. }) => parens(
                RcDoc::text("_")
                    .append(RcDoc::space())
                    .append(head.pretty())
                    .append(RcDoc::space())
                    .append(RcDoc::intersperse(
                        args.iter().map(Pretty::pretty),
                        RcDoc::space(),
                    )),
            ),
        }
    }
}

impl Pretty for QualifiedIdentifier {
    fn pretty(&self) -> RcDoc<'static> {
        let QualifiedIdentifier { id, sort, .. } = self;
        if let Some(sort) = sort {
            parens(
                RcDoc::text("as")
                    .append(RcDoc::space())
                    .append(id.pretty())
                    .append(RcDoc::space())
                    .append(sort.pretty()),
            )
        } else {
            id.pretty()
        }
    }
}

impl Pretty for Sort {
    fn pretty(&self) -> RcDoc<'static> {
        match self {
            Sort::Simple(id) => id.pretty(),
            Sort::Application(SortApplication { head, args, .. }) => parens(
                head.pretty()
                    .append(RcDoc::space())
                    .append(RcDoc::intersperse(
                        args.iter().map(Pretty::pretty),
                        RcDoc::space(),
                    )),
            ),
            Sort::Term(t) => t.pretty(),
        }
    }
}

impl Pretty for Binding {
    fn pretty(&self) -> RcDoc<'static> {
        parens(
            self.name
                .pretty()
                .append(RcDoc::space())
                .append(self.body.pretty()),
        )
    }
}

impl Pretty for SortedVar {
    fn pretty(&self) -> RcDoc<'static> {
        parens(
            self.name
                .pretty()
                .append(RcDoc::space())
                .append(self.sort.pretty()),
        )
    }
}

impl Pretty for Application {
    fn pretty(&self) -> RcDoc<'static> {
        let Application { head: id, args, .. } = self;
        parens(
            id.pretty()
                .append(RcDoc::space())
                .append(RcDoc::intersperse(
                    args.iter().map(Pretty::pretty),
                    RcDoc::space(),
                )),
        )
    }
}

impl Pretty for Let {
    fn pretty(&self) -> RcDoc<'static> {
        let Let { bindings, body, .. } = self;
        parens(
            RcDoc::text("let").append(RcDoc::space()).append(
                parens(RcDoc::intersperse(
                    bindings.iter().map(Pretty::pretty),
                    RcDoc::space(),
                ))
                .append(RcDoc::space())
                .append(body.pretty()),
            ),
        )
    }
}

impl Pretty for Pattern {
    fn pretty(&self) -> RcDoc<'static> {
        match self {
            Pattern::Symbol(SymbolPattern { symbol: None, .. }) => RcDoc::text("_"),
            Pattern::Symbol(SymbolPattern {
                symbol: Some(s), ..
            }) => s.pretty(),
            Pattern::Application(ApplicationPattern { head, args, .. }) => parens(
                head.pretty()
                    .append(RcDoc::space())
                    .append(RcDoc::intersperse(
                        args.iter().map(|o| match &o.symbol {
                            None => RcDoc::text("_"),
                            Some(arg) => arg.pretty(),
                        }),
                        RcDoc::space(),
                    )),
            ),
        }
    }
}

impl Pretty for MatchCase {
    fn pretty(&self) -> RcDoc<'static> {
        let MatchCase { pattern, body, .. } = self;

        parens(
            pattern
                .pretty()
                .append(RcDoc::space())
                .append(body.pretty()),
        )
    }
}

impl Pretty for Match {
    fn pretty(&self) -> RcDoc<'static> {
        let Match { head, cases, .. } = self;
        parens(
            RcDoc::text("match")
                .append(RcDoc::space())
                .append(head.pretty())
                .append(RcDoc::space())
                .append(parens(RcDoc::intersperse(
                    cases.iter().map(Pretty::pretty),
                    RcDoc::space(),
                ))),
        )
    }
}

impl Pretty for Term {
    fn pretty(&self) -> RcDoc<'static> {
        fn lambda(kw: &str, vars: &[SortedVar], t: &Term) -> RcDoc<'static> {
            parens(
                RcDoc::text(kw.to_string()).append(RcDoc::space()).append(
                    parens(RcDoc::intersperse(
                        vars.iter().map(Pretty::pretty),
                        RcDoc::space(),
                    ))
                    .append(RcDoc::space())
                    .append(t.pretty()),
                ),
            )
        }

        match self {
            Term::Constant(c) => c.pretty(),
            Term::Identifier(id) => id.pretty(),
            Term::Application(app) => app.pretty(),
            Term::Let(l) => l.pretty(),
            Term::Lambda(Lambda { bindings, body, .. }) => lambda("lambda", bindings, body),
            Term::Exists(Exists { bindings, body, .. }) => lambda("exists", bindings, body),
            Term::Forall(Forall { bindings, body, .. }) => lambda("forall", bindings, body),
            Term::Match(m) => m.pretty(),
            Term::Attributed(_) => todo!(),
        }
    }
}

impl Pretty for InfoFlag {
    fn pretty(&self) -> RcDoc<'static> {
        match self {
            InfoFlag::AllStatistics => RcDoc::text(":all-statistics"),
            InfoFlag::AssertionStackLevels => RcDoc::text(":assertion-stack-levels"),
            InfoFlag::Authors => RcDoc::text(":authors"),
            InfoFlag::ErrorBehavior => RcDoc::text(":error-behavior"),
            InfoFlag::Name => RcDoc::text(":name"),
            InfoFlag::ReasonUnknown => RcDoc::text(":reason-unknown"),
            InfoFlag::Version => RcDoc::text(":version"),
            InfoFlag::Keyword(kw) => kw.pretty(),
        }
    }
}

impl Pretty for Command {
    fn pretty(&self) -> RcDoc<'static> {
        let doc = match self {
            Command::Assert(assert) => RcDoc::text("assert")
                .append(RcDoc::space())
                .append(assert.term.pretty()),
            Command::CheckSat(_) => RcDoc::text("check-sat"),
            Command::CheckSatAssuming(CheckSatAssuming { assumptions, .. }) => {
                RcDoc::text("check-sat-assuming")
                    .append(RcDoc::space())
                    .append(parens(RcDoc::intersperse(
                        assumptions.iter().map(Pretty::pretty),
                        RcDoc::space(),
                    )))
            }
            Command::DeclareConst(DeclareConst { name, sort, .. }) => RcDoc::text("declare-const")
                .append(RcDoc::space())
                .append(name.pretty())
                .append(RcDoc::space())
                .append(sort.pretty()),
            Command::DeclareDatatype(_) => todo!(),
            Command::DeclareDatatypes(_) => todo!(),
            Command::DeclareFun(DeclareFun {
                name,
                domain,
                range,
                ..
            }) => RcDoc::text("declare-fun")
                .append(RcDoc::space())
                .append(name.pretty())
                .append(RcDoc::space())
                .append(parens(RcDoc::intersperse(
                    domain.iter().map(Pretty::pretty),
                    RcDoc::space(),
                )))
                .append(RcDoc::space())
                .append(range.pretty()),
            Command::DeclareSort(DeclareSort { name, arity, .. }) => RcDoc::text("declare-sort")
                .append(RcDoc::space())
                .append(name.pretty())
                .append(RcDoc::space())
                .append(arity.pretty()),
            Command::DeclareSortParameter(s) => RcDoc::text("declare-sort-parameter")
                .append(RcDoc::space())
                .append(s.pretty()),
            Command::DefineConst(DefineConst {
                name, sort, body, ..
            }) => RcDoc::text("define-const")
                .append(RcDoc::space())
                .append(name.pretty())
                .append(RcDoc::space())
                .append(sort.pretty())
                .append(RcDoc::space())
                .append(body.pretty()),
            Command::DefineFun(_) => todo!(),
            Command::DefineFunRec(_) => todo!(),
            Command::DefineFunsRec(_) => todo!(),
            Command::DefineSort(DefineSort {
                name,
                parameters,
                body,
                ..
            }) => RcDoc::text("define-sort")
                .append(RcDoc::space())
                .append(name.pretty())
                .append(RcDoc::space())
                .append(RcDoc::intersperse(
                    parameters.iter().map(Pretty::pretty),
                    RcDoc::space(),
                ))
                .append(RcDoc::space())
                .append(body.pretty()),
            Command::Echo(msg) => RcDoc::text("echo")
                .append(RcDoc::space())
                .append(msg.pretty()),
            Command::Exit(_) => RcDoc::text("exit"),
            Command::GetAssertions(_) => RcDoc::text("get-assertions"),
            Command::GetAssignments(_) => RcDoc::text("get-assignments"),
            Command::GetInfo(GetInfo { flag, .. }) => RcDoc::text("get-info")
                .append(RcDoc::space())
                .append(flag.pretty()),
            Command::GetModel(_) => RcDoc::text("get-model"),
            Command::GetOption(GetOption { keyword, .. }) => RcDoc::text("get-option")
                .append(RcDoc::space())
                .append(keyword.pretty()),
            Command::GetProof(_) => RcDoc::text("get-proof"),
            Command::GetUnsatAssumptions(_) => RcDoc::text("get-unsat-assumptions"),
            Command::GetUnsatCore(_) => RcDoc::text("get-unsat-core"),
            Command::GetValue(GetValue { terms, .. }) => RcDoc::text("get-value")
                .append(RcDoc::space())
                .append(RcDoc::intersperse(
                    terms.iter().map(Pretty::pretty),
                    RcDoc::space(),
                )),
            Command::Pop(Pop { levels, .. }) => RcDoc::text("pop")
                .append(RcDoc::space())
                .append(levels.pretty()),
            Command::Push(Push { levels, .. }) => RcDoc::text("push")
                .append(RcDoc::space())
                .append(levels.pretty()),
            Command::Reset(_) => RcDoc::text("reset"),
            Command::ResetAssertions(_) => RcDoc::text("reset-assertions"),
            Command::SetInfo(_) => todo!(),
            Command::SetLogic(SetLogic { logic, .. }) => RcDoc::text("set-logic")
                .append(RcDoc::space())
                .append(logic.pretty()),
            Command::SetOption(_) => todo!(),
        };

        parens(doc)
    }
}

impl Pretty for Script {
    fn pretty(&self) -> RcDoc<'static> {
        let Script { commands, .. } = self;

        RcDoc::intersperse(commands.iter().map(Pretty::pretty), RcDoc::hardline())
    }
}

impl Pretty for Response {
    fn pretty(&self) -> RcDoc<'static> {
        match self {
            Response::Success => RcDoc::text("success"),
            Response::Unsupported => RcDoc::text("unsupported"),
            Response::Error(msg) => parens(
                RcDoc::text("error")
                    .append(RcDoc::space())
                    .append(msg.pretty()),
            ),
            Response::CheckSat(cks) => cks.pretty(),
            Response::Echo(EchoResponse { msg, .. }) => RcDoc::text(msg.value.clone()),
            Response::GetAssertions(_) => todo!(),
            Response::GetAssignment(_) => todo!(),
            Response::GetInfo(_) => todo!(),
            Response::GetModel(_) => todo!(),
            Response::GetOption(_) => todo!(),
            Response::GetProof(_) => todo!(),
            Response::GetUnsatAssumption(_) => todo!(),
            Response::GetUnsatCore(_) => todo!(),
            Response::GetValue(GetValueResponse { values, .. }) => parens(RcDoc::intersperse(
                values.iter().map(|(name, value)| {
                    parens(name.pretty().append(RcDoc::space()).append(value.pretty()))
                }),
                RcDoc::hardline(),
            )),
        }
    }
}

impl Pretty for CheckSatResponse {
    fn pretty(&self) -> RcDoc<'static> {
        match self.response {
            Some(true) => RcDoc::text("sat"),
            Some(false) => RcDoc::text("unsat"),
            None => RcDoc::text("unknown"),
        }
    }
}
