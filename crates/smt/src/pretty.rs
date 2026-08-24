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

use crate::*;

use formally::{
    io::print::{Pretty, RcDoc},
    smt::smtlib::ast,
    support::*,
};

use formally_io::print::Print;
use std::fmt::{Display, Formatter};

impl From<Identifier<'_>> for ast::Symbol {
    fn from(value: Identifier<'_>) -> Self {
        ast::Symbol::Quoted(ast::QuotedSymbol {
            span: value.span().clone(),
            value: value.into_string(),
        })
        .simplify()
    }
}

impl From<Identifier<'_>> for ast::QualifiedIdentifier {
    fn from(value: Identifier<'_>) -> Self {
        let symbol = ast::Symbol::from(value);
        ast::QualifiedIdentifier {
            span: symbol.span(),
            id: ast::Identifier::Symbol(symbol),
            sort: None,
        }
    }
}

impl From<Constant> for ast::Constant {
    fn from(cnst: Constant) -> Self {
        match cnst {
            Constant::Integer { value, span } => ast::Constant::Numeral(ast::Numeral {
                value: (*value).clone(),
                span,
            }),
            Constant::Rational { value, span } => ast::Constant::Decimal(ast::Decimal {
                value: (*value).clone(),
                span,
            }),
        }
    }
}

impl From<Term> for ast::Term {
    fn from(term: Term) -> Self {
        match term.kind() {
            TermKind::Constant(cnst) => ast::Term::Constant(ast::Constant::from(cnst.clone())),
            TermKind::Atom(atom) => {
                let (id, arguments) = match &atom.head {
                    FunctionRef::Bound(BoundRef { function, .. }) => {
                        (function.name().clone(), &*atom.arguments)
                    }
                    FunctionRef::Unbound(UnboundRef { name: head, .. }) => {
                        (head.clone(), &*atom.arguments)
                    }
                };

                ast::Term::Application(ast::Application {
                    head: ast::QualifiedIdentifier::from(id),
                    args: arguments
                        .iter()
                        .map(|arg| ast::Term::from(arg.clone()))
                        .collect(),
                    span: None,
                })
            }
            TermKind::Quantified(quant) => match quant.quantifier {
                Quantifier::Forall => ast::Term::Forall(ast::Forall {
                    bindings: quant
                        .variables
                        .iter()
                        .map(|var| ast::SortedVar::from(var.clone()))
                        .collect(),
                    body: Box::new(ast::Term::from(quant.body.clone())),
                    span: quant.span.clone(),
                }),
                Quantifier::Exists => ast::Term::Exists(ast::Exists {
                    bindings: quant
                        .variables
                        .iter()
                        .map(|var| ast::SortedVar::from(var.clone()))
                        .collect(),
                    body: Box::new(ast::Term::from(quant.body.clone())),
                    span: quant.span.clone(),
                }),
            },
            TermKind::Let(let_) => ast::Term::Let(ast::Let {
                bindings: let_
                    .bindings
                    .iter()
                    .map(|bind| ast::Binding::from(bind.clone()))
                    .collect(),
                body: Box::new(ast::Term::from(let_.body.clone())),
                span: let_.span.clone(),
            }),
        }
    }
}

impl From<QuantifiedVariable> for ast::SortedVar {
    fn from(var: QuantifiedVariable) -> Self {
        match var {
            QuantifiedVariable::Bound(bound) => ast::SortedVar {
                name: ast::Symbol::from(bound.name().clone()),
                sort: ast::Sort::from(bound.sort().clone()),
                span: bound.span().clone(),
            },
            QuantifiedVariable::Unbound(unbound) => {
                let sort = match Sort::try_from(unbound.sort.clone()) {
                    Ok(sort) => ast::Sort::from(sort),
                    Err(_) => ast::Sort::Term(Box::new(ast::Term::from(unbound.sort.clone()))),
                };
                ast::SortedVar {
                    name: ast::Symbol::from(unbound.name.clone()),
                    sort,
                    span: None,
                }
            }
        }
    }
}

impl From<Binding> for ast::Binding {
    fn from(bind: Binding) -> Self {
        ast::Binding {
            name: ast::Symbol::from(bind.variable.name().clone()),
            body: ast::Term::from(bind.def.clone()),
            span: bind.span.clone(),
        }
    }
}

impl From<Sort> for ast::Sort {
    fn from(value: Sort) -> Self {
        let head = ast::Identifier::Symbol(ast::Symbol::from(value.head.name().clone()));

        if value.arguments.is_empty() {
            ast::Sort::Simple(head)
        } else {
            let mut args = Vec::new();
            for arg in &*value.arguments {
                match arg {
                    SortArgument::Value(_) => todo!(),
                    SortArgument::Sort(arg) => args.push(ast::Sort::from(arg.clone())),
                }
            }
            ast::Sort::Application(ast::SortApplication {
                head,
                args,
                span: None,
            })
        }
    }
}

impl Pretty for Term {
    fn pretty(&self) -> RcDoc<'static> {
        ast::Term::from(self.clone()).pretty()
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.render_fmt(f, u16::MAX)
    }
}

impl Pretty for Sort {
    fn pretty(&self) -> RcDoc<'static> {
        ast::Sort::from(self.clone()).pretty()
    }
}

impl Display for Sort {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.render_fmt(f, u16::MAX)
    }
}
