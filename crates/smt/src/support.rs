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

use crate::*;
use formally::{
    smt,
    support::{Identifier, Loc, Locatable, Located, Nominal, Span},
};

use std::{borrow::Cow, sync::Arc};

#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum Constant {
    Integer {
        value: u64,
        span: Option<Span>,
    },
    Rational {
        value: &'static str,
        span: Option<Span>,
    },
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct BoundHead {
    pub function: Function,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct UnboundHead {
    pub name: Cow<'static, str>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum AtomHead {
    Bound(BoundHead),
    Unbound(UnboundHead),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TermArgument<'t> {
    Term(Term<'t>),
    Seq(Vec<Term<'t>>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Atom<'t> {
    pub head: AtomHead,
    pub arguments: &'t [TermArgument<'t>],
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub enum Term<'t> {
    Term(Loc<Nominal<&'t dyn ToTerm>>),
    Constant(Constant),
    Atom(Atom<'t>),
}

impl Default for Term<'_> {
    fn default() -> Self {
        Term::Constant(Constant::Integer {
            value: 0,
            span: None,
        })
    }
}

impl<'t> From<&'t dyn ToTerm> for Term<'t> {
    fn from(value: &'t dyn ToTerm) -> Term<'t> {
        Term::Term(Loc::new(Nominal(value)))
    }
}

impl<'t> From<&'t smt::Term> for Term<'t> {
    fn from(term: &'t smt::Term) -> Self {
        Term::Term(Loc::new(Nominal(term)))
    }
}

impl<T: Into<Function>> From<T> for AtomHead {
    fn from(function: T) -> Self {
        AtomHead::Bound(BoundHead {
            function: function.into(),
        })
    }
}

impl From<Identifier<'static>> for AtomHead {
    fn from(name: Identifier<'static>) -> Self {
        AtomHead::Unbound(UnboundHead {
            name: name.into_inner(),
        })
    }
}

impl ToTerm for support::Term<'_> {
    fn into_term_in(self, pool: &dyn TermPool) -> smt::Term {
        match self {
            Term::Term(t) => t.to_term_in(pool),
            Term::Constant(c) => {
                let c = match c {
                    Constant::Integer { value, span } => smt::Constant::Integer {
                        value: Arc::new(Integer::from(value)),
                        span,
                    },
                    Constant::Rational { value, span } => smt::Constant::Rational {
                        value: Arc::new(Rational::from_str_radix(value, 10).unwrap()),
                        span,
                    },
                };
                TermKind::Constant(c).into_term_in(pool)
            }
            Term::Atom(a) => {
                let mut arguments = Vec::new();
                for arg in a.arguments {
                    match arg {
                        TermArgument::Term(t) => arguments.push(t.to_term_in(pool)),
                        TermArgument::Seq(seq) => {
                            arguments.extend(seq.iter().map(|arg| arg.to_term_in(pool)))
                        }
                    }
                }
                match a.head {
                    AtomHead::Bound(BoundHead { function }) => {
                        TermKind::Atom(smt::Atom {
                            head: smt::AtomHead::from(function),
                            arguments: Arc::from(arguments.into_boxed_slice()),
                            span: a.span,
                        })
                        .into_term_in(pool)
                    }
                    AtomHead::Unbound(UnboundHead { name }) => {
                        TermKind::Atom(smt::Atom {
                            head: smt::AtomHead::from(Identifier::from(name.clone())),
                            arguments: Arc::from(arguments.into_boxed_slice()),
                            span: a.span,
                        })
                        .into_term_in(pool)
                    }
                }
            }
        }
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> smt::Term {
        self.clone().into_term_in(pool)
    }
}
