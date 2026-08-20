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
use formally::support::{Identifier, Locatable, Located, Span};

use std::borrow::Cow;

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

#[derive(Debug, Clone, Hash, PartialEq, Eq, Located)]
pub enum Term<'t> {
    Term(term::Term),
    TermKind(TermKind),
    Constant(Constant),
    Atom(Atom<'t>),
}

impl<'t> Locatable for Term<'t> {
    type Located = Term<'t>;

    fn over(self, span: impl Into<Option<Span>>) -> Term<'t> {
        match self {
            Term::Term(term) => Term::TermKind(term.kind().clone().over(span)),
            Term::TermKind(kind) => Term::TermKind(kind.over(span)),
            Term::Constant(cnst) => Term::Constant(cnst.over(span)),
            Term::Atom(atom) => Term::Atom(atom.over(span)),
        }
    }
}

impl Default for Term<'_> {
    fn default() -> Self {
        Term::Constant(Constant::Integer {
            value: 0,
            span: None,
        })
    }
}

impl From<term::Term> for Term<'_> {
    fn from(term: term::Term) -> Self {
        Term::Term(term)
    }
}

impl<T: Into<TermKind>> From<T> for Term<'_> {
    fn from(value: T) -> Self {
        Term::TermKind(value.into())
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
