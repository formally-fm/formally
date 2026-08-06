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
use formally::support::Identifier;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Constant {
    Integer { value: u64 },
    Rational { value: &'static str },
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct BoundHead {
    pub function: Function,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct UnboundHead {
    pub name: Identifier<'static>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum AtomHead {
    Bound(BoundHead),
    Unbound(UnboundHead),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Atom<'t> {
    pub head: AtomHead,
    pub arguments: &'t [Term<'t>],
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Term<'t> {
    Term(term::Term),
    Constant(Constant),
    Atom(Atom<'t>),
}

impl<T: Into<term::Term>> From<T> for Term<'_> {
    fn from(value: T) -> Self {
        Term::Term(value.into())
    }
}

impl From<Constant> for term::Constant {
    fn from(cnst: Constant) -> Self {
        match cnst {
            Constant::Integer { value } => term::Constant::Integer {
                value: Integer::from(value),
                span: None,
            },
            Constant::Rational { value } => term::Constant::Rational {
                value: Rational::from_str_radix(value, 10).unwrap(),
                span: None,
            },
        }
    }
}

impl From<&'_ Atom<'_>> for term::Atom {
    fn from(atom: &Atom) -> Self {
        match &atom.head {
            AtomHead::Bound(BoundHead { function }) => term::Atom::Bound(BoundAtom {
                head: Reference {
                    function: function.clone(),
                    span: None,
                },
                arguments: atom.arguments.iter().map(Into::into).collect(),
                span: None,
            }),
            AtomHead::Unbound(UnboundHead { name }) => term::Atom::Unbound(UnboundAtom {
                head: name.clone(),
                arguments: atom.arguments.iter().map(Into::into).collect(),
                span: None,
            }),
        }
    }
}

impl From<&'_ Term<'_>> for term::Term {
    fn from(term: &'_ Term<'_>) -> Self {
        match term {
            Term::Term(t) => t.clone(),
            Term::Constant(c) => term::Term::from(term::Constant::from(*c)),
            Term::Atom(a) => term::Term::from(term::Atom::from(a)),
        }
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
        AtomHead::Unbound(UnboundHead { name })
    }
}
