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

use crate::formally;
use formally::{
    smt::*,
    support::{Comparable, Context, Contextual, Nominal},
};
use std::sync::{Arc, Mutex};

use dashmap::DashSet;

#[derive(Debug, Default, Contextual)]
pub struct TermPool {
    pub(crate) context: Context,
    pub(crate) terms: DashSet<Arc<TermKind>>,
}

impl TermPool {
    pub fn new() -> TermPool {
        TermPool::default()
    }

    pub fn term(self: &TermPool, t: impl ToTerm) -> Term {
        t.to_term(self)
    }
}

pub trait ToTerm {
    fn to_term(self, pool: &TermPool) -> Term;
}

impl ToTerm for &TermKind {
    fn to_term(self, pool: &TermPool) -> Term {
        if let Some(kind) = pool.terms.get(self) {
            Term::new(pool.context(), kind.clone())
        } else {
            let arc = Arc::new(self.clone());
            let term = Term::new(pool.context(), arc.clone());
            pool.terms.insert(arc);

            term
        }
    }
}

impl ToTerm for TermKind {
    fn to_term(self, pool: &TermPool) -> Term {
        if let Some(kind) = pool.terms.get(&self) {
            Term::new(pool.context(), kind.clone())
        } else {
            let arc = Arc::new(self);
            let term = Term::new(pool.context(), arc.clone());
            pool.terms.insert(arc);

            term
        }
    }
}

impl ToTerm for &Sort {
    fn to_term(self, pool: &TermPool) -> Term {
        let arguments = self
            .arguments
            .iter()
            .map(|arg| match arg {
                SortArgument::Value(c) => pool.term(TermKind::Constant(c.clone())),
                SortArgument::Sort(s) => pool.term(s),
            })
            .collect();
        pool.term(TermKind::Atom(Atom::Bound(BoundAtom {
            head: Reference {
                function: self.head.clone(),
                span: None,
            },
            arguments,
            span: None,
        })))
    }
}

impl ToTerm for Sort {
    fn to_term(self, pool: &TermPool) -> Term {
        let arguments = self
            .arguments
            .into_iter()
            .map(|arg| match arg {
                SortArgument::Value(c) => pool.term(TermKind::Constant(c)),
                SortArgument::Sort(s) => pool.term(s),
            })
            .collect();
        pool.term(TermKind::Atom(Atom::Bound(BoundAtom {
            head: Reference {
                function: self.head,
                span: None,
            },
            arguments,
            span: None,
        })))
    }
}

impl ToTerm for &mut macros::Term<'_> {
    fn to_term(self, pool: &TermPool) -> Term {
        match std::mem::take(self) {
            macros::Term::Term(t) => t,
            macros::Term::Constant(c) => {
                let c = match c {
                    macros::Constant::Integer { value } => Constant::Integer {
                        value: Integer::from(value),
                        span: None,
                    },
                    macros::Constant::Rational { value } => Constant::Rational {
                        value: Rational::from_str_radix(value, 10).unwrap(),
                        span: None,
                    },
                };
                pool.term(TermKind::Constant(c))
            }
            macros::Term::Atom(a) => match a.head {
                macros::AtomHead::Bound(macros::BoundHead { function }) => {
                    pool.term(TermKind::Atom(Atom::Bound(BoundAtom {
                        head: Reference {
                            function,
                            span: None,
                        },
                        arguments: a.arguments.into_iter().map(|t| pool.term(t)).collect(),
                        span: None,
                    })))
                }
                macros::AtomHead::Unbound(macros::UnboundHead { name }) => {
                    pool.term(TermKind::Atom(Atom::Unbound(UnboundAtom {
                        head: name,
                        arguments: a.arguments.into_iter().map(|t| pool.term(t)).collect(),
                        span: None,
                    })))
                }
            },
        }
    }
}
