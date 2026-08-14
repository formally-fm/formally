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
use formally::{smt::*, support::Nominal};
use std::{cell::RefCell, collections::HashSet, sync::Arc};

use dashmap::DashSet;

pub trait TermPool: Sized {
    fn shared(&self, kind: TermKind) -> Term;

    fn term(&self, term: impl ToTerm) -> Term {
        term.to_term(self)
    }
}

#[derive(Debug, Default)]
pub struct HashPool {
    pool: RefCell<HashSet<Arc<TermKind>>>,
}

impl HashPool {
    pub fn new() -> HashPool {
        HashPool::default()
    }
}

#[derive(Debug, Default)]
pub struct DashPool {
    pool: DashSet<Arc<TermKind>>,
}

impl DashPool {
    pub fn new() -> DashPool {
        DashPool::default()
    }
}

impl TermPool for DashPool {
    fn shared(&self, kind: TermKind) -> Term {
        if let Some(kind) = self.pool.get(&kind) {
            Term(Nominal(kind.clone()))
        } else {
            let arc = Arc::new(kind);
            let term = Term(Nominal(arc.clone()));
            self.pool.insert(arc);

            term
        }
    }
}

impl TermPool for HashPool {
    fn shared(&self, kind: TermKind) -> Term {
        if let Some(kind) = self.pool.borrow().get(&kind) {
            Term(Nominal(kind.clone()))
        } else {
            let arc = Arc::new(kind);
            let term = Term(Nominal(arc.clone()));
            self.pool.borrow_mut().insert(arc);

            term
        }
    }
}

pub trait ToTerm {
    fn to_term<P: TermPool>(self, pool: &P) -> Term;
}

impl ToTerm for Term {
    fn to_term<P: TermPool>(self, _pool: &P) -> Term {
        self
    }
}

impl ToTerm for &Term {
    fn to_term<P: TermPool>(self, _pool: &P) -> Term {
        self.clone()
    }
}

impl<T: Into<TermKind>> ToTerm for T {
    fn to_term<P: TermPool>(self, pool: &P) -> Term {
        pool.shared(self.into())
    }
}

impl ToTerm for &Sort {
    fn to_term<P: TermPool>(self, pool: &P) -> Term {
        self.clone().to_term(pool)
    }
}

impl ToTerm for Sort {
    fn to_term<P: TermPool>(self, pool: &P) -> Term {
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

impl ToTerm for &support::Term<'_> {
    fn to_term<P: TermPool>(self, pool: &P) -> Term {
        match self {
            support::Term::Term(t) => t.clone(),
            support::Term::TermKind(k) => pool.shared(k.clone()),
            support::Term::Constant(c) => {
                let c = match c {
                    support::Constant::Integer { value } => Constant::Integer {
                        value: Integer::from(*value),
                        span: None,
                    },
                    support::Constant::Rational { value } => Constant::Rational {
                        value: Rational::from_str_radix(value, 10).unwrap(),
                        span: None,
                    },
                };
                pool.term(TermKind::Constant(c))
            }
            support::Term::Atom(a) => match &a.head {
                support::AtomHead::Bound(support::BoundHead { function }) => {
                    pool.term(TermKind::Atom(Atom::Bound(BoundAtom {
                        head: Reference {
                            function: function.clone(),
                            span: None,
                        },
                        arguments: a.arguments.iter().map(|t| pool.term(t)).collect(),
                        span: None,
                    })))
                }
                support::AtomHead::Unbound(support::UnboundHead { name }) => {
                    pool.term(TermKind::Atom(Atom::Unbound(UnboundAtom {
                        head: name.clone(),
                        arguments: a.arguments.iter().map(|t| pool.term(t)).collect(),
                        span: None,
                    })))
                }
            },
        }
    }
}
