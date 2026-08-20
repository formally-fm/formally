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
use dashmap::DashSet;
use formally::{
    smt::*,
    support::{Identifier, Nominal},
};
use std::{
    borrow::Borrow,
    cell::RefCell,
    collections::HashSet,
    sync::{Arc, Mutex},
};

pub trait TermPool: Sized {
    fn shared(&self, kind: TermKind) -> Term;

    fn term(&self, term: impl ToTerm) -> Term {
        term.to_term(self)
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
struct Lookup<T>(T);

impl Borrow<TermKind> for Lookup<Arc<TermInner>> {
    fn borrow(&self) -> &TermKind {
        &self.0.kind
    }
}

#[derive(Debug, Default)]
pub struct HashPool {
    pool: RefCell<HashSet<Lookup<Arc<TermInner>>>>,
}

impl HashPool {
    pub fn new() -> HashPool {
        HashPool::default()
    }
}

#[derive(Debug, Default)]
pub struct DashPool {
    pool: DashSet<Lookup<Arc<TermInner>>>,
}

impl DashPool {
    pub fn new() -> DashPool {
        DashPool::default()
    }
}

impl TermPool for DashPool {
    fn shared(&self, kind: TermKind) -> Term {
        if let Some(kind) = self.pool.get(&kind) {
            Term(Nominal(kind.0.clone()))
        } else {
            let arc = Arc::new(TermInner {
                kind,
                sort: Mutex::default(),
            });
            let term = Term(Nominal(arc.clone()));
            self.pool.insert(Lookup(arc));

            term
        }
    }
}

impl TermPool for HashPool {
    fn shared(&self, kind: TermKind) -> Term {
        if let Some(kind) = self.pool.borrow().get(&kind) {
            Term(Nominal(kind.0.clone()))
        } else {
            let arc = Arc::new(TermInner {
                kind,
                sort: Mutex::default(),
            });
            let term = Term(Nominal(arc.clone()));
            self.pool.borrow_mut().insert(Lookup(arc));

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
        self.clone().to_term(pool)
    }
}

impl ToTerm for support::Term<'_> {
    fn to_term<P: TermPool>(self, pool: &P) -> Term {
        match self {
            support::Term::Term(t) => t.clone(),
            support::Term::TermKind(k) => pool.shared(k.clone()),
            support::Term::Constant(c) => {
                let c = match c {
                    support::Constant::Integer { value, span } => Constant::Integer {
                        value: Arc::new(Integer::from(value)),
                        span,
                    },
                    support::Constant::Rational { value, span } => Constant::Rational {
                        value: Arc::new(Rational::from_str_radix(value, 10).unwrap()),
                        span,
                    },
                };
                pool.term(TermKind::Constant(c))
            }
            support::Term::Atom(a) => {
                let mut arguments = Vec::new();
                for arg in a.arguments {
                    match arg {
                        support::TermArgument::Term(t) => arguments.push(pool.term(t)),
                        support::TermArgument::Seq(seq) => {
                            arguments.extend(seq.iter().map(|arg| pool.term(arg)))
                        }
                    }
                }
                match a.head {
                    support::AtomHead::Bound(support::BoundHead { function }) => {
                        pool.term(TermKind::Atom(Atom::Bound(BoundAtom {
                            head: Reference::from(function),
                            arguments: Arc::from(arguments.into_boxed_slice()),
                            span: a.span,
                        })))
                    }
                    support::AtomHead::Unbound(support::UnboundHead { name }) => {
                        pool.term(TermKind::Atom(Atom::Unbound(UnboundAtom {
                            head: Identifier::from(name.clone()),
                            arguments: Arc::from(arguments.into_boxed_slice()),
                            span: a.span,
                        })))
                    }
                }
            }
        }
    }
}
