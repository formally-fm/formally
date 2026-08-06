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
use std::hash::Hasher;
use std::ops::Deref;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    hash::Hash,
    sync::Arc,
};
use crate::macros::AtomHead;

#[derive(Debug, Clone, Default)]
pub struct Pool {
    kinds: RefCell<HashSet<Arc<TermKind>>>,
    terms: RefCell<HashSet<Term>>,
}

impl Pool {
    pub fn new() -> Pool {
        Pool::default()
    }

    pub fn unique(&self, t: impl Unique) -> Term {
        t.unique(self)
    }
}

pub trait Unique {
    fn unique(self, pool: &Pool) -> Term;
}

impl Unique for &Term {
    fn unique(self, pool: &Pool) -> Term {
        // we look up nominally (thanks to the `Eq` instance of `Term`) whether this
        // exact `Term` is already interned
        if pool.terms.borrow().contains(self) {
            return self.clone();
        }

        // otherwise we unique the `TermKind`
        pool.unique(self.kind())
    }
}

impl Unique for &TermKind {
    fn unique(self, pool: &Pool) -> Term {
        let kind = match self {
            TermKind::Constant(_) => self.clone(),
            TermKind::Atom(atom) => match atom {
                Atom::Bound(BoundAtom { head, arguments, span }) => {
                    TermKind::Atom(Atom::Bound(BoundAtom {
                        head: head.clone(),
                        arguments: arguments.iter().map(|t| pool.unique(t)).collect(),
                        span: span.clone()
                    }))
                }
                Atom::Unbound(UnboundAtom { head, arguments, span }) => {
                    TermKind::Atom(Atom::Unbound(UnboundAtom {
                        head: head.clone(),
                        arguments: arguments.iter().map(|t| pool.unique(t)).collect(),
                        span: span.clone()
                    }))
                }
            }
        };

        if let Some(kind) = pool.kinds.borrow().get(&kind) {
            Term::from(kind.clone())
        } else {
            let arc = Arc::new(kind.clone());
            let term = Term::from(arc.clone());
            pool.kinds.borrow_mut().insert(arc);
            pool.terms.borrow_mut().insert(term.clone());

            term
        }
    }
}

impl Unique for &macros::Term<'_> {
    fn unique(self, pool: &Pool) -> Term {
        match self {
            macros::Term::Term(t) => pool.unique(t),
            macros::Term::Constant(c) => pool.unique(&TermKind::Constant(Constant::from(*c))),
            macros::Term::Atom(a) => match &a.head {
                AtomHead::Bound(macros::BoundHead { function }) => {
                    pool.unique(&TermKind::Atom(Atom::Bound(BoundAtom {
                        head: Reference {
                            function: function.clone(),
                            span: None,
                        },
                        arguments: a.arguments.iter().map(|t| pool.unique(t)).collect(),
                        span: None,
                    })))
                }
                AtomHead::Unbound(macros::UnboundHead { name }) => {
                    pool.unique(&TermKind::Atom(Atom::Unbound(UnboundAtom {
                        head: name.clone(),
                        arguments: a.arguments.iter().map(|t| pool.unique(t)).collect(),
                        span: None,
                    })))
                }
            }
        }
    }
}
