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
    fmt::Debug,
    sync::{Arc, Mutex},
};

pub trait TermPool {
    fn shared(&self, kind: TermKind) -> Term;
    fn shared_ref(&self, kind: &TermKind) -> Term;
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

    fn shared_ref(&self, kind: &TermKind) -> Term {
        if let Some(kind) = self.pool.get(kind) {
            Term(Nominal(kind.0.clone()))
        } else {
            let arc = Arc::new(TermInner {
                kind: kind.clone(),
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

    fn shared_ref(&self, kind: &TermKind) -> Term {
        if let Some(kind) = self.pool.borrow().get(kind) {
            Term(Nominal(kind.0.clone()))
        } else {
            let arc = Arc::new(TermInner {
                kind: kind.clone(),
                sort: Mutex::default(),
            });
            let term = Term(Nominal(arc.clone()));
            self.pool.borrow_mut().insert(Lookup(arc));

            term
        }
    }
}

pub trait ToTerm: Debug {
    fn into_term_in(self, pool: &dyn TermPool) -> Term;
    fn to_term_in(&self, pool: &dyn TermPool) -> Term;
}

impl<T: ToTerm> ToTerm for &T {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        self.to_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        (*self).to_term_in(pool)
    }
}

impl ToTerm for Term {
    fn into_term_in(self, _pool: &dyn TermPool) -> Term {
        self
    }

    fn to_term_in(&self, _pool: &dyn TermPool) -> Term {
        self.clone()
    }
}

impl ToTerm for TermKind {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        pool.shared(self)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        pool.shared_ref(self)
    }
}

impl ToTerm for Constant {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Constant(self).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Constant(self.clone()).into_term_in(pool)
    }
}

impl ToTerm for Atom {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(self).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(self.clone()).into_term_in(pool)
    }
}

impl ToTerm for BoundAtom {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::Bound(self)).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::Bound(self.clone())).into_term_in(pool)
    }
}

impl ToTerm for Function {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self)).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self.clone())).into_term_in(pool)
    }
}

impl ToTerm for Variable {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self)).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self.clone())).into_term_in(pool)
    }
}

impl ToTerm for Primitive {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self)).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self.clone())).into_term_in(pool)
    }
}

impl ToTerm for UserFunction {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self)).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self.clone())).into_term_in(pool)
    }
}

impl ToTerm for Declared {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self)).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self.clone())).into_term_in(pool)
    }
}

impl ToTerm for Defined {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self)).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self.clone())).into_term_in(pool)
    }
}

impl ToTerm for UnboundAtom {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::Unbound(self)).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::Unbound(self.clone())).into_term_in(pool)
    }
}

impl ToTerm for Identifier<'_> {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self)).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self.clone())).into_term_in(pool)
    }
}

impl ToTerm for Quantified {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Quantified(self).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Quantified(self.clone()).into_term_in(pool)
    }
}

impl ToTerm for Let {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Let(self).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Let(self.clone()).into_term_in(pool)
    }
}

impl ToTerm for Sort {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        let arguments = self
            .arguments
            .into_iter()
            .map(|arg| match arg {
                SortArgument::Value(c) => TermKind::Constant(c).into_term_in(pool),
                SortArgument::Sort(s) => s.into_term_in(pool),
            })
            .collect();
        TermKind::Atom(Atom::Bound(BoundAtom {
            head: Reference {
                function: self.head,
                span: None,
            },
            arguments,
            span: None,
        }))
        .into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        self.clone().into_term_in(pool)
    }
}
