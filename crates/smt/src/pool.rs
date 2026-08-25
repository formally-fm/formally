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
use std::{borrow::Borrow, cell::RefCell, collections::HashSet, fmt::Debug, sync::Arc};

/// Trait for types that implement subterm sharing for [terms][Term].
///
/// [TermPool] instances provides the basic functionality for subterm sharing in the framework.
/// The trait is currently implemented only by [HashPool] and [DashPool], with the latter usable in
/// multithraeded contexts. Since [Term] cannot be publicly constructed, this trait is not designed
/// to be implemented by downstream crates.
///
/// The main use of [TermPool] instances is to give them to [TermManager::with_pool()] in order to
/// share the same pool among different term managers and solvers. This allows to share the same
/// [Term] objects between different SMT backends, even among different threads when using
/// [DashPool].
///
/// The [TermPool::shared()] method is rarely called directly. Prefer using [ToTerm::into_term_in()]
/// to manually get a [Term] out of a [ToTerm] object (which, again, is rarely needed, because
/// [ToTerm] is usually accepted directly throughout the framework).
pub trait TermPool {
    /// Return the unique [Term] whose underlying [TermKind] is equal to the argument.
    fn shared(&self, kind: TermKind) -> Term;

    /// Return the unique [Term] whose underlying [TermKind] is equal to the one referenced by the
    /// argument.
    fn shared_ref(&self, kind: &TermKind) -> Term;
}

#[derive(Debug, Hash, PartialEq, Eq)]
struct Lookup<T>(T);

impl Borrow<TermKind> for Lookup<Arc<TermInner>> {
    fn borrow(&self) -> &TermKind {
        &self.0.kind
    }
}

/// Sequential, single-threaded implementation of [TermPool].
///
/// [HashPool] is based on the standard [HashSet] so its use is limited to a single thread, and
/// consequently the type is not [Send] nor [Sync]. If the same [TermPool] has to be shared among
/// different threads, look for [DashPool] instead.
///
/// [HashPool] is the default [TermPool] implementation used by [TermManager::new()].
#[derive(Debug, Default)]
pub struct HashPool {
    pool: RefCell<HashSet<Lookup<Arc<TermInner>>>>,
}

impl HashPool {
    pub fn new() -> HashPool {
        HashPool::default()
    }
}

/// Concurrent, multithreaded implementation of [TermPool].
///
/// [DashPool] is based on [DashSet] from the [dashmap] crate. As such the type is both [Send] and
/// [Sync] and can be shared and accessed freely by multiple threads without additional
/// synchronization.
///
/// Give a [DashPool] instance to [TermManager::with_pool()] in order to share the same concurrent
/// pool among different term managers used in different threads.
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
            let arc = Arc::new(TermInner::new(kind));
            let term = Term(Nominal(arc.clone()));
            self.pool.insert(Lookup(arc));

            term
        }
    }

    fn shared_ref(&self, kind: &TermKind) -> Term {
        if let Some(kind) = self.pool.get(kind) {
            Term(Nominal(kind.0.clone()))
        } else {
            let arc = Arc::new(TermInner::new(kind.clone()));
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
            let arc = Arc::new(TermInner::new(kind));
            let term = Term(Nominal(arc.clone()));
            self.pool.borrow_mut().insert(Lookup(arc));

            term
        }
    }

    fn shared_ref(&self, kind: &TermKind) -> Term {
        if let Some(kind) = self.pool.borrow().get(kind) {
            Term(Nominal(kind.0.clone()))
        } else {
            let arc = Arc::new(TermInner::new(kind.clone()));
            let term = Term(Nominal(arc.clone()));
            self.pool.borrow_mut().insert(Lookup(arc));

            term
        }
    }
}

/// Trait for types that can be uniqued in [TermPools](TermPool) to obtain a [Term].
///
/// This trait represents types that can be converted to [Term] after being uniqued into a
/// [TermPool]. This includes of course [Term] itself and [TermKind], but also many types
/// convertible to [TermKind], the [Sort] type, and the result of the [term!] macro.
///
/// Most methods in the framework that would accept a [Term] (e.g. in [Solver]) accept a generic
/// [ToTerm] argument instead, so e.g. an invocation of the [term!] macro can be passed directly to
/// them. In the particular cases where a [Term] has to be manually obtained from a [ToTerm]
/// instance, one passes a reference to a [TermPool] to [ToTerm::into_term_in()] or
/// [ToTerm::to_term_in()].
pub trait ToTerm: Debug {
    /// Convert the object into a [Term] by uniquing in the given [TermPool].
    fn into_term_in(self, pool: &dyn TermPool) -> Term;

    /// Convert the object (by reference) into a [Term] by uniquing in the given [TermPool].
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

impl ToTerm for FunctionRef {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self)).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self.clone())).into_term_in(pool)
    }
}

impl ToTerm for BoundRef {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self)).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self.clone())).into_term_in(pool)
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

impl ToTerm for Identifier<'_> {
    fn into_term_in(self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self.into_owned())).into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        TermKind::Atom(Atom::from(self.clone().into_owned())).into_term_in(pool)
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
        let mut arguments = Vec::with_capacity(self.arguments.len());
        for arg in &*self.arguments {
            match arg {
                SortArgument::Value(c) => arguments.push(
                    Constant::Integer {
                        value: c.clone(),
                        span: None,
                    }
                    .to_term_in(pool),
                ),
                SortArgument::Sort(s) => arguments.push(s.to_term_in(pool)),
            }
        }

        Atom {
            head: FunctionRef::from(self.head.clone()),
            arguments: Arc::from(arguments.into_boxed_slice()),
            span: None,
        }
        .into_term_in(pool)
    }

    fn to_term_in(&self, pool: &dyn TermPool) -> Term {
        self.clone().into_term_in(pool)
    }
}
