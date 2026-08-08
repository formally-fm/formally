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

use derive_more::From;
use std::rc::Rc;
use std::{
    fmt::{Debug, Formatter},
    hash::{Hash, Hasher},
    ops::Deref,
    rc, sync,
};

/// Smart pointer wrapper for identity-based equality comparisons and hashing
///
/// [Nominal] wraps a [Deref] object to implement [Eq] and [Hash] based on the *value of the
/// reference* to the pointee, instead of its eventual [Eq] and [Hash] instances.
///
/// This means wrapping a pointer or reference in a [Nominal] makes it compare and hash based on its
/// identity as an object instead of its value, which would be the default in Rust.
///
/// In `formally`, this is used in places where two objects with the same value must nevertheless
/// be considered distinct, most prominently the `Declared` and `Defined` types in the `smt` crate.
#[derive(Clone, Default, From)]
#[from(T)]
#[repr(transparent)]
pub struct Nominal<T>(pub T);

impl<T> Nominal<T> {
    /// Turns the [Nominal] into its underlying object.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> AsRef<T> for Nominal<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: Debug> Debug for Nominal<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Nominal({:?})", self.0)
    }
}

impl<T: Deref> Hash for Nominal<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let ptr = &*self.0 as *const T::Target;
        ptr.hash(state)
    }
}

impl<T: Deref> PartialEq for Nominal<T> {
    fn eq(&self, other: &Self) -> bool {
        let this = &*self.0 as *const T::Target;
        let other = &*other.0 as *const T::Target;

        std::ptr::eq(this, other)
    }
}

impl<T: Deref> Eq for Nominal<T> {}

impl<T> Deref for Nominal<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

#[derive(Clone)]
pub struct Comparable<T>(pub T);

impl<T: Debug> Debug for Nominal<Comparable<rc::Weak<T>>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.0.0.upgrade() {
            Some(rc) => Debug::fmt(&rc, f),
            None => write!(f, "(expired weak pointer)"),
        }
    }
}

impl<T> Hash for Nominal<Comparable<rc::Weak<T>>> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if let Some(rc) = self.0.0.upgrade() {
            Nominal(rc).hash(state)
        } else {
            0.hash(state)
        }
    }
}

impl<T> PartialEq for Nominal<Comparable<rc::Weak<T>>> {
    fn eq(&self, other: &Self) -> bool {
        match (self.0.0.upgrade(), other.0.0.upgrade()) {
            (Some(rc1), Some(rc2)) => Nominal(rc1) == Nominal(rc2),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<T> Eq for Nominal<Comparable<rc::Weak<T>>> {}

impl<T: Debug> Debug for Nominal<Comparable<sync::Weak<T>>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.0.0.upgrade() {
            Some(arc) => Debug::fmt(&arc, f),
            None => write!(f, "(expired weak pointer)"),
        }
    }
}

impl<T> Hash for Nominal<Comparable<sync::Weak<T>>> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if let Some(arc) = self.0.0.upgrade() {
            Nominal(arc).hash(state)
        } else {
            0.hash(state)
        }
    }
}

impl<T> PartialEq for Nominal<Comparable<sync::Weak<T>>> {
    fn eq(&self, other: &Self) -> bool {
        match (self.0.0.upgrade(), other.0.0.upgrade()) {
            (Some(arc1), Some(arc2)) => Nominal(arc1) == Nominal(arc2),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<T> Eq for Nominal<Comparable<sync::Weak<T>>> {}
