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

use crate::*;
use std::ops::{Deref, DerefMut};

/// Trait to model entities that can push and pop their state on a stack structure.
///
/// Many components in `formally` allow to push and pop their state as a stack structure, most
/// prominently SMT solvers from the `smt` crate. This trait abstracts this capability.
///
/// Since the logic to support these operations can sometimes be factored out, we also provide the
/// [Stacked] type to help implementing [Stack] on your own data structure.
///
/// Implementors should note that popping out a number of frames equal or larger than the number of
/// frames pushed should, by convention, result into an object equivalent to its [Default] value.
pub trait Stack {
    /// Push the current state of the object to the stack.
    fn push(&mut self) -> Result<()>;

    /// Pop `n` frames from the stack, restoring the state of the `n`th topmost frame.
    ///
    /// It is allowed to provide a value of `n` larger than the number of frames.
    fn pop_n(&mut self, n: usize) -> Result<()>;

    /// Shortcut for `pop_n(1)`
    fn pop(&mut self) -> Result<()> {
        self.pop_n(1)
    }
}

/// A helper type to implement the [Stack] trait
///
/// This type is a wrapper for any clonable type `T` that implements [Stack] on top of it.
/// Access to the current topmost frame is granted via [Deref] and [DerefMut].
///
/// The stack structure is implemented as a vector where the current value of the inner object is
/// pushed when [Stack::push] is called, and popped when [Stack::pop_n] is called. This means that
/// types used with [Stacked] should be *efficiently* clonable. Efficient clonability is often
/// achieved in `formally` by using immutable/persistent data structures, usually from the `rpds`
/// crate.
///
/// To construct a [Stacked] object, the underlying type must implement [Default]. The [Stack]
/// traits suggests that popping out more frames than those pushed should result into an object
/// equivalent to the [Default] instance. This requirement is satisfied by [Stacked].
#[derive(Clone)]
pub struct Stacked<T> {
    current: T,
    stack: rpds::VectorSync<T>,
}

impl<T: Clone + Default> Default for Stacked<T> {
    fn default() -> Self {
        Stacked {
            current: T::default(),
            stack: rpds::Vector::new_sync(),
        }
    }
}

impl<T: Default> Stacked<T> {
    /// Creates a new default-valued stacked object.
    pub fn new(current: T) -> Self {
        Self {
            current,
            stack: Default::default(),
        }
    }

    /// Turns the stacked into the current topmost frame.
    pub fn into_current(self) -> T {
        self.current
    }
}

impl<T: Clone + Default> Stack for Stacked<T> {
    fn push(&mut self) -> Result<()> {
        self.stack.push_back_mut(self.current.clone());
        Ok(())
    }

    fn pop_n(&mut self, n: usize) -> Result<()> {
        let mut i = n;
        while !self.stack.is_empty() && i > 0 {
            self.current = std::mem::take(self.stack.get_mut(self.stack.len() - 1).unwrap());
            self.stack.drop_last_mut();
            i -= 1;
        }

        if self.stack.is_empty() && i > 0 {
            self.current = Default::default();
        }

        Ok(())
    }
}

impl<T: Clone + Default> Deref for Stacked<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.current
    }
}

impl<T: Clone + Default> DerefMut for Stacked<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.current
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stacked() -> Result<()> {
        let mut stacked: Stacked<Vec<i32>> = Stacked::default();

        (*stacked).push(42);

        assert_eq!(*stacked, vec![42]);

        stacked.push()?;

        (*stacked).push(37);

        assert_eq!(*stacked, vec![42, 37]);

        stacked.pop()?;

        assert_eq!(*stacked, vec![42]);

        stacked.pop()?;

        assert!(stacked.is_empty());
        
        Ok(())
    }
}
