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

use std::{
    fmt::{Debug, Formatter},
    ops::Deref,
    sync::Arc,
};

/// Either a static reference or an [Arc].
///
/// [SArc] is useful when declaring types that can refer to static data as well as data initialized
/// at runtime. [Arc::new()] is not usable in `const` contexts, in which case [SArc::Static] can be
/// used, while using [SArc::Arc] for all other uses.
#[derive(Hash, PartialEq, Eq)]
pub enum SArc<T: 'static + ?Sized> {
    Static(&'static T),
    Arc(Arc<T>),
}

impl<T: 'static + ?Sized> From<Box<T>> for SArc<T> {
    fn from(value: Box<T>) -> Self {
        SArc::Arc(Arc::from(value))
    }
}

impl<T: 'static + Default> Default for SArc<T> {
    fn default() -> Self {
        SArc::Arc(Arc::default())
    }
}

impl<T: 'static> Default for SArc<[T]> {
    fn default() -> Self {
        SArc::Arc(Arc::default())
    }
}

impl<T: 'static + ?Sized> Clone for SArc<T> {
    fn clone(&self) -> Self {
        match self {
            SArc::Static(st) => SArc::Static(st),
            SArc::Arc(arc) => SArc::Arc(arc.clone()),
        }
    }
}

impl<T: Debug> Debug for SArc<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", **self)
    }
}

impl<T: 'static> SArc<T> {
    pub fn new(value: T) -> SArc<T> {
        SArc::Arc(Arc::new(value))
    }
}

impl<T: 'static + ?Sized> Deref for SArc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            SArc::Static(st) => st,
            SArc::Arc(arc) => arc,
        }
    }
}
