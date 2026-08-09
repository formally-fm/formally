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

use perfect_derive::perfect_derive;

use std::{hash::Hash, sync::Arc};

use itertools::Itertools;

/// Result of a lookup by name in a [Scope].
///
/// Elements represented by a [LookupSet] can be filtered and transformed using the
/// [filter()](LookupSet::filter), [map()](LookupSet::map), [filter_map()](LookupSet::filter_map),
/// and [filter_map_ok()](LookupSet::filter_map_ok) functions, which work similarly to
/// their counterpart on iterators. `LookupSet<T, V>` represents elements coming from a `Scope<T>`
/// and transformed (by [map()](LookupSet::map) or [filter_map()](LookupSet::filter_map)) into
/// elements of type `V`.
///
/// The difference from a standard iterator is that [LookupSet] remembers enough information to
/// allow the [one()](LookupSet::one) method to emit detailed error diagnostics. See
/// [one()](LookupSet::one) for details.
pub struct LookupSet<'s, 'i, T, V = &'s T> {
    name: Identifier<'i>,
    scope: &'s Scope<T>,
    iterator: Box<dyn 's + Iterator<Item = &'s T>>,
    filter_map: Box<dyn 's + Fn(&'s T) -> Result<Option<V>>>,
    empty: bool,
}

impl<'s, 'i, T: 's, V: 's> LookupSet<'s, 'i, T, V> {
    fn new(
        name: Identifier<'i>,
        scope: &'s Scope<T>,
        entities: impl 's + IntoIterator<Item = &'s T>,
        filter_map: impl 's + Fn(&'s T) -> Result<Option<V>>,
    ) -> Self {
        let mut iterator = entities.into_iter().peekable();
        let empty = iterator.peek().is_none();
        LookupSet {
            name,
            scope,
            iterator: Box::new(iterator),
            filter_map: Box::new(filter_map),
            empty,
        }
    }

    /// Get the [Identifier] the [LookupSet] was looked up for.
    pub fn name(&self) -> &Identifier<'_> {
        &self.name
    }

    /// Tell if the [LookupSet] is empty.
    pub fn is_empty(&self) -> bool {
        self.empty
    }

    /// Get a [LookupSet] of only the elements of `self` transformed by the function `f` for only
    /// the elements `v` where `f(v)` returns `Ok(Some(_))`. If `f` returns `Err(_)`, the whole
    /// [LookupSet] becomes erroneous and any call to `all()` or `one()` will return the same
    /// `Err(_)`.
    pub fn filter_map_ok<R: 's>(
        self,
        f: impl 's + Fn(V) -> Result<Option<R>>,
    ) -> LookupSet<'s, 'i, T, R> {
        let filter_map = self.filter_map;
        LookupSet::new(
            self.name,
            self.scope,
            self.iterator,
            move |t| match filter_map(t) {
                Ok(Some(v)) => f(v),
                Ok(None) => Ok(None),
                Err(err) => Err(err),
            },
        )
    }

    /// Get a [LookupSet] of the elements of `self` transformed by the function `f` for only
    /// the elements `v` where `f(v)` returns `Some(_)`.
    pub fn filter_map<R: 's>(self, f: impl 's + Fn(V) -> Option<R>) -> LookupSet<'s, 'i, T, R> {
        self.filter_map_ok(move |v| Ok(f(v)))
    }

    /// Get a [LookupSet] of only the elements of `self` that satisfy the predicate `f`.
    pub fn filter(self, f: impl 's + Fn(&V) -> bool) -> Self {
        self.filter_map(move |v| if f(&v) { Some(v) } else { None })
    }

    /// Get a [LookupSet] of only the elements `v` of `self` such that `f(v)` returns `Ok(true)`.
    /// If `Ok(false)` is returned, the element is discarded. If `Err(_)` is returned, the whole
    /// [LookupSet] becomes erroneous and any call to `all()` or `one()` will return the same
    /// `Err(_)`.
    pub fn filter_ok(self, f: impl 's + Fn(&V) -> Result<bool>) -> Self {
        self.filter_map_ok(move |v| if f(&v)? { Ok(Some(v)) } else { Ok(None) })
    }

    /// Get a [LookupSet] of the elements of `self` transformed by the function `f`
    pub fn map<R: 's>(self, f: impl 's + Fn(V) -> R) -> LookupSet<'s, 'i, T, R> {
        self.filter_map(move |v| Some(f(v)))
    }

    /// Get an iterator of all the elements in the [LookupSet].
    pub fn all(self) -> Result<Vec<V>> {
        self.iterator
            .map(move |t| (self.filter_map)(t))
            .process_results(|c| c.flatten().collect())
    }

    /// If the current [LookupSet] is not empty, return it as-is, otherwise call the `other` closure
    /// and return its result.
    ///
    /// The returned [LookupSet] inherits the current one's [Context] (used to locate the [Emitter]
    /// for the error diagnostics emitted by [one()](LookupSet::one)).
    pub fn or_else(self, other: impl 's + FnOnce() -> LookupSet<'s, 'i, T, V>) -> Self {
        let mut this = self.iterator.peekable();
        if this.peek().is_some() {
            LookupSet::new(self.name, self.scope, this, self.filter_map)
        } else {
            other()
        }
    }
}

impl<'s, 'i, T: 's + Clone + Hash + Eq + Located, V: 's> LookupSet<'s, 'i, T, V> {
    /// Return the single element in this [LookupSet] if only one exist, otherwise produce detailed
    /// error diagnostics.
    ///
    /// The [one()](LookupSet::one) method assumes its usage is within name lookup for a typical
    /// statically scoped language (this includes quantifiers or other similar constructs in most
    /// logics). By calling this method one asserts that only a single result of the previous call
    /// to [lookup()](Scope::lookup) is required. If this is the case, the single result is
    /// returned. Otherwise, error diagnostics are produced.
    ///
    /// The diagnostics are produced after checking further conditions. If there were more than one
    /// element the lookup is treated as ambiguous (as if you asked for the name of an overloaded
    /// function in some C++-like language without specifying its argument types) and a list of
    /// matching symbols is produced as attached notes. If the [LookupSet] is empty the lookup is
    /// treated as a reference to an undefined symbol, but if it was
    /// filtered (see [filter()](LookupSet::filter)), then a list of non-matching symbols is
    /// produced as attached notes.
    pub fn one(self) -> Result<V> {
        let mut all = Vec::new();
        let mut filtered = Vec::new();

        for t in self.iterator {
            if let Some(v) = (self.filter_map)(t)? {
                filtered.push((t, v));
            }
            all.push(t);
        }

        let mut filtered = filtered.into_iter();
        let all = all.into_iter();

        match (filtered.next(), filtered.next()) {
            (Some((_, v)), None) => Ok(v),
            (Some((t1, _)), Some((t2, _))) => {
                error!(
                    self.name.span(),
                    "ambiguous reference to symbol '{}'", self.name
                );
                note!(t1.span(), "matching symbol declared here");
                note!(t2.span(), "matching symbol declared here");
                for (t, _) in filtered {
                    note!(t.span(), "matching symbol declared here");
                }
                Err(DiagnosticEmitted)
            }
            (None, _) => {
                let mut all = all.peekable();
                match all.peek() {
                    Some(_) => {
                        error!(self.name.span(), "no matching symbol '{}'", self.name);

                        for element in all {
                            if element.span().is_some() {
                                note!(element.span(), "non-matching symbol declared here");
                            }
                        }
                        Err(DiagnosticEmitted)
                    }
                    None => {
                        error!(
                            self.name.span(),
                            "undefined reference to symbol '{}'", self.name
                        );
                        Err(DiagnosticEmitted)
                    }
                }
            }
        }
    }
}

/// Utility to implement lookup scopes.
///
/// [Scope] implements the logic needed to support name lookup in a local scope, similar to what may
/// many need in simple programming languages or in logical formalisms. It supports looking up by
/// name elements of any given type and implements [Stack] to support incremental interfaces, e.g.,
/// in SAT or SMT solvers.
///
/// A call to [lookup()](Scope::lookup) method produces an instance of [LookupSet] which can be used
/// to further filter and navigate the objects found by name. [LookupSet] in turn is in charge of
/// emitting detailed error diagnostics when a lookup fails, helping to standardize such diagnostics
/// across all `formally` and its clients.
///
/// Example:
/// ```rust
/// # mod formally {
/// #    pub extern crate formally_support as support;
/// #    pub extern crate formally_smt as smt;
/// # }
/// use formally::{support::*, smt::*};
///
/// # fn main() -> Result<()> {
/// let mut scope = Scope::new();
/// scope.push();
/// scope.add("x", term!(and p q));
///
/// println!("x: {}", scope.lookup(Identifier::from("x")).one()?);
///
/// scope.pop();
/// assert!(scope.lookup(Identifier::from("x")).all()?.is_empty());
/// # Ok(())
/// # }
/// ```
///
/// Here the [LookupSet::one()] method requires a single result to exist and emits detailed
/// diagnostics if this is not the case. See its documentation for details.
///
/// [Scope] objects support being *nested* under other [Scope] objects. Nesting simulates how
/// one would implement a nested scope in a typical language, such as the scope under a function
/// definition that sees its arguments locally but the elements declared outside globally. Elements
/// defined in the local [Scope] shadow the ones defined in the parent, but if no element is defined
/// at all with a given name, lookup is delegated to the parent.
///
/// Example:
/// ```rust
/// # mod formally {
/// #    pub extern crate formally_support as support;
/// #    pub extern crate formally_smt as smt;
/// # }
/// use formally::{support::*, smt::*};
///
/// # fn main() -> Result<()> {
/// let mut parent = Scope::new();
/// parent.add("x", term!(p));
/// parent.add("x", term!(q));
/// parent.add("y", term!(and p q));
///
/// let mut scope = Scope::new().with_parent(parent);
///
/// scope.add("x", term!(=> p q));
///
/// scope.lookup("x").one()?;
/// scope.lookup("y").one()?;
/// # Ok(())
/// # }
/// ```
///
/// Note that the first call to [one()](LookupSet::one) succeeds here because the only element
/// declared in `scope` with name `"x"` shadows all the elements with the same name in `parent`. The
/// second one succeeds as well because `"y"` is found in the parent.
#[perfect_derive(Default, Clone)]
pub struct Scope<T> {
    elements: Stacked<rpds::HashTrieMapSync<String, rpds::VectorSync<T>>>,
    parent: Option<Arc<Scope<T>>>,
}

impl<T> Scope<T> {
    /// Construct an empty [Scope]
    pub fn new() -> Self {
        Scope::default()
    }

    /// Construct a new [Scope] similar to `self` but nested under a different parent.
    pub fn with_parent(self, parent: Scope<T>) -> Scope<T> {
        Scope {
            parent: Some(Arc::new(parent)),
            ..self
        }
    }

    /// Set a new parent to the current [Scope].
    pub fn set_parent(&mut self, parent: Scope<T>) {
        self.parent = Some(Arc::new(parent));
    }

    /// Add an element to the [Scope] under the given name.
    pub fn add(&mut self, name: &str, element: T) {
        if !self.elements.contains_key(name) {
            self.elements
                .insert_mut(name.to_string(), rpds::Vector::new_sync());
        }
        self.elements.get_mut(name).unwrap().push_back_mut(element);
    }

    pub fn lookup<'i>(&self, name: impl Into<Identifier<'i>>) -> LookupSet<'_, 'i, T, &'_ T> {
        let name = name.into();
        if let Some(elements) = self.elements.get(name.name()) {
            LookupSet::new(name, self, elements.iter(), |t| Ok(Some(t)))
        } else if let Some(parent) = &self.parent {
            parent.lookup(name)
        } else {
            LookupSet::new(name, self, std::iter::empty(), |t| Ok(Some(t)))
        }
    }
}

impl<T: Clone> Scope<T> {
    /// Clone all the elements of the given scope into `self`, registering them under the same
    /// names.
    pub fn merge(&mut self, other: &Scope<T>) {
        for (name, vec) in &*other.elements {
            for element in vec {
                self.add(name.as_str(), element.clone());
            }
        }
    }
}

impl<T> Stack for Scope<T> {
    fn push(&mut self) -> Result<()> {
        self.elements.push()
    }

    fn pop_n(&mut self, n: usize) -> Result<()> {
        self.elements.pop_n(n)
    }
}
