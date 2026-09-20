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

//!
//! Facilities to write SMT backends based on programmatic APIs
//!
//! This module helps writing SMT backends based on programmatic APIs (as opposed to e.g., calling a
//! command-line tool), by abstracting most of the logic needed for the conversion from
//! [formally::smt]'s data structures and the underlying backend ones.
//!
//! Using these facilities when applicable is recommended against implementing the backend from
//! scratch, because they hide a non-trivial amount of complexity.
//!
//! The module provides two types, [ApiManager] and [ApiSolver], which respectively implement
//! [backends::Manager](smt::backends::Manager) and [backends::Solver](smt::backends::Solver) on top
//! of types provided by the backend's implementor.
//!
//! These types must implement the traits [api::Manager](Manager) and [api::Solver](Solver) which
//! have a seemingly larger surface than the similarly named ones from the parent module, but are
//! largerly easier to implement on top of common SMT APIs.
//!
//! Then, your [Backend] instance can simply provide instances of [ApiManager] and [ApiSolver]
//! in its [Backend::manager()] and [Backend::solver()] methods.
//!
//! Finally, remember to register your backend using the [backend](smt::backend) attribute for
//! it to be available when looking up backends by name.

mod facade;
pub use facade::ApiManager;
pub use facade::ApiSolver;

use crate::formally;
use formally::smt::{
    self,
    backends::{Backend, Error},
    logics::{Logic, LogicEx},
};

use std::{hash::Hash, rc::Rc};

type Result<T, E = Error> = std::result::Result<T, E>;

/// Trait to allow [api::ApiManager](ApiManager) to implement the
/// [backends::Manager](smt::backends::Manager) trait.
///
/// This trait asks you to implement the bare minimum to convert [Term](smt::Term) and
/// [Sort](smt::Sort) objects into the underlying representation of terms and sorts of your SMT API.
///
/// The types of the backend's API (whether directly coming from some other language bindings or
/// wrapped somehow) are described by the associated types of the trait and the functions implement
/// what is necessary. See the single items for details.
///
/// Implementing this trait assumes that you declared a logic representing the `"ALL"` logic
/// supported by your backend using the [logic!](smt::logic!) macro.
pub trait Manager: Default + Sized {
    /// The `"ALL"` logic of your backend, i.e. the logic assumed when the
    /// [Config::logic](smt::Config::logic) field of the configuration given to a solver is
    /// `None`.
    type ALL: LogicEx;

    /// The backend type.
    type Backend: Backend;

    /// The [Solver] type of your API.
    type Solver;

    /// The type of the backend's API representing a declaration and/or definition of a function.
    type FuncDecl: Clone + Hash + PartialEq + Eq;

    /// The type of the backend's API representing a sort.
    type Sort: Clone + Hash + PartialEq + Eq;

    /// The type of the backend's API representing a term.
    type Term: Clone;

    /// A Boolean constant telling whether your API supports directly the definition of functions.
    ///
    /// If [FUNC_DEF_SUPPORTED](Manager::FUNC_DEF_SUPPORTED) is `false`, [Manager::func_def()] is
    /// never called, and definitions are instead manually expanded beforehand.
    const FUNC_DEF_SUPPORTED: bool = false;

    /// Return the backend instance this manager has been built on.
    fn backend(&self) -> &Self::Backend;

    /// Return an uninterpreted sort of a given name.
    fn uninterpreted_sort(&self, name: &str) -> Result<Self::Sort>;

    /// Return the declaration of a function.
    ///
    /// The sorts are already of the type accepted by the backend's API. The solver is passed in as
    /// well in the case the API needs it to register declarations.
    fn func_decl(
        &self,
        solver: &Self::Solver,
        name: &str,
        sorts: &[Self::Sort],
        range: Self::Sort,
    ) -> Result<Self::FuncDecl>;

    /// Return the definition of a function.
    ///
    /// All the parameters are already of the type accepted by the backend's API. The solver is
    /// passed in as well in the case the API needs it to register definitions.
    ///
    /// The `variables` argument contain the terms corresponding to the variables obtained by the
    /// [Manager::variable()] method.
    ///
    /// This method is never called if [FUNC_DEF_SUPPORTED](Manager::FUNC_DEF_SUPPORTED) is `false`.
    #[allow(unused)]
    fn func_def(
        &self,
        solver: &Self::Solver,
        name: &str,
        sorts: &[Self::Sort],
        range: Self::Sort,
        variables: &[Self::Term],
        body: Self::Term,
    ) -> Result<Self::FuncDecl> {
        unreachable!()
    }

    /// Return a variable for use in function definitions, quantifiers, etc.
    ///
    /// This supposes the API can represent bound variables as terms.
    fn variable(&self, name: &str, sort: Self::Sort) -> Result<Self::Term>;

    /// Return the application of some arguments to a function declaration/definition.
    fn application(&self, func: &Self::FuncDecl, arguments: &[Self::Term]) -> Result<Self::Term>;

    /// Return a term corresponding to the given constant value.
    fn constant(&self, cnst: &smt::Constant) -> Result<Self::Term>;

    /// Return a quantified term.
    fn quantified(
        &self,
        quantifier: smt::Quantifier,
        variables: &[Self::Term],
        body: Self::Term,
    ) -> Result<Self::Term>;

    /// Return the underlying representation of the given sort.
    ///
    /// This method is called during traversals to convert a [Sort](smt::Sort) to a [Self::Sort],
    /// and is called only on sorts supported by the [Self::ALL] logic, in the form of the
    /// [LogicEx::Sort] enum of [Self::ALL]. The implementation can do a simple pattern
    /// matching on the enum to return the appropriate representation of the sort.
    ///
    /// The `to_sort` argument is a function implementing the recursive call of the traversal.
    /// The `to_value` argument is a function properly extracting an [Integer](smt::Integer) from
    /// a [SortArgument](smt::SortArgument) if an integer is expected. Both `to_sort` and `to_value`
    /// return `Result`s whose errors can be directly propagated up. This spares the implementation
    /// of this method from generating error messages by itself.
    fn sort(
        &self,
        sort: <Self::ALL as LogicEx>::Sort<'_>,
        to_sort: impl Fn(&smt::SortArgument) -> Result<Self::Sort>,
        to_value: impl Fn(&smt::SortArgument) -> Result<&smt::Integer>,
    ) -> Result<Self::Sort>;

    /// Return the underlying representation of the given atom.
    ///
    /// This method is called during traversals to convert a [Term](smt::Term) to [Self::Term],
    /// and is called only on atoms supported by the [Self::ALL] logic, in the form of the
    /// [LogicEx::Atom] enum of [Self::ALL]. The implementation can do a simple pattern matching
    /// on the enum to return the appropriate representation of the atom.
    ///
    /// The `to_term` arguments is a function implementing the recursive call of the traversal,
    /// and `to_terms` does that on a slice of terms. These functions return `Result`s whose errors
    /// can be directly propagated up. This spares the implementation of this method from generating
    /// error messages by itself.
    fn atom(
        &self,
        atom: <Self::ALL as LogicEx>::Atom<'_>,
        to_term: impl Fn(&smt::Term) -> Result<Self::Term>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<Self::Term>>,
    ) -> Result<Self::Term>;

    /// Translates back a [Self::Term] to a [Term](smt::Term).
    ///
    /// The term is supposed to be built using the provided [TermPool](smt::TermPool).
    ///
    /// The `to_func` and `to_sort` functions provide access to the `UserFunction` and `Sort`,
    /// respectively, corresponding to the user-declared `Self::FuncDecl` and `Self::Sort` that
    /// can be encountered. Therefore, in the case of [atoms](smt::Atom), the implementation of this
    /// method only needs to take care of translating back primitive operations.
    #[allow(unused)]
    fn export(
        &self,
        term: Self::Term,
        pool: &dyn smt::TermPool,
        to_func: impl Clone + Fn(Self::FuncDecl) -> Option<smt::UserFunction>,
        to_sort: impl Clone + Fn(Self::Sort) -> Option<smt::Sort>,
    ) -> Option<smt::Term> {
        None
    }
}

/// Trait to allow [api::ApiSolver](ApiSolver) to implement the
/// [backends::Solver](smt::backends::Solver) trait.
///
/// Similarly to [api::Manager](Manager), this trait asks the implementor to provide the bare
/// minimum access to the backend solver's API.
///
/// See each item for details.
pub trait Solver: Sized {
    /// The peer [Manager] type.
    type Manager: 'static + Manager;
    /// The type of the backend's API representing the result of the solving process.
    ///
    /// It needs to implement `Into<Option<bool>>` when `Some(true)` means *satisfiable*,
    /// `Some(false)` means *unsatisfiable* and `None` means that the result is unknown.
    type Result: Into<Option<bool>>;

    /// A type implementing the [Model] trait to represent a model returned by the solver.
    type Model<'s>: Model<Term = <Self::Manager as Manager>::Term>
    where
        Self: 's;

    /// Create an instance of the solver.
    ///
    /// There are some details to clarify of this signature:
    /// 1. in contrast to [Backend::solver()], the `manager` argument is a concrete type
    ///    corresponding to the peer [api::Manager](Manager) type used with [ApiManager].
    /// 2. the `logic` argument provides a `Logic` object looked up by the
    ///    [standard_logic()](smt::logics::standard_logic()) function. However, the logic is wrapped
    ///    in a `Result` because, when the logic is not found among the standard ones, it is up to
    ///    this method to decide whether the requested logic is supported by the backend (may be a
    ///    non-standard one), or whether propagating the error up is appropriate. This mechanism
    ///    spares the implementation from coming up with error messages by itself.
    fn new(
        config: &smt::Config,
        logic: Result<Option<&'static dyn Logic>>,
        manager: Rc<Self::Manager>,
    ) -> Result<Self>;

    /// Return the [Logic] object selected during construction.
    fn logic(&self) -> &dyn Logic;

    /// Return the instance of the underlying backend's API solver.
    fn solver(&self) -> &<Self::Manager as Manager>::Solver;

    /// Update the configuration of the solver. Note that the [Config::logic](smt::Config::logic)
    /// field should be ignored after construction.
    fn config(&self, config: &smt::Config) -> Result<()>;

    /// Push a frame on the assertion stack.
    fn push(&mut self) -> Result<()>;

    /// Pop the requested number of frames from the assertion stack.
    fn pop(&mut self, n: usize) -> Result<()>;

    /// Assert the term to the current frame of the assertion stack.
    fn require(&mut self, term: <Self::Manager as Manager>::Term) -> Result<()>;

    /// Check for satisfiability of the current assertion stack.
    fn check(&self) -> Result<Self::Result>;

    /// Return the model if one exists.
    fn model(&self) -> Result<Self::Model<'_>>;
}

/// Trait to represent a model from a [Solver].
pub trait Model: Sized {
    /// The type representing terms in the backend's API solver.
    ///
    /// This must be equal to [Manager::Term].
    type Term;

    /// Return the term representing the value of the given term.
    fn value(&self, term: Self::Term) -> Option<Self::Term>;
}
