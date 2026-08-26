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

//! SMT backend(s) and facilities to write them.
//!
//! This module provides the supported SMT backends and facilities to write new ones.
//!
//! Currently, we provide a [Z3](z3::Z3) and a [cvc5](cvc5::Cvc5) backends, with others following
//! later.
//!
//! The backend is chosen when instantiating a [TermManager](smt::TermManager) or, as a shortcut,
//! with the [Solver::with_backend()](smt::Solver::with_backend) function when constructing
//! a [Solver](smt::Solver).
//!
//! ```
//! # mod formally {
//! #     pub extern crate formally_support as support;
//! #     pub extern crate formally_smt as smt;
//! # }
//! # use formally::support::*;
//! use formally::smt::{*, backend::z3::Z3};
//! # fn main() -> Result<()> {
//! let config = Config::default();
//! let manager = TermManager::new(Z3);
//! let solver = Solver::with_manager(&config, manager)?;
//!
//! // ...
//!
//! # Ok(())
//! # }
//! ```
//!
//! # How to write new backends
//!
//! A backend is a type implementing the [Backend] trait. This trait only provides three methods:
//! 1. [name()](Backend::name()), which just returns a string with the name of the backend.
//! 2. [manager()](Backend::manager()), which returns an instance of a backend's *term manager*
//!    (also called *context* in some backends).
//! 2. [solver()](Backend::solver()), which returns an instance of a backend's *solver*
//!
//! A high-level user of the framework never calls these methods.
//! 1. The backend type is what you pass around to tell *which* backend you want to use, e.g. in the
//!    [Config] of a [Solver].
//! 2. The [backend::Manager](Manager) and [backend::Solver](Manager) instances do the actual job,
//!    but are used internally by the [Solver](smt::Solver) type.
//!
//! # The API facade
//!
//! The [api] module contains two types, [SolverFacade](api::SolverFacade) and
//! [ManagerFacade](api::ManagerFacade), that help implementing a backend based on common
//! programmatic APIs (as opposed to calling a command-line tool). Using the API facade should be
//! preferred respecting to implementing [Backend] directly because it hides a non-trivial amounts
//! of complexity. We refer to the documentation of the [api] module for details.
//!
//! # How to write a backend from scratch
//!
//! When the API facade is not sufficient or suitable, a [Backend] instance has to be written from
//! scratch. The documentation of the [Backend], [Manager] and [Solver] traits provide specific
//! details. What follows explain general concepts and requirements.
//!
//! ## Managers and Solvers
//!
//! Most SMT APIs distinguish between a *term manager* (or *context*) which handles the life of
//! terms, and a *solver* which actually perform the reasoning process. The backend thus provides
//! an instance [Manager] for the former and [Solver] for the latter. the [manager](Manager) is
//! meant to be used exclusively by the corresponding [Solver] and the trait does not actually
//! provide any method beside [Manager::backend()]. Since `Manager: Any`, under the hood the backend
//! can downcast `&dyn Manager` to `&T` for any specific type `T` and use it as needed.
//!
//! Note that different [solvers][Solver] can be created with the same [Manager] through the
//! [Backend::solver()] method, so the backend code is expected to account for this fact.
//!
//! ## Theories and logics
//!
//! The logic to instantiate the backend with is set by name in the [Config] object. The backend
//! instance is then expected to provide a `&dyn Logic` reference through the
//! [logic()](Solver::logic()) method. For standard SMT-LIBv2 logics, backends can use the
//! [standard_logic()](logics::standard_logic()) function to lookup a standard logic by name.
//!
//! However, note that backends do not necessarily have to associate names of standard logics (e.g.
//! `"LIA"`) to the corresponding types declared in the [logics] module. What *is* expected is that
//! the symbols provided by the background theories of standard logics correspond to those
//! provided in the [theories](mod@smt::theories) module.
//!
//! For instance, if a backend supports some non-standard extension of `"LIA"` (e.g. an additional
//! function symbol), it can declare a custom `"LIA"` logic that combines the standard `Ints` theory
//! with a custom theory that declares the additional symbol. On the converse, if a solver supports
//! `"LIA"` partially, e.g. everything except the `abs` function, it can redeclare a custom logic
//! based on the standard [Ints](smt::theories::Ints) theory and add a syntactic requirement that
//! scan terms to forbid the use of `abs`.
//!
//! ## Error handling in backends
//!
//! In order to simplify the life of backend developers and provide a consistent experience to
//! users of different backends, backends *do not* directly emit their errors as diagnostics.
//! Instead, the methods of [Solver] return a [Result] whose error type is [Error](struct@Error),
//! which provides a non-exhaustive taxonomy of the possible errors that a backend may encounter.
//! [Error](struct@Error) is [Diagnosable], so users of the backend interface (e.g. [Solver]) can
//! still easily emit those errors as diagnostics later.
//!
//! ## Assumptions and guarantees
//!
//! The documentation of each method in [Solver] provides a set of preconditions that the methods
//! can assume to hold. When the backend instance methods are invoked by [Solver], these assumptions
//! are guaranteed to hold. However, to guarantee stability even in the presence of bugs (both
//! in the framework and in the backend), backends are expected to behave as follows.
//!
//! 1. any internal error should *not* cause *undefined behavior*, i.e. unsafe code in the backend
//!    cannot depend on external preconditions to hold. This includes C or C++ code called inside
//!    the backend code to interface with external APIs.
//! 2. any internal error should *not* cause a Rust panic or a C++ exception to unwind past the
//!    boundary of the [Solver] methods. If the backend contains code that may panic or throw an
//!    exception, that code must be wrapped either inside a [catch_unwind](std::panic::catch_unwind)
//!    call in Rust or a `try { ... } catch { ... }` block in C++, and the error turned into a
//!    [Error](struct@Error) of kind [ErrorKind::Internal].
//! 3. a violated precondition *can* result either into a [Error](struct@Error) of kind
//!    [ErrorKind::ViolatedPrecondition] or into a logical misbehaviour, i.e., wrong answers,
//!    deadlocks, etc.. In other words, backends are not *forced* to detect the violation of the
//!    preconditions, and can have arbitrary (but *not* undefined) behavior in those cases.

pub mod api;
pub mod cvc5;
pub mod z3;

use crate::formally;
use formally::{
    smt::{self, Config, Declared, Defined, ModelProvider, logics},
    support::{Diagnosable, Identifier, Level, Located, Span},
};
use std::{any::Any, fmt::Debug, fmt::Formatter, io, rc::Rc};

use derive_more::Display;
use thiserror::Error;

/// The error type for backends.
///
/// This error type is [Diagnosable] so it is emitted as a diagnostic when converted to
/// [DiagnosticEmitted](formally::support::DiagnosticEmitted) (e.g. via the `?` operator).
#[derive(Debug, Display, Error)]
#[display("SMT backend `{backend}`: {kind}")]
pub struct Error {
    /// Which error occurred.
    pub kind: Box<ErrorKind>,
    /// The name of the backend that generated the error.
    pub backend: String,
}

impl Error {
    pub fn new(backend: &str, kind: ErrorKind) -> Error {
        Error {
            kind: Box::new(kind),
            backend: backend.into(),
        }
    }
}

/// An enumeration of possible errors for [Error](struct@Error).
#[derive(Debug, Display)]
pub enum ErrorKind {
    /// Some request was unsupported.
    #[display("unsupported feature: {msg}")]
    Unsupported {
        /// A message telling what was unsupported.
        msg: String,
        /// A span associated with the unsupported request.
        span: Option<Span>,
    },

    /// The requested logic was unsupported.
    #[display("unsupported logic: {_0}")]
    UnsupportedLogic(Identifier<'static>),

    /// An external precondition was found to not hold.
    #[display("violated precondition: {_0}")]
    ViolatedPrecondition(String),

    /// An internal error occurred.
    #[display("{_0}")]
    Internal(Box<dyn std::error::Error>),

    /// An error of any kind occurred.
    #[display("{_0}")]
    Other(Box<dyn std::error::Error>),

    /// An I/O error occurred.
    #[display("input/output error: {_0}")]
    IO(io::Error),
}

impl Located for Error {
    fn span(&self) -> Option<Span> {
        match &*self.kind {
            ErrorKind::Unsupported { span, .. } => span.clone(),
            _ => None,
        }
    }
}

impl Diagnosable for Error {
    fn level(&self) -> Level {
        match *self.kind {
            ErrorKind::Unsupported { .. } => Level::Error,
            _ => Level::Internal,
        }
    }
}

/// The trait for SMT backends.
///
/// Types implementing this trait represent backends. See the top-level documentation
/// for details about [how to write a new backend](smt::backend).
pub trait Backend {
    /// Return the name of the backend.
    fn name(&self) -> &str;

    /// Create an instance of the backend term manager.
    fn manager(&self) -> Box<dyn Manager>;

    /// Create an instance of the backend solver based on the given [Config] and [Manager]
    fn solver(&self, config: &Config, manager: Rc<dyn Manager>) -> Result<Box<dyn Solver>, Error>;
}

impl Debug for dyn Backend {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// The trait for *term managers* of SMT backends.
///
/// This trait does not provide any method besides [backend()](Manager::backend()) because it is
/// only meant to be used in `dyn` objects which are downcasted as needed by the corresponding
/// [solver][Solver].
pub trait Manager: Any {
    /// Return the backend this manager is an instance of.
    ///
    /// This is useful to obtain a new solver or manager of the same backend or the name of the
    /// backend.
    fn backend(&self) -> &dyn Backend;
}

/// The trait for *solvers* of SMT backends.
///
/// Types implementing this trait are the ones doing the hard work for backends.
///
/// The documentation of each method lists its intended purpose and what external preconditions
/// the method can assume to hold when the backend is used through a [Solver].
///
/// However, please read before the documentation on [how to write a new backend](smt::backend).
pub trait Solver {
    /// Return the manager this solver was built on.
    fn manager(&self) -> &dyn Manager;

    /// Return the backend this instance is an instance of.
    ///
    /// This is useful to obtain a new different instance of the same backend or the name of the
    /// backend.
    fn backend(&self) -> &dyn Backend;

    /// Update the configuration of the solver based on the new [Config].
    ///
    /// The [Config::logic] field should be ignored (and only considered in the construction of the
    /// solver).
    fn config(&self, config: &Config) -> Result<(), Error>;

    /// Return the logic object associated with the logic selected by the original [Config] object.
    fn logic(&self) -> &'_ dyn logics::Logic;

    /// Register a new [Declared] object in the backend instance.
    ///
    /// In most cases, declared entities need to be declared to the backend somehow before being
    /// used in asserted terms. This method allows a backend to do so.
    ///
    /// This method *can assume* that the sorts mentioned by the sorts in the [Declared] object are
    /// fully [resolved](smt::Resolve::resolve()) and [type
    /// checked](smt::TypeCheck::type_check()).
    fn declare(&mut self, decl: Declared) -> Result<(), Error>;

    /// Register a new [Defined] object in the backend instance.
    ///
    /// In some cases, defined entities need to be defined to the backend somehow before being
    /// used in asserted terms. This method allows a backend to do so.
    ///
    /// This method *can assume* that the sorts mentioned by the [Defined] object are suflly
    /// [resolved](smt::Resolve::resolve()) and [type checked](smt::TypeCheck::type_check()).
    fn define(&mut self, def: Defined) -> Result<(), Error>;

    /// Push a frame on the assertions stack.
    fn push(&mut self) -> Result<(), Error>;

    /// Pop `n` frames on the assertions stack.
    ///
    /// If there are not enough pushed frames, this method *should not* return an error, but
    /// behave as if the maximum number of available frames had been specified.
    fn pop_n(&mut self, n: usize) -> Result<(), Error>;

    /// Asserts a term to the current frame of the assertions stack.
    ///
    /// This method *can assume* that the term is
    /// fully [resolved](smt::Resolve::resolve()), and
    /// [type checked](smt::TypeCheck::type_check()) is guaranteed to return
    /// [Core::Bool()](smt::theories::Core::Bool()).
    fn require(&mut self, term: &smt::Term) -> Result<(), Error>;

    /// Check the current frame on the assertions stack for satisfiability.
    fn check(&mut self) -> Result<Option<bool>, Error>;

    /// Returns the current model.
    ///
    /// If a model does not exist for any *logical* reason, including when the previous call to
    /// [check()](Solver::check()) did *not* return `Ok(Answer::Yes)`, the method should return
    /// `Ok(None)`. An error should be returned only if extracting a model failed for some
    /// unexpected reason (i.e. an I/O error).
    fn model(&self) -> Result<Option<Box<dyn '_ + ModelProvider>>, Error>;
}
