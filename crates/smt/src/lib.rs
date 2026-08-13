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

#![allow(clippy::type_complexity)]

//! Abstraction around Satisfiability Modulo Theories solvers.
#![doc = ""]
#![cfg_attr(
    not(feature = "__subcratedoc"),
    doc = "**WARNING: This crate is not supposed to be used directly.**"
)]
#![doc = ""]
#![cfg_attr(
    not(feature = "__subcratedoc"),
    doc = "**Use instead the `formally::smt` module of the main `formally` crate by enabling the `\"smt\"` feature.**"
)]
#![doc = ""]
//!
//! The [smt][self] crate is at the core of `::formally`. The goal is to provide access to different
//! SMT solvers in a uniform way while at the same time granting access to as many solver-specific
//! features as possible, without limiting the user to the lowest common denominator between the
//! supported backends.
//!
//! ### Example
//! ```
//! # mod formally {
//! #    pub extern crate formally_support as support;
//! #    pub extern crate formally_smt as smt;
//! # }
//! use formally::smt::*;
//!
//! # use formally::support::*;
//! # fn main() -> Result<()> {
//! let config = Config::default().logic("LIA");
//! let mut solver = Solver::new(&config)?;
//!
//! solver.declare(Declaration::integer("x"))?;
//! solver.declare(Declaration::integer("y"))?;
//!
//! solver.require(term!(> (- x y) 0))?;
//! solver.require(term!(< x y))?;
//!
//! let answer = solver.check()?;
//!
//! assert_eq!(answer, Answer::No);
//! # Ok(())
//! # }
//! ```
//!
//! # Overview
//!
//! At the core of the [smt][self] crate we have the [Solver] type which provides easy access to a
//! selected backend (e.g. Z3), and the [Term] type which describes an SMT term that can be asserted
//! to the [Solver] or used to represent values in a model.
//!
//! Terms are built on top of [Function] objects which can be either:
//! 1. [Primitive] entities such as the ones defined by a theory, e.g. [theories::Ints::plus()].
//! 2. [Binding] entities used in function definitions to represent function parameters.
//! 3. [Declared] entities, which are the unknowns of the SMT problem, which the solver has to find
//!    values of.
//! 2. [Defined] entities, which have a known definition and are mostly just shortcuts to repeat
//!    common expressions.
//!
//! ## Declarations and definitions
//!
//! Functions (including constants, which are functions without arguments) are declared by
//! constructing a [Declaration] object and passing it to [Solver::declare()], as in the example
//! above. [Declaration] objects act like a specification of what we want to declare. Then, the
//! [declare()](Solver::declare()) method returns a [Declared] object which represents the specific
//! declared entity. [Declared] hides a shared reference to the unique underlying [Declaration]
//! object registered inside the solver, which is accessible via [Deref](std::ops::Deref) but, at
//! this point, immutable. One can freely clone [Declared] objects to obtain different handles to
//! the same underlying declaration.
//!
//! Similarly, definitions are obtained by calling [Solver::define()] with a [Definition] object.
//! The method returns a [Defined] object which uniquely represents the definition.
//!
//! [Declared] and [Defined] objects can then be used to build more complex [Term] objects, either
//! directly or with the [term] macro, which can then be asserted using [Solver::require()].
//!
//! In the above example we used the [Declaration::integer()] function which is a shortcut to call
//! [Declaration::constant()] with sort [theories::Ints::Int()]. In turn, [Declaration::constant()]
//! is a shortcut to call [Declaration::function()] with an empty domain. [Declaration::predicate()]
//! also exists to declare functions that return [theories::Core::Bool()]. Similar shortcuts exist
//! for [Definition].
//!
//! ## Building terms
//!
//! SMT terms are represented by the [Term] type, which is a shared reference to a [TermKind] enum.
//! The latter is a simple enum which is either a constant (such as `42` or `3.14`) or an atom that
//! applies a [Function] to some arguments. Usually, interfaces to SMT solvers provide many types
//! and functions to create all the different kind of terms supported by the solvers (boolean
//! connectives, arithmetic functions, and so on). Instead, [formally::smt] takes a different
//! approach. Terms are just applications of functions to arguments, and the functions are objects
//! provided by the different theories to represent what the theory supports.
//!
//! Theories do not need to be declared upfront by this crate, but can be declared at any time using
//! the [theory] macro. This design provides maximum flexibility for each backend to support any
//! available theory without being limited to only the theories this crate knows about in advance.
//! See the [theories] module for more details on theories.
//!
//! Despite this flexibility, building terms is straightforward thanks to the [term] macro, which
//! directly accepts a convenient subset of the SMT-LIBv2 syntax for terms. Inside terms, the macro
//! supports both specifying arbitrary names which will be looked-up by the [Solver] later, or
//! expanding previously declared  [Term] objects.
//!
//! Example:
//! ```
//! # mod formally {
//! #    pub extern crate formally_support as support;
//! #    pub extern crate formally_smt as smt;
//! # }
//! # use formally::{smt::*, support::*};
//! # fn main() -> Result<()> {
//! let config = Config::default().logic("LIA");
//! let mut solver = Solver::new(&config)?;
//!
//! solver.declare(Declaration::integer("x"))?;
//! solver.declare(Declaration::integer("y"))?;
//!
//! // here, `x` and `y` are looked up by `require()` in the solver's scope
//! solver.require(term!(= (+ x y) 0));
//!
//! let z = solver.declare(Declaration::integer("z"))?;
//! // here, `z` refers to the variable `z` declared above, of type [Declared], which
//! // is expanded in place after conversion to a [Term].
//! solver.require(term!(> #z 0))?;
//!
//! // any term can be expanded
//! let t1 = term!(> x y);
//! let t2 = term!(> y z);
//! let t3 = term!(> x z);
//! solver.require(term!(=> (and #t1 #t2) #t3))?;
//!
//! # Ok(())
//! # }
//! ```
//!
//! ## Asserting terms and extracting models
//!
//! Terms can be asserted with the [require()](Solver::require()) method of [Solver]. Then, the
//! solver can be asked to check the current assertions for satisfiability by calling
//! [check()](Solver::check()), which returns a [Result](formally::support::Result) holding a
//! [Answer], a simple tri-valued enum telling [Yes](Answer::Yes), [No](Answer::No), or
//! [Unknown](Answer::Unknown). Note that returning `Result<Answer>` means we distinguish
//! the case of an error occurring during processing from the case where the solver itself was not
//! able to find a solution without any erroneous condition.
//!
//! [Solver] implements [Stack](formally::support::Stack), so assertions can be stacked with
//! [push()](formally::support::Stack::push()) and [pop()](formally::support::Stack::pop()) as is
//! customary in most SAT/SMT solvers. Currently, these methods stack declarations and definitions
//! as well (the SMT-LIBv2 standard admits an option to select this behavior, which is not yet
//! supported).
//!
//! After a call to [check()](Solver::check()) returned `Ok(Answer::Yes)`, a model can be extracted
//! with the [model()](Solver::model()) method. This method returns `Result<Option<Model>>`, so
//! again we can distinguish the case where there is no model (because the last call to
//! [check()](Solver::check()) was unsuccessful) from the case where an error occurred while
//! extracting the model itself. The [Model] object can be used to extract values for single
//! [Declared] entities using the [value()](ModelProvider::value()) method, which returns
//! `Option<ModelValue>`. The way values are represented is still under revision, and currently it
//! is only possible to extract booleans ([ModelValue::Boolean]) or constant terms representing
//! integer or real values ([ModelValue::Constant]).
//!
//! Example:
//! ```
//! # mod formally {
//! #    pub extern crate formally_support as support;
//! #    pub extern crate formally_smt as smt;
//! # }
//! # use formally::{smt::*, support::*};
//! # fn main() -> Result<()> {
//! let mut solver = Solver::new(&Config::default())?;
//!
//! let p = solver.declare(Declaration::boolean("p"))?;
//!
//! solver.require(p.clone())?;
//!
//! assert_eq!(solver.check()?, Answer::Yes);
//!
//! assert_eq!(solver.model()?.unwrap().value(&p), Some(ModelValue::Boolean(true)));
//! # Ok(())
//! # }
//! ```
//!
//! ## Declaring sorts
//!
//! Sorts can be declared or defined in the same way as functions. Indeed, sorts are seen as just
//! constants of the special sort [Sort::sort()]. A shortcut [Declaration::sort()] exists in place
//! of calling `Declaration::constant(name, Sort::sort())`.
//!
//! Example:
//! ```
//! # mod formally {
//! #    pub extern crate formally_support as support;
//! #    pub extern crate formally_smt as smt;
//! # }
//! # use formally::{smt::*, support::*};
//! # fn main() -> Result<()> {
//! let config = Config::default().logic("UFLIA");
//! let mut solver = Solver::new(&config)?;
//!
//! let people = solver.declare(Declaration::sort("People"))?;
//! let food = solver.declare(Declaration::sort("Food"))?;
//! let likes = solver.declare(Declaration::predicate("likes", [people.clone(), food.clone()]))?;
//!
//! solver.declare(Declaration::constant("mike", people))?;
//! solver.declare(Declaration::constant("cake", food))?;
//!
//! solver.require(term!(not (likes mike cake)))?;
//!
//! # Ok(())
//! # }
//! ```
//!
//! Enumerated sorts and algebraic data types are not yet supported, but will be soon.
//!
//! ## Theories and logics
//!
//! [formally::smt] strictly follows the categories of theories and logics defined in the SMT-LIBv2
//! standard. In this respect, theories (instances of the [Theory](theories::Theory) trait) describe
//! the symbols (constants, functions and sorts) provided by the theory, while logics (instances of
//! the [Logic](logics::Logic) trait) combine a few of theories with a set of syntactic
//! constraints. For example, [LIA](logics::LIA) combines the theories [Core](theories::Core) and
//! [Ints](theories::Ints) and enforces the linearity of the terms, while [QF_ALIA](logics::QF_LIA)
//! combines [Core](theories::Core), [Ints](theories::Ints) and [Arrays](theories::Arrays) and
//! enforces both linearity and the absense of quantifiers.
//! Standard theories and logics declared in this way are unit structs (i.e. an instance of
//! [LIA](logics::LIA) is just `LIA`, not `LIA {}`), which provide one associated function for each
//! symbol provided by the theory. For example, the `Ints` theory in SMT-LIBv2 provides the "+"
//! binary function, which is accessible here as [Ints::plus()](theories::Ints::plus()). Note that
//! naming these methods directly is seldom necessary because the symbols can be looked up by name
//! when using the [term] macro.
//!
//! For example, a term `term!(+ x y)` will contain an unbound name `"+"` which will be resolved by
//! the solver when the term is used (e.g. in an assertion or a definition), and found to correspond
//! to [Ints::plus()](theories::Ints::plus()) or any other symbol matching its arguments (e.g.
//! [Reals::plus()](theories::Reals::plus()) if `x` and `y` resolve to reals) in the theories
//! combined by the logic selected in the current backend.
//!
//! The crate provides a set (currently incomplete) of standard theories and logics extracted from
//! the SMT-LIBv2 standard, but new ones can be declared with the help of the [theory] and [logic]
//! macros, so we refer to their documentation for details.
//!
//! ## SMT backends
//!
//! Backends are types implementing the [Backend](backend::Backend) trait. Currently, we only
//! provide the [backend::z3::Z3] backend, implemented on top of the [z3_sys] crate.
//!
//! See the documentation of the [Backend](backend::Solver) trait for information about how to
//! implement new backends.
//!
//! ## Parsing and executing SMT-LIBv2 scripts
//!
//! This crate provides full support for parsing and executing scripts in the SMT-LIBv2 language as
//! defined by the [official specification document](https://smt-lib.org/language.shtml), currently
//! updated to version 2.7. Everything that regards the SMT-LIBv2 language is contained in the
//! [smtlib] module so we refer to that module's documentation for details.
//!
//! ## Error handling
//! [formally::smt] integrates with the error handling schema of `formally` by emitting diagnostics
//! using the [Emitter](formally::support::Emitter) currently set in the
//! [Context](formally::support::Context) currently selected in [Solver] (which is a
//! [Contextual](formally::support::Contextual) type). Almost all methods of [Solver] return a
//! [Result](formally::support::Result) to account for possible failures which are detailed in the
//! emitted diagnostics. See the documentation of [Result](formally::support::Result) and
//! [Emitter](formally::support::Emitter) for details.
//!
//! ## Current limitations
//!
//! [formally::smt], like the rest of the framework, is under active development and many features
//! are missing or incomplete. Here is a list of currently unimplemented or partially implemented
//! features that are needed for a fully compliant support of SMT-LIBv2:
//! 1. recursive function definitions
//! 2. sort definitions
//! 3. enumerated sorts and algebraic data types
//! 4. let expressions, quantifiers, and match expressions
//! 5. proper representation of models and values coming from models
//! 6. the complete taxonomy of standard SMT-LIBv2 theories and logics
//! 7. many SMT-LIBv2 commands in [Interpreter](smtlib::interpreter::Interpreter)
//! 8. many other little things...
//!
//! On top of that, more backends will be needed, probably starting from
//! [cvc5](https://cvc5.github.io).
//!
//! The project as a whole also currently lacks a proper test suite for correctness and compliance
//! with the language specification, so those features that are already implemented will have bugs.

mod formally {
    pub use formally_io as io;
    pub use formally_support as support;
    pub extern crate self as smt;
}

#[doc(hidden)]
pub mod exports {
    pub use linkme::distributed_slice;
    pub use paste::paste;
}

pub use formally_smt_macros::*;

mod decl;
mod pool;
mod pretty;
mod resolve;
mod solver;
mod sort;
mod term;
mod type_check;

#[doc(hidden)]
pub mod macros;

pub mod backend;
pub mod logics;
pub mod smtlib;
pub mod theories;

pub use decl::*;
pub use pool::*;
pub use solver::*;
pub use sort::*;
pub use term::*;
pub use type_check::*;
