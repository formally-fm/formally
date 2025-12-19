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

//!
//! The open-source formal methods toolchain.
//!
//! `::formally` is a project that aims to build a comprehensive open-source framework and
//! toolchain to help the development of formal methods applications.
//!
//! # What the project currently provides
//! The project is still in its very early stages and is in active development. These early releases
//! is meant to be a preview of where the project is going and the start of an open development
//! process for the project.
//!
//! What the project *does* currently provide consists in the following:
//! 1. [formally::support](support) provides common facilities useful for the rest of the project.
//!    Crucially, it provides a mechanism of error reporting based on the concept of *diagnostic*,
//!    similar to what seen in many modern compilers, and facilities to produce precise and
//!    informative error messages throughout the project.
//! 2. [formally::io](io) provides utilities to parse input and produce output. The main part of the
//!    module is a *parser combinators* library that allows easy and quick writing of parsers that
//!    automatically produce precise and high-quality error messages, integrated with the project's
//!    error reporting infrastructure.
//! 3. [formally::smt](smt) provides an abstraction over Satisfiability Modulo Theories solvers and
//!    (what will hopefully become) a fully conformant implementation of the SMT-LIBv2 language.
//! 4. A simple toy command-line frontend to test the [formally::smt](smt) module.
//!
//! The [formally::smt](smt) module is quite under heavy development but can already handle simple
//! SMT-LIBv2 scripts, solving them with a [Z3](https://github.com/Z3Prover/z3) backend.
//!
//! # How to run the command-line frontend
//!
//! The front-end can be installed through the `formally-cli` package.
//! ```shell
//! $ cargo install formally-cli
//! ```
//! Then, the `formally` command accepts a `solve` subcommand with the name of an SMT-LIBv2 file to
//! run.
//!
//! ```shell
//! $ cat test.smtlib
//! (set-logic ALIA)
//! (declare-const array (Array Int Int))
//!
//! (assert (not (= (select (store array 0 42) 0) 42)))
//!
//! (check-sat)
//!
//! $ formally solve test.smtlib
//! unsat
//! ```
//!
//! # How to use the sub-crates
#![doc = document_features::document_features!()]
//!
//! Each feature enables a specific sub-crate and re-exports it as a submodule of [formally].
//! Sub-crates are designed to be used in this way, and not by directly adding them as dependencies.
//! Macros may not work otherwise, because they expect the crates to be reachable as e.g.
//! `formally::support` instead of `formally_support`.

#![cfg_attr(docsrs, feature(doc_cfg))]

extern crate self as formally;

#[doc(inline)]
pub extern crate formally_support as support;

#[cfg_attr(docsrs, doc(cfg(feature = "io")))]
#[cfg(feature = "io")]
#[doc(inline)]
pub extern crate formally_io as io;

#[cfg_attr(docsrs, doc(cfg(feature = "smt")))]
#[cfg(feature = "smt")]
#[doc(inline)]
pub extern crate formally_smt as smt;
