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

//! Support utilities common to all `formally` submodules.
#![doc = ""]
#![cfg_attr(
    not(feature = "__subcratedoc"),
    doc = "**WARNING: This crate is not supposed to be used directly.**"
)]
#![doc = ""]
#![cfg_attr(
    not(feature = "__subcratedoc"),
    doc = "**Use instead the `formally::support` module of the main `formally` crate.**"
)]
#![doc = ""]
//!
//! The [support][self] crate includes several components used throughout all the `formally` modules
//! and frequently used by any client code.
//!
//! These include:
//! 1. The main [Context] object and related utilities
//! 2. The *diagnostics* system, including the [error] macro, the [Emitter] trait and different
//!    types of *emitters*.
//! 3. The [Scope] type to help implementing statically scoped languages.
//! 4. Utilities to represent and keep track of *source locations*, including the [Location] and the
//!    [Span] types.
//! 5. Procedural macros to derive the `Located` and `Locatable` traits.
//! 6. The [Nominal] smart pointer.
//! 7. The [Stack] trait and the [Stacked] utility class to help implementing it.

mod formally {
    pub extern crate self as support;
}

#[doc(inline)]
pub use formally_support_macros::*;

mod diagnostics;
mod location;
mod nominal;
mod scope;
mod stack;

pub use diagnostics::*;
pub use location::*;
pub use nominal::*;
pub use scope::*;
pub use stack::*;
