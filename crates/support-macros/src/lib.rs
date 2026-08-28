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

//! Procedural macros exported by the `formally::support` subcrate.
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

extern crate proc_macro;

mod locatable;
mod located;

use proc_macro::TokenStream;

/// Procedural macro to derive the `Located` trait.
///
/// To be able to derive `Located`, a `struct` must contain a field named `span` of type
/// `Option<Span>`.
///
/// For `enum`s, only variants with no fields or with a single field are supported at the moment.
/// In the first case, the derived `Located` implementation returns `None`, while in the second case
/// the type contained in the variant must in turn be `Located`, so that its `span()` method is
/// used.
///
/// Example:
/// ```text
/// # mod formally {
/// #     pub use formally_support as support;
/// # }
/// # use formally::support::*;
/// #
/// #[derive(Located, Locatable)]
/// struct Identifier {
///    name: String,
///    span: Option<Span>
/// }
/// ```
#[proc_macro_derive(Located)]
pub fn derive_located(item: TokenStream) -> TokenStream {
    located::derive(item)
}

/// Procedural macro to derive the `Locatable` trait.
///
/// To be able to derive `Locatable`, a `struct` must contain a field named `span` of type
/// `Option<Span>`.
///
/// For `enum`s, only variants with no fields or with a single field are supported at the moment.
/// In the first case, the derived `Locatable` returns the same variant as is, while in the second
/// case the type contained in the variant must in turn be `Locatable`, so that its `over()` method
/// is used.
///
/// Example:
/// ```text
/// # mod formally {
/// #     pub use formally_support as support;
/// # }
/// # use formally::support::*;
/// #
/// #[derive(Located, Locatable)]
/// struct Identifier {
///    name: String,
///    span: Option<Span>
/// }
/// ```
#[proc_macro_derive(Locatable)]
pub fn derive_locatable(item: TokenStream) -> TokenStream {
    locatable::derive(item)
}
