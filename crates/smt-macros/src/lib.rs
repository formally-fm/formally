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

//! Procedural macros exported by the `formally::smt` subcrate.
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

mod term;

use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;

use term::*;

/// Construct a term from a subset of the SMT-LIBv2 syntax for terms.
///
/// This macro provides a convenient way of constructing terms by implementing a subset of the
/// SMT-LIBv2 syntax.
///
/// Example:
/// ```
/// # mod formally {
/// #     pub extern crate formally_support as support;
/// #     pub extern crate formally_smt as smt;
/// # }
/// # use formally::{smt::*, support::*};
/// # fn main() -> Result<()> {
/// let mut solver = Solver::new(&Config::default())?;
///
/// solver.declare(Declaration::boolean("p"))?;
/// solver.declare(Declaration::boolean("q"))?;
///
/// let ponens = term!(=> (and (=> p q) p) q);
/// solver.require(term!(not #ponens))?;
///
/// assert_eq!(solver.check()?, Answer::No);
/// # Ok(())
/// # }
/// ```
///
/// In the above example we can note two features of the `term` macro combined with `Solver`.
/// 1. names of the symbols can be used directly, in which case the resulting term will contain
///    *unbound atoms* that the solver will resolve when needed (in this case, in the call to
///    `require()`. This is the case of the `"and"`, `"p"`, `"q"`, and `"not"` symbols in the
///    example above.
/// 2. entities declared in the surrounding Rust code, including other terms, can be expanded by
///    using the `#identifier` syntax, inspired by the `quote` macro of the `syn` crate. This is the
///    case of the `#ponens` expansion in the example above.
///
/// When an entity is expanded it is used in the resulting term appropriately. In particular, one
/// can expand `Declared` or `Defined` objects to obtain *bound atoms* that do not need
/// further name resolution.
///
/// Expansion of repetitions from iterators, as in the `quote` macro, is not supported *yet*.
#[proc_macro]
pub fn term(input: TokenStream) -> TokenStream {
    let term = parse_macro_input!(input as Root);

    quote!(#term).into()
}
