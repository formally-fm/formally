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

mod logic;
mod term;
mod theories;

use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;

#[proc_macro]
pub fn term(input: TokenStream) -> TokenStream {
    let term = parse_macro_input!(input as term::Term);

    quote!(#term).into()
}

#[proc_macro]
pub fn sort(input: TokenStream) -> TokenStream {
    let sort = parse_macro_input!(input as term::Sort);

    quote!(#sort).into()
}

#[proc_macro]
pub fn theories(input: TokenStream) -> TokenStream {
    let root = parse_macro_input!(input as theories::Root);

    quote!(#root).into()
}

#[proc_macro]
pub fn logic(input: TokenStream) -> TokenStream {
    let root = parse_macro_input!(input as logic::Root);

    quote!(#root).into()
}
