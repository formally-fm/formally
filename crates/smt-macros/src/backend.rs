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

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput};

pub fn backend(input: DeriveInput) -> TokenStream {
    if let Data::Struct(st) = &input.data
        && matches!(st.fields, syn::Fields::Unit)
    {
        let ident = &input.ident;
        let staticident = syn::Ident::new(&format!("MY_BACKEND_{ident}"), ident.span());
        return quote! {
            #input

            #[allow(nonstandard_style)]
            #[formally::smt::exports::distributed_slice(formally::smt::backends::BACKENDS)]
            static #staticident: &'static dyn formally::smt::backends::Backend = &#ident;
        };
    }

    quote! {
        compile_error!("the #[backend] attribute can only be applied to unit structs");

        #input
    }
}
