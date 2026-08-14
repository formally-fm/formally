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

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::*;

pub fn derive(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(item as DeriveInput);

    let result = match input.data {
        Data::Struct(decl) => derive_struct(input.ident, input.generics, decl),
        Data::Enum(decl) => derive_enum(input.ident, input.generics, decl),
        Data::Union(input) => derive_union(input.union_token),
    };

    match result {
        Ok(ok) => ok.into(),
        Err(err) => err.into_compile_error().into(),
    }
}

fn derive_union(token: Token![union]) -> Result<TokenStream> {
    Err(Error::new(
        token.span,
        "deriving Locatable for unions is not supported",
    ))
}

fn derive_struct(ident: Ident, generics: Generics, input: DataStruct) -> Result<TokenStream> {
    match input.fields {
        Fields::Named(named) => derive_named_struct(ident, generics, named),
        Fields::Unnamed(_) => derive_tuple_struct(ident),
        Fields::Unit => derive_unit_struct(ident),
    }
}

fn derive_named_struct(
    ident: Ident,
    generics: Generics,
    fields: FieldsNamed,
) -> Result<TokenStream> {
    let field = fields
        .named
        .iter()
        .find(|field| field.ident == Some(Ident::new("span", Span::call_site())));

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    if let Some(field) = field {
        let name = field.ident.as_ref().unwrap();
        Ok(quote_spanned! {
            name.span() =>
            impl #impl_generics formally::support::Locatable for #ident #ty_generics #where_clause
            {
                type Located = Self;

                #[allow(clippy::needless_update)]
                fn over(self, span: impl ::std::convert::Into<::std::option::Option<formally::support::Span>>) -> Self {
                    Self {
                        span: span.into(),
                        ..self
                    }
                }
            }
        })
    } else {
        Err(Error::new(
            ident.span(),
            "deriving Locatable requires a field called `span` of type `Option<Span>`",
        ))
    }
}

fn derive_tuple_struct(ident: Ident) -> Result<TokenStream> {
    Err(Error::new(
        ident.span(),
        "deriving Locatable for tuple structs is currently not supported",
    ))
}

fn derive_unit_struct(ident: Ident) -> Result<TokenStream> {
    Err(Error::new(
        ident.span(),
        "deriving Locatable for unit structs is currently not supported",
    ))
}

fn derive_enum(ident: Ident, generics: Generics, input: DataEnum) -> Result<TokenStream> {
    let mut matches = quote! {};

    for variant in input.variants {
        let name = variant.ident;
        match variant.fields {
            Fields::Named(named) => {
                let names: Vec<_> = named
                    .named
                    .iter()
                    .map(|field| field.ident.clone().unwrap())
                    .filter(|ident| ident != "span")
                    .collect();

                matches.extend(quote! {
                    #ident::#name { #(#names),*, .. } =>
                        #ident::#name { span: span.into(), #(#names),* },
                })
            }
            Fields::Unnamed(unnamed) => match unnamed.unnamed.len() {
                0 => matches.extend(quote! {
                    #ident::#name() => #ident::#name(),
                }),
                1 => matches.extend(quote! {
                    #ident::#name(field) => #ident::#name(field.over(span).into()),
                }),
                _ => {
                    return Err(Error::new(
                        name.span(),
                        "deriving Locatable for unnamed enum variants with multiple \
                                fields is not yet supported",
                    ));
                }
            },
            Fields::Unit => {
                matches.extend(quote! {
                    #ident::#name => #ident::#name,
                });
            }
        }
    }

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    Ok(quote! {
        impl #impl_generics formally::support::Locatable for #ident #ty_generics #where_clause {
            type Located = Self;

            #[allow(clippy::needless_update)]
            fn over(self, span: impl ::std::convert::Into<::std::option::Option<formally::support::Span>>) -> Self {
                match self {
                    #matches
                }
            }
        }
    })
}
