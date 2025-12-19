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
        "deriving Located for unions is not supported",
    ))
}

fn derive_struct(ident: Ident, generics: Generics, input: DataStruct) -> Result<TokenStream> {
    match input.fields {
        Fields::Named(named) => derive_named_struct(ident, generics, named),
        Fields::Unnamed(unnamed) => derive_tuple_struct(ident, generics, unnamed),
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
            impl #impl_generics formally::support::Located for #ident #ty_generics #where_clause {
                fn span(&self) -> ::std::option::Option<formally::support::Span> {
                    self.span.clone()
                }
            }
        })
    } else {
        Err(Error::new(
            ident.span(),
            "deriving Located requires a field called `span` of type `Option<Span>`",
        ))
    }
}

fn derive_tuple_struct(
    ident: Ident,
    generics: Generics,
    fields: FieldsUnnamed,
) -> Result<TokenStream> {
    let expr = match fields.unnamed.len() {
        0 => quote!(None),
        1 => quote!(self.0.span()),
        _ => {
            return Err(Error::new(
                ident.span(),
                "deriving Located for tuple structs with more than one field is \
                    currently not supported",
            ));
        }
    };

    let (params, args, where_) = generics.split_for_impl();

    Ok(quote_spanned! {
        ident.span() =>
        impl #params formally::support::Located for #ident #args #where_ {
            fn span(&self) -> ::std::option::Option<formally::support::Span> {
                #expr
            }
        }
    })
}

fn derive_unit_struct(ident: Ident) -> Result<TokenStream> {
    Err(Error::new(
        ident.span(),
        "deriving Located for unions is currently not supported",
    ))
}

fn derive_enum(ident: Ident, generics: Generics, input: DataEnum) -> Result<TokenStream> {
    let mut matches = quote! {};

    for variant in input.variants {
        let name = variant.ident;
        match variant.fields {
            Fields::Named(_) => matches.extend(quote! {
                #ident::#name { span, .. } => span.clone(),
            }),
            Fields::Unnamed(unnamed) => match unnamed.unnamed.len() {
                0 => matches.extend(quote! {
                    #ident::#name() => None,
                }),
                1 => {
                    matches.extend(quote! {
                        #ident::#name(field) => field.span(),
                    });
                }
                _ => {
                    return Err(Error::new(
                        name.span(),
                        "deriving Located for enum tuple variants of multiple \
                                fields is not yet supported",
                    ));
                }
            },
            Fields::Unit => {
                matches.extend(quote! {
                   #ident::#name => None,
                });
            }
        }
    }

    let (params, args, where_) = generics.split_for_impl();

    Ok(quote! {
        impl #params formally::support::Located for #ident #args #where_ {
            fn span(&self) -> ::std::option::Option<formally::support::Span> {
                match self {
                    #matches
                }
            }
        }
    })
}
