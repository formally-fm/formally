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
use quote::{format_ident, quote, quote_spanned};
use syn::*;

pub fn derive(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(item as DeriveInput);

    let result = match input.data {
        Data::Struct(item) => derive_struct(input.ident, input.generics, item),
        Data::Enum(item) => derive_enum(input.ident, input.generics, item),
        Data::Union(item) => derive_union(item),
    };

    match result {
        Ok(ok) => ok.into(),
        Err(err) => err.into_compile_error().into(),
    }
}

fn unnamed_fresh_ident(index: usize) -> Ident {
    format_ident!("fresh_{index}")
}

fn all_named_fields(fields: &FieldsNamed) -> Vec<Ident> {
    fields
        .named
        .iter()
        .map(|field| field.ident.clone().unwrap())
        .collect()
}

fn all_unnamed_fields(fields: &FieldsUnnamed) -> Vec<Ident> {
    fields
        .unnamed
        .iter()
        .enumerate()
        .map(|(i, _)| unnamed_fresh_ident(i))
        .collect()
}

fn context_named_field(fields: &FieldsNamed) -> Option<Ident> {
    for field in &fields.named {
        if field.ident == Some(Ident::new("context", Span::call_site())) {
            return field.ident.clone();
        }
    }

    None
}

fn context_unnamed_field(fields: &FieldsUnnamed) -> Option<Ident> {
    for (i, field) in fields.unnamed.iter().enumerate() {
        if field
            .attrs
            .iter()
            .any(|attr| matches!(&attr.meta, Meta::Path(path) if path.is_ident("context")))
        {
            return Some(unnamed_fresh_ident(i));
        }
    }

    None
}

fn contextual_unnamed_fields(fields: &FieldsUnnamed) -> Vec<Ident> {
    let mut vec = Vec::new();
    for (i, field) in fields.unnamed.iter().enumerate() {
        if field
            .attrs
            .iter()
            .any(|attr| matches!(&attr.meta, Meta::Path(path) if path.is_ident("contextual")))
        {
            vec.push(unnamed_fresh_ident(i))
        }
    }

    vec
}

fn contextual_named_fields(fields: &FieldsNamed) -> Vec<Ident> {
    let mut vec = Vec::new();
    for field in &fields.named {
        if field
            .attrs
            .iter()
            .any(|attr| matches!(&attr.meta, Meta::Path(path) if path.is_ident("contextual")))
        {
            vec.push(field.ident.clone().unwrap())
        }
    }

    vec
}

fn fields_accessors(
    ident: &Ident,
    context: &Option<Ident>,
    contextuals: &[Ident],
) -> Result<(TokenStream, TokenStream)> {
    let mut set = match contextuals {
        [] => quote! {},
        [one] if context.is_none() => quote! {
            #one.set_context(ctx);
        },
        [one] => quote! {
            #one.set_context(ctx.clone());
        },
        [first, last] => quote! {
            #first.set_context(ctx.clone());
            #last.set_context(ctx);
        },
        [first, .., last] => {
            let middle = &contextuals[1..contextuals.len() - 1];
            quote! {
                #first.set_context(ctx.clone());
                #(#middle.set_context(ctx.clone()))*
                #last.set_context(ctx);
            }
        }
    };

    let get = match (context, contextuals) {
        (Some(context), []) => {
            set = quote! {
                *#context = ctx;
            };
            quote! {
                #context.clone()
            }
        }
        (Some(context), [..]) => {
            set = quote! {
                *#context = ctx.clone();
                #set
            };
            quote! {
                #context.clone()
            }
        }
        (None, [first, ..]) => quote! {
            #first.context()
        },
        (None, []) => {
            return Err(Error::new(
                ident.span(),
                "deriving Contextual requires at least a field named `context` of \
            type `Context` or a field marked with #[contextual] implementing \
            `Contextual`",
            ));
        }
    };

    Ok((get, set))
}

fn derive_struct(ident: Ident, generics: Generics, input: DataStruct) -> Result<TokenStream> {
    let token = input.struct_token;
    match input.fields {
        Fields::Named(named) => derive_named_struct(ident, generics, named),
        Fields::Unnamed(unnamed) => derive_unnamed_struct(ident, generics, unnamed),
        Fields::Unit => derive_unit_struct(token),
    }
}

fn derive_named_struct(
    ident: Ident,
    generics: Generics,
    fields: FieldsNamed,
) -> Result<TokenStream> {
    let all = all_named_fields(&fields);
    let context = context_named_field(&fields);
    let contextuals = contextual_named_fields(&fields);
    let (get, set) = fields_accessors(&ident, &context, &contextuals)?;

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let out = quote_spanned! {
        ident.span() =>
            impl #impl_generics formally::support::Contextual for #ident #ty_generics #where_clause {
                #[allow(unused_variables)]
                fn context(&self) -> formally::support::Context {
                    let #ident { #(#all),* } = self;
                    #get
                }

                #[allow(unused_variables)]
                fn set_context(&mut self, ctx: Context) {
                    let #ident { #(#all),* } = self;
                    #set
                }
            }
    };

    Ok(out)
}

fn derive_unnamed_struct(
    ident: Ident,
    generics: Generics,
    fields: FieldsUnnamed,
) -> Result<TokenStream> {
    let all = all_unnamed_fields(&fields);
    let context = context_unnamed_field(&fields);
    let contextuals = contextual_unnamed_fields(&fields);
    let (get, set) = fields_accessors(&ident, &context, &contextuals)?;

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let out = quote_spanned! {
        ident.span() =>
            impl #impl_generics formally::support::Contextual for #ident #ty_generics #where_clause {
                #[allow(unused_variables)]
                fn context(&self) -> formally::support::Context {
                    let #ident(#(#all),*) = self;
                    #get
                }

                #[allow(unused_variables)]
                fn set_context(&mut self, ctx: Context) {
                    let #ident(#(#all),*) = self;
                    #set
                }
            }
    };

    Ok(out)
}

fn derive_unit_struct(token: Token![struct]) -> Result<TokenStream> {
    Err(Error::new(
        token.span,
        "deriving Contextual for unit structs is not possible",
    ))
}

fn derive_enum(ident: Ident, generics: Generics, input: DataEnum) -> Result<TokenStream> {
    let mut gets = Vec::new();
    let mut sets = Vec::new();

    for variant in &input.variants {
        let vname = &variant.ident;
        match &variant.fields {
            Fields::Named(named) => {
                let all = all_named_fields(named);
                let context = context_named_field(named);
                let contextuals = contextual_named_fields(named);
                let (get, set) = fields_accessors(&ident, &context, &contextuals)?;

                gets.push(quote! {
                    #ident::#vname { #(#all),* } => {
                        #get
                    }
                });

                sets.push(quote! {
                    #ident::#vname { #(#all),* } => {
                        #set
                    }
                });
            }
            Fields::Unnamed(unnamed) => {
                let all = all_unnamed_fields(unnamed);
                let context = context_unnamed_field(unnamed);
                let contextuals = contextual_unnamed_fields(unnamed);
                let (get, set) = fields_accessors(&ident, &context, &contextuals)?;

                gets.push(quote! {
                    #ident::#vname(#(#all),*) => {
                        #get
                    }
                });

                sets.push(quote! {
                    #ident::#vname(#(#all),*) => {
                        #set
                    }
                });
            }
            Fields::Unit => {
                return Err(Error::new(
                    variant.ident.span(),
                    "deriving Contextual for enums with unit variants is not possible",
                ));
            }
        }
    }

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let out = quote_spanned! {
        ident.span() =>
            impl #impl_generics formally::support::Contextual for #ident #ty_generics #where_clause {
                #[allow(unused_variables)]
                fn context(&self) -> formally::support::Context {
                    match self {
                        #(#gets)*
                    }
                }

                #[allow(unused_variables)]
                fn set_context(&mut self, ctx: Context) {
                    match self {
                        #(#sets)*
                    }
                }
            }
    };

    Ok(out)
}

fn derive_union(item: DataUnion) -> Result<TokenStream> {
    Err(Error::new(
        item.union_token.span,
        "deriving Contextual for unions is not supported",
    ))
}
