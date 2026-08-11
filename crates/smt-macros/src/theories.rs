//
// ::formally - the open-source formal methods toolchain
//
// Copyright (c) 2026 Nicola Gigante
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
use quote::{ToTokens, quote};
use syn::{
    Meta, Token, braced, parenthesized,
    parse::{Parse, ParseStream},
    parse_quote,
    punctuated::Punctuated,
};

pub struct Root {
    theories: Vec<Attributed<Theory>>,
}

struct Theory {
    visibility: syn::Visibility,
    ident: syn::Ident,
    extended: ExtendedTheoriesClause,
    brace_token: syn::token::Brace,
    decls: Vec<Attributed<Decl>>,
}

#[derive(Default)]
struct ExtendedTheoriesClause {
    colon_token: Option<Token![:]>,
    extended: Punctuated<syn::Type, Token![,]>,
}

#[derive(Default, Clone)]
struct Attributed<T> {
    attrs: Vec<syn::Attribute>,
    node: T,
}

impl<T> Attributed<T> {
    fn replace<U>(&self, value: U) -> Attributed<U> {
        Attributed {
            attrs: self.attrs.clone(),
            node: value,
        }
    }
}

enum Decl {
    Sort(Sort),
    Const(Const),
    Function(Function),
}

#[derive(Clone)]
struct Sort {
    type_token: Token![type],
    ident: syn::Ident,
    semi_token: Token![;],
}

struct Const {
    const_token: Token![const],
    ident: syn::Ident,
    colon_token: Token![:],
    sort: syn::Expr,
    semi_token: Token![;],
}

enum Associativity {
    RightAssoc,
    LeftAssoc,
    Chainable,
    Pairwise,
}

struct Function {
    fn_token: Token![fn],
    ident: syn::Ident,
    params: ParamClause,
    paren_token: syn::token::Paren,
    args: Punctuated<syn::Expr, Token![,]>,
    arrow_token: Token![->],
    range: syn::Expr,
    semi_token: Token![;],
}

#[derive(Default)]
struct ParamClause {
    open_token: Option<Token![<]>,
    params: Punctuated<syn::Ident, Token![,]>,
    close_token: Option<Token![>]>,
}

impl Parse for Root {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut theories = Vec::new();
        while !input.is_empty() {
            theories.push(input.parse()?);
        }

        Ok(Root { theories })
    }
}

impl Parse for Theory {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        Ok(Theory {
            visibility: input.parse()?,
            ident: input.parse()?,
            extended: input.parse()?,
            brace_token: braced!(content in input),
            decls: {
                let mut decls = Vec::new();
                while !content.is_empty() {
                    decls.push(content.parse()?)
                }
                decls
            },
        })
    }
}

impl Parse for ExtendedTheoriesClause {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if !input.peek(Token![:]) {
            return Ok(ExtendedTheoriesClause::default());
        }

        Ok(ExtendedTheoriesClause {
            colon_token: input.parse()?,
            extended: Punctuated::parse_terminated(input)?,
        })
    }
}

impl<T: Parse> Parse for Attributed<T> {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Attributed {
            attrs: syn::Attribute::parse_outer(input)?,
            node: input.parse()?,
        })
    }
}

impl Parse for Sort {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Sort {
            type_token: input.parse()?,
            ident: input.parse()?,
            semi_token: input.parse()?,
        })
    }
}

impl Parse for Const {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Const {
            const_token: input.parse()?,
            ident: input.parse()?,
            colon_token: input.parse()?,
            sort: input.parse()?,
            semi_token: input.parse()?,
        })
    }
}

impl Parse for ParamClause {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if !input.peek(Token![<]) {
            return Ok(ParamClause::default());
        }

        Ok(ParamClause {
            open_token: input.parse()?,
            params: Punctuated::parse_separated_nonempty(input)?,
            close_token: input.parse()?,
        })
    }
}

impl Parse for Function {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let args;
        Ok(Function {
            fn_token: input.parse()?,
            ident: input.parse()?,
            params: input.parse()?,
            paren_token: parenthesized!(args in input),
            args: Punctuated::parse_terminated(&args)?,
            arrow_token: input.parse()?,
            range: input.parse()?,
            semi_token: input.parse()?,
        })
    }
}

impl Parse for Decl {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lh = input.lookahead1();
        if lh.peek(Token![type]) {
            input.parse().map(Decl::Sort)
        } else if lh.peek(Token![const]) {
            input.parse().map(Decl::Const)
        } else if lh.peek(Token![fn]) {
            input.parse().map(Decl::Function)
        } else {
            Err(lh.error())
        }
    }
}

fn get_name_from_attr(attr: &syn::Attribute) -> Option<&syn::Expr> {
    match &attr.meta {
        Meta::NameValue(syn::MetaNameValue { path, value, .. }) if path.is_ident("name") => {
            Some(value)
        }
        _ => None,
    }
}

fn get_name_from_attrs(attrs: &[syn::Attribute]) -> Option<&syn::Expr> {
    for attr in attrs {
        if let Some(name) = get_name_from_attr(attr) {
            return Some(name);
        }
    }

    None
}

impl ToTokens for Attributed<&Const> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ident = &self.node.ident;
        let sident = syn::LitStr::new(&ident.to_string(), ident.span());
        let name = get_name_from_attrs(&self.attrs).map(|name| quote!(name = #name));
        let sort = &self.node.sort;

        tokens.extend(quote! {
            pub static #ident : std::sync::LazyLock<formally::smt::Primitive> =
                std::sync::LazyLock::new(|| {
                    let mut name = #sident;
                    #name;

                    formally::smt::Primitive::new(
                        name,
                        std::iter::empty().collect(),
                        std::iter::empty().collect(),
                        #sort,
                        None
                    )
                });
        })
    }
}

enum Flag {
    LeftAssoc,
    RightAssoc,
    Chainable,
    Pairwise,
}

fn get_flag_from_attr(attr: &syn::Attribute) -> Option<Flag> {
    match &attr.meta {
        Meta::Path(path) if path.is_ident("left_assoc") => Some(Flag::LeftAssoc),
        Meta::Path(path) if path.is_ident("right_assoc") => Some(Flag::RightAssoc),
        Meta::Path(path) if path.is_ident("chainable") => Some(Flag::Chainable),
        Meta::Path(path) if path.is_ident("pairwise") => Some(Flag::Pairwise),
        _ => None,
    }
}

fn get_flag_from_attrs(attrs: &[syn::Attribute]) -> Option<Flag> {
    for attr in attrs {
        if let Some(flag) = get_flag_from_attr(attr) {
            return Some(flag);
        }
    }

    None
}

impl ToTokens for Flag {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Flag::LeftAssoc => tokens.extend(quote!(formally::smt::Associativity::LeftAssoc)),
            Flag::RightAssoc => tokens.extend(quote!(formally::smt::Associativity::RightAssoc)),
            Flag::Chainable => tokens.extend(quote!(formally::smt::Associativity::Chainable)),
            Flag::Pairwise => tokens.extend(quote!(formally::smt::Associativity::Pairwise)),
        }
    }
}

impl ToTokens for Attributed<&Function> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ident = &self.node.ident;
        let sident = syn::LitStr::new(&ident.to_string(), ident.span());
        let name = get_name_from_attrs(&self.attrs).map(|name| quote!(name = #name));
        let params = self.node.params.params.iter();
        let params2 = params.clone();
        let sparams = params
            .clone()
            .map(|p| syn::LitStr::new(&p.to_string(), p.span()));
        let args = self.node.args.iter();
        let range = &self.node.range;
        let flag = get_flag_from_attrs(&self.attrs)
            .map(|f| quote!(Some(#f)))
            .unwrap_or(quote!(None));

        tokens.extend(quote! {
            pub static #ident : std::sync::LazyLock<formally::smt::Primitive> =
                std::sync::LazyLock::new(|| {
                    let mut name = #sident;
                    #name;

                    #(
                        let #params = &formally::smt::Parameter::new(#sparams, formally::smt::Sort::sort(), None);
                    )*

                    formally::smt::Primitive::new(
                        name,
                        vec![#(#params2.clone()),*],
                        vec![#(formally::smt::Sort::from(#args.clone())),*] as Vec<formally::smt::Sort>,
                        formally::smt::Sort::from(#range.clone()),
                        #flag
                    )
                });
        })
    }
}

impl ToTokens for Attributed<&Sort> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.replace(&Function {
            fn_token: Default::default(),
            ident: self.node.ident.clone(),
            params: Default::default(),
            paren_token: Default::default(),
            args: Default::default(),
            arrow_token: Default::default(),
            range: parse_quote!(formally::smt::Sort::sort()),
            semi_token: Default::default(),
        })
        .to_tokens(tokens)
    }
}

impl ToTokens for Attributed<Decl> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match &self.node {
            Decl::Sort(sort) => self.replace(sort).to_tokens(tokens),
            Decl::Const(cnst) => self.replace(cnst).to_tokens(tokens),
            Decl::Function(func) => self.replace(func).to_tokens(tokens),
        }
    }
}

impl ToTokens for Attributed<Theory> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let attrs = &self.attrs;
        let vis = &self.node.visibility;
        let ident = &self.node.ident;
        let decls = &self.node.decls;
        let module = syn::Ident::new(&format!("{}__details", ident), ident.span());

        tokens.extend(quote! {
            #[derive(Default, Clone, Copy, Hash, PartialEq, Eq)]
            #[allow(nonstandard_style)]
            #[allow(clippy::style)]
            #(#attrs)*
            #vis struct #ident;

            #[allow(nonstandard_style)]
            #[allow(clippy::style)]
            #[allow(unused_assignments)]
            #[allow(unused_mut)]
            mod #module {
                use super::*;

                #(#decls)*
            }
        })
    }
}

impl ToTokens for Root {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let theories = &self.theories;

        tokens.extend(quote!(#(#theories)*))
    }
}
