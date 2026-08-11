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
use quote::ToTokens;
use syn::{
    Token, braced, parenthesized,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
};

pub struct Root {
    theories: Vec<Attributed<Theory>>,
}

struct Theory {
    visibility: syn::Visibility,
    name: syn::Ident,
    paren_token: syn::token::Brace,
    decls: Vec<Attributed<Decl>>,
}

struct Attributed<T> {
    attrs: Vec<syn::Attribute>,
    node: T,
}

enum Decl {
    Sort(Sort),
    Const(Const),
    Function(Function),
}

struct Sort {
    type_token: Token![type],
    name: syn::Ident,
    semi_token: Token![;],
}

struct Const {
    const_token: Token![const],
    name: syn::Ident,
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
    name: syn::Ident,
    params: ParamClause,
    paren_token: syn::token::Paren,
    args: Punctuated<syn::Expr, Token![,]>,
    arrow_token: Token![->],
    range: syn::Expr,
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
            name: input.parse()?,
            paren_token: braced!(content in input),
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

impl<T: Parse> Parse for Attributed<T> {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Attributed {
            attrs: input.call(syn::Attribute::parse_outer)?,
            node: input.parse()?,
        })
    }
}

impl Parse for Sort {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Sort {
            type_token: input.parse()?,
            name: input.parse()?,
            semi_token: input.parse()?,
        })
    }
}

impl Parse for Const {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Const {
            const_token: input.parse()?,
            name: input.parse()?,
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
            params: Punctuated::parse_terminated(input)?,
            close_token: input.parse()?,
        })
    }
}

impl Parse for Function {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let args;
        Ok(Function {
            fn_token: input.parse()?,
            name: input.parse()?,
            params: input.parse()?,
            paren_token: parenthesized!(args in input),
            args: Punctuated::parse_terminated(&args)?,
            arrow_token: input.parse()?,
            range: input.parse()?,
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

impl ToTokens for Root {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        todo!()
    }
}
