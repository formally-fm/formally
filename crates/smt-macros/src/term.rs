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

use proc_macro2::{Punct, Spacing, TokenStream, TokenTree};

use syn::{
    Token, parenthesized,
    parse::{Parse, ParseStream, Result},
};

use quote::{ToTokens, TokenStreamExt, quote};

use std::fmt::{Display, Formatter};

#[derive(Clone)]
pub enum HeadName {
    Ident(syn::Ident),
    Punct(Vec<Punct>),
}

impl Display for HeadName {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            HeadName::Ident(ident) => write!(f, "{ident}"),
            HeadName::Punct(puncts) => {
                let mut out = String::new();
                for punct in puncts {
                    out.push_str(&punct.to_string());
                }
                write!(f, "{out}")
            }
        }
    }
}

#[derive(Clone)]
pub enum Head {
    Int(syn::LitInt),
    Real(syn::LitFloat),
    Unbound(HeadName),
    Bound(syn::Ident),
}

#[derive(Clone)]
pub enum Term {
    Atom(Atom),
    Quantified(Quantified),
}

#[derive(Clone)]
pub struct Sort {
    head: SortHead,
    args: Vec<SortArgument>,
}

#[derive(Clone)]
pub enum SortHead {
    Bound(syn::Ident),
    Unbound(syn::Ident),
}

#[derive(Clone)]
pub enum SortArgument {
    Integer(syn::LitInt),
    Sort(Sort),
}

#[derive(Clone)]
pub struct Atom {
    head: Head,
    args: Vec<TermArgument>,
}

#[derive(Clone, Copy)]
pub enum Quantifier {
    Forall,
    Exists,
}

#[derive(Clone)]
pub struct UnboundVariable {
    name: syn::Ident,
    sort: Sort,
}

#[derive(Clone)]
pub enum Variable {
    Bound(syn::Ident),
    Unbound(UnboundVariable),
}

#[derive(Clone)]
pub struct Quantified {
    quantifier: Quantifier,
    variables: Vec<Variable>,
    body: Box<Term>,
}

mod kw {
    syn::custom_keyword!(forall);
    syn::custom_keyword!(exists);
}

#[derive(Clone)]
pub enum TermArgument {
    Term(Term),
    Seq(syn::Ident),
}

fn peek_punct(input: ParseStream) -> bool {
    matches!(input.cursor().token_tree(), Some((TokenTree::Punct(punct), _)) if punct.as_char() != '#')
}

fn peek_atom(input: ParseStream) -> bool {
    input.peek(syn::Ident)
        || input.peek(Token![#])
        || peek_punct(input)
        || input.peek(syn::LitInt)
        || input.peek(syn::LitFloat)
}

fn parse_punct_sequence(input: ParseStream) -> Result<Vec<Punct>> {
    input.step(|cursor| {
        let mut tail = *cursor;
        let mut puncts = Vec::new();
        let mut found = false;
        while let Some((tt, next)) = tail.token_tree() {
            match &tt {
                TokenTree::Punct(punct) if punct.as_char() != '#' => {
                    found = true;
                    puncts.push(punct.clone());
                    tail = next;
                    if punct.spacing() == Spacing::Alone {
                        break;
                    }
                }
                _ => break,
            }
        }
        if found {
            Ok((puncts, tail))
        } else {
            Err(cursor.error("expected punctuation"))
        }
    })
}

impl Parse for HeadName {
    fn parse(input: ParseStream) -> Result<HeadName> {
        if input.peek(syn::Ident) {
            Ok(HeadName::Ident(input.parse()?))
        } else if peek_punct(input) {
            Ok(HeadName::Punct(parse_punct_sequence(input)?))
        } else {
            Err(syn::Error::new(
                input.span(),
                "expected SMT-LIBv2 identifier",
            ))
        }
    }
}

impl Parse for Head {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(syn::LitInt) {
            Ok(Head::Int(input.parse()?))
        } else if input.peek(syn::LitFloat) {
            Ok(Head::Real(input.parse()?))
        } else if input.peek(Token![#]) {
            input.parse::<Token![#]>()?;
            Ok(Head::Bound(input.parse()?))
        } else if input.peek(syn::Ident) || peek_punct(input) {
            Ok(Head::Unbound(input.parse()?))
        } else {
            Err(syn::Error::new(
                input.span(),
                "expected SMT-LIBv2 identifier or #expansion",
            ))
        }
    }
}

impl Parse for TermArgument {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![#]) && input.peek2(syn::token::Paren) {
            input.parse::<Token![#]>()?;
            let content;
            parenthesized!(content in input);
            content.parse::<Token![#]>()?;
            let ident = content.parse()?;
            input.parse::<Token![*]>()?;

            Ok(TermArgument::Seq(ident))
        } else if input.peek(syn::token::Paren) {
            let content;
            parenthesized!(content in input);
            Ok(TermArgument::Term(content.parse()?))
        } else {
            Ok(TermArgument::Term(Term::Atom(Atom {
                head: input.parse()?,
                args: Vec::new(),
            })))
        }
    }
}

impl Parse for Atom {
    fn parse(input: ParseStream) -> Result<Self> {
        let head = input.parse()?;
        let mut args = Vec::new();

        while !input.is_empty() {
            args.push(input.parse()?);
        }

        Ok(Atom { head, args })
    }
}

impl Parse for Quantifier {
    fn parse(input: ParseStream) -> Result<Self> {
        let lh = input.lookahead1();
        if lh.peek(kw::exists) {
            input.parse::<kw::exists>()?;
            Ok(Quantifier::Exists)
        } else if lh.peek(kw::forall) {
            input.parse::<kw::forall>()?;
            Ok(Quantifier::Forall)
        } else {
            Err(lh.error())
        }
    }
}

impl Parse for Variable {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![#]) {
            Ok(Variable::Bound(input.parse()?))
        } else {
            Ok(Variable::Unbound(input.parse()?))
        }
    }
}

impl Parse for UnboundVariable {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        parenthesized!(content in input);
        Ok(UnboundVariable {
            name: content.parse()?,
            sort: content.parse()?,
        })
    }
}

impl Parse for Quantified {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Quantified {
            quantifier: input.parse()?,
            variables: {
                let content;
                parenthesized!(content in input);
                let mut vars = Vec::new();
                while !content.is_empty() {
                    vars.push(content.parse()?)
                }
                vars
            },
            body: Box::new(input.parse()?),
        })
    }
}

impl Parse for Term {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(kw::forall) || input.peek(kw::exists) {
            Ok(Term::Quantified(input.parse()?))
        } else if peek_atom(input) {
            Ok(Term::Atom(input.parse()?))
        } else if input.peek(syn::token::Paren) {
            let content;
            parenthesized!(content in input);
            Ok(content.parse()?)
        } else {
            Err(syn::Error::new(input.span(), "expected SMT-LIBv2 term"))
        }
    }
}

impl Parse for SortHead {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![#]) {
            input.parse::<Token![#]>()?;
            Ok(SortHead::Bound(input.parse()?))
        } else {
            Ok(SortHead::Unbound(input.parse()?))
        }
    }
}

impl Parse for SortArgument {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(syn::LitInt) {
            Ok(SortArgument::Integer(input.parse()?))
        } else if input.peek(syn::token::Paren) {
            let content;
            parenthesized!(content in input);
            Ok(SortArgument::Sort(content.parse()?))
        } else {
            Ok(SortArgument::Sort(Sort {
                head: input.parse()?,
                args: Vec::new(),
            }))
        }
    }
}

impl Parse for Sort {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![_]) {
            input.parse::<Token![_]>()?;
        }
        Ok(Sort {
            head: input.parse()?,
            args: {
                let mut args = Vec::new();
                while !input.is_empty() {
                    args.push(input.parse()?)
                }
                args
            },
        })
    }
}

impl ToTokens for TermArgument {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            TermArgument::Term(term) => tokens.extend(quote! {
                formally::smt::macros::support::TermArgument::Term(#term)
            }),
            TermArgument::Seq(ident) => tokens.extend(quote! {
                formally::smt::macros::support::TermArgument::Seq(
                    (&#ident).into_iter().map(|t| {
                        formally::smt::macros::support::Term::Term(
                            formally::support::Loc::new(
                                formally::support::Nominal(t)
                            )
                        )
                    }).collect()
                )
            }),
        }
    }
}

impl ToTokens for Term {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Term::Atom(atom) => atom.to_tokens(tokens),
            Term::Quantified(quant) => quant.to_tokens(tokens),
        }
    }
}

impl ToTokens for Sort {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let head = &self.head;
        let args = &self.args;

        tokens.extend(quote! {
            formally::smt::Sort {
                head: #head,
                arguments: vec![#(#args),*]
            }
        })
    }
}

impl ToTokens for SortHead {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            SortHead::Bound(ident) => tokens.extend(quote! {
                formally::smt::SortHead::Bound(#ident.clone().into()),
            }),
            SortHead::Unbound(ident) => {
                let ident = ident.to_string();
                tokens.extend(quote! {
                    formally::smt::SortHead::Unbound(formally::support::Identifier::from(#ident))
                })
            }
        }
    }
}

impl ToTokens for SortArgument {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            SortArgument::Integer(lit) => tokens.extend(quote! {
               formally::smt::SortArgument::Value(
                    formally::smt::Constant::Integer { value: #lit, span: None }
                )
            }),
            SortArgument::Sort(sort) => tokens.extend(quote! {
                formally::smt::SortArgument::Sort(#sort)
            }),
        }
    }
}

impl ToTokens for Variable {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Variable::Bound(bound) => tokens.extend(quote! {
                formally::smt::macros::support::Variable::Bound(#bound)
            }),
            Variable::Unbound(unbound) => {
                let name = unbound.name.to_string();
                let sort = &unbound.sort;

                tokens.extend(quote! {
                    formally::smt::macros::support::Variable::Unbound(
                        formally::smt::macros::support::UnboundVariable {
                            name: std::borrow::Cow::Borrowed(#name),
                            sort: #sort
                        }
                    )
                })
            }
        }
    }
}

impl ToTokens for Quantified {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let quant = match self.quantifier {
            Quantifier::Forall => quote!(formally::smt::Quantifier::Forall),
            Quantifier::Exists => quote!(formally::smt::Quantifier::Exists),
        };
        let vars = &self.variables;
        let body = &*self.body;

        tokens.extend(quote! {
            formally::smt::macros::support::Term::Quantified(
                formally::smt::macros::support::Quantified {
                    quantifier: #quant,
                    variables: &[#(#vars),*],
                    body: &#body,
                    span: None
                }
            )
        })
    }
}

impl ToTokens for Atom {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match &self.head {
            Head::Int(lit) => tokens.append_all(quote! {
                formally::smt::macros::support::Term::Constant(
                    formally::smt::macros::support::Constant::Integer {
                        value: #lit,
                        span: None
                    }
                )
            }),
            Head::Real(lit) => {
                let lit = &lit.to_string();
                tokens.append_all(quote! {
                    formally::smt::Term::Constant(
                        formally::smt::Constant::Rational {
                            value: #lit,
                            span: None
                        }
                    )
                })
            }

            Head::Unbound(head) => {
                let head = head.to_string();
                let args = &self.args;
                tokens.append_all(quote! {
                    formally::smt::macros::support::Term::Atom(formally::smt::macros::support::Atom {
                        head: formally::smt::macros::support::AtomHead::Unbound(
                            formally::smt::macros::support::UnboundHead {
                                name: std::borrow::Cow::Borrowed(#head)
                            }
                        ),
                        arguments: &[#(#args),*],
                        span: None
                    })
                })
            }
            Head::Bound(head) => {
                let args = &self.args;
                if args.is_empty() {
                    tokens.append_all(quote! {
                        formally::smt::macros::support::Term::Term(
                            formally::support::Loc::new(
                                formally::support::Nominal(&#head)
                            )
                        )
                    })
                } else {
                    tokens.append_all(quote! {
                        formally::smt::macros::support::Term::Atom(formally::smt::macros::support::Atom {
                            head: formally::smt::macros::support::AtomHead::from((#head).clone()),
                            arguments: &[#(#args),*],
                            span: None
                        })
                    })
                }
            }
        }
    }
}
