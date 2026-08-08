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
    parse::{Parse, ParseStream},
    token,
};

use quote::{ToTokens, TokenStreamExt, quote};

use std::fmt::{Display, Formatter};

#[derive(Clone)]
pub enum Name {
    Ident(syn::Ident),
    Punct(Vec<Punct>),
}

impl Display for Name {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Name::Ident(ident) => write!(f, "{ident}"),
            Name::Punct(puncts) => {
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
    Unbound(Name),
    Bound(syn::Ident),
}

#[derive(Clone)]
pub enum Term {
    Int(String),
    Real(String),
    Ref(syn::Ident),
    App { head: Head, args: Vec<Term> },
}

pub struct Root {
    pub head: Head,
    pub args: Vec<Term>,
}

impl Parse for Head {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lh = input.lookahead1();
        if lh.peek(syn::Ident) {
            Ok(Head::Unbound(Name::Ident(input.parse()?)))
        } else if let Ok(puncts) = parse_punct_sequence(input) {
            Ok(Head::Unbound(Name::Punct(puncts)))
        } else if lh.peek(Token![#]) {
            input.step(|cursor| {
                let (_sharp, tail) = cursor.token_tree().unwrap();

                match tail.token_tree() {
                    Some((TokenTree::Ident(ident), tail)) => Ok((Head::Bound(ident), tail)),
                    _ => Err(cursor.error("after a '#' we expect an identifier to expand")),
                }
            })
        } else {
            Err(lh.error())
        }
    }
}

impl Parse for Root {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let head = input.parse()?;
        let mut args = Vec::new();
        while !input.is_empty() {
            args.push(input.parse()?);
        }

        Ok(Root { head, args })
    }
}

fn peek_punct(input: ParseStream) -> bool {
    matches!(input.cursor().token_tree(), Some((TokenTree::Punct(punct), _)) if punct.as_char() != '#')
}

fn parse_punct_sequence(input: ParseStream) -> syn::Result<Vec<Punct>> {
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
            Err(cursor.error("punctuation not found"))
        }
    })
}

impl Parse for Term {
    fn parse(input: ParseStream) -> syn::Result<Term> {
        let lh = input.lookahead1();
        if lh.peek(syn::Ident) || peek_punct(input) {
            Ok(Term::App {
                head: input.parse()?,
                args: Vec::new(),
            })
        } else if lh.peek(syn::LitInt) {
            let lit: syn::LitInt = input.parse()?;
            Ok(Term::Int(lit.base10_digits().to_string()))
        } else if lh.peek(syn::LitFloat) {
            let lit: syn::LitFloat = input.parse()?;
            Ok(Term::Real(lit.base10_digits().to_string()))
        } else if lh.peek(Token![#]) {
            input.step(|cursor| {
                let (_sharp, tail) = cursor.token_tree().unwrap();

                match tail.token_tree() {
                    Some((TokenTree::Ident(ident), tail)) => Ok((Term::Ref(ident), tail)),
                    _ => Err(cursor.error("after a '#' we expect an identifier to expand")),
                }
            })
        } else if lh.peek(token::Paren) {
            let sexpr;
            parenthesized!(sexpr in input);
            let head = sexpr.parse()?;
            let mut args = Vec::new();
            while !sexpr.is_empty() {
                args.push(sexpr.parse()?)
            }

            Ok(Term::App { head, args })
        } else {
            Err(lh.error())
        }
    }
}

impl ToTokens for Root {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append_all(quote!(& mut));
        Term::App {
            head: self.head.clone(),
            args: self.args.clone(),
        }
        .to_tokens(tokens);
    }
}

impl ToTokens for Term {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Term::Int(lit) => tokens.append_all(quote! {
                formally::smt::macros::Term::Integer(
                    formally::smt::macros::Constant::Integer {
                        value: #lit
                    }
                )
            }),
            Term::Real(lit) => tokens.append_all(quote! {
                formally::smt::Term::Constant(
                    formally::smt::Constant::Rational {
                        value: formally::smt::Rational::from_str_radix(#lit, 10).unwrap(),
                        span: None
                    }
                )
            }),
            Term::Ref(ident) => tokens.append_all(quote! {
                #ident.clone().into()
            }),
            Term::App { head, args } => match head {
                Head::Unbound(head) => {
                    let head = head.to_string();
                    tokens.append_all(quote! {
                        formally::smt::macros::Term::Atom(formally::smt::macros::Atom {
                            head: formally::smt::macros::AtomHead::from(formally::support::Identifier::from(#head.to_string())),
                            arguments: &[#(#args),*]
                        })
                    })
                }
                Head::Bound(head) => tokens.append_all(quote! {
                    formally::smt::macros::Term::Atom(formally::smt::macros::Atom {
                        head: formally::smt::macros::AtomHead::from((#head).clone()),
                        arguments: &[#(#args),*]
                    })
                }),
            },
        }
    }
}
