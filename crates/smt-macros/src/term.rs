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
    Int(syn::LitInt),
    Real(syn::LitFloat),
    App { head: Head, args: Vec<TermArgument> },
}

#[derive(Clone)]
pub enum TermArgument {
    Term(Term),
    Seq(syn::Ident),
}

fn peek_punct(input: ParseStream) -> bool {
    matches!(input.cursor().token_tree(), Some((TokenTree::Punct(punct), _)) if punct.as_char() != '#')
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

impl Parse for Name {
    fn parse(input: ParseStream) -> Result<Name> {
        if input.peek(syn::Ident) {
            Ok(Name::Ident(input.parse()?))
        } else if peek_punct(input) {
            Ok(Name::Punct(parse_punct_sequence(input)?))
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
        if input.peek(Token![#]) {
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
        } else {
            Ok(TermArgument::Term(input.parse()?))
        }
    }
}

impl Parse for Term {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(syn::LitInt) {
            Ok(Term::Int(input.parse()?))
        } else if input.peek(syn::LitFloat) {
            Ok(Term::Real(input.parse()?))
        } else if input.peek(syn::Ident) || input.peek(Token![#]) || peek_punct(input) {
            let head = input.parse()?;
            let mut args = Vec::new();

            while !input.is_empty() {
                args.push(input.parse()?);
            }

            Ok(Term::App { head, args })
        } else if input.peek(syn::token::Paren) {
            let content;
            parenthesized!(content in input);
            Ok(content.parse()?)
        } else {
            Err(syn::Error::new(input.span(), "expected SMT-LIBv2 term"))
        }
    }
}

impl ToTokens for TermArgument {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            TermArgument::Term(term) => tokens.extend(quote! {
                formally::smt::support::TermArgument::Term(
                    formally::smt::support::Term::from((#term).clone())
                )
            }),
            TermArgument::Seq(ident) => tokens.extend(quote! {
                formally::smt::support::TermArgument::Seq(
                    (#ident).clone().into_iter().map(|t| formally::smt::support::Term::from(t)).collect()
                )
            }),
        }
    }
}

impl ToTokens for Term {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Term::Int(lit) => tokens.append_all(quote! {
                formally::smt::support::Term::Integer(
                    formally::smt::support::Constant::Integer {
                        value: #lit,
                        span: None
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
            Term::App { head, args } => match head {
                Head::Unbound(head) => {
                    let head = head.to_string();
                    tokens.append_all(quote! {
                        formally::smt::support::Term::Atom(formally::smt::support::Atom {
                            head: formally::smt::support::AtomHead::from(formally::support::Identifier::from(#head.to_string())),
                            arguments: &[#(#args),*],
                            span: None
                        })
                    })
                }
                Head::Bound(head) => {
                    if args.is_empty() {
                        tokens.append_all(quote! {
                            formally::smt::support::Term::from((#head).clone())
                        })
                    } else {
                        tokens.append_all(quote! {
                            formally::smt::support::Term::Atom(formally::smt::support::Atom {
                                head: formally::smt::support::AtomHead::from((#head).clone()),
                                arguments: &[#(#args),*],
                                span: None
                            })
                        })
                    }
                }
            },
        }
    }
}
