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

use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, quote};
use syn::{
    Meta, Token, braced, bracketed, parenthesized,
    parse::{Parse, ParseStream},
    parse_quote,
    punctuated::Punctuated,
};

mod kw {
    syn::custom_keyword!(name);
    syn::custom_keyword!(theories);
    syn::custom_keyword!(requirements);
    syn::custom_keyword!(standard);
}

pub struct Root {
    attrs: Vec<syn::Attribute>,
    vis: syn::Visibility,
    ident: syn::Ident,
    theories: Punctuated<syn::Path, Token![,]>,
    reqs: Punctuated<syn::Type, Token![,]>,
    standard: syn::LitBool,
}

impl Parse for Root {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Root {
            attrs: syn::Attribute::parse_outer(input)?,
            vis: {
                input.parse::<kw::name>()?;
                input.parse::<Token![:]>()?;
                input.parse()?
            },
            ident: input.parse()?,
            theories: {
                input.parse::<Token![,]>()?;
                input.parse::<kw::theories>()?;
                input.parse::<Token![:]>()?;
                let theories;
                bracketed!(theories in input);
                Punctuated::parse_terminated(&theories)?
            },
            reqs: {
                input.parse::<Token![,]>()?;
                input.parse::<kw::requirements>()?;
                input.parse::<Token![:]>()?;
                let reqs;
                bracketed!(reqs in input);
                Punctuated::parse_terminated(&reqs)?
            },
            standard: {
                if !input.peek(Token![,]) {
                    syn::LitBool::new(false, Span::call_site())
                } else {
                    input.parse::<Token![,]>()?;
                    input.parse::<kw::standard>()?;
                    input.parse::<Token![:]>()?;
                    input.parse()?
                }
            },
        })
    }
}

impl ToTokens for Root {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let attrs = &self.attrs;
        let vis = &self.vis;
        let name = &self.ident;
        let theories: Vec<_> = self.theories.iter().collect();
        let reqs: Vec<_> = self.reqs.iter().collect();

        let combinedtheories = match theories.len() {
            1 => {
                let theory = theories[0].clone();
                quote! {
                    &#theory
                }
            }
            _ => {
                quote! {
                    static THEORY: std::sync::LazyLock<formally::smt::theories::CombinedTheory> =
                        std::sync::LazyLock::new(|| {
                            formally::smt::theories::CombinedTheory::new(&[#(&#theories),*])
                        });
                    &*THEORY
                }
            }
        };

        let standard = if self.standard.value {
            let staticname = syn::Ident::new(&format!("{name}LOGIC"), name.span());
            quote! {
                #[formally::smt::exports::distributed_slice(formally::smt::logics::STANDARD_LOGICS)]
                static #staticname:
                    &'static (dyn formally::smt::logics::Logic + Send + Sync) = &#name;
            }
        } else {
            quote!()
        };

        let atom = syn::Ident::new(&format!("{name}Atom"), name.span());

        let mut cases = Vec::new();
        let mut into = Vec::new();
        let mut try_from = Vec::new();
        for theory in &theories {
            let name = &theory.segments.last().unwrap().ident;

            cases.push(quote! {
                #[allow(nonstandard_style)]
                #name(<#theory as formally::smt::theories::TheoryEx>::Atom<'t>)
            });
            into.push(quote! {
                #atom::#name(atom) => atom.into()
            });
            try_from.push(quote! {
                match <<#theory as formally::smt::theories::TheoryEx>::Atom<'t> as TryFrom<&'t formally::smt::BoundAtom>>::try_from(atom) {
                    Ok(atom) => return Ok(#atom::#name(atom)),
                    Err(_) => {},
                }
            })
        }

        tokens.extend(quote! {
            #(#attrs)*
            ///
            /// Background theories:
            ///
            #(#[doc=concat!("* [", concat!(stringify!(#theories), "]"))])*
            ///
            /// Syntactic requirements:
            #(#[doc=concat!("* [", concat!(stringify!(#reqs), "]"))])*
            ///
            /// Declaration in the syntax of the [logic] macro:
            /// ```text
            /// logic! {
            #[doc=concat!("    name: ", concat!(stringify!(#name), ","))]
            #[doc=concat!("    theories: [ ", concat!(stringify!(#(#theories),*), " ],"))]
            #[doc=concat!("    requirements: [ ", concat!(stringify!(#(#reqs),*), " ],"))]
            /// }
            /// ```
            #vis struct #name;

            impl formally::smt::logics::Logic for #name {
                fn name(&self) -> &str {
                    stringify!(#name)
                }

                fn theory(&self) -> &dyn formally::smt::theories::Theory {
                    #combinedtheories
                }

                #[allow(unused_variables)]
                fn check_term(&self, term: &formally::smt::Term) -> formally::support::Result<()> {
                    #( #reqs::check_term(self, term)?; )*

                    Ok(())
                }

                #[allow(unused_variables)]
                fn check_function(&self, func: &formally::smt::UserFunction) -> formally::support::Result<()> {
                    #( #reqs::check_function(self, func)?; )*

                    match func {
                        formally::smt::UserFunction::Defined(def) => {
                            self.check_term(&def.body)
                        }
                        _ => Ok(()),
                    }
                }
            }

            #standard

            pub enum #atom<'t> {
                #(#cases),*
            }

            impl<'t> Into<formally::smt::BoundAtom> for #atom<'t> {
                fn into(self) -> formally::smt::BoundAtom {
                    match self {
                        #(#into),*
                    }
                }
            }

            impl<'t> TryFrom<&'t formally::smt::BoundAtom> for #atom<'t> {
                type Error = &'t formally::smt::BoundAtom;

                fn try_from(atom: &'t formally::smt::BoundAtom) -> Result<Self, Self::Error> {
                    #(#try_from)*

                    return Err(atom)
                }
            }

            impl formally::smt::logics::LogicEx for #name {
                type Atom<'t> = #atom<'t>;
            }
        })
    }
}
