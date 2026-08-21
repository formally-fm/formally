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
    _brace_token: syn::token::Brace,
    decls: Vec<Attributed<Decl>>,
}

#[derive(Default)]
struct ExtendedTheoriesClause {
    _colon_token: Option<Token![:]>,
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
    _type_token: Token![type],
    ident: syn::Ident,
    paren: Option<syn::token::Paren>,
    params: Punctuated<SortParam, Token![,]>,
    _semi_token: Token![;],
}

#[derive(Clone)]
struct SortParam {
    name: syn::Ident,
    _colon_token: Token![:],
    sort: syn::Expr,
}

struct Const {
    _const_token: Token![const],
    ident: syn::Ident,
    _colon_token: Token![:],
    sort: syn::Expr,
    _semi_token: Token![;],
}

struct Function {
    _fn_token: Token![fn],
    ident: syn::Ident,
    params: ParamClause,
    _paren_token: syn::token::Paren,
    args: Punctuated<syn::Expr, Token![,]>,
    _arrow_token: Token![->],
    range: syn::Expr,
    _semi_token: Token![;],
}

#[derive(Default)]
struct ParamClause {
    open_token: Option<Token![<]>,
    params: Punctuated<syn::Ident, Token![,]>,
    _close_token: Option<Token![>]>,
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
            _brace_token: braced!(content in input),
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
            _colon_token: input.parse()?,
            extended: Punctuated::parse_separated_nonempty(input)?,
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

impl Parse for SortParam {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(SortParam {
            name: input.parse()?,
            _colon_token: input.parse()?,
            sort: input.parse()?,
        })
    }
}

impl Parse for Sort {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let params;
        Ok(Sort {
            _type_token: input.parse()?,
            ident: input.parse()?,
            paren: {
                let paren;
                let content;
                if input.peek(syn::token::Paren) {
                    paren = Some(parenthesized!(content in input));
                    params = Punctuated::parse_terminated(&content)?;
                } else {
                    paren = None;
                    params = Punctuated::new();
                }

                paren
            },
            params,
            _semi_token: input.parse()?,
        })
    }
}

impl Parse for Const {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Const {
            _const_token: input.parse()?,
            ident: input.parse()?,
            _colon_token: input.parse()?,
            sort: input.parse()?,
            _semi_token: input.parse()?,
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
            _close_token: input.parse()?,
        })
    }
}

impl Parse for Function {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let args;
        Ok(Function {
            _fn_token: input.parse()?,
            ident: input.parse()?,
            params: input.parse()?,
            _paren_token: parenthesized!(args in input),
            args: Punctuated::parse_terminated(&args)?,
            _arrow_token: input.parse()?,
            range: input.parse()?,
            _semi_token: input.parse()?,
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

fn const_static(cnst: Attributed<&Const>) -> TokenStream {
    let ident = &cnst.node.ident;
    let sident = syn::LitStr::new(&ident.to_string(), ident.span());
    let name = get_name_from_attrs(&cnst.attrs).map(|name| quote!(name = #name));
    let sort = &cnst.node.sort;

    quote! {
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

fn func_static(func: Attributed<&Function>) -> TokenStream {
    let ident = &func.node.ident;
    let sident = syn::LitStr::new(&ident.to_string(), ident.span());
    let name = get_name_from_attrs(&func.attrs).map(|name| quote!(name = #name));
    let params = func.node.params.params.iter();
    let params2 = params.clone();
    let sparams = params
        .clone()
        .map(|p| syn::LitStr::new(&p.to_string(), p.span()));
    let args = func.node.args.iter();
    let range = &func.node.range;
    let flag = get_flag_from_attrs(&func.attrs)
        .map(|f| quote!(Some(#f)))
        .unwrap_or(quote!(None));

    quote! {
        pub static #ident : std::sync::LazyLock<formally::smt::Primitive> =
            std::sync::LazyLock::new(|| {
                let mut name = #sident;
                #name;

                #(
                    let #params = &formally::smt::Variable::new(#sparams, formally::smt::Sort::sort(), None);
                )*

                formally::smt::Primitive::new(
                    name,
                    vec![#(#params2.clone()),*],
                    vec![#(formally::smt::Sort::from(#args.clone())),*] as Vec<formally::smt::Sort>,
                    formally::smt::Sort::from(#range.clone()),
                    #flag
                )
            });
    }
}

fn sort_static(sort: Attributed<&Sort>) -> TokenStream {
    func_static(sort.replace(&Function {
        _fn_token: Default::default(),
        ident: sort.node.ident.clone(),
        params: Default::default(),
        _paren_token: Default::default(),
        args: sort.node.params.iter().map(|p| p.sort.clone()).collect(),
        _arrow_token: Default::default(),
        range: parse_quote!(formally::smt::Sort::sort()),
        _semi_token: Default::default(),
    }))
}

impl ToTokens for Attributed<Decl> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let code = match &self.node {
            Decl::Sort(sort) => sort_static(self.replace(sort)),
            Decl::Const(cnst) => const_static(self.replace(cnst)),
            Decl::Function(func) => func_static(self.replace(func)),
        };
        tokens.extend(code)
    }
}

fn is_custom_attr(attr: &syn::Attribute) -> bool {
    get_name_from_attr(attr).is_some() || get_flag_from_attr(attr).is_some()
}

impl ToTokens for SortParam {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let name = &self.name;
        let sort = &self.sort;

        tokens.extend(quote!(#name: #sort))
    }
}

impl ToTokens for Attributed<&Sort> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let attrs = self.attrs.iter().filter(|a| is_custom_attr(a));
        let ident = &self.node.ident;
        let params = self
            .node
            .paren
            .map(|_| self.node.params.iter())
            .map(|p| quote!((#(#p),*)));

        tokens.extend(quote! {
            #(#attrs)*
            type #ident #params;
        })
    }
}

impl ToTokens for Attributed<&Const> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let attrs = self.attrs.iter().filter(|a| is_custom_attr(a));
        let ident = &self.node.ident;
        let sort = &self.node.sort;

        tokens.extend(quote! {
            #(#attrs)*
            const #ident: #sort;
        })
    }
}

impl ToTokens for Attributed<&Function> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let attrs = self.attrs.iter().filter(|a| is_custom_attr(a));
        let ident = &self.node.ident;
        let params = &self
            .node
            .params
            .open_token
            .map(|_| self.node.params.params.iter())
            .map(|p| quote!(<#(#p),*>));
        let args = self.node.args.iter();
        let range = &self.node.range;

        tokens.extend(quote! {
            #(#attrs)*
            fn #ident #params(#(#args),*) -> #range;
        })
    }
}

fn capitalize(ident: &syn::Ident) -> syn::Ident {
    let string = ident.to_string();
    if string.is_empty() {
        ident.clone()
    } else {
        let mut chars = string.chars();
        let upper = chars.next().unwrap().to_ascii_uppercase();
        let rest: String = chars.collect();
        syn::Ident::new(&format!("{upper}{rest}"), ident.span())
    }
}

impl ToTokens for Attributed<Theory> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let attrs = &self.attrs;
        let vis = &self.node.visibility;
        let theory = &self.node.ident;
        let decls = &self.node.decls;
        let extended: Vec<_> = self.node.extended.extended.iter().collect();
        let module = syn::Ident::new(&format!("{}__details", theory), theory.span());
        let extendoc = if !extended.is_empty() {
            quote! {
                ///
                /// This theory [extends](formally::smt::theory) the following other theories:
                #(#[doc=concat!("* [", concat!(stringify!(#extended), "]"))])*
            }
        } else {
            quote! {}
        };

        let mut sorts = Vec::new();
        let mut consts = Vec::new();
        let mut funcs = Vec::new();
        let mut sortnames = Vec::new();
        let mut constnames = Vec::new();
        let mut funcnames = Vec::new();

        for decl in &self.node.decls {
            match &decl.node {
                Decl::Sort(sort) => {
                    sorts.push(decl.replace(sort));
                    sortnames.push(&sort.ident)
                }
                Decl::Const(cnst) => {
                    consts.push(decl.replace(cnst));
                    constnames.push(&cnst.ident)
                }
                Decl::Function(func) => {
                    funcs.push(decl.replace(func));
                    funcnames.push(&func.ident)
                }
            }
        }

        let mut sortitems = Vec::new();
        for sort in &sorts {
            let attrs = &sort.attrs;
            let ident = &sort.node.ident;
            let params: Vec<_> = sort.node.params.iter().map(|p| &p.name).collect();

            sortitems.push(quote! {
                #[allow(nonstandard_style)]
                #[allow(clippy::style)]
                #(#attrs)*
                ///
                /// Declaration in the syntax of the [theory] macro:
                ///
                /// ```text
                #[doc=stringify!(#sort)]
                /// ```
                pub fn #ident(#(#params: &(impl Clone + Into<formally::smt::SortArgument>)),*) -> formally::smt::Sort {
                    formally::smt::Sort {
                        head: #module::#ident.clone().into(),
                        arguments: vec![#(#params.clone().into()),*]
                    }
                }
            })
        }

        let mut constitems = Vec::new();
        for cnst in &consts {
            let attrs = cnst.attrs.iter().filter(|a| !is_custom_attr(a));
            let ident = &cnst.node.ident;

            constitems.push(quote! {
                #[allow(nonstandard_style)]
                #[allow(clippy::style)]
                #(#attrs)*
                ///
                /// Declaration in the syntax of the [theory] macro:
                ///
                /// ```text
                #[doc=stringify!(#cnst)]
                /// ```
                pub fn #ident() -> formally::smt::Primitive {
                    #module::#ident.clone()
                }
            })
        }

        let mut funcitems = Vec::new();
        for func in &funcs {
            let attrs = func.attrs.iter().filter(|a| !is_custom_attr(a));
            let ident = &func.node.ident;

            funcitems.push(quote! {
                #[allow(nonstandard_style)]
                #[allow(clippy::style)]
                #(#attrs)*
                ///
                /// Declaration in the syntax of the [theory] macro:
                ///
                /// ```text
                #[doc=stringify!(#func)]
                /// ```
                pub fn #ident() -> formally::smt::Primitive {
                    #module::#ident.clone()
                }
            })
        }

        let atomenum = syn::Ident::new(&format!("{theory}Atom"), theory.span());

        let mut atom_cases = Vec::new();
        let mut atom_into = Vec::new();
        let mut atom_try_from = Vec::new();
        for cnst in &consts {
            let ident = &cnst.node.ident;
            let cap = capitalize(ident);

            atom_cases.push(quote!(#cap));

            atom_into.push(quote! {
                #atomenum::#cap => formally::smt::Atom {
                    head: #module::#ident.clone().into(),
                    arguments: std::sync::Arc::default(),
                    span: Some(formally::support::Span::Builtin)
                }
            });

            atom_try_from.push(quote! {
                else if let FunctionRef::Bound(BoundRef { function, .. }) = &atom.head
                    && *function == #module::#ident.clone().into()
                {
                    Ok(#atomenum::#cap)
                }
            })
        }
        for func in &funcs {
            let ident = &func.node.ident;
            let cap = capitalize(ident);
            let mut args = Vec::new();
            if get_flag_from_attrs(&func.attrs).is_some() {
                atom_cases.push(quote!(#cap(&'t [formally::smt::Term])));
                atom_into.push(quote! {
                    #atomenum::#cap(arguments) => formally::smt::Atom {
                        head: #module::#ident.clone().into(),
                        arguments: std::sync::Arc::from(arguments.to_vec().into_boxed_slice()),
                        span: Some(formally::support::Span::Builtin)
                    }
                });

                atom_try_from.push(quote! {
                    else if let FunctionRef::Bound(BoundRef { function, .. }) = &atom.head
                        && *function == #module::#ident.clone().into()
                    {
                        Ok(#atomenum::#cap(&*atom.arguments))
                    }
                })
            } else {
                let argslen = func.node.args.len();
                let mut argnames = Vec::new();
                let mut argsvec = Vec::new();
                for i in 0..argslen {
                    args.push(quote!(&'t formally::smt::Term));
                    argnames.push(syn::Ident::new(&format!("arg{i}"), Span::call_site()));
                    argsvec.push(quote!(&atom.arguments[#i]));
                }
                atom_cases.push(quote!(#cap(#(#args),*)));

                atom_into.push(quote! {
                    #atomenum::#cap(#(#argnames),*) => formally::smt::Atom {
                        head: #module::#ident.clone().into(),
                        arguments: std::sync::Arc::new([#(#argnames.clone()),*]),
                        span: Some(formally::support::Span::Builtin)
                    }
                });

                atom_try_from.push(quote! {
                    else if let FunctionRef::Bound(BoundRef { function, .. }) = &atom.head
                        && *function == #module::#ident.clone().into()
                    {
                        if atom.arguments.len() == #argslen {
                            Ok(#atomenum::#cap(#(#argsvec),*))
                        } else {
                            Err(atom)
                        }
                    }
                })
            }
        }

        let sortenum = syn::Ident::new(&format!("{theory}Sort"), theory.span());

        let mut hasparams = false;
        let mut sort_cases = Vec::new();
        let mut sort_into = Vec::new();
        let mut sort_try_from = Vec::new();
        for sort in &sorts {
            let ident = &sort.node.ident;
            let mut params = Vec::new();
            let mut paramnames = Vec::new();
            let mut paramsvec = Vec::new();
            let paramslen = sort.node.params.len();
            if paramslen > 0 {
                hasparams = true;
            }
            for i in 0..paramslen {
                params.push(quote!(&'t formally::smt::SortArgument));
                paramnames.push(sort.node.params[i].name.clone());
                paramsvec.push(quote!(&sort.arguments[#i]));
            }

            if params.is_empty() {
                sort_cases.push(quote!(#ident));
                sort_into.push(quote! {
                    #sortenum::#ident => formally::smt::Sort {
                        head: #module::#ident.clone().into(),
                        arguments: vec![]
                    }
                });
                sort_try_from.push(quote! {
                    else if sort.head == #module::#ident.clone().into() {
                        if sort.arguments.len() == 0 {
                            Ok(#sortenum::#ident)
                        } else {
                            Err(sort)
                        }
                    }
                })
            } else {
                sort_cases.push(quote!(#ident(#(#params),*)));
                sort_into.push(quote! {
                    #sortenum::#ident(#(#paramnames),*) => formally::smt::Sort {
                        head: #module::#ident.clone().into(),
                        arguments: vec![#(#paramnames.clone()),*]
                    }
                });
                sort_try_from.push(quote! {
                    else if sort.head == #module::#ident.clone().into() {
                        if sort.arguments.len() == #paramslen {
                            Ok(#sortenum::#ident(#(#paramsvec),*))
                        } else {
                            Err(sort)
                        }
                    }
                })
            }
        }

        let sort_lf = if hasparams { quote!(<'t>) } else { quote!() };

        tokens.extend(quote! {
            #[derive(Default, Clone, Copy, Hash, PartialEq, Eq)]
            #[allow(nonstandard_style)]
            #[allow(clippy::style)]
            #(#attrs)*
            #extendoc
            #vis struct #theory;

            #[allow(nonstandard_style)]
            #[allow(clippy::style)]
            #[allow(unused_assignments)]
            #[allow(unused_mut)]
            mod #module {
                use super::*;

                #(#decls)*

                pub static FUNCS: std::sync::LazyLock<formally::support::Scope<formally::smt::Function>> = std::sync::LazyLock::new(|| {
                    let mut scope = formally::support::Scope::new();

                    #( scope.merge(&formally::smt::theories::Theory::functions(&#extended)); )*

                    #( scope.add(&#module::#funcnames.name(), formally::smt::Function::from(#module::#funcnames.clone())); )*

                    #( scope.add(&#module::#constnames.name(), formally::smt::Function::from(#module::#constnames.clone())); )*

                    scope
                });

                pub static SORTS: std::sync::LazyLock<formally::support::Scope<formally::smt::Function>> = std::sync::LazyLock::new(|| {
                    let mut scope = formally::support::Scope::new();

                    #( scope.merge(&formally::smt::theories::Theory::functions(&#extended)); )*

                    #( scope.add(&#module::#sortnames.name(), formally::smt::Function::from(#module::#sortnames.clone())); )*

                    scope
                });
            }

            impl #theory {
                #(#sortitems)*

                #(#constitems)*

                #(#funcitems)*
            }

            impl formally::smt::theories::Theory for #theory {
                fn functions(&self) -> formally::support::Scope<formally::smt::Function> {
                    #module::FUNCS.clone()
                }

                fn sorts(&self) -> formally::support::Scope<formally::smt::Function> {
                    #module::SORTS.clone()
                }
            }

            #[allow(nonstandard_style)]
            pub enum #atomenum<'t> {
                #(#atom_cases),*
            }

            impl Into<formally::smt::Atom> for #atomenum<'_> {
                fn into(self) -> formally::smt::Atom {
                    match self {
                        #(#atom_into),*
                    }
                }
            }

            impl<'t> TryFrom<&'t formally::smt::Atom> for #atomenum<'t> {
                type Error = &'t formally::smt::Atom;

                fn try_from(atom: &'t formally::smt::Atom) -> Result<#atomenum<'t>, Self::Error> {
                    if false { unreachable!() }
                    #(#atom_try_from)* else {
                        Err(atom)
                    }
                }
            }

            #[allow(nonstandard_style)]
            pub enum #sortenum #sort_lf {
                #(#sort_cases),*
            }

            #[allow(non_snake_case)]
            impl #sort_lf Into<formally::smt::Sort> for #sortenum #sort_lf {
                fn into(self) -> formally::smt::Sort {
                    match self {
                        #(#sort_into),*
                    }
                }
            }

            impl<'t> TryFrom<&'t formally::smt::Sort> for #sortenum #sort_lf {
                type Error = &'t formally::smt::Sort;

                fn try_from(sort: &'t formally::smt::Sort) -> Result<#sortenum #sort_lf, Self::Error> {
                    if false { unreachable!() }
                    #(#sort_try_from)* else {
                        Err(sort)
                    }
                }
            }

            impl formally::smt::theories::TheoryEx for #theory {
                type Atom<'t> = #atomenum<'t>;
                type Sort<'t> = #sortenum #sort_lf;
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
