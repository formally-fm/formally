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

use crate::*;
use formally::support::*;

use std::{collections::HashMap, iter::zip};

struct TypeCheckCacheTag {}

impl CacheTag for TypeCheckCacheTag {
    type Key = Nominal<Term>;
    type Value = Sort;
}

impl Term {
    /// Deduce the sort of a term.
    ///
    /// Typing rules are straightforward:
    /// 1. constants have their own natural sort,
    /// 2. [bound atoms](BoundAtom) are checked to ensure their arguments match the function's
    ///    domain, and then their sort is just the function's range.
    ///
    /// This method is also aliased by [Sort::of()] which provides a clearer notation.
    ///
    /// Note that type checking terms containing [unbound atoms](UnboundAtom) is not possible,
    /// because typing information for unbound symbols is not available. In this case, the method
    /// emits an [internal error](internal). As a consequence, type checking is usually performed
    /// only after [name resolution](Term::resolve), unless the term is known to not have unbound
    /// atoms by construction. If knowing the sort of the term is not needed, but one only need to
    /// check the well-sortedness of the term, type checking and name resolution can be done
    /// together by calling [Term::validated()].
    ///
    /// The method takes a [Context] argument to cache its result into the context's [data
    /// pool](Context::cache()), so a second invocation on *the same object* is faster.
    ///
    /// As advised in the documentation of [Term], caching is done by hashing the terms *nominally*,
    /// so two terms that compare equal but point to [TermKind] objects with different memory
    /// addresses will not share the cached result.
    pub fn type_check(&self, ctx: Context) -> Result<Sort> {
        let nominal = Nominal::new(self.clone());
        let cache = ctx.cache::<TypeCheckCacheTag>();
        if let Some(sort) = cache.get(&nominal) {
            return Ok(sort.clone());
        }

        let sort = match self.kind() {
            TermKind::Constant(cnst) => cnst.type_check(ctx.clone())?,
            TermKind::Atom(atom) => atom.type_check(ctx.clone())?,
        };

        cache.insert(nominal, sort.clone());

        Ok(sort)
    }
}

impl Constant {
    /// Deduce the sort of a constant term.
    ///
    /// This function is part of the job of [Term::type_check()].
    pub fn type_check(&self, _ctx: Context) -> Result<Sort> {
        match self {
            Constant::Integer { .. } => Ok(theories::Ints::Int()),
            Constant::Rational { .. } => Ok(theories::Reals::Real()),
        }
    }
}

impl BoundAtom {
    /// Deduce the sort of a bound atom.
    ///
    /// This function is part of the job of [Term::type_check()].
    pub fn type_check(&self, ctx: Context) -> Result<Sort> {
        let domain = self.domain();

        if domain.len() != self.arguments.len() {
            error!(
                &ctx,
                self.head.span(),
                "applied {} arguments to a function of {} parameters",
                self.arguments.len(),
                domain.len(),
            );
            return Err(DiagnosticEmitted);
        }

        let mut matches = HashMap::new();
        for (sort, arg) in zip(domain, &self.arguments) {
            let argsort = Sort::of(arg, ctx.clone())?;

            if !sort.matches_with(&argsort, &mut matches) {
                error!(
                    &ctx,
                    arg.span(),
                    "argument of sort `{}` given to parameter of sort `{}`",
                    argsort,
                    sort
                );
                return Err(DiagnosticEmitted);
            }
        }

        let range = self.head.function.range().instantiate(&matches, ctx)?;

        Ok(range)
    }
}

impl UnboundAtom {
    fn type_check(&self, ctx: Context) -> Result<Sort> {
        internal!(&ctx, self.head.span(), "unresolved symbol `{}`", self.head);
        Err(DiagnosticEmitted)
    }
}

impl Atom {
    fn type_check(&self, ctx: Context) -> Result<Sort> {
        match self {
            Atom::Bound(bound) => bound.type_check(ctx),
            Atom::Unbound(unbound) => unbound.type_check(ctx),
        }
    }
}

impl BoundAtom {
    pub(crate) fn domain(&self) -> Vec<Sort> {
        let domain = self.head.function.domain();

        let Function::Primitive(prim) = &self.head.function else {
            return domain;
        };

        match prim.domain() {
            [first, second, ..] if prim.associativity().is_some() => {
                if Sort::equal(first, second) {
                    std::iter::repeat_n(first.clone(), self.arguments.len()).collect()
                } else {
                    domain
                }
            }
            _ => domain,
        }
    }
}
