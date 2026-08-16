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

pub trait TypeCheck {
    fn type_check(&self) -> Result<Sort>;
}

impl TypeCheck for Term {
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
    /// pool](Context::cache()), so a second invocation on the same term is faster.
    ///
    /// As advised in the documentation of [Term], caching is done by hashing the terms *nominally*,
    /// so two terms that compare equal but point to [TermKind] objects with different memory
    /// addresses will not share the cached result.
    fn type_check(&self) -> Result<Sort> {
        let sort = match self.kind() {
            TermKind::Constant(cnst) => cnst.type_check()?,
            TermKind::Atom(atom) => atom.type_check()?,
        };

        Ok(sort)
    }
}

impl TypeCheck for TermKind {
    fn type_check(&self) -> Result<Sort> {
        let sort = match self {
            TermKind::Constant(cnst) => cnst.type_check()?,
            TermKind::Atom(atom) => atom.type_check()?,
        };

        Ok(sort)
    }
}

impl TypeCheck for Constant {
    fn type_check(&self) -> Result<Sort> {
        match self {
            Constant::Integer { .. } => Ok(theories::Ints::Int()),
            Constant::Rational { .. } => Ok(theories::Reals::Real()),
        }
    }
}

impl TypeCheck for BoundAtom {
    fn type_check(&self) -> Result<Sort> {
        let domain = self.domain();

        if domain.len() != self.arguments.len() {
            error!(
                self.head.span(),
                "applied {} arguments to a function of {} parameters",
                self.arguments.len(),
                domain.len(),
            );
            return Err(DiagnosticEmitted);
        }

        let mut matches = HashMap::new();
        for (sort, arg) in zip(domain, &self.arguments) {
            let argsort = Sort::of(arg)?;

            if !sort.matches_with(&argsort, &mut matches) {
                error!(
                    arg.span(),
                    "argument of sort `{}` given to parameter of sort `{}`", argsort, sort
                );
                return Err(DiagnosticEmitted);
            }
        }

        let range = self.head.function.range().instantiate(&matches)?;

        Ok(range)
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
                if *first == *second {
                    std::iter::repeat_n(first.clone(), self.arguments.len()).collect()
                } else {
                    domain
                }
            }
            _ => domain,
        }
    }
}

impl TypeCheck for UnboundAtom {
    fn type_check(&self) -> Result<Sort> {
        internal!(self.head.span(), "unresolved symbol `{}`", self.head);
        Err(DiagnosticEmitted)
    }
}

impl TypeCheck for Atom {
    fn type_check(&self) -> Result<Sort> {
        match self {
            Atom::Bound(bound) => bound.type_check(),
            Atom::Unbound(unbound) => unbound.type_check(),
        }
    }
}

impl TypeCheck for Declaration {
    /// Check the well-formedness of the sorts involved in the declaration.
    ///
    /// The returned [Declaration] is equal to `self`.
    fn type_check(&self) -> Result<Sort> {
        for sort in &self.domain {
            sort.type_check()?;
        }
        self.range.type_check()?;

        Ok(self.range.clone())
    }
}

impl TypeCheck for Sort {
    /// Check the well-formedness of the sort.
    fn type_check(&self) -> Result<Sort> {
        if *self.head.range() != Sort::sort() {
            error!(
                self.head.span(),
                "expected sort, found term of sort `{}`",
                self.head.range()
            );
        }

        for arg in &self.arguments {
            match arg {
                SortArgument::Value(_) => {}
                SortArgument::Sort(s) => {
                    s.type_check()?;
                }
            }
        }

        Ok(self.clone())
    }
}
