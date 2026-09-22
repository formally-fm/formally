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

/// Trait for types that can type-check themselves.
///
/// Type checking is meant here as the process of computing the [Sort] associated to a given object.
/// The most prominent example of type-checkable type is [Term], but [Sort] as well needs type
/// checking.
pub trait TypeCheck {
    fn type_check(&self) -> Result<Sort>;
}

impl TypeCheck for Term {
    fn type_check(&self) -> Result<Sort> {
        if let Some(sort) = &*self.0.sort.lock().unwrap() {
            return Ok(sort.clone());
        }
        let sort = self.kind().type_check()?;
        *self.0.sort.lock().unwrap() = Some(sort.clone());

        Ok(sort)
    }
}

impl TypeCheck for TermKind {
    fn type_check(&self) -> Result<Sort> {
        let sort = match self {
            TermKind::Constant(cnst) => cnst.type_check()?,
            TermKind::Atom(atom) => atom.type_check()?,
            TermKind::Quantified(quant) => quant.type_check()?,
            TermKind::Let(let_) => let_.type_check()?,
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

impl BoundRef {
    fn type_check(&self, arguments: &[Term]) -> Result<Sort> {
        let domain = self.domain(arguments.len());

        if domain.len() != arguments.len() {
            error!(
                self.function.span(),
                "applied {} arguments to a function of {} parameters",
                arguments.len(),
                domain.len(),
            );
            return Err(DiagnosticEmitted);
        }

        #[allow(clippy::mutable_key_type)]
        let mut matches = HashMap::new();
        for (sort, arg) in zip(domain, arguments) {
            let argsort = Sort::of(arg)?;

            if !sort.matches_with(&argsort, &mut matches) {
                error!(
                    arg.span(),
                    "argument of sort `{}` given to parameter of sort `{}`", argsort, sort
                );
                return Err(DiagnosticEmitted);
            }
        }

        let range = self.function.range().instantiate(&matches)?;

        Ok(range)
    }
}

impl BoundRef {
    pub(crate) fn domain(&self, nargs: usize) -> Vec<Sort> {
        let domain = self.function.domain();

        let Function::Primitive(prim) = &self.function else {
            return domain;
        };

        match prim.domain() {
            [first, second, ..] if prim.associativity().is_some() => {
                if *first == *second {
                    std::iter::repeat_n(first.clone(), nargs).collect()
                } else {
                    domain
                }
            }
            _ => domain,
        }
    }
}

impl TypeCheck for Atom {
    fn type_check(&self) -> Result<Sort> {
        match &self.head {
            FunctionRef::Bound(bound) => bound.type_check(&self.arguments),
            FunctionRef::Unbound(_) => {
                internal!(
                    self.head.span(),
                    "unresolved symbol `{}` during type checking",
                    self.head
                );
                Err(DiagnosticEmitted)
            }
        }
    }
}

impl TypeCheck for Quantified {
    fn type_check(&self) -> Result<Sort> {
        self.body.type_check()
    }
}

impl TypeCheck for Let {
    fn type_check(&self) -> Result<Sort> {
        self.body.type_check()
    }
}

impl TypeCheck for Declared {
    fn type_check(&self) -> Result<Sort> {
        Ok(self.range.clone())
    }
}

impl TypeCheck for Defined {
    fn type_check(&self) -> Result<Sort> {
        Ok(self.range.clone())
    }
}

impl TypeCheck for Sort {
    fn type_check(&self) -> Result<Sort> {
        match &self.head {
            SortHead::Bound(f) => {
                for (param, arg) in zip(f.domain().iter(), self.arguments.iter()) {
                    let argsort = arg.type_check()?;
                    if *param != argsort {
                        error!(
                            None,
                            "unresolved symbol `{}` during type checking", self.head
                        );
                    }
                }
                Ok(Sort::sort())
            }
            SortHead::Unbound(_) => {
                internal!(
                    None,
                    "unresolved symbol `{}` during type checking",
                    self.head
                );
                Err(DiagnosticEmitted)
            }
        }
    }
}

impl TypeCheck for SortArgument {
    fn type_check(&self) -> Result<Sort> {
        match self {
            SortArgument::Value(_) => Ok(theories::Ints::Int()),
            SortArgument::Sort(s) => s.type_check(),
        }
    }
}
