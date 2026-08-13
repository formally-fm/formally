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

use transitive::Transitive;

use std::{
    collections::HashMap,
    fmt::{Debug, Formatter},
    iter::zip,
};

/// An argument in a parametric sort such as `Int` and `Real` in `(Array Int Real)`.
#[derive(Clone, Debug, Transitive)]
#[allow(clippy::duplicated_attributes)]
pub enum SortArgument {
    /// A constant argument (e.g., `32` in `(_ BitVec 32)`).
    Value(Constant),
    /// A sort argument (e.g., `Int` and `Real` in `(Array Int Real`).
    Sort(Sort),
}

impl SortArgument {
    /// Compare two sort arguments semantically (i.e. excluding source spans).
    pub fn equal(first: &SortArgument, second: &SortArgument) -> bool {
        match (first, second) {
            (SortArgument::Value(c1), SortArgument::Value(c2)) => match (c1, c2) {
                (Constant::Integer { value: v1, .. }, Constant::Integer { value: v2, .. }) => {
                    v1 == v2
                }
                (Constant::Rational { value: v1, .. }, Constant::Rational { value: v2, .. }) => {
                    v1 == v2
                }
                _ => false,
            },
            (SortArgument::Sort(s1), SortArgument::Sort(s2)) => Sort::equal(s1, s2),
            _ => false,
        }
    }

    pub(crate) fn matches_with(
        &self,
        instance: &SortArgument,
        matches: &mut HashMap<Binding, Sort>,
    ) -> bool {
        match (self, instance) {
            (SortArgument::Value(this), SortArgument::Value(inst)) => this == inst,
            (SortArgument::Sort(this), SortArgument::Sort(inst)) => {
                this.matches_with(inst, matches)
            }
            _ => false,
        }
    }
}

impl From<Constant> for SortArgument {
    fn from(value: Constant) -> Self {
        SortArgument::Value(value)
    }
}

impl<T: Into<Sort>> From<T> for SortArgument {
    fn from(value: T) -> Self {
        SortArgument::Sort(value.into())
    }
}

/// An SMT sort.
///
/// Sorts are the types of terms in the SMT lingo, and the [Sort] type is the result of [type
/// checking][Term::type_check()]. Sorts can be constructed directly starting from
/// [functions](Function) whose range is the special sort [Sort::sort()] (i.e., the sort of sorts).
/// They can also be first constructed as [terms][Term], e.g. by parsing SMT-LIBv2 source or with
/// the [term] macro, and then evaluated as sorts using [evaluate()](Sort::evaluate()).
///
/// Sort themselves have a structure similar to [bound atoms][BoundAtom], i.e. a [Function] applied
/// to arguments. The function must have the special sort [Sort::sort()]. Such functions are
/// sometimes called *sort constructors*. Moreover, arguments are
/// not arbitrary terms but [SortArgument] objects which can be either another sort or a constant.
/// This allows the representation of both SMT-LIBv2 sorts such as `(Array Int Real)` and `(_ BitVec
/// 32)`.
///
/// Notably, [Sort] does *not* implement [Hash](std::hash::Hash), [PartialEq] and [Eq]. This is
/// because comparing sorts is a semantic operation, so the canonical implementation of these traits
/// would include also the `span` field, which should instead be excluded from a semantic
/// comparison. However, excluding fields from [PartialEq] implementations is surprising and should
/// be avoided.
///
/// For this reason, semantic comparison, excluding spans, is implemented as the [Sort::equal]
/// associated function.
#[allow(clippy::duplicated_attributes)]
#[derive(Clone, Located, Locatable)]
pub struct Sort {
    /// The sort constructor that is being applied.
    pub head: Function,
    /// The sort's arguments.
    pub arguments: Vec<SortArgument>,
    /// The sort's source span.
    pub span: Option<Span>,
}

impl<T: Into<Function>> From<T> for Sort {
    fn from(value: T) -> Self {
        Sort {
            head: value.into(),
            arguments: Vec::new(),
            span: None,
        }
    }
}

impl Debug for Sort {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if Sort::equal(self, &Sort::sort()) {
            write!(f, "Sort::sort()")
        } else {
            f.debug_struct("Sort")
                .field("head", &self.head)
                .field("span", &self.span)
                .finish()
        }
    }
}

impl From<Sort> for Term {
    fn from(sort: Sort) -> Self {
        Term::from(TermKind::from(sort))
    }
}

impl From<Sort> for TermKind {
    /// Extract a [Term] representing the given sort.
    ///
    /// The resulting term can be turned into a sort again by [Sort::evaluate()].
    fn from(sort: Sort) -> Self {
        let arguments = sort
            .arguments
            .into_iter()
            .map(|arg| match arg {
                SortArgument::Value(c) => Term::from(c),
                SortArgument::Sort(s) => Term::from(s),
            })
            .collect();
        TermKind::Atom(Atom::Bound(BoundAtom {
            head: Reference {
                function: sort.head,
                span: None,
            },
            arguments,
            span: None,
        }))
    }
}

impl Sort {
    /// Alias for `term.type_check(ctx)` which provide a slightly better notation.
    pub fn of(term: &Term) -> Result<Sort> {
        term.type_check()
    }

    /// Compare two sorts semantically (i.e. excluding source spans).
    pub fn equal(first: &Sort, second: &Sort) -> bool {
        first.head == second.head
            && zip(&first.arguments, &second.arguments).all(|(f, s)| SortArgument::equal(f, s))
    }

    /// Evaluate a term as a sort.
    ///
    /// A sort such as `(Array Int Real)` can be constructed using the term macro,
    /// such as in `term!(Array Int Real)`, and then evaluated as a sort after
    /// [name resolution](Term::resolve()).
    ///
    /// The evaluation checks that all the functions used have range [Sort::sort()] and that the
    /// arguments are of the right kind (sort arguments or constants).
    pub fn evaluate(term: &Term) -> Result<Sort> {
        let sort = Sort::of(term)?;
        if !Sort::equal(&sort, &Sort::sort()) {
            error!(term.span(), "expected sort, found term of sort `{}`", sort);
            return Err(DiagnosticEmitted);
        }

        let TermKind::Atom(Atom::Bound(BoundAtom {
            head, arguments, ..
        })) = term.kind()
        else {
            internal!(term.span(), "sort term does not evaluate to a sort");
            return Err(DiagnosticEmitted);
        };

        let mut evaluated = Vec::new();
        for (sort, arg) in zip(head.function.domain(), arguments) {
            if Sort::equal(&sort, &Sort::sort()) {
                evaluated.push(SortArgument::Sort(Sort::evaluate(arg)?))
            } else {
                match arg.kind() {
                    TermKind::Constant(c) => evaluated.push(SortArgument::Value(c.clone())),
                    TermKind::Atom(_) => {
                        error!(arg.span(), "sort arguments must be constant terms");
                        return Err(DiagnosticEmitted);
                    }
                }
            }
        }

        Ok(Sort {
            head: head.function.clone(),
            arguments: evaluated,
            span: term.span(),
        })
    }

    pub(crate) fn matches_with(
        &self,
        argument: &Sort,
        matches: &mut HashMap<Binding, Sort>,
    ) -> bool {
        match (&self.head, &argument.head) {
            (Function::Binding(this), _) => {
                if let Some(this) = matches.get(this).cloned() {
                    this.head == argument.head
                        && this.arguments.len() == argument.arguments.len()
                        && zip(&this.arguments, &argument.arguments)
                            .all(|(this, arg)| this.matches_with(arg, matches))
                } else {
                    matches.insert(this.clone(), argument.clone());
                    true
                }
            }
            (Function::Primitive(this), Function::Primitive(inst)) => {
                this == inst
                    && self.arguments.len() == argument.arguments.len()
                    && zip(self.arguments.iter(), argument.arguments.iter())
                        .all(|(this, inst)| this.matches_with(inst, matches))
            }
            (Function::User(this), Function::User(inst)) => match (this, inst) {
                (UserFunction::Declared(this), UserFunction::Declared(inst)) => {
                    this == inst
                        && self.arguments.len() == argument.arguments.len()
                        && zip(self.arguments.iter(), argument.arguments.iter())
                            .all(|(this, inst)| this.matches_with(inst, matches))
                }
                (UserFunction::Defined(_), UserFunction::Defined(_)) => {
                    todo!() // we need to expand the definitions
                }
                _ => false,
            },
            _ => false,
        }
    }

    pub(crate) fn instantiate(&self, matches: &HashMap<Binding, Sort>) -> Result<Sort> {
        if let Function::Binding(bind) = &self.head {
            return matches.get(bind).cloned().ok_or_else(|| {
                internal!(
                    None,
                    "usage of unconstrained sort parameter: {}",
                    bind.name()
                );
                DiagnosticEmitted
            });
        }

        let mut arguments = Vec::new();
        for arg in &self.arguments {
            match arg {
                SortArgument::Value(term) => arguments.push(SortArgument::Value(term.clone())),
                SortArgument::Sort(sort) => {
                    arguments.push(SortArgument::Sort(sort.instantiate(matches)?))
                }
            }
        }

        Ok(Sort {
            head: self.head.clone(),
            arguments,
            span: self.span.clone(),
        })
    }
}
