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

use derive_more::{Display, From};
use transitive::Transitive;

use std::{
    collections::HashMap,
    fmt::{Debug, Display, Formatter},
    iter::zip,
};

pub trait ToSort: Resolve + TypeCheck + TryInto<Sort, Error: Emit> {}

impl<T: Resolve + TypeCheck + TryInto<Sort, Error: Emit>> ToSort for T {}

#[derive(Clone, Copy)]
pub struct Infer;

impl Resolve for Infer {
    fn resolve(&self, _env: &Env, _pool: &dyn TermPool, _role: Role) -> Result<Self> {
        Ok(*self)
    }
}

impl TypeCheck for Infer {
    fn type_check(&self) -> Result<Sort> {
        internal!(None, "type checking of an inference place holder");
        Err(DiagnosticEmitted)
    }
}

impl TryFrom<Infer> for Sort {
    type Error = Diagnostic;

    fn try_from(_value: Infer) -> Result<Self, Diagnostic> {
        Err(Diagnostic::new(
            None,
            "type checking of an inference place holder".to_string(),
        ))
    }
}

/// An argument in a parametric sort such as `Int` and `Real` in `(Array Int Real)`.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Transitive)]
#[allow(clippy::duplicated_attributes)]
pub enum SortArgument {
    /// A constant argument (e.g., `32` in `(_ BitVec 32)`).
    Value(Constant),
    /// A sort argument (e.g., `Int` and `Real` in `(Array Int Real)`).
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
            (SortArgument::Sort(s1), SortArgument::Sort(s2)) => s1 == s2,
            _ => false,
        }
    }

    #[allow(clippy::mutable_key_type)]
    pub(crate) fn matches_with(
        &self,
        instance: &SortArgument,
        matches: &mut HashMap<Variable, Sort>,
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

#[derive(Debug, Clone, Hash, PartialEq, Eq, From, Transitive)]
#[allow(clippy::duplicated_attributes)]
#[transitive(from(Variable, Function))]
#[transitive(from(Primitive, Function))]
#[transitive(from(UserFunction, Function))]
#[transitive(from(Declared, UserFunction))]
#[transitive(from(Defined, UserFunction))]
pub enum SortHead {
    Bound(Function),
    Unbound(Identifier<'static>),
}

impl SortHead {
    pub fn name(&self) -> &Identifier<'static> {
        match self {
            SortHead::Bound(bound) => bound.name(),
            SortHead::Unbound(name) => name,
        }
    }
}

impl From<FunctionRef> for SortHead {
    fn from(funcref: FunctionRef) -> Self {
        match funcref {
            FunctionRef::Bound(bound) => SortHead::Bound(bound.function),
            FunctionRef::Unbound(unbound) => SortHead::Unbound(unbound.name),
        }
    }
}

impl From<SortHead> for FunctionRef {
    fn from(head: SortHead) -> Self {
        match head {
            SortHead::Bound(function) => FunctionRef::Bound(BoundRef {
                function,
                span: None,
            }),
            SortHead::Unbound(name) => FunctionRef::Unbound(UnboundRef { name, span: None }),
        }
    }
}

impl Display for SortHead {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SortHead::Bound(func) => write!(f, "{}", func.name()),
            SortHead::Unbound(name) => write!(f, "{name}"),
        }
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
#[allow(clippy::duplicated_attributes)]
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Sort {
    /// The sort constructor that is being applied.
    pub head: SortHead,
    /// The sort's arguments.
    pub arguments: Vec<SortArgument>,
}

impl<T: Into<Function>> From<T> for Sort {
    fn from(value: T) -> Self {
        Sort {
            head: SortHead::Bound(value.into()),
            arguments: Vec::new(),
        }
    }
}

impl From<Identifier<'_>> for Sort {
    fn from(value: Identifier<'_>) -> Self {
        Sort {
            head: SortHead::Unbound(value.into_owned()),
            arguments: Vec::new(),
        }
    }
}

impl Debug for Sort {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if *self == Sort::sort() {
            write!(f, "Sort::sort()")
        } else {
            f.debug_struct("Sort").field("head", &self.head).finish()
        }
    }
}

#[derive(Debug, Clone, Located, Display)]
#[display("sort term must be an atom")]
pub struct InvalidSortTerm {
    span: Option<Span>,
}

impl Diagnosable for InvalidSortTerm {}

impl TryFrom<Term> for Sort {
    type Error = InvalidSortTerm;

    fn try_from(term: Term) -> Result<Sort, InvalidSortTerm> {
        let TermKind::Atom(atom) = term.kind() else {
            return Err(InvalidSortTerm { span: term.span() });
        };

        let mut arguments = Vec::with_capacity(atom.arguments.len());
        for arg in &*atom.arguments {
            match arg.kind() {
                TermKind::Constant(c) => arguments.push(SortArgument::Value(c.clone())),
                _ => arguments.push(SortArgument::Sort(Sort::try_from(arg.clone())?)),
            }
        }

        let head = SortHead::from(atom.head.clone());

        Ok(Sort { head, arguments })
    }
}

impl Sort {
    /// Alias for `term.type_check(ctx)` which provide a better notation.
    pub fn of(term: &Term) -> Result<Sort> {
        term.type_check()
    }

    #[allow(clippy::mutable_key_type)]
    pub(crate) fn matches_with(
        &self,
        argument: &Sort,
        matches: &mut HashMap<Variable, Sort>,
    ) -> bool {
        let SortHead::Bound(func) = &self.head else {
            return false;
        };

        let SortHead::Bound(argfunc) = &argument.head else {
            return false;
        };

        match (&func, &argfunc) {
            (Function::Variable(this), _) => {
                if let Some(this) = matches.get(this).cloned() {
                    this.head == argument.head
                        && this.arguments.len() == argument.arguments.len()
                        && zip(&*this.arguments, &*argument.arguments)
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

    #[allow(clippy::mutable_key_type)]
    pub(crate) fn instantiate(&self, matches: &HashMap<Variable, Sort>) -> Result<Sort> {
        match &self.head {
            SortHead::Bound(func) if let Function::Variable(var) = &func => {
                return matches.get(var).cloned().ok_or_else(|| {
                    internal!(
                        None,
                        "usage of unconstrained sort parameter: {}",
                        var.name()
                    );
                    DiagnosticEmitted
                });
            }
            _ => {}
        }

        let mut arguments = Vec::with_capacity(self.arguments.len());
        for arg in &*self.arguments {
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
        })
    }
}
