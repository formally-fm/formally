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

use derive_more::From;
use transitive::Transitive;

pub use rug::{Integer, Rational};
use std::fmt::Formatter;
use std::{
    fmt::Display,
    hash::{Hash, Hasher},
    sync::{Arc, Mutex},
};

/// A constant term.
///
/// Currently, only integer and rational constants are supported. The numbers are represented with
/// arbitrary precision using the [rug] crate, whose types [Integer] and [Rational] are re-exported
/// here for convenience.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
#[non_exhaustive]
pub enum Constant {
    Integer {
        value: Arc<Integer>,
        span: Option<Span>,
    },
    Rational {
        value: Arc<Rational>,
        span: Option<Span>,
    },
}

impl From<Integer> for Constant {
    fn from(value: Integer) -> Self {
        Constant::Integer {
            value: Arc::new(value),
            span: None,
        }
    }
}

impl From<Rational> for Constant {
    fn from(value: Rational) -> Self {
        Constant::Rational {
            value: Arc::new(value),
            span: None,
        }
    }
}

/// A *bound* atom.
///
/// A bound atom represents an expression of the form `(f arg1 arg2 ...)` where `f` is already given
/// as a specific [Function] object (inside a [Reference] to keep track of its source span).
///
/// Bound atoms can be [type checked](Term::type_check) directly (supposing their children can
/// recursively be type checked) because typing information is available. Note that this should
/// not usually be a concern because [Solver::declare()], [Solver::define()], and
/// [Solver::require()] already perform name resolution and type checking appropriately.
///
/// Terms can usually better be constructed with the [term] macro, which can build both bound and
/// [unbound](UnboundHead) atoms.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct BoundHead {
    /// the function that is being applied.
    pub function: Function,
    /// the atom's source span.
    pub span: Option<Span>,
}

impl From<Function> for BoundHead {
    fn from(function: Function) -> Self {
        BoundHead {
            function,
            span: None,
        }
    }
}

impl Display for BoundHead {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.function.name())
    }
}

/// An *unbound* atom.
///
/// An unbound atom represents an expression of the form `(f arg1 arg2 ...)` where `f` is given
/// only as an [Identifier].
///
/// Unbound atoms cannot be [type checked](Term::type_check) directly because the identifier
/// does not provide any typing information. [Name resolution](Term::resolve) must be peformed
/// before type checking, for this reason. Note that this should
/// not usually be a concern because [Solver::declare()], [Solver::define()], and
/// [Solver::require()] already perform name resolution and type checking appropriately.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct UnboundHead {
    /// the name of the function that is being applied.
    pub head: Identifier<'static>,
    /// the atom's source span.
    pub span: Option<Span>,
}

impl<'a, T: Into<Identifier<'a>>> From<T> for UnboundHead {
    fn from(value: T) -> Self {
        let ident = value.into();
        UnboundHead {
            span: ident.span(),
            head: ident.into_owned(),
        }
    }
}

impl Display for UnboundHead {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.head)
    }
}

/// An atom term.
///
/// Atoms can be [bound](BoundHead) or [unbound](UnboundHead).
/// 1. bound atoms refer to a specific [Function] object and therefore can be type checked directly.
/// 2. unbound atoms contain only an [Identifier] in place of the applied function, so [name
///    resolution](Term::resolve) has to be performed on an unbound term before it can be type
///    checked.
#[derive(Debug, Clone, Hash, PartialEq, Eq, From, Located, Locatable, Transitive)]
#[allow(clippy::duplicated_attributes)]
#[transitive(from(Identifier<'static>, UnboundHead))]
#[transitive(from(Function, BoundHead))]
#[transitive(from(Variable, Function))]
#[transitive(from(Primitive, Function))]
#[transitive(from(UserFunction, Function))]
#[transitive(from(Declared, UserFunction))]
#[transitive(from(Defined, UserFunction))]
pub enum AtomHead {
    Bound(BoundHead),
    Unbound(UnboundHead),
}

impl Display for AtomHead {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomHead::Bound(bound) => bound.fmt(f),
            AtomHead::Unbound(unbound) => unbound.fmt(f),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable, Transitive)]
#[allow(clippy::duplicated_attributes)]
#[transitive(from(UnboundHead, AtomHead))]
#[transitive(from(Identifier<'_>, UnboundHead))]
#[transitive(from(BoundHead, AtomHead))]
#[transitive(from(Function, BoundHead))]
#[transitive(from(Variable, Function))]
#[transitive(from(Primitive, Function))]
#[transitive(from(UserFunction, Function))]
#[transitive(from(Declared, UserFunction))]
#[transitive(from(Defined, UserFunction))]
pub struct Atom {
    pub head: AtomHead,
    pub arguments: Arc<[Term]>,
    pub span: Option<Span>,
}

impl From<AtomHead> for Atom {
    fn from(head: AtomHead) -> Self {
        Atom {
            head,
            arguments: Arc::default(),
            span: None,
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Quantifier {
    Forall,
    Exists,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Quantified {
    pub quantifier: Quantifier,
    pub variables: Arc<[Variable]>,
    pub body: Term,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Binding {
    pub variable: Variable,
    pub def: Term,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Let {
    pub bindings: Arc<[Binding]>,
    pub body: Term,
    pub span: Option<Span>,
}

/// The payload of [Term] objects.
///
/// The [TermKind] enum lists the possible kinds of terms supported by the framework. [Term] derefs
/// immutably to [TermKind], and a term's kind is also available through the [Term::kind()] method.
/// Terms can be constructed from [TermKind] using [Term::from()], although constructing terms
/// with the [term] macro is recommended.
///
/// As mentioned in the [overview](formally::smt), we differ from most SMT APIs in that we do not
/// offer multiple functions and/or types, one for each possible term node (addition, subtraction,
/// conjunction, etc.), but rather we have a single notion of [Atom] which is the application of a
/// [Function] to a list of argument terms. This allows maximum flexibility, while still keeping the
/// construction of terms easy thanks to the [term] macro.
///
/// As a result, *currently* [TermKind] only has two variants, one for [constants](Constant)
/// (currently only integer and rational numbers), and one for atoms. Variants will be added when
/// supporting further syntactic elements of SMT-LIBv2 such as *let bindings*, *quantifiers* and
/// *match expressions*.
#[derive(Debug, Clone, Hash, PartialEq, Eq, From, Located, Locatable)]
#[allow(clippy::duplicated_attributes)]
#[non_exhaustive]
pub enum TermKind {
    /// A constant.
    Constant(Constant),
    /// An atom.
    #[from(skip)]
    Atom(Atom),
    /// A quantified formula
    Quantified(Quantified),
    /// A `let` expression
    Let(Let),
}

impl<T: Into<Atom>> From<T> for TermKind {
    fn from(atom: T) -> Self {
        TermKind::Atom(atom.into())
    }
}

/// An SMT term.
///
/// [Term] objects represent SMT terms as used throughout the framework. The objects themselves are
/// shared references to [TermKind] objects which contain the actual data.
///
/// Terms are preferably created using the [term] macro. The internal structure is useful instead to
/// destructuring terms by pattern matching for syntactic manipulations.
///
/// Important operations on terms include *type checking* ([Term::type_check()] and equivalently
/// [Sort::of()]), and *name resolution* ([Term::resolve()]).
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Term(pub(crate) Nominal<Arc<TermInner>>);

#[derive(Debug)]
pub(crate) struct TermInner {
    pub(crate) kind: TermKind,
    pub(crate) sort: Mutex<Option<Sort>>,
}

impl Hash for TermInner {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state)
    }
}

impl PartialEq for TermInner {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Eq for TermInner {}

impl Located for Term {
    fn span(&self) -> Option<Span> {
        self.0.kind.span()
    }
}

impl From<bool> for TermKind {
    fn from(value: bool) -> Self {
        if value {
            TermKind::from(theories::Core::True())
        } else {
            TermKind::from(theories::Core::False())
        }
    }
}

impl Term {
    /// Get this term's [TermKind].
    pub fn kind(&self) -> &TermKind {
        &self.0.kind
    }
}
