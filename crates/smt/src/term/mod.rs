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

pub mod macros;

use crate::*;
use formally::support::*;

use derive_more::From;
use transitive::Transitive;

use std::{ops::Deref, sync::Arc};

pub use rug::{Integer, Rational};

/// A constant term.
///
/// Currently, only integer and rational constants are supported. The numbers are represented with
/// arbitrary precision using the [rug] crate, whose types [Integer] and [Rational] are re-exported
/// here for convenience.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
#[non_exhaustive]
pub enum Constant {
    Integer { value: Integer, span: Option<Span> },
    Rational { value: Rational, span: Option<Span> },
}

impl From<Integer> for Constant {
    fn from(value: Integer) -> Self {
        Constant::Integer { value, span: None }
    }
}

impl From<Rational> for Constant {
    fn from(value: Rational) -> Self {
        Constant::Rational { value, span: None }
    }
}

/// A [Function] associated with a source [Span].
///
/// [Reference] just wraps a [Function] together with a [Span] to keep track of there the mention
/// of the function appeared in an original source code. After [name resolution], this span
/// corresponds with the span of the [Identifier] that was replaced with this [Reference].
#[allow(clippy::duplicated_attributes)]
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Reference {
    pub function: Function,
    pub span: Option<Span>,
}

impl<T: Into<Function>> From<T> for Reference {
    fn from(value: T) -> Self {
        Reference {
            function: value.into(),
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
/// [unbound](UnboundAtom) atoms.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct BoundAtom {
    /// the function that is being applied.
    pub head: Reference,
    /// the atom's argument terms.
    pub arguments: Vec<Term>,
    /// the atom's source span.
    pub span: Option<Span>,
}

impl<T: Into<Reference>> From<T> for BoundAtom {
    fn from(value: T) -> Self {
        BoundAtom {
            head: value.into(),
            arguments: Vec::new(),
            span: None,
        }
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
pub struct UnboundAtom {
    /// the name of the function that is being applied.
    pub head: Identifier<'static>,
    /// the atom's argument terms.
    pub arguments: Vec<Term>,
    /// the atom's source span.
    pub span: Option<Span>,
}

impl<'a, T: Into<Identifier<'a>>> From<T> for UnboundAtom {
    fn from(value: T) -> Self {
        UnboundAtom {
            head: value.into().into_owned(),
            arguments: Vec::new(),
            span: None,
        }
    }
}

/// An atom term.
///
/// Atoms can be [bound](BoundAtom) or [unbound](UnboundAtom).
/// 1. bound atoms refer to a specific [Function] object and therefore can be type checked directly.
/// 2. unbound atoms contain only an [Identifier] in place of the applied function, so [name
///    resolution](Term::resolve) has to be performed on an unbound term before it can be type
///    checked.
#[derive(Debug, Clone, Hash, PartialEq, Eq, From, Located, Locatable)]
pub enum Atom {
    Bound(BoundAtom),
    Unbound(UnboundAtom),
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
#[derive(Debug, Clone, Hash, PartialEq, Eq, From, Located, Locatable, Transitive)]
#[allow(clippy::duplicated_attributes)]
#[transitive(from(Identifier<'_>, Atom))]
#[transitive(from(Function, Atom))]
#[transitive(from(Primitive, Function))]
#[transitive(from(Declared, Atom))]
#[transitive(from(Defined, Atom))]
#[non_exhaustive]
pub enum TermKind {
    /// A constant.
    Constant(Constant),
    /// An atom.
    Atom(Atom),
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
///
/// Comparison of [Term] objects is *structural*, so equality and hashing account for the syntactic
/// structure of the term (including the source spans). Keep this in mind when using terms as keys
/// for hash maps because lookup can become very expensive.
///
/// To use terms as hashing keys it is better to compare them *nominally*, i.e. in such a way that
/// objects with different memory addresses compare different even when structurally equal. To do
/// that, you can wrap [Term] into a [Nominal] type.
///
/// Example:
/// ```
/// # mod formally {
/// #    pub extern crate formally_support as support;
/// #    pub extern crate formally_smt as smt;
/// # }
/// # use formally::smt::*;
/// # use formally::support::*;
/// let ponens1 = term!(=> (and (=> p q) p) q);
/// let ponens2 = term!(=> (and (=> p q) p) q);
///
/// assert_eq!(ponens1, ponens2);
///
/// assert_ne!(Nominal::new(ponens1), Nominal::new(ponens2));
/// ```
#[allow(clippy::duplicated_attributes)]
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located)]
pub struct Term(Arc<TermKind>);

impl From<bool> for TermKind {
    fn from(value: bool) -> Self {
        if value {
            TermKind::from(theories::Core::True())
        } else {
            TermKind::from(theories::Core::False())
        }
    }
}

impl<T: Into<TermKind>> From<T> for Term {
    fn from(value: T) -> Self {
        Term(Arc::new(value.into()))
    }
}

impl<T: Into<Reference>> From<T> for Atom {
    fn from(value: T) -> Self {
        Atom::Bound(BoundAtom {
            head: value.into(),
            arguments: Vec::new(),
            span: None,
        })
    }
}

impl From<Identifier<'_>> for Atom {
    fn from(id: Identifier) -> Self {
        Atom::Unbound(UnboundAtom {
            head: id.into_owned(),
            arguments: Vec::new(),
            span: None,
        })
    }
}

impl Term {
    /// Get this term's [TermKind].
    pub fn kind(&self) -> &TermKind {
        &self.0
    }
}

impl Deref for Term {
    type Target = TermKind;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

