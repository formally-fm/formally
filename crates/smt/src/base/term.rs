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
    /// An integer constant.
    Integer {
        value: Arc<Integer>,
        span: Option<Span>,
    },
    /// A rational constant.
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

/// A reference to a [Function] occurring at a given [Span].
///
/// This type is used as *head* of *bound atoms*, i.e. fully name-resolved atoms.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct BoundRef {
    /// the function that is being applied.
    pub function: Function,
    /// the atom's source span.
    pub span: Option<Span>,
}

impl From<Function> for BoundRef {
    fn from(function: Function) -> Self {
        BoundRef {
            function,
            span: None,
        }
    }
}

impl Display for BoundRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.function.name())
    }
}

/// A bound or unbound reference to a function.
#[derive(Debug, Clone, Hash, PartialEq, Eq, From, Located, Locatable, Transitive)]
#[allow(clippy::duplicated_attributes)]
#[transitive(from(Function, BoundRef))]
#[transitive(from(Variable, Function))]
#[transitive(from(Primitive, Function))]
#[transitive(from(UserFunction, Function))]
#[transitive(from(Declared, UserFunction))]
#[transitive(from(Defined, UserFunction))]
pub enum FunctionRef {
    /// A bound reference to a [Function]
    Bound(BoundRef),
    /// A reference to an unbound identifier
    Unbound(Identifier<'static>),
}

impl Display for FunctionRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            FunctionRef::Bound(bound) => bound.fmt(f),
            FunctionRef::Unbound(unbound) => unbound.fmt(f),
        }
    }
}

impl FunctionRef {
    pub fn name(&self) -> &Identifier<'static> {
        match self {
            FunctionRef::Bound(bound) => bound.function.name(),
            FunctionRef::Unbound(unbound) => unbound,
        }
    }
}

/// An atom term.
///
/// Atoms are applications of arguments to functions. These are the most common type of
/// [terms][Term], which include also references to *constants* (functions without arguments) and
/// *variables*.
///
/// Atoms can be *bound* or *unbound*:
/// 1. bound atoms, with [FunctionRef::Bound] as `head`, refer to a specific [Function] object and
///    therefore can be type checked directly.
/// 2. unbound atoms, with [FunctionRef::Unbound] as `head`, contain only an [Identifier] in place
///    of the applied function, so name resolution has to be performed on an unbound term before it
///    can be type checked.
///
/// Most methods in [Solver] are responsible of performing name resolution (and type checking) on
/// the terms they receive.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable, Transitive)]
#[allow(clippy::duplicated_attributes)]
#[transitive(from(Identifier<'static>, FunctionRef))]
#[transitive(from(BoundRef, FunctionRef))]
#[transitive(from(Function, BoundRef))]
#[transitive(from(Variable, Function))]
#[transitive(from(Primitive, Function))]
#[transitive(from(UserFunction, Function))]
#[transitive(from(Declared, UserFunction))]
#[transitive(from(Defined, UserFunction))]
pub struct Atom {
    /// The head of the atom, i.e., the [Function] being applied.
    pub head: FunctionRef,
    /// The arguments of the atom.
    pub arguments: Arc<[Term]>,
    /// The source span of this atom.
    pub span: Option<Span>,
}

impl From<FunctionRef> for Atom {
    fn from(head: FunctionRef) -> Self {
        Atom {
            head,
            arguments: Arc::default(),
            span: None,
        }
    }
}

/// Either the `exists` or `forall` quantifier.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Quantifier {
    Forall,
    Exists,
}

/// A quantified formula.
///
/// [Quantified] represents existentially or universally quantified formulas. The body must be of
/// sort [Core::Bool()](theories::Core::Bool()) for the term to be considered well-typed.
///
/// The [variables](Variable) can be used in the body freely.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Quantified {
    /// Which quantifier is used.
    pub quantifier: Quantifier,
    /// The quantified variables.
    pub variables: Arc<[Variable]>,
    /// The body of the quantified formula.
    pub body: Term,
    /// The source span of the formula.
    pub span: Option<Span>,
}

/// A binding of a variable to a term in a `let` expression.
///
/// The type is parameterized by a type `V: ToSort` representing the sorts of the variables and
/// a type `T: ToTerm` representing the defining term of the binding.
///
/// [Binding] is usually constructed using [Binding::new()] and given to [Solver::lookup_binding()]
/// to apply name resolution and type checking to its constituent parts.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Binding<V: ToSort = Sort, T: ToTerm = Term> {
    /// The variable
    pub variable: Variable<V>,
    pub def: T,
    pub span: Option<Span>,
}

impl<T: TypeCheck + ToTerm> Binding<Infer, T> {
    /// Construct a new [Binding] with a to-be-inferred sort.
    ///
    /// The result can be given to [Solver::lookup_binding()] to apply name resolution and type
    /// checking, to obtain a binding actually usable in a [Let] term.
    pub fn new(name: Identifier<'_>, def: T) -> Binding<Infer, T> {
        let namespan = name.span();
        Binding {
            variable: Variable::new(name, Infer).over(namespan),
            def,
            span: None,
        }
    }
}

/// A `let` expression.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Let {
    /// The variable bindings of the `let` expression
    pub bindings: Arc<[Binding]>,
    /// The body of the `let` expression
    pub body: Term,
    /// The source span of the term
    pub span: Option<Span>,
}

/// The payload of [Term] objects.
///
/// The [TermKind] enum lists the possible kinds of terms supported by the framework. A term's kind
/// is also available through the [Term::kind()] method. Terms can be constructed from [TermKind]
/// using a [TermPool], such as the one provided by [Solver::pool()].
///
/// As mentioned in the [overview](formally::smt), we differ from most SMT APIs in that we do not
/// offer multiple functions and/or types, one for each possible term node (addition, subtraction,
/// conjunction, etc.), but rather we have a single notion of [Atom] which is the application of a
/// [Function] to a list of argument terms. This allows maximum flexibility, while still keeping the
/// construction of terms easy thanks to the [term!] macro. This is why this enum has relatively few
/// variants.
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
/// Terms are uniqued and shared through the use of a [TermPool], usually indirectly by means of
/// a [Solver]. Constructing a [Term] directly is often not needed, because most methods that
/// would accept one accept instead generic instances of [ToTerm], which include the result of the
/// [term!] macro, which is the recommended way of constructing terms.
///
/// See the [ToTerm] trait for more informations about how to construct [Term] objects from [ToTerm]
/// instances.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Term(pub(crate) Nominal<Arc<TermInner>>);

#[derive(Debug)]
pub(crate) struct TermInner {
    pub(crate) kind: TermKind,
    pub(crate) sort: Mutex<Option<Sort>>,
    pub(crate) resolved: bool,
}

impl TermInner {
    pub(crate) fn new(kind: TermKind) -> TermInner {
        let resolved = match &kind {
            TermKind::Constant(_) => true,
            TermKind::Atom(atom) => {
                matches!(&atom.head, FunctionRef::Bound(_))
                    && atom.arguments.iter().all(Term::is_resolved)
            }
            TermKind::Quantified(quant) => quant.body.is_resolved(),
            TermKind::Let(let_) => let_.body.is_resolved(),
        };

        TermInner {
            kind,
            sort: Mutex::default(),
            resolved,
        }
    }
}

impl Term {
    pub fn is_resolved(&self) -> bool {
        self.0.resolved
    }
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

impl PartialEq<bool> for Term {
    fn eq(&self, other: &bool) -> bool {
        if let TermKind::Atom(atom) = self.kind()
            && let Atom { head, .. } = atom
            && let FunctionRef::Bound(bound) = head
            && let BoundRef { function, .. } = bound
            && let Function::Primitive(prim) = function
        {
            (*other && *prim == theories::Core::True())
                || (!*other && *prim == theories::Core::False())
        } else {
            false
        }
    }
}

impl PartialEq<Integer> for Term {
    fn eq(&self, other: &Integer) -> bool {
        if let TermKind::Constant(cnst) = self.kind()
            && let Constant::Integer { value, .. } = cnst
        {
            **value == *other
        } else {
            false
        }
    }
}

impl PartialEq<Rational> for Term {
    fn eq(&self, other: &Rational) -> bool {
        if let TermKind::Constant(cnst) = self.kind()
            && let Constant::Rational { value, .. } = cnst
        {
            **value == *other
        } else {
            false
        }
    }
}
