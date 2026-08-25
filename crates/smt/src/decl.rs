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
use std::ops::Deref;

use formally::support::*;

use derive_more::{Deref, From};
use transitive::Transitive;

use std::{
    fmt::{Debug, Formatter},
    sync::Arc,
};

// Wrapper over an Arc or a `'static` reference, used to declare static primitives in the
// theories macro.
#[derive(Clone, Hash, PartialEq, Eq)]
pub(crate) enum SArc<T: 'static> {
    Static(&'static T),
    Arc(Arc<T>),
}

impl<T: Debug> Debug for SArc<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", **self)
    }
}

impl<T: 'static> Deref for SArc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            SArc::Static(st) => st,
            SArc::Arc(arc) => arc,
        }
    }
}

/// Associativity attribute of a primitive function.
///
/// These correspond to the `:left-assoc`, `:right-assoc`, `:chainable` and `:pairwise`
/// annotations supported by SMT-LIBv2 theory declarations. They are mostly used to express
/// associativity and similar syntactic properties of functions such as binary arithmetic
/// operations, equality, etc.
///
/// See Section 3.7 "Theory Declarations" of the SMT-LIBv2
/// [specification manual](https://smt-lib.org/language.shtml).
///
/// These annotations look like syntactic properties, but in fact have nothing to do with the
/// parser. When parsing `(+ a b c d)`, the parser only sees a term applying function `+` to four
/// arguments. Then, the name resolver ([Env::resolve()]) and the type checker
/// ([Term::type_check()]) look for those attributes and understand that, even if `+` is declared as
/// a *binary* function, it can take more than two arguments in the way that the annotation
/// specifies.
///
/// See also the [theories!] macro to see how to specify these annotations when declaring theory
/// symbols.
#[derive(Copy, Clone, Debug)]
pub enum Associativity {
    /// Equivalent to the `:left-assoc` annotation.
    LeftAssoc,
    /// Equivalent to the `:right-assoc` annotation.
    RightAssoc,
    /// Equivalent to the `:chainable` annotation.
    Chainable,
    /// Equivalent to the `:pairwise` annotation.
    Pairwise,
}

/// A free variable.
///
/// [Variable] represents a free variable in a term that can be bound by `let` expressions,
/// quantified by `forall` or `exists` quantifiers, or bound to function parameters.
///
/// [Variable] objects can be created using the [Variable::new()] constructor or with the [var!] or
/// [vars!] macros.
///
/// For example:
/// ```
/// # mod formally {
/// #    pub extern crate formally_support as support;
/// #    pub extern crate formally_smt as smt;
/// # }
/// # use formally::{smt::*, support::*};
/// # fn main() -> Result<()> {
/// let config = Config::default();
/// let mut solver = Solver::new(&config)?;
///
/// solver.define(Definition::function("f", [var!(x Int)], sort!(Int), term!(* x 2)));
///
/// solver.require(term!(not (= (f 21) 42)))?;
///
/// assert_eq!(solver.check()?, Answer::No);
///
/// # Ok(())
/// # }
/// ```
///
/// The [Variable<S>] type is parametric in a [ToSort] type `S` used to represent the sort of the
/// variable, such as [Sort] itself or the result of the [sort!] macro. See the documentation of
/// [ToSort] for details.
///
/// Comparison of [Variable] objects is *nominal*, that is, equality and hashing operate on the
/// identity of the objects, not on their values. In other words, two [Variable] objects with
/// exactly the same fields (and in particular the same *name*) created by two different calls to
/// [Variable::new()] will compare *different* and have a possibly different hash. Moreover,
/// cloning a [Variable] object is a cheap operation and produces a second object which compares
/// *equal* to the first. Under the hood, this is the behavior of `Nominal<Arc<T>>` for some inner
/// type `T`, so we also refer to the [Nominal] type for details.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Located)]
pub struct Variable<S: ToSort = Sort>(Nominal<Arc<VariableData<S>>>);

#[derive(Clone, Debug, Located, Locatable)]
struct VariableData<S: ToSort> {
    pub name: Identifier<'static>,
    pub sort: S,
    pub span: Option<Span>,
}

impl<S: ToSort> Variable<S> {
    /// Create a new [Variable].
    pub fn new<'a>(name: impl Into<Identifier<'a>>, sort: S) -> Variable<S> {
        Variable(Nominal(Arc::new(VariableData {
            name: name.into().into_owned(),
            sort,
            span: None,
        })))
    }

    /// Get the variable's name.
    pub fn name(&self) -> &Identifier<'static> {
        &self.0.name
    }

    /// Get the variable's sort.
    pub fn sort(&self) -> &S {
        &self.0.sort
    }
}

impl<S: Clone + ToSort> Locatable for Variable<S> {
    type Located = Variable<S>;

    fn over(self, span: impl Into<Option<Span>>) -> Self::Located {
        Variable(Nominal(Arc::new((**self.0).clone().over(span.into()))))
    }
}

/// A primitive function (or constant, or sort).
///
/// [Primitive] represents a primitive symbol provided by a theory. As such it is usually not
/// created directly by users of the framework but indirectly by the [theories!] macro.
///
/// Comparison of [Primitive] objects is *nominal*, that is, equality and hashing operate on the
/// identity of the objects, not on their values. In other words, two [Primitive] objects with
/// exactly the same fields (and in particular the same *name*) created by two different invocations
/// of the [theory] macro will compare *different* and have a possibly different hash. Moreover,
/// cloning a [Primitive] object is a cheap operation and produces a second object which compares
/// *equal* to the first. Under the hood, this is the behavior of `Nominal<Arc<T>>` for some inner
/// type `T`, so we also refer to the [Nominal] type for details.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Primitive(pub(crate) Nominal<SArc<PrimitiveData>>);

#[derive(Clone, Debug)]
pub(crate) struct PrimitiveData {
    pub name: Identifier<'static>,
    pub parameters: Vec<Variable>,
    pub domain: Vec<Sort>,
    pub range: Sort,
    pub associativity: Option<Associativity>,
}

impl Located for Primitive {
    fn span(&self) -> Option<Span> {
        None
    }
}

impl Primitive {
    /// Create a new [Primitive].
    ///
    /// Using this method directly should very seldom be necessary, as the preferred way of
    /// introducing primitive symbols if through the [theories!] macro.
    pub fn new<'a>(
        name: impl Into<Identifier<'a>>,
        parameters: Vec<Variable>,
        domain: Vec<Sort>,
        range: Sort,
        associativity: Option<Associativity>,
    ) -> Primitive {
        Primitive(Nominal(SArc::Arc(Arc::new(PrimitiveData {
            name: name.into().into_owned(),
            parameters,
            domain,
            range,
            associativity,
        }))))
    }

    /// Get the name of the primitive function.
    pub fn name(&self) -> &Identifier<'static> {
        &self.0.name
    }

    /// Get the *type-level parameters* of the primitive function.
    ///
    /// Only primitive functions can be parametric and the parameters returned here are the
    /// ones that SMT-LIBv2 theory declarations introduce with the `par` keyword.
    ///
    /// These are *not* the sorts of the arguments of the function. For that, call
    /// [domain()](Primitive::domain()).
    pub fn parameters(&self) -> &[Variable] {
        &self.0.parameters
    }

    /// Get the domain of the primitive function, i.e. the sorts of its arguments.
    pub fn domain(&self) -> &[Sort] {
        &self.0.domain
    }

    /// Get the range of the primitive function, i.e. the sort of its return value.
    pub fn range(&self) -> &Sort {
        &self.0.range
    }

    /// Get the associativity annotation, if any, of the primitive function.
    ///
    /// See [Associativity] for details.
    pub fn associativity(&self) -> Option<Associativity> {
        self.0.associativity
    }
}

/// Specification for declarations of functions (and constants, and sorts).
///
/// [Declaration] objects are passed to the [Solver::declare()] method to declare entities in a
/// solver, by specifying all the attributes of such declarations. Then, the method returns a
/// [Declared] object which is an opaque shared reference to a specific [Declaration] object which
/// represents the actual entity the solver is keeping track of.
///
/// The [Declaration<D, R>] type is parametric in two [ToSort] types `D` and `R` used to represent
/// the sort of the domain and of the range of the function, respectively. These can be e.g.,
/// [Sort] itself or the result of the [sort!] macro. See the documentation of [ToSort] for details.
///
/// The fields are public and the type can be constructed freely, but some constructors are also
/// provided ([function()](Declaration::function), [constant()](Declaration::constant), and
/// [sort()](Declaration::sort)), for common cases.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Declaration<D: ToSort, R: ToSort> {
    /// The name of the declared function.
    pub name: Identifier<'static>,
    /// The domain of the declared function, i.e. the sorts of its arguments.
    pub domain: Vec<D>,
    /// The range of the declared function, i.e. its return type.
    pub range: R,
    /// The optional source span the declaration comes from.
    pub span: Option<Span>,
}

impl<D: ToSort, R: ToSort> Declaration<D, R> {
    /// Declare a function (or a constant, or a sort).
    ///
    /// This is the most general constructor. It is more convenient than directly constructing the
    /// [Declaration] struct because of implicit conversions of the arguments and the absence
    /// of the `span` argument which is put to `None` by default, since most of the time when
    /// using the API directly, declarations do not have a source span.
    ///
    /// If the declaration do have a span it can be set using [over()](Declaration::over()).
    ///
    /// In the following example we declare a function taking a integer argument and returning a
    /// real and we set it to a given span.
    /// ```
    /// # mod formally {
    /// #     pub extern crate formally_smt as smt;
    /// #     pub extern crate formally_support as support;
    /// # }
    /// # use formally::{smt::*, support::*};
    /// #
    /// # fn main() -> Result<()> {
    /// # let mut solver = Solver::new(&Config::new())?;
    /// solver.declare(Declaration::function("f", [sort!(Int)], sort!(Real)))?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn function<'a>(
        name: impl Into<Identifier<'a>>,
        domain: impl IntoIterator<Item = D>,
        range: R,
    ) -> Declaration<D, R> {
        Declaration {
            name: name.into().into_owned(),
            domain: domain.into_iter().collect(),
            range,
            span: None,
        }
    }
}

impl<D: ToSort> Declaration<D, Sort> {
    /// Declare a predicate (i.e. a function returning [Core::Bool()](theories::Core::Bool()).
    ///
    /// This is equivalent to `Declaration::function(name, domain, theories::Core::Bool())`.
    pub fn predicate<'a>(
        name: impl Into<Identifier<'a>>,
        domain: impl IntoIterator<Item = D>,
    ) -> Declaration<D, Sort> {
        Declaration::function(name, domain, theories::Core::Bool())
    }
}

impl<R: ToSort> Declaration<Sort, R> {
    /// Declare a constant (i.e. a function with no arguments).
    ///
    /// This is equivalent to `Declaration::function(name, Vec::<Sort>::new(), sort)`.
    pub fn constant<'a>(name: impl Into<Identifier<'a>>, sort: R) -> Declaration<Sort, R> {
        Declaration::function(name, Vec::<Sort>::new(), sort)
    }
}

impl Declaration<Sort, Sort> {
    /// Declare a sort (i.e. a constant of the special sort [Sort::sort()]).
    ///
    /// This is equivalent to `Declaration::constant(name, Sort::sort())`.
    pub fn sort<'a>(name: impl Into<Identifier<'a>>) -> Declaration<Sort, Sort> {
        Declaration::constant(name, Sort::sort())
    }

    /// Declare a Boolean constant (i.e. a constant of sort [Core::Bool()](theories::Core::Bool()).
    ///
    /// This is equivalent to `Declaration::constant(name, theories::Core::Bool())`.
    pub fn boolean<'a>(name: impl Into<Identifier<'a>>) -> Declaration<Sort, Sort> {
        Declaration::constant(name, theories::Core::Bool())
    }

    /// Declare an integer constant (i.e. a constant of sort [Ints::Int()](theories::Ints::Int()).
    ///
    /// This is equivalent to `Declaration::constant(name, theories::Ints::Int())`.
    pub fn integer<'a>(name: impl Into<Identifier<'a>>) -> Declaration<Sort, Sort> {
        Declaration::constant(name, theories::Ints::Int())
    }

    /// Declare a real constant (i.e. a constant of sort [Reals::Real()](theories::Reals::Real()).
    ///
    /// This is equivalent to `Declaration::constant(name, theories::Reals::Real())`.
    pub fn real<'a>(name: impl Into<Identifier<'a>>) -> Declaration<Sort, Sort> {
        Declaration::constant(name, theories::Reals::Real())
    }
}

/// Represent a specific function (or constant, or sort) declared in a [Solver].
///
/// [Declared] is an opaque shared reference to a [Declaration] declared in a [Solver].
/// The only way to obtain a [Declared] is through [Solver::declare()]. [Declared] derefs to the
/// underlying [Declaration] to immutably access its fields.
///
/// Comparison of [Declared] objects is *nominal*, that is, equality and hashing operate on the
/// identity of the objects, not on their values. In other words, two [Declared] objects with
/// exactly the same fields (and in particular the same *name*), created by two different calls to
/// [Solver::declare()] will compare *different* and have a possibly different hash. Moreover,
/// cloning a [Declared] object is a cheap operation and produces a second object which compares
/// *equal* to the first. Under the hood, this is the behavior of `Nominal<Arc<Declaration>>`, so we
/// also refer to the [Nominal] type for details.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Located, Deref)]
pub struct Declared(pub(crate) Nominal<Arc<Declaration<Sort, Sort>>>);

/// Specification for definitions of functions (and constants, and sorts).
///
/// [Definition] objects are passed to the [Solver::define()] method to define entities in a
/// solver, by specifying all the attributes of such definitions. Then, the method returns a
/// [Defined] object which is an opaque shared reference to a specific [Definition] object which
/// represents the actual entity the solver is keeping track of.
///
/// The [Definition<V, R, B>] type is parametric in two [ToSort] types `V` and `R` used to
/// represent the sort of the variables and of the range of the definition, respectively, and in
/// a [ToTerm] `B` type used to represent the term of the body of the definition. See the
/// documentation of [ToSort] and [ToTerm] for details.
///
/// The fields are public and the type can be constructed freely, but some constructors are also
/// provided ([function()](Definition::function), [constant()](Definition::constant), and
/// [sort()](Definition::sort)), for common cases.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Located, Locatable)]
pub struct Definition<V: ToSort, R: ToSort, B: ToTerm> {
    pub name: Identifier<'static>,
    pub domain: Vec<Variable<V>>,
    pub range: R,
    pub body: B,
    pub span: Option<Span>,
}

impl<V: ToSort, R: ToSort, B: ToTerm> Definition<V, R, B> {
    /// Define a function (or a constant, or a sort).
    ///
    /// This is the most general constructor. It is more convenient than directly constructing the
    /// [Definition] struct because of implicit conversions of the arguments and the absence
    /// of the `span` argument which is put to `None` by default, since most of the time when
    /// using the API directly, declarations do not have a source span.
    ///
    /// If the declaration do have a span it can be set using [over()](Definition::over()).
    ///
    /// The function parameters are created as objects of type [Variable] which are given to the
    /// `domain` field and freely used in the body.
    ///
    /// In the following example we define a function `mult-add` taking three real arguments,
    /// computing a *multiply-add* operation argument and returning it. Note that when defining
    /// the body with the `term!` macro, the parameters are in scope and can just be referred to by
    /// name (the same name given to the constructor of [Variable]).
    /// ```
    /// # mod formally {
    /// #    pub extern crate formally_smt as smt;
    /// #    pub extern crate formally_support as support;
    /// # }
    /// # use formally::{smt::{*, theories::*}, support::*};
    /// # fn main() -> Result<()> {
    /// # let mut solver = Solver::new(&Config::new().logic("NRA"))?;
    ///
    /// let a = var!(a Real);
    /// let b = var!(b Real);
    /// let c = var!(c Real);
    ///
    /// solver.define(
    ///     Definition::function("mult-add", [a, b, c], Reals::Real(), term!(+ (* a b) c))
    /// )?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn function<'a>(
        name: impl Into<Identifier<'a>>,
        domain: impl IntoIterator<Item = Variable<V>>,
        range: R,
        body: B,
    ) -> Definition<V, R, B> {
        Definition {
            name: name.into().into_owned(),
            domain: domain.into_iter().collect(),
            range,
            body,
            span: None,
        }
    }
}

impl<V: ToSort, B: ToTerm> Definition<V, Sort, B> {
    /// Define a predicate (i.e. a function returning [Core::Bool()](theories::Core::Bool()).
    ///
    /// This is equivalent to `Definition::function(name, domain, theories::Core::Bool(), body)`.
    pub fn predicate<'a>(
        name: impl Into<Identifier<'a>>,
        domain: impl IntoIterator<Item = Variable<V>>,
        body: B,
    ) -> Definition<V, Sort, B> {
        Definition::function(name, domain, theories::Core::Bool(), body)
    }

    /// Define a parametric sort (i.e. a function returning the special sort [Sort::sort()]).
    ///
    /// This is equivalent to `Definition::function(name, domain, Sort::sort(), body)`.
    pub fn sort<'a>(
        name: impl Into<Identifier<'a>>,
        domain: impl IntoIterator<Item = Variable<V>>,
        body: B,
    ) -> Definition<V, Sort, B> {
        Definition::function(name, domain, Sort::sort(), body)
    }
}

impl<R: ToSort, B: ToTerm> Definition<Sort, R, B> {
    /// Define a constant (i.e. a function with no arguments).
    ///
    /// This is equivalent to `Definition::function(name, [], sort, body)`.
    pub fn constant<'a>(
        name: impl Into<Identifier<'a>>,
        sort: R,
        body: B,
    ) -> Definition<Sort, R, B> {
        Definition::function(name, [], sort, body)
    }
}

impl<B: ToTerm> Definition<Sort, Sort, B> {
    /// Define a Boolean constant (i.e. a constant of sort [Core::Bool()](theories::Core::Bool()).
    ///
    /// This is equivalent to `Definition::constant(name, theories::Core::Bool(), value)`.
    pub fn boolean<'a>(name: impl Into<Identifier<'a>>, value: B) -> Definition<Sort, Sort, B> {
        Definition::constant(name, theories::Core::Bool(), value)
    }

    /// Define an integer constant (i.e. a constant of sort [Ints::Int()](theories::Ints::Int()).
    ///
    /// This is equivalent to `Definition::constant(name, theories::Ints::Int(), value)`.
    pub fn integer<'a>(name: impl Into<Identifier<'a>>, value: B) -> Definition<Sort, Sort, B> {
        Definition::constant(name, theories::Ints::Int(), value)
    }

    /// Define a real constant (i.e. a constant of sort [Reals::Real()](theories::Reals::Real()).
    ///
    /// This is equivalent to `Definition::constant(name, theories::Reals::Real(), value)`.
    pub fn real<'a>(name: impl Into<Identifier<'a>>, value: B) -> Definition<Sort, Sort, B> {
        Definition::constant(name, theories::Reals::Real(), value)
    }
}

/// Represent a specific function (or constant, or sort) defined in a [Solver].
///
/// [Defined] is an opaque shared reference to a [Definition] defined in a [Solver].
/// The only way to obtain a [Defined] is through [Solver::define()]. [Defined] derefs to the
/// underlying [Definition] to immutably access its fields.
///
/// Comparison of [Defined] objects is *nominal*, that is, equality and hashing operate on the
/// identity of the objects, not on their values. In other words, two [Defined] objects with
/// exactly the same fields (and in particular the same *name*) created by two different calls to
/// [Solver::define()] will compare *different* and have a possibly different hash. Moreover,
/// cloning a [Defined] object is a cheap operation and produces a second object which compares
/// *equal* to the first. Under the hood, this is the behavior of `Nominal<Arc<Definition>>`, so we
/// also refer to the [Nominal] type for details.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Located, Deref)]
pub struct Defined(pub(crate) Nominal<Arc<Definition<Sort, Sort, Term>>>);

/// A function.
///
/// The [Function] type represent any function usable to build terms.
///
/// A function can be a *user function*, i.e. a [UserFunction] object which in turn can be either
/// [Declared] or [Defined], a [Variable], or a [Primitive].
///
/// Some accessor methods are provided to get fields in common between the variants avoiding
/// redundant pattern matches.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Located, From, Transitive)]
#[allow(clippy::duplicated_attributes)]
#[transitive(from(Declared, UserFunction))]
#[transitive(from(Defined, UserFunction))]
pub enum Function {
    /// A variable.
    Variable(Variable),
    /// A primitive function declared by some theory.
    Primitive(Primitive),
    /// A user function, i.e. either [Declared] or [Defined].
    User(UserFunction),
}

impl Function {
    /// Get the name of the function.
    pub fn name(&self) -> &Identifier<'static> {
        match self {
            Function::Variable(var) => var.name(),
            Function::Primitive(prim) => prim.name(),
            Function::User(user) => user.name(),
        }
    }

    /// Get the *type-level parameters* of a function.
    ///
    /// Only primitive functions can be parametric and the parameters returned here are the
    /// ones that SMT-LIBv2 theory declarations introduce with the `par` keyword.
    ///
    /// These are *not* the sorts of the arguments of the function. For that, call
    /// [domain()](Function::domain()).
    pub fn parameters(&self) -> Vec<Sort> {
        match self {
            Function::Variable(_) => Vec::new(),
            Function::Primitive(prim) => {
                prim.parameters().iter().map(|p| p.sort().clone()).collect()
            }
            Function::User(_) => Vec::new(),
        }
    }

    /// Get the domain of the function, i.e. the sorts of its arguments.
    pub fn domain(&self) -> Vec<Sort> {
        match self {
            Function::Variable(_) => Vec::new(),
            Function::Primitive(prim) => prim.domain().to_vec(),
            Function::User(user) => user.domain(),
        }
    }

    /// Get the range of the function, i.e. the sort of its return value.
    pub fn range(&self) -> &Sort {
        match self {
            Function::Variable(var) => var.sort(),
            Function::Primitive(prim) => prim.range(),
            Function::User(user) => user.range(),
        }
    }
}

/// A *user function*, i.e. a function either declared or defined in some [Solver].
///
/// Some accessor methods are provided to get fields in common between the variants avoiding
/// redundant pattern matches.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Located, From)]
pub enum UserFunction {
    /// A declared function.
    Declared(Declared),
    /// A defined function.
    Defined(Defined),
}

impl UserFunction {
    /// Get the name of the function.
    pub fn name(&self) -> &Identifier<'static> {
        match self {
            UserFunction::Declared(decl) => &decl.name,
            UserFunction::Defined(def) => &def.name,
        }
    }

    /// Get the domain of the function, i.e. the sorts of its arguments.
    pub fn domain(&self) -> Vec<Sort> {
        match self {
            UserFunction::Declared(decl) => decl.domain.clone(),
            UserFunction::Defined(def) => def.domain.iter().map(|p| p.sort().clone()).collect(),
        }
    }

    /// Get the range of the function, i.e. the sort of its return value.
    pub fn range(&self) -> &Sort {
        match self {
            UserFunction::Declared(decl) => &decl.range,
            UserFunction::Defined(def) => &def.range,
        }
    }
}
