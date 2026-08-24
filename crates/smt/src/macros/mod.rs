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

pub mod support;

/// Declare an SMT-LIBv2 logic.
///
/// This macro helps with the proper declaration of types implementing the
/// [Logic](crate::logics::Logic) trait. Logic types obtained by this macro are unit structs (e.g.
/// declared as `pub struct LIA;`, and therefore instantiated as `LIA`, not as `LIA {}`) providing a
/// suitable implementation of the trait.
///
/// A logic combines a set of theories and a set of *requirements*, which are types implementing
/// [LogicRequirement](crate::logics::requirements::LogicRequirement). Both are specified as
/// follows.
///
/// Let us look at the concrete example of the declaration of the [QF_LIA](crate::logics::QF_LIA)
/// logic.
///
/// ```text
/// logic! {
///     /// Quantifier-Free Linear Integer Arithmetic.
///     name: pub QF_LIA,
///     theories: [ Core, Ints ],
///     requirements: [ Linear, QuantifierFree, NoUF ]
/// }
/// ```
///
/// We can observe a few details in this declaration:
/// 1. The `name:` parameter specifies the name of the logic, which is both the Rust name of the
///    corresponding type, and the name to be used as a string when setting the
///    [logic](crate::Config::logic) field of [Config](crate::Config) when instantiating a
///    [Solver](crate::Solver).
/// 2. The `pub` keyword before the name is the visibility specifier that will be attached to the
///    declared type (it can be absent for private types, or `pub`, `pub(crate)`, etc.).
/// 3. An optional *doc comment* can be placed above the `name:` parameter and will document the
///    resulting type. The documentation of the type will contain automatically the list of theories
///    and requirements (see how the above example is rendered in the documentation of
///    [QF_LIA](crate::logics::QF_LIA)).
/// 4. The `theories:` parameter accepts a comma-separated list of theories enclosed in brackets.
///    The names specified here are paths of any type currently in scope implementing the
///    [Theory](crate::theories::Theory) trait (usually declared with the
///    [theories!](crate::theories!) macro).
/// 5. The `requirements:` parameter accepts a comma-separated list of requirements enclosed in
///    brackets. The names specified here are paths of any type currently in scope implementing the
///    [LogicRequirement](crate::logics::requirements::LogicRequirement) trait.
///
/// Standard SMT-LIBv2 theories are declared in the [theories](crate::theories) module and some
/// logic requirements commonly needed in standard SMT-LIBv2 logics are declared in the
/// [logics::requirements](crate::logics::requirements) module.
#[macro_export]
macro_rules! logic {
    ($($tokens:tt)*) => {$crate::macros::proc::logic!{$($tokens)*}};
}

/// Declare new SMT-LIBv2 theories.
///
/// This macro automates the process of defining types suitably implementing the
/// [Theory](smt::theories::Theory) trait. It allows one to specify:
/// - the name of the new theory
/// - possibly other theories to inherit symbols from
/// - sorts, constants, and function symbols provided by the theory
///
/// ## How to declare a new theory
///
/// Let us start, as an example, with the declaration of the [Core](crate::theories::Core)
/// theory.
///
/// ```ignore
/// # mod formally {
/// #   pub extern crate formally_support as support;
/// #   pub extern crate formally_smt as smt;
/// # }
/// # use formally::smt::theories;
/// theories! {
///     /// The core SMT-LIBv2 theory, with basic Boolean connectives.
///     ///
///     /// See [the official specification](https://smt-lib.org/theories-Core.shtml).
///     pub Core {
///         /// The sort of Boolean terms.
///         type Bool;
///
///         /// The true constant.
///         const True: Core::Bool();
///
///         /// The false constant.
///         const False: Core::Bool();
///
///         /// Logical negation.
///         fn not(Core::Bool()) -> Core::Bool();
///
///         /// Logical implication.
///         #[name = "=>"]
///         #[right_assoc]
///         fn implies(Core::Bool(), Core::Bool()) -> Core::Bool();
///
///         /// Logical conjunction.
///         #[left_assoc]
///         fn and(Core::Bool(), Core::Bool()) -> Core::Bool();
///
///         /// Logical disjunction.
///         #[left_assoc]
///         fn or(Core::Bool(), Core::Bool()) -> Core::Bool();
///
///         /// Logical exclusive disjunction.
///         #[left_assoc]
///         fn xor(Core::Bool(), Core::Bool()) -> Core::Bool();
///
///         /// Equality.
///         #[name = "="]
///         #[chainable]
///         fn equals<A>(A, A) -> Core::Bool();
///
///         /// Disequality.
///         #[pairwise]
///         fn distinct<A>(A, A) -> Core::Bool();
///
///         /// If-then-else choice construct.
///         fn ite<A>(Core::Bool(), A, A) -> A;
///     }
/// }
/// # fn main() { }
/// ```
///
/// There are a few elements to dissect in this declaration:
/// 1. `pub Core` specifies the name of the theory and the visibility of the resulting Rust type.
/// 2. `type Bool;` declares the `Bool` sort provided by the theory
/// 3. `const` declarations declare constants provided by the theory
/// 4. `fn` declarations declare functions provided by the theory
/// 5. the *doc comment* above the theory declaration and above any of the inner declarations are
///    used to document the resulting Rust code. The documentation of each item will include also
///    its verbatim definition for reference (see the result in the documentation of
///    [Core](crate::theories::Core)).
///
/// ### How to declare sorts
///
/// The `type` declarations describe the sorts provided by the theory.
/// In the above example, we only declare a single sort, `Bool`, which simple, i.e., non-parametric.
///
/// A parametric sort is specified instead by appending a list of arguments and their sorts between
/// parens. For example, the sort [Array](crate::theories::Arrays::Array) of the
/// [Arrays](crate::theories::Arrays) theory is declared as:
/// ```text
/// type Array(X: Sort::sort(), Y: Sort::sort());
/// ```
/// Here, `X` and `Y` are the names of the parameters and `Sort::sort()` is their sort, i.e. these
/// are sort parameters. Although SMT-LIBv2 only supports sort parameters and integer constant
/// parameters, in this syntax we support parameters of any sort.
///
/// The resulting theory type (e.g. [Core](crate::theories::Core)) provides one function for
/// each sort, of the given name (e.g. `Bool` or `Array`), accepting the given number of parameters
/// in the form of references to `SortParameter`, and returning a [Sort](crate::Sort).
///
/// For example, from the above declarations, [Core](crate::theories::Core) provides
/// [Core::Bool()](crate::theories::Core::Bool()), and [Arrays](crate::theories::Arrays) provides
/// [Arrays::Array](crate::theories::Arrays::Array) which accepts two parameters.
///
/// To be precise, the parameters of sort constructors are references to any clonable type that can
/// be converted to [SortArgument](crate::SortArgument). So we can refer to the sort `(Array Int
/// Int)` by the call `Arrays::Array(Ints::Int(), Ints::Int())`.
///
/// When looking up the sort by name in the [environment][crate::theories::Theory::env()] of the
/// theory, for example when using the [sort!](crate::sort!) macro, the sort will be
/// found by the same name used in the declaration.
///
/// ### How to declare constants
///
/// Constants (i.e. functions without arguments) can be specified with `const` declarations.
///
/// In the above example, we declare a constant `True` of sort `Core::Bool()`.
/// Note how `Core::Bool()`, which we are declaring, is already in scope.
///
/// The resulting theory type provides one function for each constant, accepting no arguments
/// and returning a [Primitive](crate::Primitive) representing the constant.
///
/// In the [environment][crate::theories::Theory::env()] of the theory, the constant will be
/// found by the same name used in the declaration. If the symbol to be provided by the theory is
/// not a valid Rust identifier, one can specify it as an attribute `#[name = "name"]`. For example:
/// ```text
/// #[name = "."]
/// const Point: Core::Bool();
/// ```
///
/// ### How to declare functions
///
/// The `fn` declarations describe the functions provided by the theory. The syntax resembles
/// vaguely the Rust syntax for functions but there are many differences.
///
/// For example, a simple declaration is that of [Ints::abs()](crate::theories::Ints::abs()), which
/// declares a function named `abs` which accepts two integers and returns an integer.
/// ```text
/// abs (Ints::Int(), Ints::Int()) -> Ints::Int();
/// ```
///
/// For more complex features, let us dissect the declaration of
/// [equals()](crate::theories::Core::equals()).
///
/// ```text
/// /// Equality.
/// #[name = "="]
/// #[chainable]
/// fn equals<A>(A, A) -> Core::Bool();
/// ```
/// Here we have:
/// 1. `equals` is the identifier used to refer to the function at the Rust level
/// 2. The attribute `#[name = "="]` specifies which name the function will be found by when looked
///    up in the [environment][crate::theories::Theory::env()] of the theory, for example when
///    parsing SMT-LIBv2 code or when using the [term!](crate::term!) macro. The attribute is needed
///    only when the name is not a valid Rust identifier.
/// 3. The optional `<A>` clause is the list of *type-level* parameters, in this case a single
///    parameter named `A` which represents a sort that will be inferred from the functions'
///    arguments.
/// 4. `(A,A)` is the list of arguments of the funcion, in this case two arguments of sort `A`. The
///    arguments here can be any sort or names introduced by the previous parametric type list. If
///    the function takes not argument, an empty pair of parenthesis is needed, but in this case it
///    is probably better to declare a constant instead.
/// 5. The `#[chainable]` attribute specifies the associativity of the function, better described in
///    the doc of [Associativity](crate::Associativity).
/// 6. `-> Core::Bool()` specifies the range (codomain) of the function.
///
/// The result is that `(= a1 a2 a3 a4)` is a valid term for any terms `a1`...`a4` of the same sort,
/// because the function is parametric, so accepts arguments of any sort as long as both are the
/// same, and accepts four arguments even though it is declared as binary, because of the
/// `:chainable` annotation (again, see [Associativity](crate::Associativity) or Section 3.7 "Theory
/// Declarations" of the SMT-LIBv2 [specification manual](https://smt-lib.org/language.shtml)).
///
/// In parametric functions, the type-level parameters can be used freely when specifying the sorts
/// of the arguments and the range, and appear as references to [crate::Parameter] objects, which,
/// in particular, is convertible to `SortArgument`, so can be used to instantiate other parametric
/// sorts. For example, the following declaration is the valid declaration of the
/// [select](crate::theories::Arrays::select()) function from the [Arrays](crate::theories::Arrays)
/// theory.
///
/// ```text
/// fn select<X, Y>(Arrays::Array(X, Y), X) -> Y;
/// ```
///
/// ### Extending other theories
///
/// Sometimes a theory is the extension of another one. An example among the standard SMT-LIBv2
/// theories is [Reals_Ints](crate::theories::Reals_Ints), which provides all the symbols provided
/// by [Reals](crate::theories::Reals) and [Ints](crate::theories::Reals), with the addition of
/// functions to convert between integers and reals and *vice versa*. In this case, redeclaring
/// all the symbols is tedious and, more importantly, needlessly duplicates symbols with the same
/// meaning. For example, it would be strange if the integer overload of the `plus` function for
/// [Reals_Ints](crate::theories::Reals_Ints) was a different object w.r.t.
/// [Ints::plus()](crate::theories::Ints::plus()), and it would complicate the usage of these
/// theories by backends.
///
/// Instead, theories like [Reals_Ints](crate::theories::Reals_Ints) are declared by extending
/// other theories, so inheriting all their symbols in their scopes. This is done by
/// adding a `extends:` field to the invocation of the macro.
///
/// As an example, [Reals_Ints](crate::theories::Reals_Ints) is declared as follows:
/// ```ignore
/// # mod formally {
/// #   pub extern crate formally_support as support;
/// #   pub extern crate formally_smt as smt;
/// # }
/// # use formally::smt::{theories, theories::*};
/// theory! {
///     /// The combined theory of integers and reals.
///     ///
///     /// See [the official specification](https://smt-lib.org/theories-Reals_Ints.shtml).
///     identifier: pub Reals_Ints,
///     name: "Reals_Ints",
///     extends: [ Ints, Reals ],
///     functions: {
///         /// Convert integers to reals.
///         to_real(Ints::Int()) -> Reals::Real();
///
///         /// Convert reals to integers.
///         to_int(Reals::Real()) -> Ints::Int();
///
///         /// Test if a real is an integer.
///         is_int(Reals::Real()) -> Core::Bool();
///     }
/// }
/// # fn main() { }
/// ```
///
/// When a theory extends others, it inherits their symbols in scope. The theory type itself
/// only provides the accessors functions for the new symbols, though. Therefore, for example, the
/// integer overload of the plus operator for the [Reals_Ints](crate::theories::Reals_Ints) is still
/// [Ints::plus()](crate::theories::Ints::plus()).
///
/// Finally, that the documentation of the resulting theory type automatically lists the extended
/// theories. For the example above, see how the documentation is rendered for
/// [Reals_Ints](crate::theories::Reals_Ints).
#[macro_export]
macro_rules! theories {
    ($($tokens:tt)*) => {$crate::macros::proc::theories!{$($tokens)*}};
}

/// Construct a term from a subset of the SMT-LIBv2 syntax for terms.
///
/// This macro provides a convenient way of constructing terms by implementing a subset of the
/// SMT-LIBv2 syntax.
///
/// Example:
/// ```
/// # mod formally {
/// #     pub extern crate formally_support as support;
/// #     pub extern crate formally_smt as smt;
/// # }
/// # use formally::{smt::*, support::*};
/// # fn main() -> Result<()> {
/// let mut solver = Solver::new(&Config::default())?;
///
/// solver.declare(Declaration::boolean("p"))?;
/// solver.declare(Declaration::boolean("q"))?;
///
/// let ponens = term!(=> (and (=> p q) p) q);
/// solver.require(term!(not #ponens))?;
///
/// assert_eq!(solver.check()?, Answer::No);
/// # Ok(())
/// # }
/// ```
///
/// The macro returns a temporary object of a hidden type implementing the [ToTerm](crate::ToTerm)
/// trait, so it can be used anywhere such types are accepted, including many methods of [Solver].
///
/// The object constructed by the macro is local and allocation-free, but this means its lifetime
/// is tied to the local scope and cannot be returned from the current function. To do anything
/// meaningful with it, it has to be passed to some function accepting [ToTerm] (e.g.
/// [Solver::require()] as in the example above).
///
/// To obtain an actual [Term] one can use the [ToTerm::into_term_in()] function with a [TermPool],
/// but most of the time one wishes to apply *name resolution* on the term as well after
/// construction, so the recommended way to get a [Term] out of the [term!] macro is to pass its
/// result to [Solver::lookup()]. This is however seldom necessary because most methods of [Solver]
/// accept [ToTerm] instances so the result of the macro can be used directly, as in the example
/// above.
///
/// In the above example we can note two features of the `term` macro combined with `Solver`.
/// 1. names of the symbols can be used directly, in which case the resulting term will contain
///    *unbound atoms* that the solver will resolve when needed (in this case, in the call to
///    `require()`. This is the case of the `"and"`, `"p"`, `"q"`, and `"not"` symbols in the
///    example above.
/// 2. entities declared in the surrounding Rust code, including objects of any type implementing
///    [ToTerm], can be expanded by using the `#identifier` syntax, inspired by the `quote` macro of
///    the `syn` crate. This is the case of the `#ponens` expansion in the example above.
///
/// When an entity is expanded it is used in the resulting term appropriately. In particular, one
/// can expand `Declared` or `Defined` objects to obtain *bound atoms* that do not need
/// further name resolution.
///
/// A sequence of arguments to a function can be expanded from any object implementing
/// `IntoIterator<Item: &T> where T: ToTerm`, for example `&Vec<Term>` or `&[Declared]` etc., with
/// the `#(#seq)*` syntax inspired again by the `quote` macro.
///
/// Example:
/// ```
/// # mod formally {
/// #     pub extern crate formally_support as support;
/// #     pub extern crate formally_smt as smt;
/// # }
/// # use formally::{smt::*, support::*};
/// # fn main() -> Result<()> {
/// let mut solver = Solver::new(&Config::default())?;
///
/// let x = solver.declare(Declaration::integer("x"))?;
/// let y = solver.declare(Declaration::integer("y"))?;
/// let z = solver.declare(Declaration::integer("z"))?;
///
/// let args = &[x, y, z];
///
/// solver.require(term!(= #(#args)*))?;
/// solver.require(term!(not (= x y)));
///
/// assert_eq!(solver.check()?, Answer::No);
/// # Ok(())
/// # }
/// ```
///
/// The accepted fragment of SMT-LIBv2 syntax for terms currently includes common atoms and
/// quantified formulas.
///
/// Example with a quantified formula:
/// ```
/// # mod formally {
/// #     pub extern crate formally_support as support;
/// #     pub extern crate formally_smt as smt;
/// # }
/// # use formally::{smt::{*, backend::z3::Z3}, support::*};
/// # fn main() -> Result<()> {
/// let mut solver = Solver::with_backend(&Config::default(), Z3)?;
///
/// let density = term!(
///     (forall ((x Real) (y Real)) (=> (< x y) (exists ((z Real)) (and (> z x) (< z y)))))
/// );
/// solver.require(term!(not #density))?;
///
/// assert_eq!(solver.check()?, Answer::No);
/// # Ok(())
/// # }
/// ```
#[macro_export]
macro_rules! term {
    ($($tokens:tt)*) => {$crate::macros::proc::term!{$($tokens)*}};
}

/// Construct a term from a subset of the SMT-LIBv2 syntax for sorts.
///
/// The [sort!] macro is similar to [term!] but restricted to the fragment of SMT-LIBv2 syntax for
/// sorts. The result is still an object of a type that implements [ToTerm]. In [formally::smt],
/// sorts are represented as terms since their shape is that of atoms where a function with a
/// codomain of [Sort::sort()] is applied to some arguments (e.g. in `(Array Int Int)`).
///
/// See the documentation for [Sort] for more information.
#[macro_export]
macro_rules! sort {
    ($($tokens:tt)*) => {$crate::macros::proc::sort!{$($tokens)*}};
}

#[macro_export]
macro_rules! var {
    ($name:ident $($sort:tt)*) => {
        $crate::Variable::new(stringify!($name), $crate::sort!($($sort)*))
    };
}

#[macro_export]
macro_rules! vars {
    ($(($name:ident $($sort:tt)*))*) => {
        [$($crate::var!($name $($sort)*)),*]
    };
}

#[doc(hidden)]
pub mod proc {
    pub use formally_smt_macros::*;
}
