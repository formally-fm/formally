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

//! Procedural macros exported by the `formally::smt` subcrate.
#![doc = ""]
#![cfg_attr(
    not(feature = "__subcratedoc"),
    doc = "**WARNING: This crate is not supposed to be used directly.**"
)]
#![doc = ""]
#![cfg_attr(
    not(feature = "__subcratedoc"),
    doc = "**Use instead the `formally::smt` module of the main `formally` crate by enabling the `\"smt\"` feature.**"
)]
#![doc = ""]

mod term;
mod theories;
mod logic;

use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;

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
/// In the above example we can note two features of the `term` macro combined with `Solver`.
/// 1. names of the symbols can be used directly, in which case the resulting term will contain
///    *unbound atoms* that the solver will resolve when needed (in this case, in the call to
///    `require()`. This is the case of the `"and"`, `"p"`, `"q"`, and `"not"` symbols in the
///    example above.
/// 2. entities declared in the surrounding Rust code, including other terms, can be expanded by
///    using the `#identifier` syntax, inspired by the `quote` macro of the `syn` crate. This is the
///    case of the `#ponens` expansion in the example above.
///
/// When an entity is expanded it is used in the resulting term appropriately. In particular, one
/// can expand `Declared` or `Defined` objects to obtain *bound atoms* that do not need
/// further name resolution.
///
/// Expansion of repetitions from iterators, as in the `quote` macro, is not supported *yet*.
#[proc_macro]
pub fn term(input: TokenStream) -> TokenStream {
    let term = parse_macro_input!(input as term::Term);

    quote!(#term).into()
}

/// Declare a new SMT-LIBv2 theory.
///
/// This macro automates the process of defining a type suitably implementing the
/// [Theory](crate::theories::Theory) trait. It allows one to specify:
/// - the name of the new type and the string name of the new theory
/// - possibly other theories to inherit symbols from
/// - sorts, constants, and function symbols provided by the theory
///
/// ## How to declare a new theory
///
/// Let us start, as an example, with the declaration of the [Core](crate::theories::Core)
/// theory.
///
/// ```
/// # mod formally {
/// #   pub extern crate formally_support as support;
/// #   pub extern crate formally_smt as smt;
/// # }
/// # use formally::smt::theory;
/// theory! {
///     /// The core SMT-LIBv2 theory, with basic Boolean connectives.
///     ///
///     /// See [the official specification](https://smt-lib.org/theories-Core.shtml).
///     identifier: pub Core,
///     name: "Core",
///     sorts: {
///         /// The sort of Boolean terms.
///         Bool
///     },
///     constants: {
///         /// The true constant.
///         True: Core::Bool();
///         /// The false constant.
///         False: Core::Bool();
///     },
///     functions: {
///         /// Logical negation.
///         not(Core::Bool()) -> Core::Bool();
///
///         /// Logical implication.
///         implies/"=>"(Core::Bool(), Core::Bool()) :right_assoc -> Core::Bool();
///
///         /// Logical conjunction.
///         and(Core::Bool(), Core::Bool()) :left_assoc -> Core::Bool();
///
///         /// Logical disjunction.
///         or(Core::Bool(), Core::Bool()) :left_assoc -> Core::Bool();
///
///         /// Logical exclusive disjunction.
///         xor(Core::Bool(), Core::Bool()) :left_assoc -> Core::Bool();
///
///         /// Equality.
///         equals/"="[A](A, A) :chainable -> Core::Bool();
///
///         /// Disequality.
///         distinct[A](A, A) :pairwise -> Core::Bool();
///
///         /// If-then-else choice construct.
///         ite[A](Core::Bool(), A, A) -> A;
///     }
/// }
/// # fn main() { }
/// ```
///
/// There are a few elements to dissect in this declaration:
/// 1. the `identifier` argument is the name the theory type will have at the Rust level
/// 2. The `pub` keyword before the identifier is the visibility specifier that will be attached to
///    the declared type (it can be absent for private types, or `pub`, `pub(crate)`, etc.).
/// 3. the `name` argument is the name of the theory to set to the [logic](crate::Config::logic)
///    field of [Config](crate::Config) when instantiating a new [Solver](crate::Solver).
/// 4. `sorts`, `constants` and `functions` specify the symbols provided by the theory.
/// 5. the *doc comment* above the `identifier` parameter will document the theory type itself,
///    while the doc comments above each declared item will document the item. The documentation of
///    each item will include also its verbatim definition for reference (see the result in the
///    documentation of [Core](crate::theories::Core)).
///
/// ### How to declare sorts
///
/// The `sort` parameter accepts a semicolon-separated list of sort declarations enclosed by braces.
/// In the above example, we only declare a single sort, `Bool`, which simple, i.e., non-parametric.
///
/// A parametric sort is specified by appending a list of arguments and their sorts between parens.
/// For example, the sort [Array](crate::theories::Arrays::Array) of the
/// [Arrays](crate::theories::Arrays) theory is declared as:
/// ```text
/// sorts: {
///     Array(X: Sort::sort(), Y: Sort::sort())
/// }
/// ```
/// Here, `X` and `Y` are the names of the parameters and `Sort::sort()` is their sort, i.e. these
/// are sort parameters. Although SMT-LIBv2 only supports sort parameters and integer constant
/// parameters, here we support parameters of any sort.
///
/// The resulting theory type (e.g. [Core](crate::theories::Core) provides one function for
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
/// In the [environment][crate::theories::Theory::env()] of the theory, the constant will be
/// found by the same name used in the declaration. If the symbol to be provided by the theory is
/// not a valid Rust identifier, one can specify it as a string by appending it to the Rust
/// identifier after a slash. For example:
///
/// ```text
/// sorts: {
///     All/"@all@"
/// }
/// ```
///
/// ### How to declare constants
///
/// Constants (i.e. functions without arguments) can be specified with the `constants` parameter,
/// which accepts a semicolon-separated list of declarations enclosed by braces.
///
/// In the above example, we declare two constants, `True` and `False`, of sort `Core::Bool()`.
/// Note how `Core::Bool()`, declared just above, is already in scope.
///
/// The resulting theory type provides one function for each constant, accepting no arguments
/// and returning a [Primitive](crate::Primitive) representing the constant.
///
/// In the [environment][crate::theories::Theory::env()] of the theory, the constant will be
/// found by the same name used in the declaration. If the symbol to be provided by the theory is
/// not a valid Rust identifier, one can specify it as a string by appending it to the Rust
/// identifier after a slash. For example:
/// ```text
/// constants: {
///     MyConst/"My:Const"
/// }
/// ```
///
/// ### How to declare functions
///
/// The `functions:` parameter accepts a semicolon-separated list of declarations enclosed by
/// braces. Function declarations are the most complex in this macro. They specify:
/// 1. the Rust identifier of the function and optionally a different lookup name.
/// 2. possibly a list of *type-level* parameters
/// 3. the list of sorts of the arguments of the function
/// 4. an optional *associativity annotation*
/// 5. the range, i.e., the sort the return value
///
/// Let us dissect the declaration of [equals()](crate::theories::Core::equals()).
///
/// ```text
/// equals/"="[A](A, A) :chainable -> Core::Bool();
/// ```
/// Here we have:
/// 1. `equals` is the identifier used to refer to the function at the Rust level
/// 2. `"="` is the name the function will be found by through name lookup, i.e. how to refer to
///    this function in SMT-LIBv2 code.
/// 3. `[A]` is the list of *type-level* parameters, in this case a single parameter named `A` which
///    represents a sort that will be inferred from the functions' arguments.
/// 4. `(A,A)` is the list of arguments of the funcion, in this case two arguments of sort `A`.
/// 5. `:chainable` is an associativity annotation, better described in the doc of
///    [Associativity](crate::Associativity).
/// 6. `-> Core::Bool()` specifies the range of the function.
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
/// select[X, Y](Arrays::Array(X, Y), X) -> Y;
/// ```
///
/// The lookup name, the list of type-level parameters, and the associativity annotation can be
/// omitted, while if the function takes no arguments, an empty pair of parens is needed.
///
/// For example, a simpler declaration is that of [Ints::abs()](crate::theories::Ints::abs()):
/// ```text
/// abs (Ints::Int(), Ints::Int()) -> Ints::Int();
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
/// ```
/// # mod formally {
/// #   pub extern crate formally_support as support;
/// #   pub extern crate formally_smt as smt;
/// # }
/// # use formally::smt::{theory, theories::*};
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
#[proc_macro]
pub fn theories(input: TokenStream) -> TokenStream {
    let root = parse_macro_input!(input as theories::Root);

    quote!(#root).into()
}

/// Declare an SMT-LIBv2 logic.
///
/// This macro helps the proper declaration of types implementing the [Logic](crate::logics::Logic)
/// trait. Logic types obtained by this macro are unit structs (e.g. declared as `pub struct LIA;`,
/// and therefore instantiated as `LIA`, not as `LIA {}`) providing a suitable implementation of
/// the trait.
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
/// 3. An optional *doc comment* can be place above the `name:` parameter and will document the
///    resulting type. The documentation of the type will contain automatically the list of theories
///    and requirements (see how the above example is rendered in the documentation of
///    [QF_LIA](crate::logics::QF_LIA)).
/// 4. The `theories:` parameter accepts a comma-separated list of theories enclosed in brackets.
///    The names specified here are paths of any type currently in scope implementing the
///    [Theory](crate::theories::Theory) trait.
/// 5. The `requirements:` parameter accepts a comma-separated list of requirements enclosed in
///    brackets. The names specified here are paths of any type currently in scope implementing the
///    [LogicRequirement](crate::logics::requirements::LogicRequirement) trait.
///
/// Standard SMT-LIBv2 theories are declared in the [theories](crate::theories) module and some
/// logic requirements commonly needed in standard SMT-LIBv2 logics are declared in the
/// [logics::requirements](crate::logics::requirements) module.
#[proc_macro]
pub fn logic(input: TokenStream) -> TokenStream {
    let root = parse_macro_input!(input as logic::Root);

    quote!(#root).into()
}
