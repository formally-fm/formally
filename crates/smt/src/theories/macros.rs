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
// AUTHORS OR COPYRIGHT HOLDERS BE IntsBLE FOR ANY CLAIM, DAMAGES OR OTHER
// IntsBILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//

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
/// # use formally::smt::theory;
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
macro_rules! theory {
    {$($tokens:tt)*} => {
        $crate::theory_impl! {
            $($tokens)*
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! theory_impl {
    {impl function { $fident:ident$(/$name:literal)? $([$($param:ident),*])? ($($arg:expr),*) $(:$flag:ident)? -> $range:expr} } => {
        #[allow(nonstandard_style)]
        #[allow(clippy::style)]
        pub static $fident : std::sync::LazyLock<$crate::Primitive> =
            std::sync::LazyLock::new(|| {
                let mut name = stringify!($fident);
                $(name = $name;)?
                $(
                    $(
                        let $param = &$crate::Parameter::new(stringify!($param), $crate::Sort::sort(), None);
                    )*
                )?

                $crate::Primitive::new(
                    name,
                    vec![$($($param.clone()),*)?],
                    vec![$( $crate::Sort::from($arg.clone()) ),*] as Vec<$crate::Sort>,
                    $crate::Sort::from($range.clone()),
                    $crate::theory!(impl flag { $($flag)? } )
                ).into()
            });
    };

    {impl const {$cident:ident$(/$name:literal)? : $sort:expr}} => {
        #[allow(nonstandard_style)]
        #[allow(clippy::style)]
        pub static $cident : std::sync::LazyLock<$crate::Primitive> =
            std::sync::LazyLock::new(|| {
                let mut name = stringify!($cident);
                $(name = $name;)?
                $crate::Primitive::new(
                    name,
                    std::iter::empty().collect(),
                    std::iter::empty().collect(),
                    $sort,
                    None
                ).into()
            });
    };

    {impl sort {$sident:ident$(/$name:literal)? $(($($params:ident:$kind:expr),*))?}} => {
        $crate::theory!{impl function { $sident$(/$name)? ($($($kind),*)?) -> $crate::Sort::sort() } }
    };

    {impl length { } } => { 0 };
    {impl length { $x:ident } } => { 1 };
    {impl length { $x:ident, $($tail:ident),*} } => { 1 + $crate::theory!{ impl length { $($tail),* } } };

    {impl flag { } } => { None };
    {impl flag { left_assoc } } => { Some($crate::Associativity::LeftAssoc) };
    {impl flag { right_assoc } } => { Some($crate::Associativity::RightAssoc) };
    {impl flag { chainable } } => { Some($crate::Associativity::Chainable) };
    {impl flag { pairwise } } => { Some($crate::Associativity::Pairwise) };

    {
        $(#[$attr:meta])*
        identifier: $vis:vis $theory:ident,
        name: $name:literal
        $(, extends: [ $( $other:expr ),* ])?
        $(, sorts: { $($(#[$sattr:meta])* $sid:ident$(/$sname:literal)? $(($($sparams:ident:$kind:expr),*))?);*$(;)? })?
        $(, constants: { $($(#[$cattr:meta])* $cid:ident$(/$cname:literal)? : $sort:expr);*$(;)? })?
        $(, functions: { $($(#[$fattr:meta])* $fid:ident$(/$fname:literal)? $([$($fparam:ident),*])? ($($arg:expr),*) $(:$flag:ident)? -> $range:expr);*$(;)? })?
    }=> {
        $crate::exports::paste!{
            #[derive(Default, Clone, Copy, Hash, PartialEq, Eq)]
            #[allow(nonstandard_style)]
            #[allow(clippy::style)]
            $(#[$attr])*
            $(
                ///
                /// This theory [extends](formally::smt::theory) the following other theories:
                $(#[doc=concat!("* [", concat!(stringify!($other), "]"))])*
            )?
            $vis struct $theory;

            #[allow(nonstandard_style)]
            #[allow(clippy::style)]
            #[allow(unused_assignments)]
            #[allow(unused_mut)]
            mod [<$theory __details>] {
                use super::*;

                pub static FUNCS: std::sync::LazyLock<formally::support::Scope<formally::smt::Function>> = std::sync::LazyLock::new(|| {
                    let mut scope = formally::support::Scope::new();

                    $($( scope.merge(&$crate::theories::Theory::functions(&$other)); )*)?

                    $($( scope.add(&[<$theory __details>]::$fid.name(), $crate::Function::from([<$theory __details>]::$fid.clone())); )*)?

                    $($( scope.add(&[<$theory __details>]::$cid.name(), $crate::Function::from([<$theory __details>]::$cid.clone())); )*)?

                    scope
                });

                pub static SORTS: std::sync::LazyLock<formally::support::Scope<$crate::Function>> = std::sync::LazyLock::new(|| {
                    let mut scope = formally::support::Scope::new();

                    $($( scope.merge(&$crate::theories::Theory::sorts(&$other)); )*)?

                    $($( scope.add(&[<$theory __details>]::$sid.name(), $crate::Function::from([<$theory __details>]::$sid.clone())); )*)?

                    scope
                });

                $($( $crate::theory! { impl sort { $sid$(/$sname)? $(($($sparams:$kind),*))? } } )*)?
                $($( $crate::theory! { impl const { $cid$(/$cname)? : $sort } } )*)?
                $($( $crate::theory! { impl function { $fid$(/$fname)? $([$($fparam),*])? ($($arg),*) $(:$flag)? -> $range } } )*)?
            }

            impl $theory {
                $(
                    $(
                        #[allow(nonstandard_style)]
                        #[allow(clippy::style)]
                        $(#[$sattr])*
                        ///
                        /// Declaration in the syntax of the [theory] macro:
                        ///
                        /// ```text
                        #[doc=stringify!($sid$(/$sname)? $([$($sparams:$kind),*])?)]
                        /// ```
                        pub fn $sid ($($($sparams: &(impl Clone + Into<$crate::SortArgument>)),*)?) -> $crate::Sort {
                            $crate::Sort {
                                head: $crate::Function::Primitive([<$theory __details>]::$sid.clone()),
                                arguments: vec![$($($sparams.clone().into()),*)?],
                                span: None
                            }
                        }
                    )*
                )?
                $(
                    $(
                        #[allow(nonstandard_style)]
                        #[allow(clippy::style)]
                        $(#[$cattr])*
                        ///
                        /// Declaration in the syntax of the [theory] macro:
                        ///
                        /// ```text
                        #[doc=stringify!($cid$(/$cname)? : $sort)]
                        /// ```
                        pub fn $cid () -> $crate::Primitive {
                            [<$theory __details>]::$cid.clone()
                        }
                    )*
                )?
                $(
                    $(
                        #[allow(nonstandard_style)]
                        #[allow(clippy::style)]
                        $(#[$fattr])*
                        ///
                        /// Declaration in the syntax of the [theory] macro:
                        ///
                        /// ```text
                        #[doc=stringify!($fid$(/$fname)? $([$($fparam),*])? ($($arg),*) $(:$flag)? -> $range;)]
                        /// ```
                        pub fn $fid () -> $crate::Primitive {
                            [<$theory __details>]::$fid.clone()
                        }
                    )*
                )?
            }

            impl $crate::theories::Theory for $theory {
                fn functions(&self) -> formally::support::Scope<$crate::Function> {
                    [<$theory __details>]::FUNCS.clone()
                }

                fn sorts(&self) -> formally::support::Scope<$crate::Function> {
                    [<$theory __details>]::SORTS.clone()
                }
            }
        }
    };
}
