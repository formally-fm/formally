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
#[macro_export]
macro_rules! logic {
    ($($tokens:tt)*) => {
        $crate::logic_impl! {
            $($tokens)*
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! logic_impl {
    {
        $(#[$attr:meta])*
        name: $vis:vis $name:ident,
        theories: [ $($theories:expr),*$(,)? ],
        requirements: [ $($reqs:ident),*$(,)? ]
        $(, standard: $standard:ident )?
    } => {
        $(#[$attr])*
        ///
        /// Background theories:
        ///
        $(#[doc=concat!("* [", concat!(stringify!($theories), "]"))])*
        ///
        /// Syntactic requirements:
        $(#[doc=concat!("* [", concat!(stringify!($reqs), "]"))])*
        ///
        /// Declaration in the syntax of the [logic] macro:
        /// ```text
        /// logic! {
        #[doc=concat!("    name: ", concat!(stringify!($name), ","))]
        #[doc=concat!("    theories: [ ", concat!(stringify!($($theories),*), " ],"))]
        #[doc=concat!("    requirements: [ ", concat!(stringify!($($reqs),*), " ],"))]
        /// }
        /// ```
        $vis struct $name;

        impl $crate::logics::Logic for $name {
            fn name(&self) -> &str {
                stringify!($name)
            }

            fn theory(&self) -> &dyn $crate::theories::Theory {
                logic!(impl theories for $($theories),*)
            }

            #[allow(unused_variables)]
            fn check_term(
                &self,
                context: &formally::support::Context,
                term: &$crate::Term
            ) -> formally::support::Result<()> {
                $( $reqs::check_term(self, context, term)?; )*

                Ok(())
            }

            #[allow(unused_variables)]
            fn check_function(
                &self,
                context: &formally::support::Context,
                func: &$crate::UserFunction
            ) -> formally::support::Result<()> {
                $( $reqs::check_function(self, context, func)?; )*

                match func {
                    $crate::UserFunction::Defined(def) => {
                        self.check_term(context, &def.body)
                    }
                    _ => Ok(()),
                }
            }
        }

        $(logic! { impl collect standard logic: $standard for $name} )?
    };

    (impl collect standard logic: False for $name:ident) => { };
    (impl collect standard logic: True for $name:ident) => {
        $crate::exports::paste! {
            #[$crate::exports::distributed_slice($crate::logics::STANDARD_LOGICS)]
            static [<$name LOGIC>]:
                &'static (dyn $crate::logics::Logic + Send + Sync) = &$name;
        }
    };

    (impl theories for $theory:expr) => { &$theory };
    (impl theories for $($theories:expr),*) => {
        {
            static THEORY: std::sync::LazyLock<$crate::theories::CombinedTheory> =
                std::sync::LazyLock::new(|| {
                    $crate::theories::CombinedTheory::new(&[$(&$theories),*])
                });
            &*THEORY
        }
    }
}
