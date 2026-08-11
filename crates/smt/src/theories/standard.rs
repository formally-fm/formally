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

use crate::*;

theories! {
    /// The core SMT-LIBv2 theory, with basic Boolean connectives.
    ///
    /// See [the official specification](https://smt-lib.org/theories-Core.shtml).
    pub Core {
        /// The sort of Boolean terms.
        type Bool;

        /// The true constant.
        const True: Core::Bool();

        /// The false constant.
        const False: Core::Bool();

        /// Logical negation.
        fn not(Core::Bool()) -> Core::Bool();

        /// Logical implication.
        #[name = "=>"]
        #[right_assoc]
        fn implies(Core::Bool(), Core::Bool()) -> Core::Bool();

        /// Logical conjunction.
        #[left_assoc]
        fn and(Core::Bool(), Core::Bool()) -> Core::Bool();

        /// Logical disjunction.
        #[left_assoc]
        fn or(Core::Bool(), Core::Bool()) -> Core::Bool();

        /// Logical exclusive disjunction.
        #[left_assoc]
        fn xor(Core::Bool(), Core::Bool()) -> Core::Bool();

        /// Equality.
        #[name = "="]
        #[chainable]
        fn equals<A>(A, A) -> Core::Bool();

        /// Disequality.
        #[pairwise]
        fn distinct<A>(A, A) -> Core::Bool();

        /// If-then-else choice construct.
        fn ite<A>(Core::Bool(), A, A) -> A;
    }

    /// The theory of reals.
    ///
    /// See [the official specification](https://smt-lib.org/theories-Reals.shtml).
    pub Reals {
        /// The sort of real numbers.
        type Real;

        /// Unary negation.
        #[name = "-"]
        fn unary_minus(Reals::Real()) -> Reals::Real();

        /// Subtraction.
        #[name = "-"]
        #[left_assoc]
        fn minus(Reals::Real(), Reals::Real()) -> Reals::Real();

        /// Addition.
        #[name = "+"]
        #[left_assoc]
        fn plus(Reals::Real(), Reals::Real()) -> Reals::Real();

        /// Multiplication.
        #[name = "*"]
        #[left_assoc]
        fn mult(Reals::Real(), Reals::Real()) -> Reals::Real();

        /// Division.
        #[name = "/"]
        #[left_assoc]
        fn div (Reals::Real(), Reals::Real()) -> Reals::Real();

        /// Less-than-or-equal comparison.
        #[name = "<="]
        #[chainable]
        fn le(Reals::Real(), Reals::Real()) -> Core::Bool();

        /// Less-than comparison.
        #[name = "<"]
        #[chainable]
        fn lt(Reals::Real(), Reals::Real()) -> Core::Bool();

        /// Greater-than-or-equal comparison.
        #[name = ">="]
        #[chainable]
        fn ge(Reals::Real(), Reals::Real()) -> Core::Bool();

        /// Greater-than comparison.
        #[name = ">"]
        #[chainable]
        fn gt(Reals::Real(), Reals::Real()) -> Core::Bool();

    }

    /// The theory of integers.
    ///
    /// See [the official specification](https://smt-lib.org/theories-Ints.shtml).
    pub Ints {
        /// The sort of real numbers.
        type Int;

        /// Unary negation.
        #[name = "-"]
        fn unary_minus (Ints::Int()) -> Ints::Int();

        /// Subtraction.
        #[name = "-"]
        #[left_assoc]
        fn minus (Ints::Int(), Ints::Int()) -> Ints::Int();

        /// Addition.
        #[name = "+"]
        #[left_assoc]
        fn plus (Ints::Int(), Ints::Int()) -> Ints::Int();

        /// Multiplication.
        #[name = "*"]
        #[left_assoc]
        fn mult (Ints::Int(), Ints::Int()) -> Ints::Int();

        /// Division.
        #[name = "/"]
        #[left_assoc]
        fn div (Ints::Int(), Ints::Int()) -> Ints::Int();

        /// Modulo operation.
        #[name = "mod"]
        fn mod_ (Ints::Int(), Ints::Int()) -> Ints::Int();

        /// Absolute value.
        fn abs (Ints::Int(), Ints::Int()) -> Ints::Int();

        /// Less-than-or-equal comparison.
        #[name = "<="]
        #[chainable]
        fn le (Ints::Int(), Ints::Int()) -> Core::Bool();

        /// Less-than comparison.
        #[name = "<"]
        #[chainable]
        fn lt (Ints::Int(), Ints::Int()) -> Core::Bool();

        /// Greater-than-or-equal comparison.
        #[name = ">="]
        #[chainable]
        fn ge (Ints::Int(), Ints::Int()) -> Core::Bool();

        /// Greater-than comparison.
        #[name = ">"]
        #[chainable]
        fn gt (Ints::Int(), Ints::Int()) -> Core::Bool();
    }

    /// The combined theory of integers and reals.
    ///
    /// See [the official specification](https://smt-lib.org/theories-Reals_Ints.shtml).
    pub Reals_Ints : Ints, Reals {
        /// Convert integers to reals.
        fn to_real(Ints::Int()) -> Reals::Real();

        /// Convert reals to integers.
        fn to_int(Reals::Real()) -> Ints::Int();

        /// Test if a real is an integer.
        fn is_int(Reals::Real()) -> Core::Bool();
    }

    /// The theory of arrays.
    ///
    /// See [the official specification](https://smt-lib.org/theories-ArraysEx.shtml).
    pub Arrays {
        /// The sort of arrays from indices of sort `X` to elements of sort `Y`.
        type Array(X: Sort::sort(), Y: Sort::sort());

        /// Reads an element of an array.
        fn select<X, Y>(Arrays::Array(X, Y), X) -> Y;

        /// Writes an element to an array.
        fn store<X, Y>(Arrays::Array(X, Y), X, Y) -> Arrays::Array(X, Y);
    }
}
