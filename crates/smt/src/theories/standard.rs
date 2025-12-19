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

theory! {
    /// The core SMT-LIBv2 theory, with basic Boolean connectives.
    ///
    /// See [the official specification](https://smt-lib.org/theories-Core.shtml).
    identifier: pub Core,
    name: "Core",
    sorts: {
        /// The sort of Boolean terms.
        Bool
    },
    constants: {
        /// The true constant.
        True: Core::Bool();
        /// The false constant.
        False: Core::Bool();
    },
    functions: {
        /// Logical negation.
        not(Core::Bool()) -> Core::Bool();

        /// Logical implication.
        implies/"=>"(Core::Bool(), Core::Bool()) :right_assoc -> Core::Bool();

        /// Logical conjunction.
        and(Core::Bool(), Core::Bool()) :left_assoc -> Core::Bool();

        /// Logical disjunction.
        or(Core::Bool(), Core::Bool()) :left_assoc -> Core::Bool();

        /// Logical exclusive disjunction.
        xor(Core::Bool(), Core::Bool()) :left_assoc -> Core::Bool();

        /// Equality.
        equals/"="[A](A, A) :chainable -> Core::Bool();

        /// Disequality.
        distinct[A](A, A) :pairwise -> Core::Bool();

        /// If-then-else choice construct.
        ite[A](Core::Bool(), A, A) -> A;
    }
}

theory! {
    /// The theory of reals.
    ///
    /// See [the official specification](https://smt-lib.org/theories-Reals.shtml).
    identifier: pub Reals,
    name: "Reals",
    sorts: {
        /// The sort of real numbers.
        Real
    },
    functions: {
        /// Unary negation.
        unary_minus/"-" (Reals::Real()) -> Reals::Real();

        /// Subtraction.
        minus/"-" (Reals::Real(), Reals::Real()) :left_assoc -> Reals::Real();

        /// Addition.
        plus/"+" (Reals::Real(), Reals::Real()) :left_assoc -> Reals::Real();

        /// Multiplication.
        mult/"*" (Reals::Real(), Reals::Real()) :left_assoc -> Reals::Real();

        /// Division.
        div/"/" (Reals::Real(), Reals::Real()) :left_assoc -> Reals::Real();

        /// Less-than-or-equal comparison.
        le/"<=" (Reals::Real(), Reals::Real()) :chainable -> Core::Bool();

        /// Less-than comparison.
        lt/"<" (Reals::Real(), Reals::Real()) :chainable -> Core::Bool();

        /// Greater-than-or-equal comparison.
        ge/">=" (Reals::Real(), Reals::Real()) :chainable -> Core::Bool();

        /// Greater-than comparison.
        gt/">" (Reals::Real(), Reals::Real()) :chainable -> Core::Bool();
    }
}

theory! {
    /// The theory of integers.
    ///
    /// See [the official specification](https://smt-lib.org/theories-Ints.shtml).
    identifier: pub Ints,
    name: "Ints",
    sorts: {
        /// The sort of real numbers.
        Int
    },
    functions: {
        /// Unary negation.
        unary_minus/"-" (Ints::Int()) -> Ints::Int();

        /// Subtraction.
        minus/"-" (Ints::Int(), Ints::Int()) :left_assoc -> Ints::Int();

        /// Addition.
        plus/"+" (Ints::Int(), Ints::Int()) :left_assoc -> Ints::Int();

        /// Multiplication.
        mult/"*" (Ints::Int(), Ints::Int()) :left_assoc -> Ints::Int();

        /// Division.
        div/"/" (Ints::Int(), Ints::Int()) :left_assoc -> Ints::Int();

        /// Modulo operation.
        mod_/"mod" (Ints::Int(), Ints::Int()) -> Ints::Int();

        /// Absolute value.
        abs (Ints::Int(), Ints::Int()) -> Ints::Int();

        /// Less-than-or-equal comparison.
        le/"<=" (Ints::Int(), Ints::Int()) :chainable -> Core::Bool();

        /// Less-than comparison.
        lt/"<" (Ints::Int(), Ints::Int()) :chainable -> Core::Bool();

        /// Greater-than-or-equal comparison.
        ge/">=" (Ints::Int(), Ints::Int()) :chainable -> Core::Bool();

        /// Greater-than comparison.
        gt/">" (Ints::Int(), Ints::Int()) :chainable -> Core::Bool();
    }
}

theory! {
    /// The combined theory of integers and reals.
    ///
    /// See [the official specification](https://smt-lib.org/theories-Reals_Ints.shtml).
    identifier: pub Reals_Ints,
    name: "Reals_Ints",
    extends: [ Ints, Reals ],
    functions: {
        /// Convert integers to reals.
        to_real(Ints::Int()) -> Reals::Real();

        /// Convert reals to integers.
        to_int(Reals::Real()) -> Ints::Int();

        /// Test if a real is an integer.
        is_int(Reals::Real()) -> Core::Bool();
    }
}

theory! {
    /// The theory of arrays.
    ///
    /// See [the official specification](https://smt-lib.org/theories-ArraysEx.shtml).
    identifier: pub Arrays,
    name: "Arrays",
    sorts: {
        /// The sort of arrays from indices of sort `X` to elements of sort `Y`.
        Array(X: Sort::sort(), Y: Sort::sort())
    },
    functions: {
        /// Reads an element of an array.
        select[X, Y](Arrays::Array(X, Y), X) -> Y;

        /// Writes an element to an array.
        store[X, Y](Arrays::Array(X, Y), X, Y) -> Arrays::Array(X, Y);
    }
}
