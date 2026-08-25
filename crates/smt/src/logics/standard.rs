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

use formally::smt::{logics::requirements::*, theories::*};

logic! {
    /// Linear Integer Arithmetic with Uninterpreted Functions.
    name: pub UFLIA,
    theories: [ Core, Ints ],
    requirements: [ Linear ],
    standard: true
}

logic! {
    /// Linear Real Arithmetic with Uninterpreted Functions.
    name: pub UFLRA,
    theories: [ Core, Reals ],
    requirements: [ Linear ],
    standard: true
}

logic! {
    /// Linear Integer Arithmetic.
    name: pub LIA,
    theories: [ Core, Ints ],
    requirements: [ Linear, NoUF ],
    standard: true
}

logic! {
    /// Linear Real Arithmetic.
    name: pub LRA,
    theories: [ Core, Reals ],
    requirements: [ Linear, NoUF ],
    standard: true
}

logic! {
    /// Linear Real Arithmetic.
    name: pub LIRA,
    theories: [ Core, RealsInts ],
    requirements: [ Linear, NoUF ],
    standard: true
}

logic! {
    /// Non-linear Integer Arithmetic.
    name: pub NIA,
    theories: [ Core, Ints ],
    requirements: [ NoUF ],
    standard: true
}

logic! {
    /// Non-linear Real Arithmetic.
    name: pub NRA,
    theories: [ Core, Reals ],
    requirements: [ NoUF ],
    standard: true
}

logic! {
    /// Quantifier-Free Linear Integer Arithmetic with Uninterpreted Functions.
    name: pub QF_UFLIA,
    theories: [ Core, Ints ],
    requirements: [ Linear, QuantifierFree ],
    standard: true
}

logic! {
    /// Quantifier-Free Linear Real Arithmetic with Uninterpreted Functions.
    name: pub QF_UFLRA,
    theories: [ Core, Reals ],
    requirements: [ Linear, QuantifierFree ],
    standard: true
}

logic! {
    /// Quantifier-Free Non-linear Integer Arithmetic with Uninterpreted Functions.
    name: pub QF_UFNIA,
    theories: [ Core, Ints ],
    requirements: [ QuantifierFree ],
    standard: true
}

logic! {
    /// Quantifier-Free Non-linear Real Arithmetic with Uninterpreted Functions.
    name: pub QF_UFNRA,
    theories: [ Core, Reals ],
    requirements: [ QuantifierFree ],
    standard: true
}

logic! {
    /// Quantifier-Free Linear Integer Arithmetic.
    name: pub QF_LIA,
    theories: [ Core, Ints ],
    requirements: [ Linear, QuantifierFree, NoUF ],
    standard: true
}

logic! {
    /// Quantifier-Free Linear Real Arithmetic.
    name: pub QF_LRA,
    theories: [ Core, Reals ],
    requirements: [ Linear, QuantifierFree, NoUF ],
    standard: true
}

logic! {
    /// Quantifier-Free Non-linear Integer Arithmetic.
    name: pub QF_NIA,
    theories: [ Core, Ints ],
    requirements: [ QuantifierFree, NoUF ],
    standard: true
}

logic! {
    /// Quantifier-Free Non-linear Real Arithmetic.
    name: pub QF_NRA,
    theories: [ Core, Reals ],
    requirements: [ QuantifierFree, NoUF ],
    standard: true
}

logic! {
    /// Quantifier-Free Linear Real/Integer Arithmetic.
    name: pub QF_LIRA,
    theories: [ Core, RealsInts ],
    requirements: [ Linear, QuantifierFree, NoUF ],
    standard: true
}

logic! {
    /// Linear Integer Arithmetic with Arrays.
    name: pub ALIA,
    theories: [ Core, Ints, Arrays ],
    requirements: [ Linear, NoUF ],
    standard: true
}

logic! {
    /// Quantifier-Free Linear Integer Arithmetic with Arrays.
    name: pub QF_ALIA,
    theories: [ Core, Ints, Arrays ],
    requirements: [ Linear, QuantifierFree, NoUF ],
    standard: true
}

logic! {
    /// Linear Integer Arithmetic with Arrays and Uninterpreted Functions.
    name: pub UFALIA,
    theories: [ Core, Ints, Arrays ],
    requirements: [ Linear ],
    standard: true
}

logic! {
    /// Quantifier-Free Linear Integer Arithmetic with Arrays and Uninterpreted Functions.
    name: pub QF_UFALIA,
    theories: [ Core, Ints, Arrays ],
    requirements: [ Linear, QuantifierFree ],
    standard: true
}
