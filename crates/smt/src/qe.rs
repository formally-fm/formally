//
// ::formally - the open-source formal methods toolchain
//
// Copyright (c) 2026 Nicola Gigante
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

//! Interfaces for quantifier elimination.
//!
//! This module collects everything regarding quantifier elimination.
//!
//! For now, just the [QE] trait which is implemented by the result of
//! [Backend::qe()](backends::Backend::qe()), for SMT backends that support QE, but may also be
//! implemented separately by other engines implementing QE exclusively.

use crate::formally;
use formally::{smt::*, support::*};

/// A trait for backends providing quantifier elimination functionalities.
pub trait QE {
    /// Perform quantifier elimination on the given `term`, constructing the result using `pool`.
    fn qe(&self, term: Term, pool: &dyn TermPool) -> Result<Term, Box<dyn Diagnosable>>;
}
