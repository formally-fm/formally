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

use crate::parse::*;

/// A combinator repeating a parser for each element in a vector.
///
/// [foreach()] accepts an iterable collection  and a function that accepts one element of the
/// collection and returns a parser. For each element, the function is invoked and the
/// resulting parser invoked, with the result appended to the output collection using
/// [Extend].
///
/// Example:
/// ```
/// # use formally_io::parse::{*, combinators::*, parsers::*};
/// # use formally_support::*;
/// # mod formally {
/// #     pub mod io { pub use formally_io::*; }
/// #     pub mod support { pub use formally_support::*; }
/// # }
/// fn uppercased(txt: &str) -> Parser<'_, String> {
///     foreach(txt.chars(), |ch| char(ch).map(|ch| ch.to_ascii_uppercase()))
/// }
///
/// let result = uppercased("hello").parse("hello");
///
/// assert_eq!(result.unwrap(), "HELLO".to_string());
/// ```
pub fn foreach<'c, I, E, F, A, T>(elems: I, f: F) -> Parser<'c, E>
where
    I: 'c + IntoIterator<Item = A, IntoIter: Clone>,
    A: 'c + Clone,
    F: 'c + Clone + Fn(A) -> Parser<'static, T>,
    E: 'c + Default + Extend<T>,
    T: 'c,
{
    let iterator = elems.into_iter();

    Parser::new(move |state: &mut State| {
        let mut result = E::default();

        for v in iterator.clone() {
            result.extend(Some(f(v).parse_from(state)?));
        }

        Ok(result)
    })
}
