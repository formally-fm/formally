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

use crate::parse::{parsers::*, *};

/// Trait providing a few combinators for lexical elements of common languages.
pub trait Lexical<'c, Out: 'c>: Parse<'c, Out> {
    /// Match a parser inbetween the matches of two delimiter parsers.
    fn between<TA, TB>(self, before: Parser<'c, TB>, after: Parser<'c, TA>) -> Parser<'c, Out>
    where
        TA: 'c,
        TB: 'c,
    {
        let name = self.name().clone();
        before
            .and(self)
            .and(after)
            .map(|((_, v), _)| v)
            .with_name(name)
    }

    /// Match a parser inbetween parens.
    fn parens(self) -> Parser<'c, Out> {
        self.between(char('('), char(')'))
    }

    /// Match a parser inbetween brackets.
    fn brackets(self) -> Parser<'c, Out> {
        self.between(char('['), char(']'))
    }

    /// Match a parser inbetween braces.
    fn braces(self) -> Parser<'c, Out> {
        self.between(char('{'), char('}'))
    }
}

impl<'c, Out: 'c, T: Parse<'c, Out>> Lexical<'c, Out> for T {}
