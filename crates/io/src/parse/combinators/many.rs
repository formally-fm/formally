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
use formally_support::*;

/// Trait providing combinators to match sequences.
pub trait Many<'c, Out: 'c>: Parse<'c, Out> {
    /// Ignore zero or more occurrences of the given parser.
    ///
    /// This combinator behaves similarly to `many().ignore()` except that it plays well with type
    /// inference.
    fn skip(self) -> Parser<'c, ()> {
        Parser::new(move |state: &mut State| {
            loop {
                let mut split = state.split();
                match self.parse_from(&mut split) {
                    Ok(_) => split.commit(),
                    Err(_) if !split.has_advanced() => return Ok(()),
                    Err(err) => return Err(err),
                }
            }
        })
    }

    /// Parse multiple matches of the same parser separated by a separator until a condition
    /// occurs.
    ///
    /// [sep_by_while_counting()](Many::sep_by_while_counting) is a quite flexible combinator and
    /// the basic building blocks for almost all the combinators of the [Many] trait.
    ///
    /// It parses at least `min` and at most `max` matches of the given parser, stopping either at
    /// the first silent rejection or when `cond(&v)` returns false, where `v` is the result value
    /// of the last match. The matches of the main parser are interleaved by matches of the `sep`
    /// parser. If the separator succeeds, a subsequent match of the main parser has to succeed as
    /// well. That is, separators are not consumed until the subsequent element matches completely
    /// or fails with an error. Therefore, trailing separators are not consumed.
    ///
    /// To recap, the combinator fails with an error in the following cases:
    /// 1. the number of matches found satisfying `cond()` is less than `min`
    /// 2. the parser fails with an error instead of a silent rejection
    /// 3. the separator parser fails with an error instead of a silent rejection
    ///
    /// In the latter cases the error is emitted as-is.
    ///
    /// The result is a collection containing all the results from the matched elements. The type
    /// of the collection is not fixed, but any type implementing [Default] and [Extend] can be
    /// used. This includes, among others, [Vec] and, if the element result type is [prim@char],
    /// also [String]. This flexibility has the cost of sometimes produce a type inference
    /// ambiguity. If the result of the combinator is not used, the compiler cannot know which
    /// result type to instance it with. This happens even when the result is ignored with
    /// [ignore()](Control::ignore). There are a few ways to solve the issue without annoying
    /// type annotations. One is to ignore the return value using [sink()](Sink::sink) instead of
    /// [ignore()](Control::ignore). In contrast to the latter, the former pins down
    /// the return type so type inference works. The second way, when the result has not to be
    /// ignored but type inference is not possible either, is to use [to_vec()](ToVec::to_vec),
    /// which explicitly collects the elements into a [Vec]. If the elements are [prim@char] values,
    /// [to_string()](ToString::to_string) can be used to obtain a [String] instead.
    fn sep_by_while_counting<S, E, F>(
        self,
        cond: F,
        sep: Parser<'static, S>,
        min: usize,
        max: usize,
    ) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
        F: 'c + Clone + Fn(&Out) -> bool,
        S: 'c,
    {
        Parser::new(move |state: &mut State| {
            let mut out = E::default();

            let mut found = 0;
            let mut elapsed = None;
            let mut first = true;
            loop {
                let mut split = state.split();
                if !first {
                    State::skip(&mut split);
                    match sep.parse_from(&mut split) {
                        Ok(_) => {}
                        Err(_) if split.has_advanced() => {
                            split.commit();
                            return Err(DiagnosticEmitted.into());
                        }
                        Err(_) => break,
                    }
                }
                first = false;

                let mut split2 = split.split();
                State::skip(&mut split2);
                match self.parse_from(&mut split2) {
                    Ok(value) => {
                        if !cond(&value) {
                            elapsed = split.elapsed();
                            break;
                        }
                        out.extend(Some(value));
                        split2.commit();
                        split.commit();
                        found += 1;
                        if found == max {
                            break;
                        }
                    }
                    Err(_) if split2.has_advanced() => {
                        split2.commit();
                        split.commit();
                        return Err(DiagnosticEmitted.into());
                    }
                    Err(_) => break,
                }
            }

            if found < min {
                error!(
                    state,
                    elapsed,
                    SyntaxIssue::ManyButNotEnough {
                        min,
                        found,
                        name: self.name().clone(),
                    }
                );
                return Err(DiagnosticEmitted.into());
            }

            Ok(out)
        })
    }

    /// Equivalent to `sep_by_while_counting(cond, sep, 0, usize::MAX)`
    fn sep_by_while<S, E, F>(self, cond: F, sep: Parser<'static, S>) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
        F: 'c + Clone + Fn(&Out) -> bool,
        S: 'c,
    {
        self.sep_by_while_counting(cond, sep, 0, usize::MAX)
    }

    /// Equivalent to `sep_by_while(|_| true, sep)`
    fn sep_by<S, E>(self, sep: Parser<'static, S>) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
        S: 'c,
    {
        self.sep_by_while(|_| true, sep)
    }

    /// Equivalent to `sep_by_while_counting(cond, sep, 1, usize::MAX)`
    fn sep_by1_while<S, E, F>(self, cond: F, sep: Parser<'static, S>) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
        F: 'c + Clone + Fn(&Out) -> bool,
        S: 'c,
    {
        self.sep_by_while_counting(cond, sep, 1, usize::MAX)
    }

    /// Equivalent to `sep_by1_while(|_| true, sep)`
    fn sep_by1<S, E>(self, sep: Parser<'static, S>) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
        S: 'c,
    {
        self.sep_by1_while(|_| true, sep)
    }

    /// Equivalent to `sep_by_while_counting(|_| true, sep, n, n)`
    fn sep_by_n<S, E>(self, n: usize, sep: Parser<'static, S>) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
        S: 'c,
    {
        self.sep_by_while_counting(|_| true, sep, n, n)
    }

    /// Equivalent to `sep_by_while_counting(cond, succeed(), min, max)`
    fn many_while_counting<E, F>(self, cond: F, min: usize, max: usize) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
        F: 'c + Clone + Fn(&Out) -> bool,
    {
        self.sep_by_while_counting(cond, succeed(), min, max)
    }

    /// Execute two parsers sequentially that return sequences and concatenate the sequences.
    fn concat(self, p2: Parser<'c, Out>) -> Parser<'c, Out>
    where
        Out: Default + IntoIterator + Extend<<Out as IntoIterator>::Item>,
    {
        Parser::new(move |state: &mut State| {
            let mut out = Out::default();
            out.extend(self.parse_from(state)?);
            out.extend(p2.parse_from(state)?);

            Ok(out)
        })
    }

    /// Equivalent to `many_while_counting(cond, 0, usize::MAX)`
    fn many_while<E, F>(self, cond: F) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
        F: 'c + Clone + Fn(&Out) -> bool,
    {
        self.many_while_counting(cond, 0, usize::MAX)
    }

    /// Equivalent to `many_while(|_| true)`
    fn many<E>(self) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
    {
        self.many_while(|_| true)
    }

    /// Equivalent to `many_while_counting(cond, 1, usize::MAX)`
    fn many1_while<E, F>(self, cond: F) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
        F: 'c + Clone + Fn(&Out) -> bool,
    {
        self.many_while_counting(cond, 1, usize::MAX)
    }

    /// Equivalent to `many1_while(|_| true)`
    fn many1<E>(self) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
    {
        self.many1_while(|_| true)
    }

    /// Equivalent to `many_while_counting(|_| true, min, max)`
    fn many_counting<E>(self, min: usize, max: usize) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
    {
        self.many_while_counting(|_| true, min, max)
    }

    /// Equivalent to `many_while_counting(|_| true, n, n)`
    fn many_n<E>(self, n: usize) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
    {
        self.many_while_counting(|_| true, n, n)
    }

    /// Equivalent to `many_n(1)`. Useful to turn a result into a sequence containing a single
    /// element.
    fn once<E>(self) -> Parser<'c, E>
    where
        E: 'c + Default + Extend<Out>,
    {
        self.many_n(1)
    }
}

impl<'c, Out: 'c, T: Parse<'c, Out>> Many<'c, Out> for T {}

/// Trait providing the [to_vec()](ToVec::to_vec) combinator.
pub trait ToVec<'c, Out>: Parse<'c, Vec<Out>> {
    /// Collect the elements of a sequential result into a vector.
    ///
    /// The combinator itself actually does nothing, it just pins down to `Vec<_>` the return type
    /// of other combinators such as [many()](Many::many) so type inference can work.
    fn to_vec(self) -> Self {
        self
    }
}

impl<'c, Out: 'c, T: Parse<'c, Vec<Out>>> ToVec<'c, Out> for T {}

mod private {
    #[derive(Default)]
    pub struct SinkT {}
}

impl<A> Extend<A> for private::SinkT {
    fn extend<T: IntoIterator<Item = A>>(&mut self, _iter: T) {}
}

/// Trait providing the [sink()](Sink::sink) combinator.
pub trait Sink<'c>: Parse<'c, private::SinkT> {
    /// Ignore the result of a sequential parser.
    ///
    /// The combinator itself is equivalent to [ignore()](Control::ignore) but it also pins down
    /// the return type of other combinators such as [many()](Many::many) so type inference can
    /// work.
    fn sink(self) -> Parser<'c, ()> {
        self.ignore()
    }
}

impl<'c, T: Parse<'c, private::SinkT>> Sink<'c> for T {}

/// Trait providing the [to_string()](ToString::to_string) combinator.
pub trait ToString<'c>: Parse<'c, String> {
    /// Collect a sequence of [prim@char] values into a [String].
    ///
    /// The combinator itself actually does nothing, it just pins down to `String` the return type
    /// of other combinators such as [many()](Many::many) so type inference can work.
    fn to_string(self) -> Self {
        self
    }
}

impl<'c, T: Parse<'c, String>> ToString<'c> for T {}
