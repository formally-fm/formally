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
use formally_support::*;

/// Fundamental combinators.
///
/// This trait is implemented for any [Parse] type and provides fundamental control-flow
/// combinators.
pub trait Control<'c, Out: 'c>: Parse<'c, Out> {
    /// Map a function on the value returned by a parser.
    ///
    /// The parser is executed and, if successful, the function `f` is applied to the result.
    fn map<F, R>(self, f: F) -> Parser<'c, R>
    where
        F: 'c + Fn(Out) -> R,
        R: 'c,
    {
        Parser::new_with_name(self.name().clone(), move |state: &mut State| {
            Ok(f(self.parse_from(state)?))
        })
    }

    /// Disjunct two parsers.
    ///
    /// The first parser (`self`) is tried and the result returned if successful. If the parser
    /// fails *with a silent rejection* (see
    /// [here](crate::parse#error-diagnostics-and-input-consumption) for details), then the second
    /// parser is tried.
    fn or(self, other: impl Parse<'c, Out>) -> Parser<'c, Out> {
        let name = self.name().or(other.name());
        Parser::new_with_name(name.clone(), move |state: &mut State| {
            let mut first = state.split();
            match self.parse_from(&mut first) {
                Ok(out) => {
                    first.commit();
                    Ok(out)
                }
                Err(_) if !first.has_advanced() => {
                    let mut second = state.split();
                    match other.parse_from(&mut second) {
                        Ok(out) => {
                            second.commit();
                            Ok(out)
                        }
                        Err(_) if !second.has_advanced() => {
                            let Token(token, span) = state.token();
                            error!(
                                state,
                                span,
                                SyntaxIssue::Expected(name.clone(), token.to_string())
                            );
                            Err(DiagnosticEmitted.into())
                        }
                        Err(err) => {
                            second.commit();
                            Err(err)
                        }
                    }
                }
                Err(err) => {
                    first.commit();
                    Err(err)
                }
            }
        })
    }

    /// Turns parse errors into silent rejections.
    ///
    /// Calling [silent()](Control::silent) on a parser makes it suppress any error diagnostic in
    /// case of failures and turn any parse error into a silent rejection. This is useful when using
    /// multiple combinators to build a parser for an atomic token of the language at hand.
    ///
    /// Consider this parser for floating-point numbers.
    /// ```rust
    /// # use formally_io::parse::{*, combinators::*, parsers::*};
    /// # use formally_support::*;
    /// fn float() -> Parser<'static, f32> {
    ///     ascii_digit()
    ///         .many1()
    ///         .to_string()
    ///         .and(char('.'))
    ///         .and(ascii_digit().many1().to_string())
    ///         .silent()
    ///         .map(|((mut int,_),frac)| {
    ///             int.push_str(&frac);
    ///             int.parse()
    ///          }).ok()
    /// }
    ///
    /// let emitter = StdErrEmitter::new();
    /// let result = float().parse(&emitter, "1234/4321");
    ///
    /// assert!(matches!(result, Err(ParseError::Reject)));
    /// ```
    ///
    /// If we do not put a call to [silent()](Control::silent) here, a sequence of digits *not*
    /// followed by a dot would cause an error, while here we wanted floating-point values to be
    /// considered as atomic tokens of our language and therefore not cause an error but just a
    /// silent rejection when not present.
    fn silent(self) -> Parser<'c, Out> {
        Parser::new_with_name(self.name().clone(), move |state: &mut State| {
            let mut split = state.split();
            match self.parse_from(&mut split) {
                Ok(out) => {
                    split.commit();
                    Ok(out)
                }
                Err(_) => Err(ParseError::Reject),
            }
        })
    }

    /// Execute two parsers in order and return a pair with both results
    fn and<T>(self, other: impl Parse<'c, T>) -> Parser<'c, (Out, T)>
    where
        T: 'c,
    {
        Parser::new(move |state: &mut State| {
            let v1 = self.parse_from(state)?;
            state.skip();
            let v2 = other.parse_from(state)?;

            Ok((v1, v2))
        })
    }

    /// Execute two parsers in order and return the result of the second one
    fn then<T>(self, other: impl Parse<'c, T>) -> Parser<'c, T>
    where
        T: 'c,
    {
        Parser::new(move |state: &mut State| {
            self.parse_from(state)?;
            state.skip();
            other.parse_from(state)
        })
    }

    /// Test a predicate function on the result of a parser and emits an error if the test fails.
    ///
    /// This combinator produces an error in case of failure of the predicate.
    /// To reject silently instead, see [only_if()](Control::only_if).
    fn requires<F>(self, test: F, error: impl Into<String>) -> Parser<'c, Out>
    where
        F: 'c + Fn(&Out) -> bool,
    {
        let error = error.into();
        Parser::new_with_name(self.name().clone(), move |state: &mut State| {
            let mut split = state.split();

            let v = self.parse_from(&mut split)?;
            if !test(&v) {
                let span = split.elapsed();
                split.commit();

                error!(state, span, error.clone());
                Err(DiagnosticEmitted.into())
            } else {
                split.commit();
                Ok(v)
            }
        })
    }

    /// Test a predicate function on the result of a parser and reject silently if the test fails.
    ///
    /// This combinator rejects silently in case of failure of the predicate.
    /// To produce an error instead, see [requires()](Control::requires).
    fn only_if<F>(self, test: F) -> Parser<'c, Out>
    where
        F: 'c + Fn(&Out) -> bool,
    {
        Parser::new_with_name(self.name().clone(), move |state: &mut State| {
            let mut new = state.split();
            match self.parse_from(&mut new) {
                Ok(out) if test(&out) => {
                    new.commit();
                    Ok(out)
                }
                _ => Err(ParseError::Reject),
            }
        })
    }

    /// Wrap a parser with a new skip parser.
    fn skipping(self, p: Parser<'static, ()>) -> Parser<'c, Out> {
        Parser::new_with_name(self.name().clone(), move |state: &mut State| {
            let mut new = state.split().skipping(p.clone());
            State::skip(&mut new);
            let out = self.parse_from(&mut new);
            new.commit();
            out
        })
    }

    /// Give a new name to a parser starting from a singular and a plural variant.
    ///
    /// If you already have a [Name] object instead, use [with_name()](Control::with_name).
    fn named(self, singular: impl Into<String>, plural: impl Into<String>) -> Parser<'c, Out> {
        let name = Name::Name {
            singular: singular.into(),
            plural: plural.into(),
        };
        Parser::new_with_name(name.clone(), move |state: &mut State| {
            let mut split = state.split();

            match self.parse_from(&mut split) {
                Ok(out) => {
                    split.commit();
                    Ok(out)
                }
                Err(_) if !split.has_advanced() => {
                    let Token(token, span) = state.token();
                    error!(
                        state,
                        span,
                        SyntaxIssue::Expected(name.clone(), token.to_string())
                    );
                    Err(DiagnosticEmitted.into())
                }
                Err(_) => {
                    let elapsed = split.elapsed();
                    split.commit();
                    trace!(state, elapsed, SyntaxIssue::Trace(name.clone()));
                    Err(DiagnosticEmitted.into())
                }
            }
        })
    }

    /// Set a new [Name] object as name of the parser.
    ///
    /// If you only have strings for the singular and plural variants of the name, you can use
    /// [named()](Control::named) instead.
    fn with_name(self, name: Name) -> Parser<'c, Out> {
        Parser {
            parse: Rc::new(move |state| self.parse_from(state)),
            name,
        }
    }

    /// Execute the parser and return the result together with a  [Span] of the input buffer that
    /// was parsed.
    fn spanned(self) -> Parser<'c, (Out, Span)> {
        Parser::new_with_name(self.name().clone(), move |state: &mut State| {
            let begin = state.location();
            let value = self.parse_from(state)?;
            let end = state.location();
            let span = Span::Span {
                origin: state.origin.clone(),
                begin,
                end,
            };

            Ok((value, span))
        })
    }

    /// Execute the parser and calls [over](Locatable::over) on the result passing the [Span] of the
    /// input buffer that was parsed.
    fn located(self) -> Parser<'c, <Out as Locatable>::Located>
    where
        Out: Locatable,
    {
        self.spanned().map(|(value, span)| value.over(span))
    }

    /// Try to execute the parser and return an [Option] with the result value if successful, or
    /// [None] otherwise.
    fn optional(self) -> Parser<'c, Option<Out>> {
        self.map(Some).or(none())
    }

    /// Execute the parser but replace the result value with a fixed given one.
    fn with_value<T>(self, value: T) -> Parser<'c, T>
    where
        T: 'c + Clone,
    {
        self.map(move |_| value.clone())
    }

    /// Execute the parser but ignore the result value, returning `()` instead.
    fn ignore(self) -> Parser<'c, ()> {
        self.with_value(())
    }

    /// Forces the parser to match the entire input buffer (i.e., to be followed by [eof()].
    fn whole(self) -> Parser<'c, Out> {
        self.and(eof()).map(|(v, _)| v)
    }
}

impl<'c, Out: 'c, T: Parse<'c, Out>> Control<'c, Out> for T {}

/// Trait providing the [unwrap()](Unwrap::unwrap) combinator.
///
/// This trait is implemented for any [Parse] type returning an [Option].
pub trait Unwrap<'c, Out: 'c>: Parse<'c, Option<Out>> {
    /// For a parser returning an [Option], unwrap it with [Option::unwrap].
    fn unwrap(self) -> Parser<'c, Out> {
        Parser::new(move |state: &mut State| {
            self.parse_from(state).map(|o: Option<Out>| o.unwrap())
        })
    }
}

impl<'c, Out: 'c, T: Parse<'c, Option<Out>>> Unwrap<'c, Out> for T {}

/// Trait providing the [ok()](Ok::ok) combinator.
///
/// This trait is implemented for any [Parse] type returning an [Result].
pub trait Ok<'c, Out: 'c, E: 'c + Display>: Parse<'c, std::result::Result<Out, E>> {
    /// For a parser returning a [Result], unwrap it and return the value if `Ok`, or emit
    /// an error diagnostic otherwise displaying the content of the `Err` variant.
    fn ok(self) -> Parser<'c, Out> {
        Parser::new_with_name(self.name().clone(), move |state: &mut State| {
            let (value, span) = self.clone().spanned().parse_from(state)?;

            match value {
                Ok(value) => Ok(value),
                Err(err) => {
                    error!(state, span, "{err}");
                    Err(DiagnosticEmitted.into())
                }
            }
        })
    }
}

impl<'c, Out: 'c, E: 'c + Display, T: Parse<'c, std::result::Result<Out, E>>> Ok<'c, Out, E> for T {}
