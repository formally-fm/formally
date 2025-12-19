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

/// A parser that alwasys succeeds.
pub fn succeed<'c>() -> Parser<'c, ()> {
    Parser::new(|_: &mut State| Ok(()))
}

/// A parser that alwasys fails.
pub fn reject<'c, Out: 'c>() -> Parser<'c, Out> {
    Parser::new(|_: &mut State| Err(ParseError::Reject))
}

/// Same as [reject()] but returning `()` instead of an arbitrary type.
pub fn nothing<'c>() -> Parser<'c, ()> {
    reject()
}

/// Converts a function returning a parser into a parser.
///
/// [lazy()] takes a function of the form `Fn() -> Parser<Out>` and returns a `Parser<Out>` just
/// by invoking the given function, but *during parsing*, i.e., inside the parsing function.
///
/// This means the given function is actually executed each time, and only if, the parser is
/// executed.
///
/// This is useful to implement recursive parsers, see [recursive()].
pub fn lazy<'c, Out, F>(f: F) -> Parser<'c, Out>
where
    Out: 'c,
    F: 'c + Fn() -> Parser<'c, Out>,
{
    Parser::new(move |state: &mut State| f().parse_from(state))
}

/// Utility to create recursive parsers.
///
/// [recursive()] does not actually implement any recursion, but is just an alias for
/// `lazy(f).map(Box::new)`. This is however exactly what we need when building recursive parsers.
///
/// Consider a parser for the following type:
/// ```rust
/// pub enum Expr {
///     Var(String),
///     Plus(Box<Expr>, Box<Expr>),
///     Mult(Box<Expr>, Box<Expr>)
/// }
/// ```
/// The `Expr` fields in the enum are boxed because the type is recursive, as is common in many
/// recursive data types in Rust. Now, to parse such a type, one may write something like this:
///
/// ```rust,no_run
/// # use formally_io::parse::{*, combinators::*, parsers::*};
/// # use formally_support::*;
/// # mod formally {
/// #     pub mod io { pub use formally_io::*; }
/// #     pub mod support { pub use formally_support::*; }
/// # }
/// # pub enum Expr {
/// #     Var(String),
/// #     Plus(Box<Expr>, Box<Expr>),
/// #     Mult(Box<Expr>, Box<Expr>)
/// # }
/// pub fn variable() -> Parser<'static, String> {
///     alphabetic().many1().to_string()
/// }
///
/// pub fn expr() -> Parser<'static, Expr> {
///     variable().map(Expr::Var)
///         .or(expr().and(char('+')).and(expr())
///             .map(|((e1,_), e2)| Expr::Plus(Box::new(e1), Box::new(e2))))
///         .or(expr().and(char('*')).and(expr())
///             .map(|((e1,_), e2)| Expr::Mult(Box::new(e1), Box::new(e2))))
/// }
/// ```
///
/// However, the code above does not work, because `expr()` calls itself in an infinite recursion.
/// What we need is to delay the execution of `expr()` to when the parser will be actually executed.
/// This is exactly the job of [lazy()]. On top of this, [recursive()] boxes the results to ease the
/// common pattern above. The correct code therefore is the following:
///
/// ```rust,no_run
/// # use formally_io::parse::{*, combinators::*, parsers::*};
/// # use formally_support::*;
/// # mod formally {
/// #     pub mod io { pub use formally_io::*; }
/// #     pub mod support { pub use formally_support::*; }
/// # }
/// # pub enum Expr {
/// #     Var(String),
/// #     Plus(Box<Expr>, Box<Expr>),
/// #     Mult(Box<Expr>, Box<Expr>)
/// # }
/// # pub fn variable() -> Parser<'static, String> {
/// #     alphabetic().many1().to_string()
/// # }
/// pub fn expr() -> Parser<'static, Expr> {
///     variable().map(Expr::Var)
///         .or(recursive(expr).and(char('+')).and(recursive(expr))
///             .map(|((e1,_), e2)| Expr::Plus(e1, e2)))
///         .or(recursive(expr).and(char('*')).and(recursive(expr))
///             .map(|((e1,_), e2)| Expr::Mult(e1, e2)))
/// }
/// ```
///
/// If a different smart pointer is needed, one can always use [lazy()] directly.
pub fn recursive<'c: 'c, T, F>(f: F) -> Parser<'c, Box<T>>
where
    T: 'c,
    F: 'c + Fn() -> Parser<'c, T>,
{
    lazy(f).map(Box::new)
}

/// A parser which always succeeds returning a `None`.
pub fn none<'c, Out: 'c>() -> Parser<'c, Option<Out>> {
    Parser::new(move |_: &mut State| Ok(None))
}

/// A parser which always succeeds returning the current parsing location.
pub fn location<'c>() -> Parser<'c, Location> {
    Parser::new(move |state: &mut State| Ok(state.location()))
}

/// A parser that succeeds if and only if the argument fails.
pub fn not<'c: 'c, T>(p: Parser<'c, T>) -> Parser<'c, char>
where
    T: 'c,
{
    Parser::new(move |state: &mut State| {
        let mut split = state.split();
        match p.parse_from(&mut split) {
            Ok(_) => Err(ParseError::Reject),
            Err(_) => any().parse_from(state),
        }
    })
}
