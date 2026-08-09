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

//! A little parsing combinators library.
//!
//! # Overview
//!
//! The `parse` module provides a *parser combinators library* as a facility to parse text
//! everywhere in `formally`. Parsing combinators are a technique for parsing which, instead of
//! formalizing the grammar separately and having some tool produce the parser code, you write
//! parsers directly in your source code by composing little simple parsing functions together into
//! more complex ones.
//!
//! The approach comes from the world of functional languages, and Rust is a great fit for this
//! paradigm. Other mature parser combinator libraries exist for Rust, such as
//! [Nom](https://docs.rs/nom/8.0.0/nom/). However, the library provided here are specifically
//! crafted for `formally` and provide a greater integration with the rest of the framework.
//!
//! The `parse` module is designed around the [Parser] struct which stores a parsing function (any
//! closure of type `Fn(&mut State) -> Result<Out>`) and the name of the parser (used in the
//! diagnositcs). Parsers can be created by providing such a parsing function, by calling one of the
//! functions in the [parsers] submodule, or by composing them from simpler parsers by using
//! [Parser]'s methods such as [map()](Control::map), [or()](Control::or) or many others.
//!
//! ## Example
//!
//! As an example, the following function produces a parser that parses any string of decimal digits
//! as an integer number, returning an `i32`.
//! ```
//! # mod formally { pub mod io { pub use formally_io::*; }}
//! use formally::io::parse::{*, combinators::*, parsers::*};
//!
//! fn integer() -> Parser<'static, i32> {
//!     ascii_digit() // match any character that is an ascii digit, i.e. [0-9]
//!         .many1() // match any sequence of one or more ascii digits
//!         .to_string() // convert such a sequence of characters into a string
//!         .map(|s| s.parse()) // call the `str::parse` method to convert the string to `i32`
//!         .ok() // unwrap the `Result<i32, E>` returned by `str::parse`, emits error on `Err`
//!         .named("integer number", "integer numbers") // gives a name to this parser
//! }
//! ```
//!
//! The lifetime parameter of [Parser] is the lifetime of things captured by the construction of the
//! parser, such as in cases where your parser depend on external parameters that are borrowed. In
//! this case, we do not capture anything, so we specified the `'static` lifetime.
//!
//! The produced parsers are designed to give detailed diagnostics. One ingredient to do that is to
//! keep track of the human-understandable name of the entity being parsed to use it in errors and
//! warnings. This is done above by the [named()](Control::named) combinator applied at
//! the end, which takes both a singular and a plural form of the name, each used in different
//! situations.
//!
//! ## Using parsers
//!
//! Parsers can be used by calling the [parse()](Parse::parse) method. The method takes a [Source]
//! object, which can be created from strings, from [File] objects, or from [PathBuf] objects
//! representing a filesystem path to read a file from. The method also takes an [Emitter] used to
//! emit diagnostics.
//!
//! For example:
//!
//! ```rust
//! # mod formally {
//! #     pub mod io { pub use formally_io::*; }
//! #     pub mod support { pub use formally_support::*; }
//! # }
//! #
//! # use formally::io::parse::{*, parsers::*, combinators::*};
//! # use formally::support::*;
//! #
//! # fn integer() -> Parser<'static, i32> {
//! #     ascii_digit().many1().to_string().map(|s| s.parse()).ok()
//! #         .named("integer number", "integer numbers")
//! # }
//! let emitter = StdErrEmitter::new();
//!
//! let result = integer().parse(&emitter, "1234");
//!
//! assert!(matches!(result, Ok(1234)));
//!
//! let result = integer().parse(&emitter, "hello");
//!
//! assert!(result.is_err());
//! ```
//!
//! The second invocation of `parse` will emit a diagnostic through the emitter. In this case we
//! used [StdErrEmitter], so we get this message printed to the error stream of the process:
//! ```text
//! <buffer>:[1:0, 1:5):error: expected integer number, found `hello`
//! ```
//!
//! We can note several components in this error message:
//! 1. `<buffer>` is a representation of the [Source] used to parse, which in this case is an
//!    in-memory string without an associated file name.
//! 2. `[1:0, 1:5)` is the [Span] associated with the diagnostic
//! 3. in `expected integer number`, the name of the parser given to the [named()](Control::named)
//!    combinator is appropriately shown in the error message
//!
//! ## Error diagnostics and input consumption
//!
//! There are two different error values a parser can return when rejecting its input:
//! [ParseError::Reject], and [Parse::Error(DiagnosticEmitted)](ParseError::Error). Many
//! combinators, including [or()](Control::or) and the family of
//! [many()](Many::many) and [sep_by()](Many::sep_by), work on the basis
//! of a simple agreement: [Parse::Error(DiagnosticEmitted)](ParseError::Error) is returned *if and
//! only if* the parser has *consumed* some input, and in this case an *error* diagnostic must have
//! been emitted. *Vice versa*, [ParseError::Reject] is a *silent* rejection, because no error
//! diagnostic must have been emitted, and no input consumed. This protocol is automatically
//! observed by all combinators provided here, and a user of those combinators does not need to
//! worry about it. However, it is useful to keep this in mind when understanding the behavior of
//! combinators such as [or()](Control::or) and [grouped()](Control::silent),
//! or when trying to tune the error diagnostics produced by a parser.
//!
//! ## Skipping whitespaces, comments, etc.
//!
//! Most languages out there are space insensitive, meaning they allow separating two tokens with an
//! arbitrary amount of white space. Most also support some form syntax to write comments, which
//! simple parsers usually want to discard. Handling these two elements explicitly when using
//! combinators can be cumbersome, so `formally::io` provides a way to declare once what to skip
//! when applying a parser.
//!
//! The [skipping()](Control::skipping) method accepts a parser of type `Parser<'static, ()>` that
//! is meant to represent syntactic elements that, when recognised, must be skipped and ignored. The
//! parser set by [skipping()](Control::skipping) is called the "skip parser". The looping
//! combinators, such as [many_while_counting()](Many::many_while_counting) and its derived
//! combinators [many()](Many::many), [many1()](Many::many1), etc., invoke the skip parser at
//! each iteration. The sequence combinators [and()](Control::and) and [then()](Control::then)
//! invoke the skip parser in the middle of the two sequenced parsers.
//!
//! The result is that one can define a parser independently of what comes in the middle of tokens,
//! and then provide a skip parser that takes care of it.
//!
//! In the following example, we write a combinator `tuple_of`, which takes a parser for single
//! elements and parses a tuple of elements separated by commas and enclosed in parens, while
//! ignoring whitespaces between tokens and C++/Rust-style comments starting with `//` until a
//! newline.
//!
//! ```
//! # mod formally {
//! #     pub mod io { pub use formally_io::*; }
//! #     pub mod support { pub use formally_support::*; }
//! # }
//! #
//! # use formally::io::parse::{*, parsers::*, combinators::*};
//! # use formally::support::*;
//! #
//! # fn integer() -> Parser<'static, i32> {
//! #     ascii_digit().many1().to_string().map(|s| s.parse()).ok()
//! #         .named("integer number", "integer numbers")
//! # }
//! fn comment() -> Parser<'static, ()> {
//!     text("//") // match the start of the comment
//!         .then(any().only_if(|c| *c != '\n').skip()) // and then anything but newlines
//!         .then(char('\n')) // and then a newline
//!         .ignore() // we don't care about the content of the comment
//! }
//!
//! fn tuple_of<'c, T: 'c>(element: Parser<'c, T>) -> Parser<Vec<T>> {
//!     let to_skip = // we skip...
//!         whitespace() // ...either a whitespace character...
//!             .ignore() // (turn `Parser<char>` into `Parser<()>`)
//!             .or(comment()) // ...or a comment...
//!             .skipping(nothing()); // ...in turn skipping nothing in the meantime
//!
//!     // the following parses the tuple itself
//!     element // match an element
//!         .sep_by1(char(',')) // one or more times separated by a comma
//!         .parens() // everything inside parens
//!         .skipping(to_skip) // everything while skipping whitespaces and comments
//! }
//!
//! let input = "
//!     (1, 2,   3, // a comment
//!     4, 5)
//! ";
//!
//! let emitter = StdErrEmitter::new();
//!
//! let result = tuple_of(integer()).parse(&emitter, input);
//!
//! assert_eq!(result.unwrap(), vec![1,2,3,4,5])
//! ```
//! Note that the skip parser has to match *one* occurrence of the things to skip. During parsing,
//! an unbounded number of occurrences of the skip parser will be ignored.
//!
//! ## Writing new combinators
//!
//! If existing parsers and combinators are not enough, new parsers of type `Parser<T>` can be
//! constructed by providing an arbitrary parsing function of the form `Fn(&mut State) ->
//! Result<T>`. The [State] type tracks relevant information about the current state of the parsing
//! such as the current position in the buffer, the selected emitter, and the current skip parser.
//! See the documentation of [State] for details.

pub mod combinators;
pub mod parsers;

use combinators::*;

use crate::parse::parsers::*;
use formally_support::*;

use itertools::{Itertools, concat};
use std::{
    borrow::Cow,
    fmt::{self, Debug, Display, Formatter},
    fs,
    fs::File,
    io::{self, Read},
    path::{Path, PathBuf},
    rc::Rc,
    str::CharIndices,
    sync::Arc,
};
use thiserror::Error;

/// Type representing the source of the parsing buffer
///
/// [Source] keeps track of the provenance of the buffer that is currently being parsed.
/// Sources can either come from an in-memory buffer ([Source::Buffer]), a [File] ([Source::File]),
/// or the path to a file [Source::Path]. Parsing from the latter option is preferred when possible,
/// because the file name can be displayed to the user in the diagnostics. The [Source::File]
/// variant can also keep track of the file path if available.
pub enum Source<'s> {
    /// The source is a file path.
    Path(Cow<'s, Path>),
    /// The source is a [File].
    File(File, Option<Cow<'s, Path>>),
    /// The source is an in-memory buffer.
    Buffer(Cow<'s, str>),
}

impl<'s> Source<'s> {
    /// Constructs a [Source] from a `& Path` or a [PathBuf].
    pub fn from_path(path: impl Into<Cow<'s, Path>>) -> Self {
        Source::Path(path.into())
    }

    /// Constructs a [Source] from a `&str` or a [String].
    pub fn from_buffer(buffer: impl Into<Cow<'s, str>>) -> Self {
        Source::Buffer(buffer.into())
    }

    /// Constructs a [Source] from a [File].
    pub fn from_file(file: File) -> Self {
        Self::File(file, None)
    }

    /// Constructs a [Source] from a [File] with an associated path.
    pub fn from_file_and_path(file: File, path: impl Into<Cow<'s, Path>>) -> Self {
        Self::File(file, Some(path.into()))
    }

    /// Retrieves the contents of the [Source].
    ///
    /// The method behaves as follows:
    /// 1. If the [Source] is [Source::Buffer], the buffer it is returned as-is.
    /// 2. If the [Source] is [Source::File], the file is read until the end.
    /// 3. If the [Source] is [Source::Path], the file is open and read until the end.
    ///
    /// The [Emitter] is used to emit error diagnostics in case the file cannot be read.
    pub fn content(self) -> Result<Cow<'s, str>> {
        let origin = self.origin();
        match self {
            Source::Path(path) => match fs::read_to_string(path) {
                Ok(content) => Ok(Cow::from(content)),
                Err(err) => {
                    error!(Span::Whole(origin), "unable to read file: {err}");
                    Err(DiagnosticEmitted.into())
                }
            },
            Source::File(mut file, _) => {
                let mut data = String::new();
                match file.read_to_string(&mut data) {
                    Ok(_) => Ok(Cow::from(data)),
                    Err(err) => {
                        error!(Span::Whole(origin), "unable to read file: {err}");
                        Err(DiagnosticEmitted.into())
                    }
                }
            }
            Source::Buffer(buffer) => Ok(buffer),
        }
    }

    /// Retrieves the [Origin] of this [Source].
    pub fn origin(&self) -> Origin {
        match self {
            Source::Path(path) | Source::File(_, Some(path)) => {
                Origin::Path(Arc::new(path.clone().into_owned()))
            }
            Source::File(_, None) => Origin::Unknown,
            Source::Buffer(_) => Origin::Buffer,
        }
    }
}

impl<'a> From<&'a Path> for Source<'a> {
    fn from(path: &'a Path) -> Self {
        Source::from_path(path)
    }
}

impl From<PathBuf> for Source<'_> {
    fn from(path: PathBuf) -> Self {
        Source::from_path(path)
    }
}

impl<'a> From<&'a str> for Source<'a> {
    fn from(buffer: &'a str) -> Self {
        Source::from_buffer(buffer)
    }
}

impl From<String> for Source<'_> {
    fn from(buffer: String) -> Self {
        Source::from_buffer(buffer)
    }
}

impl From<File> for Source<'_> {
    fn from(file: File) -> Self {
        Source::from_file(file)
    }
}

/// A cursor pointing at the current position in the source buffer
///
/// [View] points at the current position in the source buffer during parsing and behave as an
/// iterator of characters able to retrieve the next one with the [next()](Iterator::next) method.
/// The [location()](View::location) method retrieves the current location.
///
/// Using [View] should be useful only when writing one's own parsing function. See also the
/// documentation of [State] in this case.
#[derive(Clone)]
pub struct View<'b> {
    buffer: &'b str,
    iterator: CharIndices<'b>,
    location: Location,
}

impl<'b> View<'b> {
    /// Construct a new [View] pointing to a buffer.
    ///
    /// Explicitly constructing new [View] objects should not be needed, even when writing custom
    /// parsing functions. Usually, a [View] can be retrieved from the reference to the current
    /// parsing [State].
    pub fn new(buffer: &'b str) -> View<'b> {
        View {
            buffer,
            iterator: buffer.char_indices(),
            location: Location::default(),
        }
    }

    /// Return the [Location] of the current [View].
    pub fn location(&self) -> Location {
        self.location
    }
}

impl Iterator for View<'_> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        if let Some((_, ch)) = self.iterator.next() {
            self.location.position = self.iterator.offset();
            self.location.column += 1;
            if ch == '\n' {
                self.location.line += 1;
                self.location.column = 0;
            }

            Some(ch)
        } else {
            None
        }
    }
}

/// Keep track of the current state of the parsing process.
///
/// [State] objects contains everything needed to know when writing a parsing function.
///
/// # How to write a custom parsing function
///
/// Parsing functions for parsers of type `Parser<T>` are functions or closures of the form
/// `Fn(&mut State) -> Result<T>`. They accept a mutable reference to the current [State] and return
/// the result of the parse or an error, possibly emitting a diagnostic in the latter case.
///
/// Before reading further, be sure to read the [module-level documentation](crate::parse).
///
/// [State] provide the following functionalities to a parsing function:
/// 1. the current [View], from which the current [Location] and the next character in the buffer
///    can be retrieved.
/// 2. the [Origin] of the source buffer.
/// 3. a [BatchEmitter] linked to the [Emitter] selected by the call to [parse()](Parser::parse).
/// 4. the skip parser, usable through the [skip()][State::skip] method.
///
/// The following creates a parser that recognises integer numbers, as in the example
/// [here](crate::parse), but using a custom parsing function instead of combinators.
///
/// ```
/// # mod formally {
/// #     pub mod io { pub use formally_io::*; }
/// #     pub mod support { pub use formally_support::*; }
/// # }
/// #
/// # use formally::io::parse::{*, parsers::*, combinators::*};
/// # use formally::support::*;
/// #
/// pub fn integer() -> Parser<'static, i32> {
///     Parser::new(move |state: &mut State| {
///         let mut split = state.split();
///         let mut number = String::new();
///
///         while let Some(ch) = split.view.next() && ch.is_ascii_digit() {
///             number.push(ch);
///         }
///
///         match number.parse() {
///             Ok(number) => {
///                 split.commit();
///                 Ok(number)
///             }
///             Err(err) if split.has_advanced() => {
///                 error!(&split.emitter, split.elapsed(), "{err}");
///                 split.commit();
///                 Err(DiagnosticEmitted.into())
///             }
///             Err(_) => Err(ParseError::Reject)
///         }
///     })
/// }
///
/// let emitter = StdErrEmitter::new();
///
/// let result = integer().parse(&emitter, "1234");
///
/// assert!(matches!(result, Ok(1234)));
/// ```
///
/// There are many ingredients to explain here. At the start of the function, the state is "split".
/// [split()](State::split) returns a cheap clone of the state that is linked to its "parent" and
/// can commit any changes to it later using the [commit()](State::commit) method. The latter sets
/// to the parent the position of the split state and emits to the original emitter all the
/// diagnostics emitted to the split state.
///
/// Here, we split the state for the following reason. As explained in the section of the
/// [module-level documentation](crate::parse#error-diagnostics-and-input-consumption) about parsing
/// errors and input consumptions, we must make sure that any input is consumed, *i.e.*
/// [next()][Iterator::next] is called on the [View] *if and only if* we either succeed or we emit
/// an error diagnostic. In our example, we split the state and get the characters from the split
/// one, so we are sure the original will not advance until we explicitly call
/// [commit()](State::commit), which is called only later in case of successful parsing or if we
/// reject with an error instead of silently.
///
/// When to emit an error and when to reject silenty is totally up to the specific parser at hand.
/// In this case, we reject silently when there are no digits at all, to signal that the integer
/// was "just not there", as opposed to a "wrong integer".
///
/// In any case, splitting the state helps to adopt the convention, avoiding to accidentally
/// consuming input when not appropriate. Note that [split()](State::split) takes a mutable
/// reference, so the parent state is unusable while the split state is alive.
/// [commit()](State::commit) moves `self`, so after that the parent state becomes available again.
/// Moreover, no diagnostic is emitted to the parent's emitter until the [commit()](State::commit)
/// method is called. The methods [has_advanced()](State::has_advanced) and
/// [elapsed()][State::elapsed] help knowing when the split state has advanced w.r.t. its parent and
/// of how much.
pub struct State<'b, 'o, 'e, 'p> {
    pub view: View<'b>,
    pub origin: &'o Origin,
    pub emitter: BatchEmitter<'e>,
    skip: Parser<'static, ()>,
    parent: Option<&'p mut View<'b>>,
}

impl<'b, 'o, 'e, 'p> State<'b, 'o, 'e, 'p> {
    /// Construct a new [State]. Calling this explicitly should never be necessary.
    pub fn new(buffer: &'b str, origin: &'o Origin) -> State<'b, 'o, 'static, 'p> {
        State {
            origin,
            view: View::new(buffer),
            emitter: BatchEmitter::new(&*Diagnostic::emitter()),
            skip: ascii_whitespace().ignore(),
            parent: None,
        }
    }

    /// Get the current location from the [State]'s [View].
    pub fn location(&self) -> Location {
        self.view.location
    }

    /// Return a span covering how much the parsing position has been advanced w.r.t. the parent
    /// [State] after the call to [split()](State::split). If there is no parent, returns
    /// `None`.
    pub fn elapsed(&self) -> Option<Span> {
        let Some(parent) = &self.parent else {
            return None;
        };

        Some(Span::Span {
            origin: self.origin.clone(),
            begin: parent.location,
            end: self.view.location,
        })
    }

    /// Tell whether the parsing position has been advanced w.r.t. the parent [State] after the
    /// call to [split()](State::split). If there is no parent, returns `false`.
    pub fn has_advanced(&self) -> bool {
        if let Some(parent) = &self.parent {
            self.view.location != parent.location
        } else {
            false
        }
    }

    /// Return a new [State] object with a different skip parser.
    pub fn skipping<T: 'static>(self, skip: Parser<'static, T>) -> State<'b, 'o, 'e, 'p> {
        State {
            skip: skip.ignore(),
            ..self
        }
    }

    /// Ignore and skip an unbounded number of matches of the skip parser.
    pub fn skip(&mut self) {
        self.skip.clone().skip().parse_from(self).ok();
    }

    /// Return a slice of the buffer betwen the current position and the next match of the skip
    /// parser.
    ///
    /// This is useful for producing error messages. Suppose we are parsing a programming language,
    /// we asked for a parenthesis but the keyword `while` was found. We want to produce a useful
    /// error message such as `expected '(', found 'while'`, but we only have the current
    /// character which is `w`. If the current skip parser skips whitespaces, we can call
    /// [token()](State::token) to get a slice of all the characters up to the next whitespace,
    /// thus obtaining a slice pointing to the string `while`, that we can use to produce the error
    /// message.
    pub fn token(&mut self) -> Token<'b> {
        let begin = self.view.clone();
        let skip = self.skip.clone();
        let mut split = self.split();

        (not(skip).skip().skipping(nothing()).parse)(&mut split).ok();
        Token(
            &split.view.buffer[begin.location.position..split.view.location.position],
            split.elapsed().unwrap(),
        )
    }

    /// Split the state. See the documentation for [State] for details.
    pub fn split<'p2>(&'p2 mut self) -> State<'b, 'o, 'p2, 'p2> {
        State {
            origin: self.origin,
            view: self.view.clone(),
            parent: Some(&mut self.view),
            emitter: BatchEmitter::new(&self.emitter),
            skip: self.skip.clone(),
        }
    }

    /// Commit a split state. See the documentation for [State] for details.
    ///
    /// If `self` has been split from a parent state, the parent's view is set to `self.view`.
    /// Moreover, the diagnostics emitted to `self` from the last split are emitted with the
    /// parent's emitter.
    pub fn commit(self) {
        if let Some(parent) = self.parent {
            *parent = self.view;
        }
        self.emitter.commit()
    }
}

/// The type returned by [State::token()].
pub struct Token<'s>(&'s str, pub Span);

impl Emitter for State<'_, '_, '_, '_> {
    fn emit(&self, level: Level, diag: Diagnostic) {
        self.emitter.emit(level, diag)
    }

    fn note(&self, kind: NoteKind, note: Diagnostic) {
        self.emitter.note(kind, note)
    }
}

impl Iterator for State<'_, '_, '_, '_> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        self.view.next()
    }
}

/// The name of a parser.
///
/// [Name] keeps track of the name of a parser, to be shown by combinators in error messages.
#[derive(Debug, Clone)]
pub enum Name {
    /// The parser has no set name.
    None,
    /// The parser has a name with a singular and a plural variant.
    Name { singular: String, plural: String },
    /// The parser is a disjunction of other parsers, each with its own [Name].
    ///
    /// Names of this kind are usually composed by the [or()](Control::or) combinator.
    Or { names: Vec<Name> },
}

impl Name {
    /// Format the name in the correct variant depending on the given cardinality.
    pub fn display(&self, cardinality: usize) -> String {
        match self {
            Name::None => match cardinality {
                1 => "element",
                _ => "elements",
            }
            .to_string(),
            Name::Name { singular, plural } => {
                if cardinality == 1 { singular } else { plural }.to_string()
            }
            Name::Or { names } => names
                .iter()
                .map(|n| n.display(cardinality).to_string())
                .join(if names.len() == 2 { " or " } else { ", or " }),
        }
    }

    /// Compose a disjunction of two [Name]s merging subnames that are already disjunctions,
    /// in order to maintain a flat structure.
    pub fn or(&self, other: &Name) -> Name {
        match (self.clone(), other.clone()) {
            (Name::Or { names: lnames }, Name::Or { names: rnames }) => Name::Or {
                names: concat(vec![lnames, rnames]),
            },
            (Name::Or { names }, rn) => Name::Or {
                names: concat(vec![names, vec![rn]]),
            },
            (ln, Name::Or { names }) => Name::Or {
                names: concat(vec![vec![ln], names]),
            },
            (ln, rn) => Name::Or {
                names: vec![ln, rn],
            },
        }
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(&self.display(1))
    }
}

#[derive(Debug, Clone, Error)]
enum SyntaxIssue {
    #[error("expected {0}, found `{1}`")]
    Expected(Name, String),
    #[error("unexpected end of input")]
    UnexpectedEOF,
    #[error(
        "at least {min} {what} {minverb} required, but {found} {foundverb} found",
        what = name.display(*.min),
        minverb = if *.min == 1 { "is" } else { "are" },
        foundverb = if *.found == 1 { "was" } else { "were" },
    )]
    ManyButNotEnough {
        min: usize,
        found: usize,
        name: Name,
    },
    #[error("in this {0}")]
    Trace(Name),
}

/// Error type used in parsing functions.
///
/// See [How to write a custom parsing function](State#how-to-write-a-custom-parsing-function) for
/// an explanation of when to use [ParseError::Reject] as opposed to [ParseError::Error].
/// The third variant, [ParseError::IOError], is used by [Source::content()] to signal an I/O error
/// when reading a source file and should not be needed in custom parsing functions (unless of
/// course the parsing function performs actual I/O operations).
#[derive(Debug, Clone)]
pub enum ParseError {
    /// A silent rejection
    Reject,
    /// A parsing error
    Error(DiagnosticEmitted),
    /// An I/O error
    IOError(Rc<io::Error>),
}

impl From<DiagnosticEmitted> for ParseError {
    fn from(_value: DiagnosticEmitted) -> Self {
        ParseError::Error(DiagnosticEmitted)
    }
}

impl From<io::Error> for ParseError {
    fn from(value: io::Error) -> Self {
        ParseError::IOError(Rc::new(value))
    }
}

/// Exports a parsing-specific [Result] type.
pub mod result {
    /// Result type for parsing functions.
    pub type Result<T> = std::result::Result<T, super::ParseError>;
}

use result::Result;

/// The main type for parsers.
///
/// The [Parser] type stores a parsing function and its name.
pub struct Parser<'c, Out> {
    parse: Rc<dyn 'c + Fn(&mut State) -> Result<Out>>,
    name: Name,
}

/// The [Parse] trait abstractly models parsers.
///
/// The trait is implemented by the [Parser] type and is there mainly to support extension traits
/// providing combinator methods, such as [Control] or [Many]. The need to
/// implement it directly should be rare. Instead, when writing custom combinators, it is advisable
/// to write them accepting arbitrary [Parse] types instead of concrete [Parser] instances, in order
/// to make the combinator available from other extension traits implementing other combinators.
///
/// Example:
/// ```
/// # use formally_io::parse::{*, combinators::*, parsers::*};
/// # use formally_support::*;
/// pub trait MyCombinators<'c>: Parse<'c, i32> {
///     fn multiplied(p: impl Parse<'c, i32>) -> Parser<'c, i32> {
///         p.map(|v| v * 2)
///     }
/// }
/// ```
pub trait Parse<'c, Out>: 'c + Clone + Sized {
    /// Get the name of the parser
    fn name(&self) -> &Name;

    /// Invoke the parser starting from the given [State]
    fn parse_from(&self, state: &mut State) -> Result<Out>;

    /// Invoke the parser on the given [Source] using the given [Emitter] for diagnostics.
    ///
    /// This is the main entry point for using parsers. See the
    /// [module-level documentation](crate::parse) for details.
    fn parse<'i>(&self, source: impl Into<Source<'i>>) -> Result<Out> {
        let source = source.into();
        let origin = source.origin();
        let content = source.content()?;

        let mut state = State::new(&content, &origin);
        let result = self.parse_from(&mut state);
        state.commit();

        result
    }
}

impl<Out> Clone for Parser<'_, Out> {
    fn clone(&self) -> Self {
        Parser {
            parse: self.parse.clone(),
            name: self.name.clone(),
        }
    }
}

impl<'c, Out: 'c> Parser<'c, Out> {
    /// Create a new [Parser] from the given parsing function.
    pub fn new(p: impl 'c + Fn(&mut State) -> Result<Out>) -> Parser<'c, Out> {
        Parser::new_with_name(Name::None, p)
    }

    /// Create a new [Parser] from the given parsing function and the given name.
    pub fn new_with_name(
        name: Name,
        p: impl 'c + Fn(&mut State) -> Result<Out>,
    ) -> Parser<'c, Out> {
        Parser {
            parse: Rc::new(p),
            name,
        }
    }
}

impl<'c, Out: 'c> Parse<'c, Out> for Parser<'c, Out> {
    fn name(&self) -> &Name {
        &self.name
    }

    fn parse_from(&self, state: &mut State) -> Result<Out> {
        (self.parse)(state)
    }
}

/// Trait for types that know how to parse themselves.
pub trait Parsable<'c>: 'c + Sized {
    /// Get a parser for the type.
    fn parser() -> Parser<'c, Self>;
}
