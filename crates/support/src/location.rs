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

use std::{
    borrow::Cow,
    error::Error,
    fmt::{self, Display, Formatter},
    hash::Hash,
    ops::Deref,
    ops::Sub,
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::*;

use derive_more::Display;

/// Wrap any type with location information.
///
/// [Loc] is used to wrap a type to give it location information. It is a simple struct adjoining
/// any given type to an `Option<Span>` and implementing [Located] and [Locatable]. This is meant to
/// be done to types that are not under control and cannot be made to implement the traits directly
/// because of the orphan instance rules, or because giving them a [Span] all the time does not make
/// sense. Otherwise, deriving [Located] and [Locatable] directly using the associated derive
/// macros is preferred.
///
/// It is often controverial to decide whether a [Located] type should compare equal accounting for
/// its span or not. For this reason, [Loc] intentionally does not implement [PartialEq] nor [Eq].
#[derive(Debug, Clone)]
pub struct Loc<T> {
    pub value: T,
    pub span: Option<Span>,
}

impl<T: Default> Default for Loc<T> {
    fn default() -> Self {
        Self {
            value: Default::default(),
            span: Default::default(),
        }
    }
}

impl<T> Loc<T> {
    /// Creates a new [Loc] from a value without any [Span] information.
    pub const fn new(value: T) -> Loc<T> {
        Loc { span: None, value }
    }

    /// Transforms the inner value by applying the given function
    pub fn map<F, R>(self, f: F) -> Loc<R>
    where
        F: FnOnce(T) -> R,
    {
        Loc {
            value: f(self.value),
            span: self.span,
        }
    }
}

impl<T> Located for Loc<T> {
    fn span(&self) -> Option<Span> {
        self.span.clone()
    }
}

impl<T> Locatable for Loc<T> {
    type Located = Loc<T>;

    fn over(self, span: impl Into<Option<Span>>) -> Loc<T> {
        Loc {
            span: span.into(),
            ..self
        }
    }
}

impl<T: Display> Display for Loc<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.value, f)
    }
}

impl<T: Error> Error for Loc<T> {}

impl<T> From<T> for Loc<T> {
    fn from(value: T) -> Self {
        Loc::new(value)
    }
}

impl<T> Deref for Loc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.value
    }
}

/// Tracks the origin of a set of source locations
///
/// This type is used as a component of a [Span] to tell the origin of a source file
/// (e.g. an actual file, or stdin, or a buffer, etc.). This is mainly useful to give show error
/// messages to the user.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq)]
pub enum Origin {
    /// The origin of the source locations is unknown
    #[default]
    Unknown,
    /// The origin of the source locations is an in-memory buffer or string
    Buffer,
    /// The origin of the source locations is the standard input stream
    StdIn,
    /// The origin of the source locations is a file at the given path
    Path(Arc<PathBuf>),
}

impl Display for Origin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Origin::Unknown => f.write_str("<unknown>"),
            Origin::StdIn => f.write_str("<stdin>"),
            Origin::Buffer => f.write_str("<buffer>"),
            Origin::Path(path) => Display::fmt(&path.display(), f),
        }
    }
}

impl<T: AsRef<Path>> From<T> for Origin {
    fn from(value: T) -> Self {
        Origin::Path(Arc::new(PathBuf::from(value.as_ref())))
    }
}

/// Represent a position in a source file.
///
/// [Location] represents the position of a single character or token in a source file, given by its
/// `position` which is the actual index in the corresponding buffer, and a pair of `line` and
/// `column` information.
///
/// Line and column information start from zero, but the [Display] instance of [Location] and [Span]
/// show line numbers to the user as starting from one.
#[derive(Debug, Clone, Copy, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Location {
    /// The index of this location in the corresponding buffer
    pub position: usize,
    /// The line number corresponding to this location
    pub line: usize,
    /// The column number corresponding to this location
    pub column: usize,
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.column)
    }
}

impl Sub for Location {
    type Output = usize;

    fn sub(self, rhs: Self) -> usize {
        self.position - rhs.position
    }
}

/// Track an interval between two locations in a source file.
///
/// [Span] tracks an interval in a source file, represented either as a pair of `begin`/`end`
/// [Location] objects in the [Span::Span] variant, or as the [Span::Whole] variant that represents
/// the entire source file under consideration.
///
/// All the components in `formally` try hard to preserve locations and spans across the board, in
/// order to give users informative error messages even for errors originating quite far from the
/// parsers.
///
/// This means that any type that can be created even indirectly by parsing something from the user
/// should probably contain a [Span] and implement at least the [Located] trait, and maybe also
/// [Locatable].
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Span {
    /// The [Span] represents the whole source file at the given [Origin].
    Whole(Origin),
    /// The [Span] represents the interval between `begin` (included) and `end` (excluded) at the
    /// given [Origin].
    Span {
        /// The origin of the span.
        origin: Origin,
        /// The starting position of the interval (included).
        begin: Location,
        /// The end of the interval (excluded).
        end: Location,
    },
}

impl Default for Span {
    /// The default [Span] is `Span::Whole(Origin::Unknown)`
    fn default() -> Self {
        Span::Whole(Origin::default())
    }
}

impl Span {
    /// Creates a default [Span], i.e. `Span::Whole(Origin::Unknown)`
    pub fn new() -> Span {
        Span::default()
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Span::Whole(origin) => Display::fmt(origin, f),
            Span::Span { origin, begin, end } => {
                if end.column > begin.column + 1 {
                    write!(
                        f,
                        "{}:[{}:{}, {}:{})",
                        origin,
                        begin.line + 1,
                        begin.column,
                        end.line + 1,
                        end.column
                    )
                } else {
                    write!(f, "{}:{}:{}", origin, begin.line + 1, begin.column)
                }
            }
        }
    }
}

/// Types that track a [Span].
///
/// [Located] is a small trait to get a [Span] from types that track span information. The [Span] is
/// returned in an [Option] because even types that track spans very precisely may not have such
/// information available in the first place, probably when constructed by hand instead of being
/// parsed.
///
/// [Located] can be automatically derived (see the corresponding proc-macro for details).
pub trait Located {
    /// Gets the [Span] tracked by the type.
    fn span(&self) -> Option<Span>;
}

impl Located for Option<Span> {
    fn span(&self) -> Option<Span> {
        self.clone()
    }
}

/// Add or set a [Span] to a type.
///
/// [Locatable] is for [Located] types that support changing their tracked [Span], or for types that
/// can be turned into [Located] types. The [Locatable::over] method is a builder method used to
/// create a new object with a different [Span], and the `Located` associated type tell the type of
/// the result.
///
/// Example:
/// ```rust,ignore
/// let term = smt::Term::new(...).over(span);
/// ```
///
/// [Locatable] can be automatically derived (see the corresponding proc-macro for details).
pub trait Locatable: Sized {
    type Located: Located;

    /// Turns `self` into an object of type `Self::Located` tracking the new span.
    fn over(self, span: impl Into<Option<Span>>) -> Self::Located;
}

impl Locatable for Option<Span> {
    type Located = Option<Span>;

    fn over(self, span: impl Into<Option<Span>>) -> Self::Located {
        span.into()
    }
}

/// A string associated with its source span.
///
/// [Identifier] just holds a `Cow<'a, str>` together with a [Span]. It is used in `formally`
/// whenever an identifier coming from an origin source code has to be stored or passed as argument.
/// Using [Cow] allows to avoid unnecessary clones when identifiers are passed directly as arguments
/// from string slices.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Display, Located, Locatable)]
#[display("{name}")]
pub struct Identifier<'a> {
    name: Cow<'a, str>,
    span: Option<Span>,
}

impl<'a> Identifier<'a> {
    pub const fn new(name: &'a str) -> Self {
        Identifier {
            name: Cow::Borrowed(name),
            span: None,
        }
    }

    /// Return a reference to the stored name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Turn the identifier into its inner string.
    pub fn into_string(self) -> String {
        self.name.into_owned()
    }

    pub fn into_owned(self) -> Identifier<'static> {
        match self.name {
            Cow::Borrowed(name) => Identifier {
                name: Cow::Owned(name.to_string()),
                span: self.span,
            },
            Cow::Owned(name) => Identifier {
                name: Cow::Owned(name),
                span: self.span,
            },
        }
    }
}

impl Deref for Identifier<'_> {
    type Target = str;

    fn deref(&self) -> &str {
        &self.name
    }
}

impl From<String> for Identifier<'_> {
    fn from(name: String) -> Self {
        Identifier {
            name: Cow::from(name),
            span: None,
        }
    }
}

impl<'a> From<&'a str> for Identifier<'a> {
    fn from(name: &'a str) -> Self {
        Identifier::new(name)
    }
}
