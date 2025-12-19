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

use crate::*;

use std::{
    cell::RefCell,
    fmt::{self, Debug, Display},
    sync::Mutex,
};

use thiserror::Error;

/// Severity level of a diagnostic.
///
/// Note that [Level::Internal] is supposed to indicate some internal error (e.g. a violated
/// precondition).
#[derive(Debug, Clone, Copy, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    /// Debug messages that should be usually hidden from the user
    Debug = 0,
    /// Non-erroneus conditions that the user should pay attention to
    Warning = 1,
    /// Errors
    #[default]
    Error = 2,
    /// Internal errors (e.g., a violated precondition).
    Internal = 3,
}

impl Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Level::Debug => "debug",
            Level::Warning => "warning",
            Level::Error => "error",
            Level::Internal => "internal error",
        };
        f.write_str(msg)
    }
}

/// Kind of note to emit in [Emitter::note]
#[derive(Debug, Clone, Copy, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NoteKind {
    /// Note with any kind of additional information attached to a diagnostic
    #[default]
    Note = 0,
    /// Note carrying backtrace information on the provenance of a diagnostic
    Trace = 1,
}

/// Tag error type to signal that a diagnostic has been emitted
///
/// See the [Result] documentation for details.
#[derive(Debug, Clone, Copy, Error)]
pub struct DiagnosticEmitted;

impl Display for DiagnosticEmitted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "see previous error messages")
    }
}

/// Trait for types that can emit themselves as diagnostics.
///
/// Even in the error handling framework set up in `formally`, in some cases the best design for a
/// function is to return a classic `Result<T, E>` for some specific error type `E` and postpone the
/// emission of diagnostics. In this case one can embedd in the error type all the necessary
/// information to generate the diagnostics later, and implement [Emit] for the error type.
///
/// Then, the error type can be used as any other, but in addition, [DiagnosticEmitted] implements
/// `From<E>` for any `E` that implement [Emit], and the conversion emits the diagnostics. This
/// means that one can very conveniently apply to `E` the `?` operator in a function returning
/// `Result<T, DiagnosticEmitted>`, if and when one desires to finally emit the diagnostics.
///
/// A suggested way to declare error types is using the [thiserror] crate. In this case, to inherit
/// a sensible implementation of [Emit] for common error types one can implement [Diagnosable]
/// instead. For an example see `formally::smt::backends::BackendError` type, and the documentation
/// of [Diagnosable].
pub trait Emit: Contextual {
    /// Emit the object as diagnostics using the current [Context] of the object as the [Emitter].
    fn emit(&self) -> DiagnosticEmitted;
}

/// Trait for types that contain all the necessary information to implement the [Emit] trait.
///
/// Implementing [Diagnosable] for an error type requires it to be [Display] (required by
/// [Error](std::error::Error) as well anyway) to know what to write to the diagnostic,
/// [Located] to obtain a [Span] for the diagnostic, and [Contextual] to know the [Emitter] to use.
/// In addition, the [Diagnosable::level()] method (which by default returns [Level::Error]) tells
/// the level of the diagnostic. With all these information, [Emit] can be implemented
/// automatically. In addition, the [Diagnosable::notes()] method, empty by default, can be
/// implemented to emit further notes after the main diagnostic.
///
/// The following example uses the [thiserror] crate to declare a "diagnosable" error type very
/// easily for a hypothetical parsing function.
///
/// ```rust,no_run
/// # mod formally {
/// #     pub extern crate formally_support as support;
/// # }
/// use formally::support::{
///     Context, Span, Located, Contextual, Diagnosable, DiagnosticEmitted
/// };
/// use thiserror::Error;
///
/// #[derive(Debug, Error)]
/// pub enum ParsingErrorKind {
///    #[error("syntax error: {0}")]
///    SyntaxError(String),
///    #[error("type error: {0}")]
///    TypeError(String),
///    #[error(transparent)]
///    IO(std::io::Error)
/// }
///
/// #[derive(Debug, Error, Located, Contextual)]
/// #[error("parsing error: {kind}")]
/// pub struct ParsingError {
///     kind: ParsingErrorKind,
///     context: Context,
///     span: Option<Span>
/// }
///
/// // this is sufficient to implement `Emit` as well.
/// impl Diagnosable for ParsingError { }
///
/// pub enum AST {
///   // ...
/// }
///
/// pub fn parse(input: &str) -> Result<AST, ParsingError> {
///     // ...
/// # todo!()
/// }
///
/// fn main() -> Result<(), DiagnosticEmitted> {
///     // here, the diagnostic is emitted when `?` converts `ParsingError` to `DiagnosticEmitted`.
///     let ast = parse("...")?;
///
///    // ...
///
///    Ok(())
/// }
/// ```
pub trait Diagnosable: Display + Located + Contextual {
    /// The level at which the diagnostic has to be emitted.
    fn level(&self) -> Level {
        Level::Error
    }

    /// Emit additional notes after the main diagnostic.
    fn notes(&self) -> DiagnosticEmitted {
        DiagnosticEmitted
    }
}

impl<T: Diagnosable> Emit for T {
    fn emit(&self) -> DiagnosticEmitted {
        self.context()
            .emit(self.level(), Diagnostic::new(self.span(), self));
        self.notes()
    }
}

impl<T: Emit> From<T> for DiagnosticEmitted {
    fn from(err: T) -> Self {
        err.emit();
        DiagnosticEmitted
    }
}

/// Error type for usage in `formally`.
///
/// `formally` uses common Rust error handling strategies involving the [Result] type, but the
/// actual content of errors is not contained in the [Result] `Err` variant. Instead, errors are
/// emitted as diagnostics using [Emitter] and just the existence of the failure is propagated back
/// to the called with an `Err(DiagnosticEmitted)` value.
///
/// As the name says, when returning `Err(DiagnosticEmitted)` one should before emit a diagnostic
/// (usually an error) through an [Emitter], usually with the [error!] macro.
pub type Result<T> = std::result::Result<T, DiagnosticEmitted>;

/// Trait to extend the standard [Result](std::result::Result) type with the
/// [recover()](Recover::recover()) method.
///
/// This trait is implemented for any `Result<T, E>`.
pub trait Recover<T, E> {
    /// Recover an erroneous [Result](std::result::Result) by replacing it with `Ok(value)`.
    fn recover(self, value: T) -> std::result::Result<T, E>;
}

impl<T, E> Recover<T, E> for std::result::Result<T, E> {
    fn recover(self, value: T) -> std::result::Result<T, E> {
        match self {
            Ok(ok) => Ok(ok),
            Err(_) => Ok(value),
        }
    }
}

/// Trait for objects capable of emitting (or routing) diagnostics.
///
/// [Emitter] is the core of `formally`'s error handling strategy. Diagnostics, in the form of
/// [Diagnostic] objects, are just messages sent to the user possibly associated with a source span.
/// Emitters can potentially do whatever they wish with a diagnostic, including rendering them to
/// the user, ignoring them, delaying them (as with [BatchEmitter]), or relaying them to other
/// emitters, possibly after some processing.
///
/// The emission of a diagnostic can be followed by one or more notes that allow to specify
/// additional information associated with different source spans.
///
/// For consistency of the user experience, it is important that everybody uses the same [Emitter].
/// For this reason, a shared [Emitter] is always held by the current [Context], and [Context] iself
/// implements [Emitter] to access to it confortably.
///
/// [Diagnostic] objects are usually not constructed and emitted directly but using the [debug],
/// [warning] and [error] macros. Similarly, notes are usually emitted with the [note] and [trace]
/// macros.
///
/// Example:
/// ```
/// # use formally_support::*;
/// # let ctx = &Context::new();
/// # let span = Span::Span {
/// #    origin: Default::default(),
/// #    begin: Default::default(),
/// #    end: Default::default()
/// # };
/// # let ident = "";
/// error!(ctx, span, "unable to parse identifier: {}", ident);
/// ```
pub trait Emitter {
    /// Emit a diagnostic.
    fn emit(&self, level: Level, diag: Diagnostic);

    /// Emit a note.
    fn note(&self, kind: NoteKind, note: Diagnostic);
}

/// Information attached to a diagnostic.
///
/// See the [Emitter] trait for general information on the error reporting strategy of `formally`.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// The source span associated with this diagnostic.
    pub span: Option<Span>,

    /// The message attached to this diagnostic.
    pub msg: String,
}

impl Diagnostic {
    /// Constructs a diagnostic using any [Display] type as the source of the message.
    pub fn new(span: Option<Span>, msg: impl Display) -> Diagnostic {
        Diagnostic {
            span,
            msg: format!("{msg}"),
        }
    }
}

enum Batched {
    Diagnostic(Level, Diagnostic),
    Note(NoteKind, Diagnostic),
}

/// [Emitter] that throws away any diagnostic.
///
/// Any diagnostic emitted through this [NullEmitter] is completely discarded. This is useful when
/// we are interested in the success or failure of something that may emit diagnostics but not
/// in the diagnostics themselves. This is also equivalent to use a [BatchEmitter] without ever
/// calling the [commit()](BatchEmitter::commit) method, but is more efficient.
pub struct NullEmitter;

impl Emitter for NullEmitter {
    fn emit(&self, _level: Level, _diag: Diagnostic) {}

    fn note(&self, _kind: NoteKind, _note: Diagnostic) {}
}

/// [Emitter] that delays the emission of diagnostics until an explicit commit.
///
/// [BatchEmitter] is useful whenever any sort of *error recovery* is possible, thus allowing to
/// ignore the diagnostics associated with the recovered error.
///
/// [BatchEmitter] works by relaying all the received diagnostics to an inner [Emitter] instance,
/// but only after a call to [BatchEmitter::commit]. If the object is destroyed before a call to
/// [BatchEmitter::commit], the pending dianostics are ignored.
pub struct BatchEmitter<'e> {
    emitter: &'e dyn Emitter,
    batched: RefCell<Vec<Batched>>,
}

impl<'e> BatchEmitter<'e> {
    /// Constructs a new [BatchEmitter] relaying to the provided [Emitter] instance.
    pub fn new(emitter: &'e dyn Emitter) -> BatchEmitter<'e> {
        BatchEmitter {
            emitter,
            batched: RefCell::default(),
        }
    }

    /// Flushes the pending diagnostics to the underlying [Emitter]
    pub fn commit(self) {
        for batched in self.batched.into_inner() {
            match batched {
                Batched::Diagnostic(level, diag) => self.emitter.emit(level, diag),
                Batched::Note(kind, diag) => self.emitter.note(kind, diag),
            }
        }
    }
}

impl Emitter for BatchEmitter<'_> {
    /// Emit a diagnostic.
    ///
    /// Note that diagnostics and notes are relayed to the underlying [Emitter] only after a call to
    /// [BatchEmitter::commit].
    fn emit(&self, level: Level, diag: Diagnostic) {
        self.batched
            .borrow_mut()
            .push(Batched::Diagnostic(level, diag));
    }

    /// Emit a note.
    ///
    /// Note that diagnostics and notes are relayed to the underlying [Emitter] only after a call to
    /// [BatchEmitter::commit].
    fn note(&self, kind: NoteKind, note: Diagnostic) {
        self.batched.borrow_mut().push(Batched::Note(kind, note));
    }
}

///
/// An [Emitter] rendering diagnositcs on the standard error stream.
///
/// This is a simple [Emitter] to just print diagnostic messages to the standard error stream of the
/// process with attached the source span information.
///
/// This type is currently the default [Emitter] for newly constructed [Context] objects.
pub struct StdErrEmitter {
    trace_emitted: Mutex<bool>,
    note_emitted: Mutex<bool>,
}

impl StdErrEmitter {
    /// Constructs a new [StdErrEmitter].
    pub fn new() -> StdErrEmitter {
        StdErrEmitter {
            trace_emitted: Mutex::new(false),
            note_emitted: Mutex::new(false),
        }
    }

    fn print(&self, preamble: impl Display, span: Option<Span>, msg: impl Display) {
        if let Some(span) = span {
            eprint!("{span}:")
        }

        eprintln!("{preamble}: {msg}");
    }
}

impl Default for StdErrEmitter {
    fn default() -> Self {
        StdErrEmitter::new()
    }
}

impl Emitter for StdErrEmitter {
    fn emit(&self, level: Level, diag: Diagnostic) {
        let mut note_emitted = self.note_emitted.lock().unwrap();
        let mut trace_emitted = self.trace_emitted.lock().unwrap();

        if *note_emitted {
            eprintln!()
        }
        self.print(level, diag.span, diag.msg);
        *trace_emitted = false;
        *note_emitted = false;
    }

    fn note(&self, kind: NoteKind, note: Diagnostic) {
        if kind == NoteKind::Trace {
            let mut trace_emitted = self.trace_emitted.lock().unwrap();
            if *trace_emitted {
                return;
            } else {
                *trace_emitted = true;
            }
        }
        *self.note_emitted.lock().unwrap() = true;
        self.print("note", note.span, note.msg);
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! diagnose {
    ($emitter:expr, $ty:ident::$level:ident, $arg:literal) => {
        $crate::diagnose!(
            impl $emitter, $ty, $level, None, format!($arg)
        )
    };
    ($emitter:expr, $ty:ident::$level:ident, $arg:expr) => {
        $crate::diagnose!(
            impl $emitter, $ty, $level, None, $arg
        )
    };
    ($emitter:expr, $ty:ident::$level:ident, $span:expr, $arg:literal) => {
        $crate::diagnose!(
            impl $emitter, $ty, $level, $span.clone().into(), format!($arg)
        )
    };
    ($emitter:expr, $ty:ident::$level:ident, $span:expr, $arg:expr) => {
        $crate::diagnose!(
            impl $emitter, $ty, $level, $span.clone().into(), $arg
        )
    };
    ($emitter:expr, $ty:ident::$level:ident, $span:expr, $($args:tt)+) => {
        $crate::diagnose!(
            impl $emitter, $ty, $level, $span.clone().into(), format!($($args)*)
        )
    };
    ($emitter:expr, $ty:ident::$level:ident, $($args:tt)+) => {
        $crate::diagnose!(
            impl $emitter, $ty, $level, None, format!($($args)*)
        )
    };
    (impl $emitter:expr, NoteKind, $level:ident, $span:expr, $arg:expr) => {
        $crate::Emitter::note(
            $emitter,
            $crate::NoteKind::$level,
            $crate::Diagnostic::new($span, $arg),
        )
    };
    (impl $emitter:expr, Level, $level:ident, $span:expr, $arg:expr) => {
        $crate::Emitter::emit(
            $emitter,
            $crate::Level::$level,
            $crate::Diagnostic::new($span, $arg),
        )
    };
}

/// Emit a note of kind [NoteKind::Note] with a formatted message.
///
/// Notes are meant to be attached to diagnostics, so one should be sure that a diagnostic (e.g., an
/// error) has been emitted before emitting a note. Notes are used to provide additional
/// information, possibly attached to different source spans, to a previously emitted diagnostic.
///
/// Example:
/// Example:
/// ```
/// # use formally_support::*;
/// # let ctx = &Context::new();
/// # let span = Span::default();
/// # let ident = "";
/// error!(ctx, span, "unable to parse identifier: {}", ident);
/// note!(ctx, span, "it seems to be a number instead");
#[macro_export]
macro_rules! note {
    ($emitter:expr, $($args:tt)+) => {
        $crate::diagnose!($emitter, NoteKind::Note, $($args)*)
    };
}

/// Emit a note of kind [NoteKind::Trace] with a formatted message.
///
/// Trace notes are meant to provide information about the execution history that led to the
/// emission of the previous diagnostic. This is usally done by matching on a [Result] and emit the
/// trace note in the `Err` case.
///
/// Example:
/// ```rust,no_run
/// # use formally_support::*;
/// # fn parse_message(s: &str) -> Result<i32> {
/// # let ctx = &Context::new();
/// # let span = Span::default();
/// # fn parse_int(s: &str) -> Result<i32> { Ok(0) }
/// # fn something(i: i32) -> i32 { i }
///  match parse_int(s) {
///     Ok(value) => Ok(something(value)),
///     Err(_) => {
///         trace!(ctx, span, "while parsing a message");
///         Err(DiagnosticEmitted)
///     }
///  }
/// # }
/// ```
#[macro_export]
macro_rules! trace {
    ($emitter:expr, $($args:tt)+) => {
        $crate::diagnose!($emitter, NoteKind::Trace, $($args)*)
    };
}

/// Emit a diagnostic of level [Level::Internal] with a formatted message.
///
/// Example:
/// ```
/// # use formally_support::*;
/// # let ctx = &Context::new();
/// # let span = Span::default();
/// internal!(ctx, span, "violated precondition: index out of bounds");
/// ```
#[macro_export]
macro_rules! internal {
    ($emitter:expr, $($args:tt)+) => {
        $crate::diagnose!($emitter, Level::Internal, $($args)*)
    };
}

/// Emit a diagnostic of level [Level::Error] with a formatted message.
///
/// Example:
/// ```
/// # use formally_support::*;
/// # let ctx = &Context::new();
/// # let span = Span::default();
/// # let ident = "";
/// error!(ctx, span, "unable to parse identifier: {}", ident);
/// ```
#[macro_export]
macro_rules! error {
    ($emitter:expr, $($args:tt)+) => {
        $crate::diagnose!($emitter, Level::Error, $($args)*)
    };
}

/// Emits a diagnostic of level [Level::Warning] with a formatted message.
///
/// Warnings are conditions that do not harm the correct execution of the task at hand but that the
/// user should pay attention to.
///
/// Example:
/// ```
/// # use formally_support::*;
/// # let ctx = &Context::new();
/// # let span = Span::default();
/// # let ident = "";
/// warning!(ctx, span, "misleading identifier: {}", ident);
/// ```
#[macro_export]
macro_rules! warning {
    ($emitter:expr, $($args:tt)+) => {
        $crate::diagnose!($emitter, Level::Warning, $($args)*)
    };
}

/// Emits a diagnostic of level [Level::Debug] with a formatted message.
///
/// Debug messages are meant to be hidden from the user by default and shown only when requested
/// (although this behavior is completely in the hands of the selected [Emitter]), so they should
/// not contain information that cannot be ignored.
///
/// Example:
/// ```
/// # use formally_support::*;
/// # let ctx = &Context::new();
/// # let span = Span::default();
/// let x = 42;
/// debug!(ctx, span, "variable x holds: {}", x);
/// ```
#[macro_export]
macro_rules! debug {
    ($emitter:expr, $($args:tt)+) => {
        $crate::diagnose!($emitter, Level::Debug, $($args)*)
    };
}
