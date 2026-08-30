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
    convert::Infallible,
    fmt::{self, Debug, Display},
    ops::Deref,
    rc::Rc,
    sync::{Arc, LazyLock, Mutex},
};

use scoped_tls_hkt::scoped_thread_local;
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
pub trait Emit {
    /// Emit the object as a diagnostic.
    fn emit(self) -> DiagnosticEmitted;
}

impl Emit for Infallible {
    fn emit(self) -> DiagnosticEmitted {
        DiagnosticEmitted
    }
}

impl Emit for Diagnostic {
    fn emit(self) -> DiagnosticEmitted {
        GlobalEmitter.emit(Level::Error, self);
        DiagnosticEmitted
    }
}

/// Trait for types that contain all the necessary information to implement the [Emit] trait.
///
/// Implementing [Diagnosable] for an error type requires it to be [Display] (required by
/// [Error](std::error::Error) as well anyway) to know what to write to the diagnostic, and
/// [Located] to obtain a [Span] for the diagnostic. In addition, the [Diagnosable::level()] method
/// (which by default returns [Level::Error]) tells the level of the diagnostic. With all these
/// information, [Emit] can be implemented automatically. In addition, the [Diagnosable::notes()]
/// method, empty by default, can be implemented to emit further notes after the main diagnostic.
///
/// The following example uses the [thiserror] crate to declare a "diagnosable" error type very
/// easily for a hypothetical parsing function.
///
/// ```rust,no_run
/// # mod formally {
/// #     pub extern crate formally_support as support;
/// # }
/// use formally::support::{
///     Span, Located, Diagnosable, DiagnosticEmitted
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
/// #[derive(Debug, Error, Located)]
/// #[error("parsing error: {kind}")]
/// pub struct ParsingError {
///     kind: ParsingErrorKind,
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
pub trait Diagnosable: Display + Located {
    /// The level at which the diagnostic has to be emitted.
    fn level(&self) -> Level {
        Level::Error
    }

    /// Emit additional notes after the main diagnostic.
    fn notes(&self) -> DiagnosticEmitted {
        DiagnosticEmitted
    }
}

impl Emit for std::io::Error {
    fn emit(self) -> DiagnosticEmitted {
        error!(None, "input/output error: {self}");
        DiagnosticEmitted
    }
}

impl Emit for &dyn std::error::Error {
    fn emit(self) -> DiagnosticEmitted {
        error!(None, "error: {self}")
    }
}

impl Emit for Box<dyn std::error::Error> {
    fn emit(self) -> DiagnosticEmitted {
        error!(None, "error: {self}")
    }
}

impl Emit for Arc<dyn std::error::Error> {
    fn emit(self) -> DiagnosticEmitted {
        error!(None, "error: {self}")
    }
}

impl Emit for Rc<dyn std::error::Error> {
    fn emit(self) -> DiagnosticEmitted {
        error!(None, "error: {self}")
    }
}

impl<T: Diagnosable> Emit for T {
    fn emit(self) -> DiagnosticEmitted {
        GlobalEmitter.emit(self.level(), Diagnostic::new(self.span(), &self));
        self.notes()
    }
}

impl<T: Emit> From<T> for DiagnosticEmitted {
    fn from(err: T) -> Self {
        err.emit()
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
pub type Result<T, E = DiagnosticEmitted> = std::result::Result<T, E>;

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
/// For this reason, a global [Emitter] is always available as the [GlobalEmitter] type.
/// The behavior of [GlobalEmitter] can be changed with [Diagnostic::with()] or by setting a
/// different behavior for [DefaultGlobalEmitter] with [DefaultGlobalEmitter::set()].
///
/// Different implementations of [Emitter] are provided and more will be added.
/// Currently, we have:
/// - [StdErrEmitter], to direct formatted messages to the standard error stream. This is currently
///   the default global emitter.
/// - [BatchEmitter], to group diagnostics and emitting them all at once if and when requested
/// - [NullEmitter], to suppress any diagnostic.
///
/// [Diagnostic] objects are usually not constructed and emitted directly but using the [debug!],
/// [warning!], [error!] and similar macros. Similarly, notes are usually emitted with the [note!]
/// and [trace!] macros. These macros use the global [Emitter].
///
/// Example:
/// ```
/// # use formally_support::*;
/// # let span = Span::Span {
/// #    origin: Default::default(),
/// #    begin: Default::default(),
/// #    end: Default::default()
/// # };
/// # let ident = "";
/// error!(span, "unable to parse identifier: {}", ident);
/// ```
pub trait Emitter {
    /// Emit a diagnostic.
    fn emit(&self, level: Level, diag: Diagnostic) -> DiagnosticEmitted;

    /// Emit a note.
    fn note(&self, kind: NoteKind, note: Diagnostic) -> DiagnosticEmitted;
}

impl<E: Deref<Target: Emitter>> Emitter for Mutex<E> {
    fn emit(&self, level: Level, diag: Diagnostic) -> DiagnosticEmitted {
        self.lock().unwrap().emit(level, diag)
    }

    fn note(&self, kind: NoteKind, note: Diagnostic) -> DiagnosticEmitted {
        self.lock().unwrap().note(kind, note)
    }
}

/// The default global [Emitter].
///
/// This is the emitter used as the global emitter ([GlobalEmitter]) unless a call
/// of [Diagnostic::with()] is ongoing in the current thread.
///
/// This is a unit struct, so a reference to it (`&DefaultGlobalEmitter`) can be directly passed
/// to anyone expecting a `&dyn Emitter`.
pub struct DefaultGlobalEmitter;

impl DefaultGlobalEmitter {
    /// Set the default global [Emitter].
    pub fn set(emitter: impl 'static + Send + Sync + Emitter) {
        *DEFAULT_GLOBAL_EMITTER.lock().unwrap() = Arc::new(emitter);
    }
}

/// The global [Emitter].
///
/// This is the [Emitter] everyone should use, in general, to ensure a consistent rendering of
/// diagnostics in an application based on [formally]. It is used by all the diagnostic macros
/// ([error!], [warning!], [note!], etc.).
///
/// The behavior of [GlobalEmitter] can be changed locally with [Diagnostic::with()], or by changing
/// the *default* global emitter with [DefaultGlobalEmitter::set()].
///
/// This is a unit struct, so a reference to it (`&GlobalEmitter`) can be directly passed to anyone
/// expecting a `&dyn Emitter`.
pub struct GlobalEmitter;

impl Emitter for DefaultGlobalEmitter {
    fn emit(&self, level: Level, diag: Diagnostic) -> DiagnosticEmitted {
        DEFAULT_GLOBAL_EMITTER.emit(level, diag)
    }

    fn note(&self, kind: NoteKind, note: Diagnostic) -> DiagnosticEmitted {
        DEFAULT_GLOBAL_EMITTER.note(kind, note)
    }
}

impl Emitter for GlobalEmitter {
    fn emit(&self, level: Level, diag: Diagnostic) -> DiagnosticEmitted {
        if GLOBAL_EMITTER.is_set() {
            GLOBAL_EMITTER.with(|e| e.emit(level, diag))
        } else {
            DefaultGlobalEmitter.emit(level, diag)
        }
    }

    fn note(&self, kind: NoteKind, note: Diagnostic) -> DiagnosticEmitted {
        if GLOBAL_EMITTER.is_set() {
            GLOBAL_EMITTER.with(|e| e.note(kind, note))
        } else {
            DefaultGlobalEmitter.note(kind, note)
        }
    }
}

static DEFAULT_GLOBAL_EMITTER: LazyLock<Mutex<Arc<dyn Send + Sync + Emitter>>> =
    LazyLock::new(|| Mutex::new(Arc::new(StdErrEmitter::new())));

scoped_thread_local!(static GLOBAL_EMITTER: for<'a> &'a (dyn 'a + Emitter));

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
            msg: msg.to_string(),
        }
    }

    /// Temporarily changes the global [Emitter].
    ///
    /// Changes the global emitter for the current thread, executes the given function, and then
    /// restores the old global emitter. If the function panics, the old emitter is restored and the
    /// panic propagated.
    pub fn with<F, R>(emitter: &(dyn '_ + Emitter), f: F) -> R
    where
        F: FnOnce() -> R,
    {
        GLOBAL_EMITTER.set(emitter, f)
    }
}

/// [Emitter] that throws away any diagnostic.
///
/// Any diagnostic emitted through this [NullEmitter] is completely discarded. This is useful when
/// we are interested in the success or failure of something that may emit diagnostics but not
/// in the diagnostics themselves. This is also equivalent to use a [BatchEmitter] without ever
/// calling the [commit()](BatchEmitter::commit) method, but is more efficient.
pub struct NullEmitter;

impl Emitter for NullEmitter {
    fn emit(&self, _level: Level, _diag: Diagnostic) -> DiagnosticEmitted {
        DiagnosticEmitted
    }

    fn note(&self, _kind: NoteKind, _note: Diagnostic) -> DiagnosticEmitted {
        DiagnosticEmitted
    }
}

/// [Emitter] that delays the emission of diagnostics until an explicit commit.
///
/// [BatchEmitter] is useful whenever any sort of *error recovery* is possible, thus allowing to
/// ignore the diagnostics associated with the recovered error.
///
/// [BatchEmitter] works by relaying all the received diagnostics to an inner [Emitter] instance,
/// but only after a call to [BatchEmitter::commit]. If the object is destroyed before a call to
/// [BatchEmitter::commit], the pending dianostics are discarded.
pub struct BatchEmitter<'e> {
    emitter: &'e dyn Emitter,
    emitted: RefCell<Vec<Emitted>>,
}

/// An emitted diagnostic together with its level or an emitted note together with its kind,
/// collected by [BatchEmitter].
pub enum Emitted {
    Diagnostic(Level, Diagnostic),
    Note(NoteKind, Diagnostic),
}

impl Emit for Emitted {
    fn emit(self) -> DiagnosticEmitted {
        match self {
            Emitted::Diagnostic(level, diag) => GlobalEmitter.emit(level, diag),
            Emitted::Note(kind, note) => GlobalEmitter.note(kind, note),
        }
    }
}

impl Emit for Vec<Emitted> {
    fn emit(self) -> DiagnosticEmitted {
        for emitted in self {
            emitted.emit();
        }
        DiagnosticEmitted
    }
}

impl<'e> BatchEmitter<'e> {
    /// Construct a new [BatchEmitter] relaying to the global [Emitter].
    pub fn new() -> BatchEmitter<'static> {
        BatchEmitter::with_emitter(&GlobalEmitter)
    }

    /// Construct a new [BatchEmitter] relaying to the provided [Emitter] instance.
    pub fn with_emitter(emitter: &'e dyn Emitter) -> BatchEmitter<'e> {
        BatchEmitter {
            emitter,
            emitted: RefCell::default(),
        }
    }

    /// Flushes the pending diagnostics to the underlying [Emitter].
    ///
    /// The method returns `Ok(())` if no diagnostics were collected, or `Err(DiagnosticEmitted)`
    /// otherwise.
    pub fn commit(self) -> Result<(), DiagnosticEmitted> {
        Diagnostic::with(self.emitter, || Ok(self.ok()?))
    }

    /// Return the collected emitted diagnostics as an `Err(Vec<Emitted>)` if any, or `Ok(())` if no
    /// diagnostics were emitted.
    ///
    /// Note that `Vec<Emitted>` is `Emit` so can be used with the `?` operator in a function
    /// returning `Result<_, DiagnosticEmitted>` to emit the diagnostics on early return.
    pub fn ok(self) -> Result<(), Vec<Emitted>> {
        let emitted = self.emitted.into_inner();
        if emitted.is_empty() {
            Ok(())
        } else {
            Err(emitted)
        }
    }
}

impl Emitter for BatchEmitter<'_> {
    /// Emit a diagnostic.
    ///
    /// Note that diagnostics and notes are relayed to the underlying [Emitter] only after a call to
    /// [BatchEmitter::commit].
    fn emit(&self, level: Level, diag: Diagnostic) -> DiagnosticEmitted {
        self.emitted
            .borrow_mut()
            .push(Emitted::Diagnostic(level, diag));
        DiagnosticEmitted
    }

    /// Emit a note.
    ///
    /// Note that diagnostics and notes are relayed to the underlying [Emitter] only after a call to
    /// [BatchEmitter::commit].
    fn note(&self, kind: NoteKind, note: Diagnostic) -> DiagnosticEmitted {
        self.emitted.borrow_mut().push(Emitted::Note(kind, note));
        DiagnosticEmitted
    }
}

///
/// An [Emitter] rendering diagnositcs on the standard error stream.
///
/// This is a simple [Emitter] to just print diagnostic messages to the standard error stream of the
/// process with attached the source span information.
///
/// This type is currently the default global [Emitter].
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
    fn emit(&self, level: Level, diag: Diagnostic) -> DiagnosticEmitted {
        let mut note_emitted = self.note_emitted.lock().unwrap();
        let mut trace_emitted = self.trace_emitted.lock().unwrap();

        if *note_emitted {
            eprintln!()
        }
        self.print(level, diag.span, diag.msg);
        *trace_emitted = false;
        *note_emitted = false;

        DiagnosticEmitted
    }

    fn note(&self, kind: NoteKind, note: Diagnostic) -> DiagnosticEmitted {
        if kind == NoteKind::Trace {
            let mut trace_emitted = self.trace_emitted.lock().unwrap();
            if *trace_emitted {
                return DiagnosticEmitted;
            } else {
                *trace_emitted = true;
            }
        }
        *self.note_emitted.lock().unwrap() = true;
        self.print("note", note.span, note.msg);

        DiagnosticEmitted
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! diagnose_impl {
    ($ty:ident::$level:ident, $emitter:expr, $span:expr, $arg:literal) => {
        $crate::diagnose_impl!(
            impl $ty, $level, $emitter, $span.clone().into(), format!($arg)
        )
    };
    ($ty:ident::$level:ident, $emitter:expr, $span:expr, $arg:expr) => {
        $crate::diagnose_impl!(
            impl $ty, $level, $emitter, $span.clone().into(), $arg
        )
    };
    ($ty:ident::$level:ident, $emitter:expr, $span:expr, $($args:tt)+) => {
        $crate::diagnose_impl!(
            impl $ty, $level, $emitter, $span.clone().into(), format!($($args)*)
        )
    };
    (impl NoteKind, $level:ident, $emitter:expr, $span:expr, $arg:expr) => {
        $crate::Emitter::note(
            $emitter,
            $crate::NoteKind::$level,
            $crate::Diagnostic::new($span, $arg),
        )
    };
    (impl Level, $level:ident, $emitter:expr, $span:expr, $arg:expr) => {
        $crate::Emitter::emit(
            $emitter,
            $crate::Level::$level,
            $crate::Diagnostic::new($span, $arg),
        )
    };
}

/// Generic and more flexible version of the [error!], [warning!], etc. macros.
///
/// The [error!], [warning!], [debug!], [internal!], [note!], and [trace!] macro are based on
/// invocations of [diagnose!] which is the most flexible and generic of the set.
///
/// It accepts as a first argument a literal value of [Level] or [NoteKind], depending on which it
/// emits a diagnostic or a note. It accepts then an emitter, a span, and a message, optionally
/// formatted à la [format!] followed by the format arguments.
#[macro_export]
macro_rules! diagnose {
    ($ty:ident::$level:ident, $emitter:expr, $span:expr, $($args:tt)+) => {
        $crate::diagnose_impl!($ty::$level, $emitter, $span, $($args)*)
    }
}

/// Emit a note of kind [NoteKind::Note] with a formatted message.
///
/// Notes are meant to be attached to diagnostics, so one should be sure that a diagnostic (e.g., an
/// error) has been emitted before emitting a note. Notes are used to provide additional
/// information, possibly attached to different source spans, to a previously emitted diagnostic.
///
/// Example:
/// ```
/// # use formally_support::*;
/// # let span = Span::default();
/// # let ident = "";
/// error!(span, "unable to parse identifier: {}", ident);
/// note!(span, "it seems to be a number instead");
#[macro_export]
macro_rules! note {
    ($($args:tt)+) => {
        $crate::diagnose!(NoteKind::Note, &$crate::GlobalEmitter, $($args)*)
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
/// # let span = Span::default();
/// # fn parse_int(s: &str) -> Result<i32> { Ok(0) }
/// # fn something(i: i32) -> i32 { i }
///  match parse_int(s) {
///     Ok(value) => Ok(something(value)),
///     Err(_) => {
///         trace!(span, "while parsing a message");
///         Err(DiagnosticEmitted)
///     }
///  }
/// # }
/// ```
#[macro_export]
macro_rules! trace {
    ($($args:tt)+) => {
        $crate::diagnose!(NoteKind::Trace, &$crate::GlobalEmitter, $($args)*)
    };
}

/// Emit a diagnostic of level [Level::Internal] with a formatted message.
///
/// Example:
/// ```
/// # use formally_support::*;
/// # let span = Span::default();
/// internal!(span, "violated precondition: index out of bounds");
/// ```
#[macro_export]
macro_rules! internal {
    ($($args:tt)+) => {
        $crate::diagnose!(Level::Internal, &$crate::GlobalEmitter, $($args)*)
    };
}

/// Emit a diagnostic of level [Level::Error] with a formatted message.
///
/// Example:
/// ```
/// # use formally_support::*;
/// # let span = Span::default();
/// # let ident = "";
/// error!(span, "unable to parse identifier: {}", ident);
/// ```
#[macro_export]
macro_rules! error {
    ($($args:tt)+) => {
        $crate::diagnose!(Level::Error, &$crate::GlobalEmitter, $($args)*)
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
/// # let span = Span::default();
/// # let ident = "";
/// warning!(span, "misleading identifier: {}", ident);
/// ```
#[macro_export]
macro_rules! warning {
    ($($args:tt)+) => {
        $crate::diagnose!(Level::Warning, &$crate::GlobalEmitter, $($args)*)
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
/// # let span = Span::default();
/// let x = 42;
/// debug!(span, "variable x holds: {}", x);
/// ```
#[macro_export]
macro_rules! debug {
    ($($args:tt)+) => {
        $crate::diagnose!(Level::Debug, &$crate::GlobalEmitter, $($args)*)
    };
}
