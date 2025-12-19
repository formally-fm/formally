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

//! Facilities to pretty-print output text.
//!
//! The [print] module is for now just a set of small amenities on top of the [pretty] crate, which
//! provides facilities to pretty-print text accounting for the number of columns available (e.g.
//! the size of the terminal).
//!
//! The [Print] trait is used for this purpose, rather than [std::fmt::Display], indeed because of
//! the possibility of specifying the number of columns to print in.

pub use ::pretty::RcDoc;
use std::{fmt, io};

/// A trait for write streams that know if they are terminals.
///
/// This trait is automatically implemented for any type implementing both [io::Write] and
/// [io::IsTerminal].
pub trait RenderTarget: io::Write + io::IsTerminal {}
impl<T: io::Write + io::IsTerminal> RenderTarget for T {}

/// Types that can print themselves accounting for the number of available columns.
pub trait Print {
    /// Render an object to the given `target` write stream in `width` number of columns.
    fn render(&self, target: &mut dyn io::Write, width: u16) -> io::Result<()>;

    /// Render an object to the given `fmt::Write` formatter in `width` number of columns.
    fn render_fmt(&self, target: &mut dyn fmt::Write, width: u16) -> fmt::Result;

    /// Prints an object to the given [RenderTarget] by calling [render()](Print::render) with an
    /// automatically detected `width` parameter if a terminal is attached.
    fn print(&self, target: &mut dyn RenderTarget) -> io::Result<()> {
        if target.is_terminal()
            && let Some(size) = termsize::get()
        {
            self.render(target, size.cols)
        } else {
            self.render(target, u16::MAX)
        }
    }

    /// As [print()](Print::print) but appends a new line at the end.
    fn println(&self, target: &mut dyn RenderTarget) -> io::Result<()> {
        self.print(target)?;
        writeln!(target)
    }
}

/// Types that can print themselves to an [RcDoc] object.
pub trait Pretty {
    fn pretty(&self) -> RcDoc<'static>;
}

impl<T: Pretty> Print for T {
    fn render(&self, target: &mut dyn io::Write, width: u16) -> io::Result<()> {
        self.pretty().render(width as usize, target)
    }

    fn render_fmt(&self, target: &mut dyn fmt::Write, width: u16) -> fmt::Result {
        self.pretty().render_fmt(width as usize, target)
    }
}

/// Little helper to put quotes around an [RcDoc].
pub fn quotes(doc: RcDoc) -> RcDoc {
    let quote = RcDoc::as_string('"');
    quote.clone().append(doc).append(quote)
}

/// Little helper to put delimiters around an [RcDoc] with softlines telling the renderer to break
/// lines there but only if needed.
pub fn enclose<'a>(doc: RcDoc<'a>, start: &str, end: &str) -> RcDoc<'a> {
    RcDoc::as_string(start)
        .append(
            RcDoc::softline_()
                .append(doc)
                .append(RcDoc::softline_())
                .nest(1)
                .group(),
        )
        .append(RcDoc::as_string(end))
}

/// Little helper to put parens around an [RcDoc] with softelines.
pub fn parens(doc: RcDoc) -> RcDoc {
    enclose(doc, "(", ")")
}

/// Little helper to put brackets around an [RcDoc] with softelines.
pub fn brackets(doc: RcDoc) -> RcDoc {
    enclose(doc, "[", "]")
}

/// Little helper to put braces around an [RcDoc] with softelines.
pub fn braces(doc: RcDoc) -> RcDoc {
    enclose(doc, "{", "}")
}
