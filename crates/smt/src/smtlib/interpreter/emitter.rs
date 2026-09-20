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

use crate::smtlib::*;
use formally::io::{print::Print, print::RenderTarget};
use formally::support::*;

use std::{io, io::Write, sync::RwLock};

/// An [Emitter] which formats diagnostics in the SMT-LIBv2 response syntax.
///
/// The write stream used to output the diagnostics can be chosen with the
/// [writing_to](SMTLibEmitter::writing_to()) method, and by default is [io::stderr()].
pub struct SMTLibEmitter {
    write: RwLock<Box<dyn RenderTarget + Send + Sync>>,
}

impl SMTLibEmitter {
    /// Create a new emitter with [io::stderr()] as the default output stream.
    pub fn new() -> SMTLibEmitter {
        SMTLibEmitter {
            write: RwLock::new(Box::new(io::stderr())),
        }
    }

    /// Return a new emitter with a different output stream.
    pub fn writing_to(self, write: impl 'static + RenderTarget + Send + Sync) -> SMTLibEmitter {
        SMTLibEmitter {
            write: RwLock::new(Box::new(write)),
        }
    }
}

impl Default for SMTLibEmitter {
    fn default() -> Self {
        SMTLibEmitter::new()
    }
}

impl Emitter for SMTLibEmitter {
    fn emit(&self, level: Level, diag: Diagnostic) -> DiagnosticEmitted {
        let mut msg = "error:".to_string();
        if level != Level::Error {
            msg.push_str(&format!("{level}:"));
        }
        if let Some(span) = diag.span {
            msg.push_str(&format!("{span}:"));
        }
        msg.push(' ');
        msg.push_str(&diag.msg);
        let error = ast::Response::Error(ast::StringLiteral {
            value: msg,
            span: None,
        });
        error.print(&mut **self.write.write().unwrap()).unwrap();
        writeln!(&mut *self.write.write().unwrap()).unwrap();

        DiagnosticEmitted
    }

    fn note(&self, _kind: NoteKind, note: Diagnostic) -> DiagnosticEmitted {
        let mut msg = "note:".to_string();
        if let Some(span) = note.span {
            msg.push_str(&format!("{span}:"));
        }
        msg.push(' ');
        msg.push_str(&note.msg);
        let error = ast::Response::Error(ast::StringLiteral {
            value: msg,
            span: None,
        });
        error.print(&mut **self.write.write().unwrap()).unwrap();
        writeln!(&mut *self.write.write().unwrap()).unwrap();

        DiagnosticEmitted
    }
}
