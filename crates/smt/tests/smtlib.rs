//
// ::formally - the open-source formal methods toolchain
//
// Copyright (c) 2026 Nicola Gigante
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

use rstest::*;

mod formally {
    pub extern crate formally_io as io;
    pub extern crate formally_smt as smt;
    pub extern crate formally_support as support;
}

use formally::{
    io::print::RenderTarget,
    smt::{backends, smtlib::interpreter::Interpreter, *},
    support::*,
};

use formally_smt::smtlib::interpreter::Settings;
use std::{
    ffi::OsStr,
    fs, io,
    path::{Path, PathBuf},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Category {
    Sat,
    Unsat,
    Unknown,
    Error,
}

fn enumerate_rec(dir: PathBuf, files: &mut Vec<(Category, PathBuf)>) -> io::Result<()> {
    for dir in fs::read_dir(dir)? {
        let entry = dir?;

        if entry.file_type()?.is_dir() {
            enumerate_rec(entry.path(), files)?;
        } else {
            let filename = PathBuf::from(entry.file_name());
            let category = match filename.file_stem().and_then(|s| Path::new(s).extension()) {
                Some(c) if c == "sat" => Category::Sat,
                Some(c) if c == "unsat" => Category::Unsat,
                Some(c) if c == "unknown" => Category::Unknown,
                Some(c) if c == "error" => Category::Error,
                _ => continue,
            };

            if let Some(ext) = filename.extension().and_then(OsStr::to_str)
                && ext == "smtlib"
            {
                files.push((category, entry.path()))
            }
        }
    }

    Ok(())
}

fn enumerate() -> io::Result<Vec<(Category, PathBuf)>> {
    let root = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());

    let mut paths = Vec::new();
    enumerate_rec(root, &mut paths)?;

    Ok(paths)
}

#[derive(Clone, Copy)]
struct Sink;

impl io::Write for Sink {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        io::Write::write(&mut io::sink(), buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        io::Write::flush(&mut io::sink())
    }
}

impl RenderTarget for Sink {
    fn is_terminal(&self) -> bool {
        false
    }
}

#[rstest]
pub fn smtlib(#[values("z3", "cvc5")] backend: &str) -> Result<()> {
    for (category, test) in enumerate()? {
        let mut interpreter =
            Interpreter::with_backend(Settings::default().output(Sink), backends::get(backend)?);

        let emitter = BatchEmitter::new(&NullEmitter);
        let result = Diagnostic::with(&emitter, || interpreter.run(&test));

        match emitter.ok() {
            Ok(_) => match result {
                Ok(Answer::Yes) => assert_eq!(category, Category::Sat),
                Ok(Answer::No) => assert_eq!(category, Category::Unsat),
                Ok(Answer::Unknown) => assert_eq!(category, Category::Unknown),
                Err(_) => assert_eq!(category, Category::Error),
            },
            Err(_) => assert_eq!(category, Category::Error),
        }
    }

    Ok(())
}
