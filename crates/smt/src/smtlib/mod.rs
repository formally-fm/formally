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

//! Support for the SMT-LIBv2 language.
//!
//! This module provides support for the concrete syntax of the SMT-LIBv2 language.
//! * the [ast] submodule provides types to represent a detailed abstract syntax tree of an
//!   SMT-LIBv2 source file, together with their [Parsable](crate::formally::io::parse::Parsable)
//!   and [Print](crate::formally::io::print::Print) instances.
//! * the [interpreter] submodule provides the [Interpreter](interpreter::Interpreter) type which is
//!   in charge of actually executing SMT-LIBv2 commands.

pub mod interpreter;
mod parse;
mod print;

pub mod ast;
