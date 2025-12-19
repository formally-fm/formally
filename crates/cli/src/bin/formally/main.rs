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

use formally::{
    io::parse::{Parsable, Parse},
    smt::{
        Config,
        smtlib::{ast, interpreter::*},
    },
    support::{Contextual, DiagnosticEmitted},
};

use std::{path::*, process::ExitCode};

use clap::{Parser, Subcommand};

#[derive(Subcommand)]
enum Command {
    /// Solve SMT-LIB scripts
    Solve {
        /// The path to the SMT-LIB script to solve
        filename: PathBuf,
    },
}

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let result = match cli.command {
        Command::Solve { filename } => solve(filename),
    };

    match result {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}

fn solve(filename: PathBuf) -> Result<(), DiagnosticEmitted> {
    let emitter = SMTLibEmitter::new();

    let ast::Script { commands, .. } = match ast::Script::parser().parse(&emitter, filename) {
        Ok(script) => script,
        Err(_) => return Err(DiagnosticEmitted),
    };

    let config = Config::new().with_emitter(emitter);
    let mut interpreter = Interpreter::new(config);

    for cmd in commands {
        interpreter.command(cmd).ok();

        if interpreter.has_exited() {
            break;
        }
    }

    Ok(())
}
