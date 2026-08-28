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
    smt,
    smt::{Config, backends::Register, smtlib::interpreter::*},
    support::{Diagnostic, DiagnosticEmitted},
};

use clap::{Args, Parser, Subcommand};
use itertools::*;

use std::{path::*, process::ExitCode};

fn backend_opt_help() -> String {
    let mut backends = Vec::new();
    for backend in Register::backends() {
        if let Ok(name) = backend.name() {
            backends.push(name);
        }
    }

    format!(
        "The SMT backend to use. Available backends: {}",
        backends.into_iter().join(", ")
    )
}

#[derive(Args)]
struct Solve {
    #[arg(short = 'B', long, help = backend_opt_help())]
    backend: Option<String>,
    /// The path to the SMT-LIB script to solve
    filename: PathBuf,
}

#[derive(Subcommand)]
enum Command {
    /// Solve SMT-LIB scripts
    Solve(Solve),
}

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let result = match cli.command {
        Command::Solve(args) => solve(args),
    };

    match result {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}

fn solve(args: Solve) -> Result<(), DiagnosticEmitted> {
    Diagnostic::with(SMTLibEmitter::new(), || {
        let backend = match args.backend {
            Some(backend) => Register::backend(backend)?,
            None => &smt::backends::Default,
        };

        let mut interpreter = Interpreter::with_backend(Config::default(), backend);

        interpreter.run(&args.filename)?;

        Ok(())
    })
}
