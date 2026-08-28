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

//!
//! An interpreter for SMT-LIBv2 commands.
//!
//! This module provides the [Interpreter] type and related types. [Interpreter] can execute
//! SMT-LIBv2 [commands](ast::Command) and keep track of their execution during the execution of an
//! entire script.
//!
//! The module also provides [SMTLibEmitter], an [Emitter] that prints diagnostics to the terminal
//! in the format specified by the SMT-LIBv2 syntax for responses.
use crate::formally;

use formally::{
    io::{
        parse::Parsable as _,
        print::{Print, RenderTarget},
    },
    smt::{self, Config, ToTerm, backends::Backend, smtlib::ast},
    support::*,
};

use std::{fmt::Debug, io, path::Path};

use thiserror::Error;

mod translate;

mod emitter;
pub use emitter::*;
use formally_io::parse::Parse;

/// An SMT-LIBv2 interpreter.
///
/// [Interpreter] handles the execution of a sequence of SMT-LIBv2 [commands](ast::Command).
///
/// Note that support for the language is still incomplete, and only a few commands (the most
/// common) are supported at the moment.
///
/// A command is executed by calling the [command()](Interpreter::command()) method, which updates
/// the current state of the interpreter and makes it ready to execute the next.
///
/// The internal state of the interpreter follows the state diagram of Section 4.1
/// "General Requirements" of the [specification manual](https://smt-lib.org/language.shtml).
///
/// In particular, the interpreter starts in a configurable state where a
/// [Solver](smt::Solver) has not been instantiated yet. In this state, any configuration
/// option can still be changed. A `(set-logic)` command starts the interpreter completely and
/// cannot be repeated. In this situation, [has_started()](Interpreter::has_started()) returns
/// `true`. Then, an `(exit)` command deallocates the solver but keeps the current [Config] for
/// future use. In this situation, [has_exited()](Interpreter::has_exited()) returns `true`.
///
/// Note that SMT-LIBv2 commands are defined to print their output and errors to the streams
/// configured with the `:diagnostic-output-channel` and `:regular-output-channel` options which,
/// however, are not implemented yet, therefore currently output is produced on the standard
/// output stream of the process, and errors (through [SMTLibEmitter]) are produced on the standard
/// error stream.
#[allow(clippy::large_enum_variant)]
#[allow(private_interfaces)]
pub enum Interpreter {
    #[doc(hidden)]
    Start(Settings),
    #[doc(hidden)]
    Started(State),
    #[doc(hidden)]
    Exited(Config, Mode),
}

#[derive(Debug, Clone, Copy)]
enum Mode {
    Assert,
    Sat,
    Unsat,
}

impl From<Mode> for smt::Answer {
    fn from(mode: Mode) -> smt::Answer {
        match mode {
            Mode::Assert => smt::Answer::Unknown,
            Mode::Sat => smt::Answer::Yes,
            Mode::Unsat => smt::Answer::No,
        }
    }
}

/// Type specifying the operating settings for the interpreter.
pub struct Settings {
    /// The [Config] for the underlying [Solver].
    pub config: Config,
    /// The SMT backend to use.
    pub backend: &'static dyn Backend,
    /// The output write stream to use for the output messages (not the diagnostics, which are
    /// handled by the global emitter).
    pub output: Box<dyn RenderTarget>,
}

impl Settings {
    pub fn config(self, config: Config) -> Settings {
        Settings { config, ..self }
    }

    pub fn backend(self, backend: &'static impl Backend) -> Settings {
        Settings { backend, ..self }
    }

    pub fn output(self, output: impl 'static + RenderTarget) -> Settings {
        Settings { output: Box::new(output), ..self }
    }
}

impl From<Config> for Settings {
    fn from(config: Config) -> Self {
        Settings {
            config,
            ..Settings::default()
        }
    }
}

impl Default for Settings {
    fn default() -> Self {
        Settings {
            config: Config::default(),
            backend: &smt::backends::Default,
            output: Box::new(io::stdout()),
        }
    }
}

struct State {
    mode: Mode,
    config: Config,
    solver: smt::Solver,
    output: Box<dyn RenderTarget>,
}

impl Default for Interpreter {
    fn default() -> Self {
        Interpreter::Start(Settings::default())
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Error)]
enum RequiredMode {
    #[error("once")]
    Start,
    #[error("after a `check-sat` or `check-sat-assuming` command returned a `sat` response")]
    Sat,
    #[error("after a `check-sat` or `check-sat-assuming` command returned an `unsat` response")]
    Unsat,
    #[error("after the solver has been configured completely by the `set-logic` command")]
    Started,
}

impl Interpreter {
    /// Create a new interpreter with the given starting configuration.
    pub fn new(settings: impl Into<Settings>) -> Interpreter {
        Interpreter::Start(settings.into())
    }

    pub fn with_backend(
        settings: impl Into<Settings>,
        backend: &'static dyn Backend,
    ) -> Interpreter {
        Interpreter::Start(Settings {
            backend,
            ..settings.into()
        })
    }

    /// Execute a command.
    pub fn command(&mut self, command: ast::Command) -> Result<()> {
        use Interpreter::*;
        use ast::Command::*;

        match self {
            Start(Settings { config, output, .. }) => match command {
                Echo(msg) => Self::echo(&mut **output, msg),
                Exit(_) => Self::exit(self),
                GetInfo(_) => Self::unsupported(&mut **output),
                GetOption(_) => Self::unsupported(&mut **output),
                Reset(_) => Self::unsupported(&mut **output),
                ResetAssertions(_) => Self::unsupported(&mut **output),
                SetInfo(_) => Self::unsupported(&mut **output),
                SetLogic(sl) => Self::set_logic(self, sl),
                SetOption(so) => Self::set_option_start(config, &mut **output, so),
                command => Self::fail(config, RequiredMode::Started, command),
            },
            Started(state) => match command {
                Assert(assert) => Self::assert(state, assert),
                CheckSat(_) => Self::check_sat(state),
                CheckSatAssuming(_) => Self::unsupported(&mut *state.output),
                DeclareConst(decl) => Self::declare_const(state, decl),
                DeclareDatatype(_) => Self::unsupported(&mut *state.output),
                DeclareDatatypes(_) => Self::unsupported(&mut *state.output),
                DeclareFun(decl) => Self::declare_fun(state, decl),
                DeclareSort(decl) => Self::declare_sort(state, decl),
                DeclareSortParameter(_) => Self::unsupported(&mut *state.output),
                DefineConst(def) => Self::define_const(state, def),
                DefineFun(def) => Self::define_fun(state, def),
                DefineFunRec(_) => Self::unsupported(&mut *state.output),
                DefineFunsRec(_) => Self::unsupported(&mut *state.output),
                DefineSort(_) => Self::unsupported(&mut *state.output),
                Echo(msg) => Self::echo(&mut *state.output, msg),
                Exit(_) => Self::exit(self),
                GetAssertions(_) => Self::unsupported(&mut *state.output),
                GetInfo(_) => Self::unsupported(&mut *state.output),
                GetOption(_) => Self::unsupported(&mut *state.output),
                Pop(pop) => Self::pop(state, pop),
                Push(push) => Self::push(state, push),
                Reset(_) => Self::unsupported(&mut *state.output),
                ResetAssertions(_) => Self::unsupported(&mut *state.output),
                SetInfo(_) => Self::unsupported(&mut *state.output),
                SetOption(so) => Self::set_option_started(state, so),
                _ => match (command, state.mode) {
                    (GetAssignments(_), Mode::Sat) => Self::unsupported(&mut *state.output),
                    (GetModel(_), Mode::Sat) => Self::unsupported(&mut *state.output),
                    (GetValue(cmd), Mode::Sat) => Self::get_value(state, cmd),
                    (GetProof(_), Mode::Unsat) => Self::unsupported(&mut *state.output),
                    (GetUnsatAssumptions(_), Mode::Unsat) => Self::unsupported(&mut *state.output),
                    (GetUnsatCore(_), Mode::Unsat) => Self::unsupported(&mut *state.output),
                    (command @ (GetModel(_) | GetValue(_) | GetAssignments(_)), _) => {
                        Self::fail(&state.config, RequiredMode::Sat, command)
                    }
                    (command @ (GetProof(_) | GetUnsatAssumptions(_) | GetUnsatCore(_)), _) => {
                        Self::fail(&state.config, RequiredMode::Unsat, command)
                    }
                    (command, _) => Self::fail(&state.config, RequiredMode::Start, command),
                },
            },
            Exited(_, _) => self.exited(command),
        }
    }

    /// Execute a script directly from a text file.
    ///
    /// The function returns an [Answer](smt::Answer) corresponding to the last executed
    /// `(check-sat)` instruction, if any, not followed by further `(assert)` commands.
    pub fn run(&mut self, path: &Path) -> Result<smt::Answer> {
        let ast::Script { commands, .. } = match ast::Script::parser().parse(path) {
            Ok(script) => script,
            Err(_) => return Err(DiagnosticEmitted),
        };

        for cmd in commands {
            self.command(cmd).ok();

            if let Interpreter::Exited(_, mode) = self {
                return Ok((*mode).into());
            }
        }

        match self {
            Interpreter::Start(_) => Ok(smt::Answer::Unknown),
            Interpreter::Started(state) => Ok(state.mode.into()),
            Interpreter::Exited(_, mode) => Ok((*mode).into()),
        }
    }

    /// Tell if a `(set-logic)` (but no `(exit)`) command has been executed.
    pub fn has_started(&self) -> bool {
        !matches!(self, Interpreter::Start(_))
    }

    /// Tell if an `(exit)` command has been executed.
    pub fn has_exited(&self) -> bool {
        matches!(self, Interpreter::Exited(_, _))
    }

    fn exited(&self, command: ast::Command) -> Result<()> {
        error!(
            command.span(),
            "command `{}` is not available because the solver has exited",
            command.name()
        );
        Err(DiagnosticEmitted)
    }

    fn fail(_config: &Config, mode: RequiredMode, command: ast::Command) -> Result<()> {
        error!(
            command.span(),
            "the `{}` command is only available {}",
            command.name(),
            mode
        );
        Err(DiagnosticEmitted)
    }

    fn unsupported(output: &mut dyn RenderTarget) -> Result<()> {
        Interpreter::response(output, ast::Response::Unsupported)
    }

    // TODO: supporting setting the output stream through the `Config`
    fn response(output: &mut dyn RenderTarget, response: impl Print) -> Result<()> {
        match response.println(output) {
            Ok(_) => Ok(()),
            Err(err) => {
                error!(None, "input/output error: {err}");
                Err(DiagnosticEmitted)
            }
        }
    }

    fn echo(output: &mut dyn RenderTarget, msg: ast::StringLiteral) -> Result<()> {
        Interpreter::response(
            output,
            ast::Response::Echo(ast::EchoResponse {
                msg: msg.clone(),
                span: None,
            }),
        )
    }

    fn exit(&mut self) -> Result<()> {
        let (config, mode) = match self {
            Interpreter::Start(Settings { config, .. }) => (config, Mode::Assert),
            Interpreter::Started(State { config, mode, .. }) => (config, *mode),
            Interpreter::Exited(config, mode) => (config, *mode),
        };
        *self = Interpreter::Exited(std::mem::take(config), mode);

        Ok(())
    }

    fn set_logic(&mut self, sl: ast::SetLogic) -> Result<()> {
        let Interpreter::Start(mut settings) = std::mem::take(self) else {
            return Ok(());
        };

        settings.config.logic = match sl.logic.inner() {
            "ALL" => None,
            logic => Some(Identifier::from(logic).into_owned().over(sl.logic.span())),
        };

        match smt::Solver::with_backend(&settings.config, settings.backend) {
            Ok(solver) => {
                *self = Interpreter::Started(State {
                    mode: Mode::Assert,
                    config: settings.config,
                    solver,
                    output: settings.output,
                })
            }
            Err(_) => *self = Interpreter::Start(settings),
        }

        Ok(())
    }

    fn set_option_start(
        config: &mut Config,
        output: &mut dyn RenderTarget,
        so: ast::SetOption,
    ) -> Result<()> {
        match so.option {
            ast::AstOption::ProduceModels(pm) => {
                config.produce_models = pm.value;
                Ok(())
            }
            _ => Self::unsupported(output),
        }
    }

    fn set_option_started(state: &mut State, so: ast::SetOption) -> Result<()> {
        Self::set_option_start(&mut state.config, &mut *state.output, so)?;

        state.solver.config(&state.config)
    }

    fn assert(state: &mut State, assert: ast::Assert) -> Result<()> {
        let term = Interpreter::term_to_smt(&state.solver, assert.term)?;
        state.solver.require(term)?;

        state.mode = Mode::Assert;

        Ok(())
    }

    fn check_sat(state: &mut State) -> Result<()> {
        let (response, mode) = match state.solver.check()? {
            smt::Answer::Yes => (
                ast::CheckSatResponse {
                    response: Some(true),
                    span: None,
                },
                Mode::Sat,
            ),
            smt::Answer::No => (
                ast::CheckSatResponse {
                    response: Some(false),
                    span: None,
                },
                Mode::Unsat,
            ),
            smt::Answer::Unknown => (
                ast::CheckSatResponse {
                    response: None,
                    span: None,
                },
                Mode::Assert,
            ),
        };

        Interpreter::response(&mut *state.output, response)?;
        state.mode = mode;

        Ok(())
    }

    fn declare_const(state: &mut State, decl: ast::DeclareConst) -> Result<()> {
        let sort = Interpreter::sort_to_smt_term(&state.solver, &decl.sort);
        let id = Identifier::from(decl.name.inner()).over(decl.name.span());
        state
            .solver
            .declare(smt::Declaration::constant(id, sort).over(decl.span))?;

        state.mode = Mode::Assert;

        Ok(())
    }

    fn declare_fun(state: &mut State, decl: ast::DeclareFun) -> Result<()> {
        let mut sorts = Vec::new();
        for sort in decl.domain {
            sorts.push(Interpreter::sort_to_smt_term(&state.solver, &sort));
        }
        let range = Interpreter::sort_to_smt_term(&state.solver, &decl.range);
        let id = Identifier::from(decl.name.inner()).over(decl.name.span());

        state
            .solver
            .declare(smt::Declaration::function(id, sorts, range).over(decl.span))?;

        state.mode = Mode::Assert;

        Ok(())
    }

    fn declare_sort(state: &mut State, decl: ast::DeclareSort) -> Result<()> {
        if decl.arity.value > 0 {
            error!(
                decl.arity.span,
                "parametric uninterpreted sorts are not supported yet"
            );
            return Err(DiagnosticEmitted);
        }

        let id = Identifier::from(decl.name.inner()).over(decl.name.span());
        state
            .solver
            .declare(smt::Declaration::sort(id).over(decl.span))?;

        state.mode = Mode::Assert;

        Ok(())
    }

    fn define_const(state: &mut State, def: ast::DefineConst) -> Result<()> {
        let id = Identifier::from(def.name.inner()).over(def.name.span());
        let value = Interpreter::term_to_smt(&state.solver, def.body)?;
        let sort = Interpreter::sort_to_smt_term(&state.solver, &def.sort);

        state
            .solver
            .define(smt::Definition::constant(id, sort, value).over(def.span))?;

        state.mode = Mode::Assert;

        Ok(())
    }

    fn define_fun(state: &mut State, def: ast::FunctionDef) -> Result<()> {
        let mut domain = Vec::new();
        for arg in def.domain {
            domain.push(
                smt::Variable::new(
                    Identifier::from(arg.name.inner()).over(arg.name.span()),
                    Interpreter::sort_to_smt_term(&state.solver, &arg.sort),
                )
                .over(arg.span.clone()),
            );
        }

        let id = Identifier::from(def.name.inner()).over(def.name.span());
        let body = Interpreter::term_to_smt(&state.solver, def.body)?;
        let range = Interpreter::sort_to_smt_term(&state.solver, &def.range);

        state
            .solver
            .define(smt::Definition::function(id, domain, range, body).over(def.span))?;

        state.mode = Mode::Assert;

        Ok(())
    }

    fn pop(state: &mut State, pop: ast::Pop) -> Result<()> {
        state.solver.pop_n(pop.levels.value.to_usize().unwrap())?;

        state.mode = Mode::Assert;

        Ok(())
    }

    fn push(state: &mut State, push: ast::Push) -> Result<()> {
        for _ in 0..push.levels.value.to_usize().unwrap() {
            state.solver.push()?;
        }

        state.mode = Mode::Assert;

        Ok(())
    }

    fn get_value(state: &mut State, cmd: ast::GetValue) -> Result<()> {
        if !state.config.produce_models {
            error!(
                cmd.span,
                "no model value can be produced if the `:produce-models` option is not set to true"
            );
            return Err(DiagnosticEmitted);
        }

        match state.solver.model()? {
            Some(model) => {
                let mut values = Vec::new();
                for term in cmd.terms {
                    match term {
                        ast::Term::Identifier(ast::QualifiedIdentifier { id, .. }) => match id {
                            ast::Identifier::Symbol(symbol) => {
                                let symbol = Identifier::from(symbol.inner()).over(symbol.span());
                                let functions = state.solver.env().functions.clone();
                                let function = functions.lookup(symbol.clone()).one()?;
                                let value = model.value(function)?;

                                if let Some(value) = value {
                                    values.push((
                                        ast::Term::from(ast::Symbol::new(function.name()).unwrap()),
                                        ast::Term::from(value.into_term_in(state.solver.pool())),
                                    ))
                                } else {
                                    error!(
                                        symbol.span(),
                                        "no value for symbol `{}` in the model", symbol
                                    );
                                    return Err(DiagnosticEmitted);
                                }
                            }
                            ast::Identifier::Application(_) => todo!(),
                        },
                        _ => todo!(),
                    }
                }
                Interpreter::response(
                    &mut *state.output,
                    ast::Response::GetValue(ast::GetValueResponse { values, span: None }),
                )?;

                Ok(())
            }
            None => {
                error!(cmd.span, "model not available");
                Err(DiagnosticEmitted)
            }
        }
    }
}
