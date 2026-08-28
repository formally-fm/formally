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
    io::print::Print,
    smt::{self, Config, ToTerm, backends::Backend, smtlib::ast},
    support::*,
};

use std::{fmt::Debug, io};

use thiserror::Error;

mod translate;

mod emitter;
pub use emitter::*;

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
    Start(Config, &'static dyn Backend),
    #[doc(hidden)]
    Started(State),
    #[doc(hidden)]
    Exited(Config),
}

#[derive(Debug, Clone, Copy)]
enum Mode {
    Assert,
    Sat,
    Unsat,
}

struct State {
    mode: Mode,
    config: Config,
    solver: smt::Solver,
}

impl Default for Interpreter {
    fn default() -> Self {
        Interpreter::Start(Config::default(), &smt::backends::Default)
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
    pub fn new(config: Config) -> Interpreter {
        Interpreter::Start(config, &smt::backends::Default)
    }

    pub fn with_backend(config: Config, backend: &'static dyn Backend) -> Interpreter {
        Interpreter::Start(config, backend)
    }

    /// Execute a command.
    pub fn command(&mut self, command: ast::Command) -> Result<()> {
        use Interpreter::*;
        use ast::Command::*;

        match self {
            Start(config, _) => match command {
                Echo(msg) => Self::echo(config, msg),
                Exit(_) => Self::exit(self),
                GetInfo(_) => Self::unsupported(config),
                GetOption(_) => Self::unsupported(config),
                Reset(_) => Self::unsupported(config),
                ResetAssertions(_) => Self::unsupported(config),
                SetInfo(_) => Self::unsupported(config),
                SetLogic(sl) => Self::set_logic(self, sl),
                SetOption(so) => Self::set_option_start(config, so),
                command => Self::fail(config, RequiredMode::Started, command),
            },
            Started(state) => match command {
                Assert(assert) => Self::assert(state, assert),
                CheckSat(_) => Self::check_sat(state),
                CheckSatAssuming(_) => Self::unsupported(&state.config),
                DeclareConst(decl) => Self::declare_const(state, decl),
                DeclareDatatype(_) => Self::unsupported(&state.config),
                DeclareDatatypes(_) => Self::unsupported(&state.config),
                DeclareFun(decl) => Self::declare_fun(state, decl),
                DeclareSort(decl) => Self::declare_sort(state, decl),
                DeclareSortParameter(_) => Self::unsupported(&state.config),
                DefineConst(def) => Self::define_const(state, def),
                DefineFun(def) => Self::define_fun(state, def),
                DefineFunRec(_) => Self::unsupported(&state.config),
                DefineFunsRec(_) => Self::unsupported(&state.config),
                DefineSort(_) => Self::unsupported(&state.config),
                Echo(msg) => Self::echo(&state.config, msg),
                Exit(_) => Self::exit(self),
                GetAssertions(_) => Self::unsupported(&state.config),
                GetInfo(_) => Self::unsupported(&state.config),
                GetOption(_) => Self::unsupported(&state.config),
                Pop(pop) => Self::pop(state, pop),
                Push(push) => Self::push(state, push),
                Reset(_) => Self::unsupported(&state.config),
                ResetAssertions(_) => Self::unsupported(&state.config),
                SetInfo(_) => Self::unsupported(&state.config),
                SetOption(so) => Self::set_option_started(state, so),
                _ => match (command, state.mode) {
                    (GetAssignments(_), Mode::Sat) => Self::unsupported(&state.config),
                    (GetModel(_), Mode::Sat) => Self::unsupported(&state.config),
                    (GetValue(cmd), Mode::Sat) => Self::get_value(state, cmd),
                    (GetProof(_), Mode::Unsat) => Self::unsupported(&state.config),
                    (GetUnsatAssumptions(_), Mode::Unsat) => Self::unsupported(&state.config),
                    (GetUnsatCore(_), Mode::Unsat) => Self::unsupported(&state.config),
                    (command @ (GetModel(_) | GetValue(_) | GetAssignments(_)), _) => {
                        Self::fail(&state.config, RequiredMode::Sat, command)
                    }
                    (command @ (GetProof(_) | GetUnsatAssumptions(_) | GetUnsatCore(_)), _) => {
                        Self::fail(&state.config, RequiredMode::Unsat, command)
                    }
                    (command, _) => Self::fail(&state.config, RequiredMode::Start, command),
                },
            },
            Exited(_) => self.exited(command),
        }
    }

    /// Tell if a `(set-logic)` (but no `(exit)`) command has been executed.
    pub fn has_started(&self) -> bool {
        !matches!(self, Interpreter::Start(_, _))
    }

    /// Tell if an `(exit)` command has been executed.
    pub fn has_exited(&self) -> bool {
        matches!(self, Interpreter::Exited(_))
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

    fn unsupported(config: &Config) -> Result<()> {
        Interpreter::response(config, ast::Response::Unsupported)
    }

    // TODO: supporting setting the output stream through the `Config`
    fn response(_config: &Config, response: impl Print) -> Result<()> {
        match response.println(&mut io::stdout()) {
            Ok(_) => Ok(()),
            Err(err) => {
                error!(None, "input/output error: {err}");
                Err(DiagnosticEmitted)
            }
        }
    }

    fn echo(config: &Config, msg: ast::StringLiteral) -> Result<()> {
        Interpreter::response(
            config,
            ast::Response::Echo(ast::EchoResponse {
                msg: msg.clone(),
                span: None,
            }),
        )
    }

    fn exit(&mut self) -> Result<()> {
        let config = match self {
            Interpreter::Start(config, _) => config,
            Interpreter::Started(State { config, .. }) => config,
            Interpreter::Exited(config) => config,
        };
        *self = Interpreter::Exited(std::mem::take(config));

        Ok(())
    }

    fn set_logic(&mut self, sl: ast::SetLogic) -> Result<()> {
        let Interpreter::Start(mut config, backend) = std::mem::take(self) else {
            return Ok(());
        };

        config.logic = match sl.logic.inner() {
            "ALL" => None,
            logic => Some(Identifier::from(logic).into_owned().over(sl.logic.span())),
        };

        match smt::Solver::with_backend(&config, backend) {
            Ok(solver) => {
                *self = Interpreter::Started(State {
                    mode: Mode::Assert,
                    config,
                    solver,
                })
            }
            Err(_) => *self = Interpreter::Start(config, backend),
        }

        Ok(())
    }

    fn set_option_start(config: &mut Config, so: ast::SetOption) -> Result<()> {
        match so.option {
            ast::AstOption::ProduceModels(pm) => {
                config.produce_models = pm.value;
                Ok(())
            }
            _ => Self::unsupported(config),
        }
    }

    fn set_option_started(state: &mut State, so: ast::SetOption) -> Result<()> {
        Self::set_option_start(&mut state.config, so)?;

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

        Interpreter::response(&state.config, response)?;
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
                    &state.config,
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
