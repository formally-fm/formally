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
use formally::{
    smt::{
        backend::{Backend, z3::Z3},
        logics::Logic,
    },
    support::*,
};

use crate::type_check::TypeCheck;
use derive_more::From;
use std::{
    fmt::{Debug, Formatter},
    rc::Rc,
};

/// Configuration for SMT solvers.
///
/// This is a simple struct holding many parameters used to instantiate SMT solvers. [Config]
/// instances are usually constructed from the default one by changing the desired parameters and
/// then passed to [Solver::new()] and related constructors. Fields are public and can be set
/// arbitrarily but a builder method for each parameter is also provided, for convenience.
///
/// Example:
/// ```
/// # mod formally {
/// #     pub extern crate formally_smt as smt;
/// #     pub extern crate formally_support as support;
/// # }
/// # use formally::{smt::{*, backend::z3::Z3}, support::*};
/// # fn main() -> Result<()> {
/// let config =
///     Config::default()
///         .logic("LIA")
///         .produce_models(true);
///
/// let solver = Solver::new(&config)?;
/// // ...
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, Default)]
pub struct Config {
    /// The name of the logic to instantiate the solver for.
    ///
    /// A [None] value is the default, which means a logic is not selected and the solver will
    /// accept symbols from all the known theories, as if "ALL" had been specified (such as
    /// with the `(set-logic ALL)` command in SMT-LIBv2).
    pub logic: Option<Identifier<'static>>,
    /// Whether the solver has to activate the machinery for generating models for satisfiable
    /// instances.
    pub produce_models: bool,
}

impl Config {
    /// Create a new [Config] object with default values.
    pub fn new() -> Config {
        Config::default()
    }

    /// Set the `logic` fied.
    pub fn logic<'a>(self, logic: impl Into<Identifier<'a>>) -> Config {
        Config {
            logic: Some(logic.into().into_owned()),
            ..self
        }
    }

    /// Set the `produce_models` fied.
    pub fn produce_models(self, produce_models: bool) -> Config {
        Config {
            produce_models,
            ..self
        }
    }
}

/// Wrap two [Scope] objects for declared/defined functions and sorts.
///
/// SMT-LIBv2 specifies two different namespaces for function and sort symbols in a module.
/// It is therefore common, especially in backends, to keep around two `Scope<Function>` objects
/// keeping track of the two namespaces. [Env] is a small utility to keep two scopes together and
/// perform lookups in the right one as needed.
#[derive(Default, Clone)]
pub struct Env {
    pub functions: Scope<Function>,
    pub sorts: Scope<Function>,
}

impl Env {
    /// Creates an [Env] with empty scopes.
    pub fn new() -> Self {
        Env::default()
    }
}

/// Select which scope to use in [Env::lookup()] and [Term::resolve()].
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum Role {
    /// Lookup/resolve a function.
    Function,
    /// Lookup/resolve a sort.
    Sort,
}

impl Env {
    /// Calls [lookup()](Scope::lookup) on the functions or the sorts scope depending on `role`.
    ///
    /// If `role` is `Role::Function`, the call goes to the functions scope. Otherwise
    /// (`Role::Sort`), to the sorts scope.
    pub fn lookup<'i>(&self, name: Identifier<'i>, role: Role) -> LookupSet<'_, 'i, Function> {
        match role {
            Role::Function => self.functions.lookup(name),
            Role::Sort => self.sorts.lookup(name),
        }
    }

    /// Creates a new [Env] from a parent one using the two scopes of the parent as parents of each
    /// single scope.
    pub fn with_parent(self, parent: Env) -> Env {
        Env {
            functions: self.functions.with_parent(parent.functions),
            sorts: self.sorts.with_parent(parent.sorts),
        }
    }
}

#[derive(Clone)]
pub struct TermManager {
    backend_manager: Rc<dyn backend::Manager>,
    pool: Rc<dyn TermPool>,
}

impl Debug for TermManager {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "TermManager {{ backend: {} }}",
            self.backend_manager.backend().name()
        )
    }
}

impl Default for TermManager {
    fn default() -> Self {
        TermManager::new(Z3)
    }
}

impl TermPool for TermManager {
    fn shared(&self, kind: TermKind) -> Term {
        self.pool.shared(kind)
    }
}

impl TermManager {
    pub fn new(backend: impl Backend) -> TermManager {
        TermManager {
            backend_manager: Rc::from(backend.manager()),
            pool: Rc::new(HashPool::new()),
        }
    }
    
    pub fn new_with_pool(backend: impl Backend, pool: Rc<dyn TermPool>) -> TermManager {
        TermManager {
            backend_manager: Rc::from(backend.manager()),
            pool,
        }
    } 
}

/// Main interface to SMT solvers.
///
/// The [Solver] type is at the core of [formally::smt], providing high-level access to backend
/// solvers.
///
/// Solvers are instantiated from [Config] values from which they take also their [Context] used to
/// emit diagnostics and cache type lookups for [terms](Term). See the [overview](formally::smt) for
/// simple usage examples.
///
/// [Solver] is responsible to implement name lookup on terms used in definitions and assertions.
/// A term such as `term!(> p q)` contains three unresolved symbols, `">"`, `"p"`, and `"q"`.
/// Without name resolution the term would be unusable by the backends. [Solver] performs name
/// resolution by calling [Term::resolve()] appropriately using an [Env] instance that holds all
/// the symbols declared and defined and which refers to the current logics' theory as parent.
/// This allows the free use of names in the [term] macro and saves users and clients from the
/// burden of keeping track of the names of the used entities.
///
/// [Solver] implements [Stack] to provide the usual incremental interface of most SAT/SMT solvers.
pub struct Solver {
    backend_solver: Box<dyn backend::Solver>,
    env: Env,
    manager: Rc<TermManager>,
}

impl Solver {
    pub fn new_with_manager(
        config: &Config,
        manager: impl Into<Rc<TermManager>>,
    ) -> Result<Solver> {
        let manager = manager.into();
        let backend_solver = manager
            .backend_manager
            .backend()
            .solver(config, manager.backend_manager.clone())?;
        Ok(Solver {
            env: Env::new().with_parent(backend_solver.logic().theory().env()),
            backend_solver,
            manager,
        })
    }

    pub fn new_with_backend(config: &Config, backend: impl Backend) -> Result<Solver> {
        Solver::new_with_manager(config, TermManager::new(backend))
    }

    pub fn new(config: &Config) -> Result<Solver> {
        Solver::new_with_manager(config, TermManager::default())
    }

    /// Get the currently selected [Logic].
    pub fn logic(&self) -> &dyn Logic {
        self.backend_solver.logic()
    }

    pub fn config(&self, config: &Config) -> Result<()> {
        Ok(self.backend_solver.config(config)?)
    }

    /// Get the [Env] object holding the current scopes for functions and sorts declared and defined
    /// in the solver.
    pub fn env(&self) -> Env {
        self.env.clone()
    }

    /// The current [Scope] for functions.
    pub fn functions(&self) -> Scope<Function> {
        self.env.functions.clone()
    }

    /// The current [Scope] for sorts.
    pub fn sorts(&self) -> Scope<Function> {
        self.env.sorts.clone()
    }

    pub fn resolve(&self, term: &Term, role: Role) -> Result<Term> {
        self.env.resolve(term, role, self)
    }

    /// Declare a function (or a constant, or a sort).
    ///
    /// As explained in the [overview](formally::smt), [declare()](Solver::declare) registers a
    /// [Declaration] value in the suitable scope and returns a [Declared] object that immutably
    /// points to the registered [Declaration] object. The registered [Declaration] object is
    /// not equal to the one passed as argument, in general, because [name
    /// resolution](Term::resolve()) occurs.
    ///
    /// Remember that constants are seen as functions with no arguments, and sorts as constants of
    /// the special sort [Sort::sort()]. See also [Declaration::function()],
    /// [Declaration::constant()], and [Declaration::sort()] for details.
    pub fn declare(&mut self, decl: Declaration) -> Result<Declared> {
        decl.type_check()?;
        let decl = Declared::new(decl);
        self.backend_solver
            .logic()
            .check_function(&decl.clone().into())?;

        if decl.range == Sort::sort() {
            self.env.sorts.add(&decl.name, decl.clone().into());
        } else {
            self.env.functions.add(&decl.name, decl.clone().into());
        }
        self.backend_solver.declare(decl.clone())?;

        Ok(decl)
    }

    /// Define a function (or a constant, or a sort).
    ///
    /// As explained in the [overview](formally::smt), [define()](Solver::define) registers a
    /// [Definition] value in the suitable scope and returns a [Defined] object that immutably
    /// points to the registered [Definition] object. The registered [Definition] object is not
    /// equal to the one passed as argument, in general, because [name
    /// resolution](Term::resolve()) occurs.
    ///
    /// Remember that constants are seen as functions with no arguments, and sorts as constants of
    /// the special sort [Sort::sort()]. See also [Definition::function()],
    /// [Definition::constant()], and [Definition::sort()] for details.
    pub fn define<T: ToTerm>(&mut self, def: Definition<T>) -> Result<Defined> {
        let mut def = def.map(|body| body.to_term_in(self));

        let mut nested = Env::new().with_parent(self.env());
        for var in &def.domain {
            var.sort().type_check()?;
            nested
                .functions
                .add(var.name(), Function::Variable(var.clone()));
        }

        def.body = nested.resolve(&def.body, Role::Function, self)?;
        def.body.type_check()?;

        let def = Defined::new(def);
        self.backend_solver
            .logic()
            .check_function(&def.clone().into())?;

        if def.range == Sort::sort() {
            self.env.sorts.add(&def.name, def.clone().into());
        } else {
            self.env.functions.add(&def.name, def.clone().into());
        }
        self.backend_solver.define(def.clone())?;

        Ok(def)
    }

    /// Assert the given term to the current assertion stack
    ///
    /// The term undergoes [name resolution](Term::resolve()) and must be well-typed and be of
    /// sort [Core::Bool()](theories::Core::Bool()).
    pub fn require<T: ToTerm>(&mut self, term: T) -> Result<()> {
        let term = self.resolve(&term.to_term_in(&*self.manager), Role::Function)?;
        self.backend_solver.logic().check_term(&term)?;
        let sort = Sort::of(&term)?;

        if sort != theories::Core::Bool() {
            error!(term.span(), "can only assert Boolean terms");
            note!(term.span(), "asserted term is of sort `{}`", sort);
            return Err(DiagnosticEmitted);
        }

        self.backend_solver.require(&term)?;

        Ok(())
    }

    /// Check the satisfiability of the current assertions.
    ///
    /// The return value distinguishes between errors occurred during the solving process (`Err(_)`)
    /// and the case where no error occurred but the solver gave up on finding an answer
    /// (`Ok(Answer::Unknown)`).
    pub fn check(&mut self) -> Result<Answer> {
        match self.backend_solver.check()? {
            Some(true) => Ok(Answer::Yes),
            Some(false) => Ok(Answer::No),
            None => Ok(Answer::Unknown),
        }
    }

    /// Get a model of the current assertions, if they were found to be satisfiable.
    ///
    /// The return value distinguishes between errors occurred while extracting the model from the
    /// backend (`Err(_)`), and the case where no error occurred but there is no model available
    /// (`Ok(None)`), for example because the last call to [check()](Solver::check()) did not
    /// return `Ok(Answer::Yes)` or because model production was turned off in the solver's
    /// [Config].
    ///
    /// Note that the representation of model values is still incomplete and only Boolean and
    /// numerical values can be currently extracted.
    pub fn model(&self) -> Result<Option<Model<'_>>> {
        match self.backend_solver.model()? {
            Some(provider) => Ok(Some(Model {
                solver: self,
                provider,
            })),
            None => Ok(None),
        }
    }
}

impl TermPool for Solver {
    fn shared(&self, kind: TermKind) -> Term {
        self.manager.shared(kind)
    }
}

impl Stack for Solver {
    /// Push a new frame in the assertions stack.
    ///
    /// The assertion stack includes asserted terms and declared/defined entities.
    /// Currently, the `:global-declarations` option of SMT-LIBv2 is not supported.
    fn push(&mut self) -> Result<()> {
        Ok(self.backend_solver.push()?)
    }

    /// Pops a frame from the assertions stack, doing nothing if there is no frame to remove.
    ///
    /// The assertion stack includes asserted terms and declared/defined entities.
    /// Currently, the `:global-declarations` option of SMT-LIBv2 is not supported.
    fn pop_n(&mut self, n: usize) -> Result<()> {
        Ok(self.backend_solver.pop_n(n)?)
    }
}

/// Represent a value from a model.
#[derive(Debug, Clone, Hash, PartialEq, Eq, From)]
pub enum ModelValue {
    /// A Boolean value, model (assignment) of a Boolean declaration.
    Boolean(bool),
    /// A Boolean value, model of a declaration of sort [Ints::Int()](theories::Ints::Int()) or
    /// [Reals::Real()](theories::Reals::Real()).
    Constant(Constant),
}

impl From<ModelValue> for TermKind {
    fn from(value: ModelValue) -> Self {
        match value {
            ModelValue::Boolean(b) => TermKind::from(b),
            ModelValue::Constant(c) => TermKind::from(c),
        }
    }
}

/// A trait for types that can provide model values.
pub trait ModelProvider {
    fn value(&self, term: &Term) -> Option<ModelValue>;
}

/// The answer to a call to [Solver::check()].
#[derive(Clone, Default, PartialEq, Eq)]
pub enum Answer {
    /// The assertions are satisfiable.
    Yes,
    /// The assertions are unsatisfiable.
    No,
    /// A definite answer could not be found.
    #[default]
    Unknown,
}

impl Debug for Answer {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Answer::Yes => write!(f, "sat"),
            Answer::No => write!(f, "unsat"),
            Answer::Unknown => write!(f, "unknown"),
        }
    }
}

/// A model to the current set of assertions of a [Solver].
pub struct Model<'s> {
    solver: &'s Solver,
    provider: Box<dyn 's + ModelProvider>,
}

impl Model<'_> {
    pub fn value(&self, term: impl ToTerm) -> Option<ModelValue> {
        self.provider.value(&term.to_term_in(self.solver))
    }
}
