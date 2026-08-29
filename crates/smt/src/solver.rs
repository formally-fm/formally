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

use crate::formally;
use formally::{
    smt::{backends::Backend, logics::Logic, *},
    support::*,
};

use std::{
    cell::RefCell,
    collections::HashSet,
    fmt::{Debug, Formatter},
    rc::Rc,
    sync::Arc,
};

/// Configuration for SMT solvers.
///
/// This is a simple struct holding some parameters used to instantiate SMT solvers. [Config]
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
/// # use formally::{smt::{*, backends::z3::Z3}, support::*};
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
    ///
    /// Note that the `"ALL"` string itself has no special meaning, but is looked up as any other
    /// logic name (and probably not found).
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

/// Select which scope to use in [Env::lookup()] and [Resolve::resolve()].
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

/// Type that manages the backend's "term manager" (or "context") and subterm sharing.
///
/// Most SMT APIs separate the "term manager" (also called "context"), responsible for managing
/// subterm sharing and the creation and lifetime management of term objects, from the "solver",
/// which is responsible for the actual reasoning.
///
/// [formally::smt] does the same, where [TermManager] manages subterm sharing (through an
/// underlying instance of [TermPool]) and a handle to the underlying backend's term manager (e.g.
/// [TermManager](cvc5_sys::TermManager) in cvc5 or [Z3_context](z3_sys::Z3_context) in Z3).
///
/// The handle to the underlying backend's manager performs the conversion from [Term] to the
/// internal representation of terms of the backend (e.g. [Z3_ast](z3_sys::Z3_ast) in Z3).
///
/// A term manager is mainly used by giving a reference to it to one or more [Solver] instances.
/// Solvers built on the same manager can use the same terms which will be converted to the
/// underlying backend's representation only once, saving time.
///
/// Example:
/// ```
/// # mod formally {
/// #    pub extern crate formally_smt as smt;
/// #    pub extern crate formally_support as support;
/// # }
///  use formally::{smt::{*, backends::z3::Z3}};
/// # use formally::support::*;
///
/// # use std::rc::Rc;
/// #
/// # fn main() -> Result<()> {
///  let manager = Rc::new(TermManager::with_backend(Z3)?);
///  let config = Config::new();
///  let mut slv1 = Solver::with_manager(&config, manager.clone())?;
///  let mut slv2 = Solver::with_manager(&config, manager)?;
///
///  let x1 = slv1.declare(Declaration::constant("x", sort!(Int)))?;
///  let x2 = slv2.declare(Declaration::constant("x", sort!(Int)))?;
///
///  // Equivalent declarations/definitions result in the same `Declared`/`Defined` objects
///  assert_eq!(x1, x2);
///
///  let t1 = slv1.lookup(term!(* x x), Role::Function)?;
///  let t2 = slv2.lookup(term!(* x x), Role::Function)?;
///
///  // Equivalent terms result into the same [Term] objects
///  assert_eq!(t1, t2);
///
/// #   Ok(())
/// # }
/// ```
///
/// Since most SMT APIs are not threadsafe, [TermManager] is not [Send] nor [Sync] and must
/// therefore be accessed and used by a single thread only. However, one can construct it using
/// [TermManager::with_pool()] and passing a [DashPool] instance, which is a concurrent [TermPool]
/// that allows to at least share the same terms among different threads.
#[derive(Clone)]
pub struct TermManager {
    backend_manager: Rc<dyn backends::Manager>,
    pool: Rc<dyn TermPool>,
    decls: RefCell<HashSet<Arc<Declaration<Sort, Sort>>>>,
    defs: RefCell<HashSet<Arc<Definition<Sort, Sort, Term>>>>,
}

impl TermManager {
    fn decl(&self, decl: Declaration<Sort, Sort>) -> Declared {
        if let Some(decl) = self.decls.borrow().get(&decl) {
            return Declared(Nominal(decl.clone()));
        }

        let arc = Arc::new(decl);
        self.decls.borrow_mut().insert(arc.clone());

        Declared(Nominal(arc))
    }

    fn def(&self, def: Definition<Sort, Sort, Term>) -> Defined {
        if let Some(def) = self.defs.borrow().get(&def) {
            return Defined(Nominal(def.clone()));
        }

        let arc = Arc::new(def);
        self.defs.borrow_mut().insert(arc.clone());

        Defined(Nominal(arc))
    }
}

impl Debug for TermManager {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "TermManager {{ }}")
    }
}

impl TermManager {
    /// Construct a [TermManager] with the default backend (if any is available).
    pub fn new() -> Result<TermManager> {
        TermManager::with_backend(backends::default()?)
    }

    /// Construct a [TermManager] over a given [Backend] looked up by name, if it exists.
    pub fn with_backend_name<'a>(backend: impl Into<Identifier<'a>>) -> Result<TermManager> {
        let backend = backends::get(backend)?;

        TermManager::with_backend(backend)
    }

    /// Construct a [TermManager] over a given [Backend].
    pub fn with_backend(backend: impl Backend) -> Result<TermManager> {
        Ok(TermManager {
            backend_manager: Rc::from(backend.manager()?),
            pool: Rc::new(HashPool::new()),
            decls: RefCell::default(),
            defs: RefCell::default(),
        })
    }

    /// Construct a [TermManager] over a given [Backend] and [TermPool].
    pub fn with_pool(backend: impl Backend, pool: Rc<dyn TermPool>) -> Result<TermManager> {
        Ok(TermManager {
            backend_manager: Rc::from(backend.manager()?),
            pool,
            decls: RefCell::default(),
            defs: RefCell::default(),
        })
    }

    /// Return a reference to the underlying [TermPool].
    pub fn pool(&self) -> &dyn TermPool {
        &*self.pool
    }
}

/// Main interface to SMT solvers.
///
/// The [Solver] type is at the core of [formally::smt], providing high-level access to backend
/// solvers.
///
/// One can create a [Solver] in three ways, all accepting a [Config] reference to configure the
/// solver:
/// - [Solver::new()] creates a solver with a default backend and a dedicated [TermManager].
/// - [Solver::with_backend()] creates a solver with a given backend and a dedicated [TermManager].
/// - [Solver::with_manager()] creates a solver over the given [TermManager].
///
/// [Solver] is responsible to implement name lookup on terms used in definitions and assertions.
/// A term such as `term!(> p q)` contains three unresolved symbols, `">"`, `"p"`, and `"q"`.
/// Without name resolution the term would be unusable by the backends.
///
/// [Solver] implements [Stack] to provide the usual incremental interface of most SAT/SMT solvers.
pub struct Solver {
    backend_solver: Box<dyn backends::Solver>,
    env: Env,
    manager: Rc<TermManager>,
}

impl Solver {
    /// Create a [Solver] over a given [TermManager].
    ///
    /// Use this constructor to share the same [TermManager] among different solvers.
    pub fn with_manager(config: &Config, manager: impl Into<Rc<TermManager>>) -> Result<Solver> {
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

    /// Create a [Solver] over a given [Backend].
    ///
    /// Backends provided by this crate are defined in [formally::smt::backend](backends).
    pub fn with_backend(config: &Config, backend: impl Backend) -> Result<Solver> {
        Solver::with_manager(config, TermManager::with_backend(backend)?)
    }

    /// Create a [Solver] over the given [Backend] specified by name, if it exists.
    ///
    /// Backends provided by this crate are defined in [formally::smt::backend](backends).
    pub fn with_backend_name<'a>(
        config: &Config,
        backend: impl Into<Identifier<'a>>,
    ) -> Result<Solver> {
        Solver::with_manager(config, TermManager::with_backend_name(backend)?)
    }

    /// Create a [Solver] with a default backend and a dedicated [TermManager].
    pub fn new(config: &Config) -> Result<Solver> {
        Solver::with_manager(config, TermManager::new()?)
    }

    /// Get the currently selected [Logic].
    pub fn logic(&self) -> &dyn Logic {
        self.backend_solver.logic()
    }

    /// Set a new configuration for the solver.
    ///
    /// Note that the [logic](Config::logic) field is ignored when changing configuration after
    /// construction.
    pub fn config(&self, config: &Config) -> Result<()> {
        Ok(self.backend_solver.config(config)?)
    }

    /// Get the [Env] object holding the current scopes for functions and sorts declared and defined
    /// in the solver.
    pub fn env(&self) -> &Env {
        &self.env
    }

    /// Return a reference to the [TermPool] of the underlying [TermManager].
    pub fn pool(&self) -> &dyn TermPool {
        self.manager.pool()
    }

    /// Convert a [ToTerm] object into a [Term] including name resolution and type checking.
    ///
    /// This method uniques a [ToTerm] object into a [Term] using the [TermPool] of the underlying
    /// [TermManager] and then performs name resolution and type checking on the term.
    ///
    /// The resulting term is guaranteed to be well typed and fully resolved.
    ///
    /// Since terms can describe sorts as well, and SMT-LIBv2 defines two different namespaces for
    /// sorts and functions, the [Role] argument is needed to tell whether the term has to be
    /// interpreted as a sort or as a value term.
    pub fn lookup<T: ToTerm>(&self, term: T, role: Role) -> Result<Term> {
        let interned = term.into_term_in(self.manager.pool());
        let resolved = interned.resolve(self.env(), self.manager.pool(), role)?;
        resolved.type_check()?;

        Ok(resolved)
    }

    /// Convert a [ToSort] object into a [Sort] including name resolution and type checking.
    ///
    /// This method uniques a [ToSort] object into a [Sort] and then performs name resolution and
    /// type checking on the sort.
    ///
    /// The resulting sort is guaranteed to be well-formed and fully resolved.
    pub fn lookup_sort<S: ToSort>(&self, sort: &S) -> Result<Sort> {
        let resolved = sort.resolve(self.env(), self.manager.pool(), Role::Sort)?;
        resolved.type_check()?;

        Ok(resolved.try_into()?)
    }

    /// Create a fully resolved [Variable] by looking up its sort.
    ///
    /// This convenience method is equivalent to constructing a new [Variable] instance by
    /// calling [Solver::lookup_sort()] on the variable's sort.
    ///
    /// This method is needed to obtain a fully resolved [Variable] that can be used without further
    /// name resolution, but it is *not* needed when normally using variables to define functions
    /// that then refer to them by name.
    ///
    /// Example:
    /// ```
    /// # mod formally {
    /// #    pub extern crate formally_smt as smt;
    /// #    pub extern crate formally_support as support;
    /// # }
    ///  use formally::smt::*;
    /// # use formally::support::*;
    ///
    /// # fn main() -> Result<()> {
    ///  let config = Config::default();
    ///  let mut solver = Solver::new(&config)?;
    ///
    ///  // we construct the variable directly.
    ///  let x = Variable::new("x", sort!(Int));
    ///
    ///  // here the variable `x` is moved and `lookup_var()` is called internally.
    ///  let f = solver.define(Definition::function("f", [x], sort!(Int), term!(* x 2)));
    ///
    ///  // here the variable is #expanded in the term so we need to do name resolution earlier
    ///  let y = solver.lookup_var(&Variable::new("y", sort!(Int)))?;
    ///  let g = solver.define(Definition::function("g", [y.clone()], sort!(Int), term!(* #y 2)));
    ///
    ///  solver.require(term!(distinct (f 21) (g 21) 42))?;
    ///
    ///  assert_eq!(solver.check()?, Answer::No);
    ///
    /// #    Ok(())
    /// # }
    /// ```
    pub fn lookup_var<S: ToSort>(&self, variable: &Variable<S>) -> Result<Variable> {
        Ok(
            Variable::new(variable.name().clone(), self.lookup_sort(variable.sort())?)
                .over(variable.span()),
        )
    }

    /// Create a fully resolved [Binding] by looking up its sort and term.
    ///
    /// This convenience method is useful to infer automatically the sort of the binding from its
    /// defining term. It is designed to be used in pair with [Binding::new()].
    pub fn lookup_binding<T: ToTerm>(&self, binding: Binding<Infer, T>) -> Result<Binding> {
        let def = self.lookup(&binding.def, Role::Function)?;
        let sort = Sort::of(&def)?;

        let variable =
            Variable::new(binding.variable.name().clone(), sort).over(binding.variable.span());

        Ok(Binding {
            variable,
            def,
            span: binding.span,
        })
    }

    /// Declare a function (or a constant, or a sort).
    ///
    /// As explained in the [overview](formally::smt), [declare()](Solver::declare) registers a
    /// [Declaration] value in the suitable scope and returns a [Declared] object that immutably
    /// points to the registered [Declaration] object. The registered [Declaration] object is
    /// not equal to the one passed as argument, in general, because name
    /// resolution occurs.
    ///
    /// Remember that constants are seen as functions with no arguments, and sorts as constants of
    /// the special sort [Sort::sort()]. See also [Declaration::function()],
    /// [Declaration::constant()], and [Declaration::sort()] for details.
    pub fn declare<R: ToSort, B: ToSort>(&mut self, decl: Declaration<R, B>) -> Result<Declared> {
        let mut domain = Vec::with_capacity(decl.domain.len());
        for d in &decl.domain {
            domain.push(self.lookup_sort(d)?);
        }

        let decl = Declaration {
            name: decl.name,
            domain,
            range: self.lookup_sort(&decl.range)?,
            span: decl.span,
        };

        let decl = self.manager.decl(decl);
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
    /// equal to the one passed as argument, in general, because name
    /// resolution occurs.
    ///
    /// Remember that constants are seen as functions with no arguments, and sorts as constants of
    /// the special sort [Sort::sort()]. See also [Definition::function()],
    /// [Definition::constant()], and [Definition::sort()] for details.
    ///
    /// See also the documentation of [Solver::lookup_var()] to know when name lookup is needed to
    /// be done manually on the variables used in a definition.
    pub fn define<V: ToSort, R: ToSort, B: ToTerm>(
        &mut self,
        def: Definition<V, R, B>,
    ) -> Result<Defined> {
        let mut nested = Env::new().with_parent(self.env().clone());
        let mut domain = Vec::with_capacity(def.domain.len());
        for var in &def.domain {
            let var = self.lookup_var(var)?;
            domain.push(var.clone());
            nested
                .functions
                .add(var.name(), Function::Variable(var.clone()));
        }

        let range = self.lookup_sort(&def.range)?;
        let body = def.body.into_term_in(self.manager.pool()).resolve(
            &nested,
            self.manager.pool(),
            Role::Function,
        )?;
        let bodysort = body.type_check()?;

        if range == Sort::sort() {
            if bodysort != Sort::sort() {
                error!(
                    body.span(),
                    "expected sort in definition of `{}`, found `{}`", def.name, bodysort
                );
                return Err(DiagnosticEmitted);
            }
        } else {
            if bodysort != range {
                error!(
                    body.span(),
                    "expected term of sort `{}` in definition of `{}`, found `{}`",
                    range,
                    def.name,
                    bodysort
                );
                return Err(DiagnosticEmitted);
            }
        }

        let def = Definition {
            name: def.name,
            domain,
            range,
            body,
            span: None,
        };

        let def = self.manager.def(def);
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
    /// The term undergoes [name resolution](Resolve::resolve()) and must be well-typed and be of
    /// sort [Core::Bool()](theories::Core::Bool()).
    pub fn require<T: ToTerm>(&mut self, term: T) -> Result<()> {
        let term = self.lookup(term, Role::Function)?;
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

/// A trait for types that can provide model values.
pub trait ModelProvider {
    fn value(&self, term: &Term, pool: &dyn TermPool) -> Option<Term>;
}

/// The answer to a call to [Solver::check()].
#[derive(Clone, Copy, Default, PartialEq, Eq)]
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
    /// Get the value of a [ToTerm] object (after name lookup and type checking) in the model.
    pub fn value(&self, term: impl ToTerm) -> Result<Option<Term>> {
        Ok(self.provider.value(
            &self.solver.lookup(term, Role::Function)?,
            self.solver.pool(),
        ))
    }
}
