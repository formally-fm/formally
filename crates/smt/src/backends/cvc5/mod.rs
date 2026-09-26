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

mod bindings;

use crate::formally;
use formally::smt::{
    self, ToTerm as _,
    backends::{
        self, Backend,
        api::{self, Manager as _},
    },
    logic,
    logics::{Logic, LogicEx},
    theories,
};

use bindings as cvc5;

pub use cvc5::Sort;
pub use cvc5::Term;

use std::{cell::RefCell, ffi, ptr::NonNull, rc::Rc, sync::Arc};

type Result<T, E = backends::Error> = std::result::Result<T, E>;

/// The `cvc5` backend.
///
/// See the [high-level documentation](crate) for how to use the backend.
///
/// Some `cvc5`-specific features and the native [cvc5_sys] handles are available by downcasting the
/// result of the [Cvc5::solver()] method to `api::ApiSolver<cvc5::Solver>` and calling the
/// [api::ApiSolver::solver()] method.
#[smt::backend]
#[derive(Clone, Copy, Default)]
pub struct Cvc5;

/// The [api::Manager] implementation for the [Cvc5] backend.
#[derive(Default)]
pub struct Manager {
    cvc5manager: Rc<cvc5::TermManager>,
}

impl Manager {
    /// Return the underlying [cvc5_sys::TermManager] handle.
    pub fn cvc5_term_manager(&self) -> NonNull<cvc5_sys::TermManager> {
        self.cvc5manager.manager
    }
}

/// The [api::Solver] implementation for the [Cvc5] backend.
pub struct Solver {
    cvc5solver: Rc<cvc5::Solver>,
    logic: &'static dyn Logic,
    plugins: RefCell<Vec<Rc<dyn Plugin>>>,
    #[allow(clippy::vec_box)]
    cvc5_plugins: RefCell<Vec<Box<cvc5::Plugin>>>,
}

impl Solver {
    /// Return the underlying [cvc5_sys::Solver] handle.
    pub fn cvc5_solver(&self) -> NonNull<cvc5_sys::Solver> {
        self.cvc5solver.solver
    }
}

/// The [api::Model] implementation for the [Cvc5] backend.
pub struct Model<'s> {
    solver: &'s Solver,
}

logic! {
    /// The SMT logic corresponding to `(set-logic ALL)` for the [Cvc5] backend.
    name: pub ALL,
    theories: [
        theories::Core,
        theories::Ints,
        theories::Reals,
        theories::RealsInts,
        theories::Arrays
    ],
    requirements: [ ]
}

impl Backend for Cvc5 {
    fn name(&self) -> Result<&str> {
        Ok("cvc5")
    }

    fn manager(&self) -> Result<Box<dyn backends::Manager>> {
        Ok(Box::new(api::ApiManager::new(Manager::default())))
    }

    fn solver(
        &self,
        config: &smt::Config,
        manager: Rc<dyn backends::Manager>,
    ) -> Result<Box<dyn backends::Solver>> {
        Ok(Box::new(api::ApiSolver::<Solver>::new(
            self, config, manager,
        )?))
    }
}

impl api::Solver for Solver {
    type Manager = Manager;
    type Result = cvc5::Result;
    type Model<'s>
        = Model<'s>
    where
        Self: 's;

    fn new(
        config: &smt::Config,
        logic: Result<Option<&'static dyn Logic>>,
        manager: Rc<Self::Manager>,
    ) -> Result<Self> {
        let cvc5solver = Rc::new(cvc5::Solver::new(manager.cvc5manager.clone()));

        let logic = match logic? {
            Some(logic) => {
                cvc5solver.set_logic(logic.name());
                logic
            }
            None => &ALL,
        };

        let solver = Solver {
            cvc5solver,
            logic,
            plugins: RefCell::default(),
            cvc5_plugins: RefCell::default(),
        };

        solver.config(config)?;

        Ok(solver)
    }

    fn backend(&self) -> &'static <Self::Manager as api::Manager>::Backend {
        &Cvc5
    }

    fn logic(&self) -> &dyn Logic {
        self.logic
    }

    fn solver(&self) -> &<Self::Manager as api::Manager>::Solver {
        &self.cvc5solver
    }

    fn config(&self, config: &smt::Config) -> Result<()> {
        if config.produce_models {
            self.cvc5solver.set_option("produce-models", "true")
        } else {
            self.cvc5solver.set_option("produce-models", "false")
        }
        Ok(())
    }

    fn push(&mut self) -> Result<()> {
        self.cvc5solver.push();

        Ok(())
    }

    fn pop(&mut self, n: usize) -> Result<()> {
        self.cvc5solver.pop(n as u32);

        Ok(())
    }

    fn require(&mut self, term: <Self::Manager as api::Manager>::Term) -> Result<()> {
        self.cvc5solver.assert_formula(term);

        Ok(())
    }

    fn check(&self) -> Result<Self::Result> {
        Ok(self.cvc5solver.check_sat())
    }

    fn model(&self) -> Result<Self::Model<'_>> {
        Ok(Model { solver: self })
    }

    fn qe(
        &self,
        term: <Self::Manager as api::Manager>::Term,
    ) -> Result<<Self::Manager as api::Manager>::Term> {
        Ok(self.cvc5solver.get_quantifier_elimination(term))
    }
}

/// A plugin for the `cvc5` solver.
///
/// This mimics the [the cvc5 C API plug-in interface](https://cvc5.github.io/docs/cvc5-1.4.0/api/c/structs/cvc5plugin.html).
///
/// Install a plugin into a [cvc5::Solver](Solver) with the
/// [cvc5::Solver::add_plugin()](Solver::add_plugin()) method.
pub trait Plugin: 'static {
    /// Return a list of lemmas to add to the SAT solver. Called periodically, roughly at every SAT
    /// decision.
    fn check(&self) -> &[Term] {
        &[]
    }

    /// Notify SAT clause, called when `clause` is learned by the SAT solver.
    #[allow(unused)]
    fn notify_sat_clause(&self, clause: Term) {
        // nop
    }

    /// Notify theory lemma, called when `lemma` is sent by a theory solver.
    #[allow(unused)]
    fn notify_theory_lemma(&self, lemma: Term) {
        // nop
    }

    /// Get the name of the plugin (for debugging).
    fn get_name() -> &'static ffi::CStr
    where
        Self: Sized;
}

impl Solver {
    unsafe extern "C" fn plugin_check<P: Plugin>(
        size: *mut usize,
        state: *mut ffi::c_void,
    ) -> *const *mut cvc5_sys::cvc5_term_t {
        unsafe {
            let slice = P::check(&*state.cast());
            size.write(slice.len());
            slice.as_ptr().cast()
        }
    }

    unsafe extern "C" fn plugin_notify_sat_clause<P: Plugin>(
        clause: *mut cvc5_sys::cvc5_term_t,
        state: *mut ffi::c_void,
    ) {
        unsafe { P::notify_sat_clause(&*state.cast(), NonNull::new(clause).unwrap()) }
    }

    unsafe extern "C" fn plugin_notify_theory_lemma<P: Plugin>(
        lemma: *mut cvc5_sys::cvc5_term_t,
        state: *mut ffi::c_void,
    ) {
        unsafe { P::notify_theory_lemma(&*state.cast(), NonNull::new(lemma).unwrap()) }
    }

    unsafe extern "C" fn plugin_get_name<P: Plugin>() -> *const ffi::c_char {
        P::get_name().as_ptr()
    }

    pub fn add_plugin<P: Plugin>(&self, plugin: Rc<P>) {
        let mut cvc5_plugin = Box::new(cvc5::Plugin {
            check: Some(Self::plugin_check::<P>),
            notify_sat_clause: Some(Self::plugin_notify_sat_clause::<P>),
            notify_theory_lemma: Some(Self::plugin_notify_theory_lemma::<P>),
            get_name: Some(Self::plugin_get_name::<P>),
            d_check_state: Rc::as_ptr(&plugin) as *mut ffi::c_void,
            d_notify_sat_clause_state: Rc::as_ptr(&plugin) as *mut ffi::c_void,
            d_notify_theory_lemma_state: Rc::as_ptr(&plugin) as *mut ffi::c_void,
        });

        self.cvc5solver
            .add_plugin(Box::as_mut_ptr(&mut cvc5_plugin));
        self.cvc5_plugins.borrow_mut().push(cvc5_plugin);
        self.plugins.borrow_mut().push(plugin);
    }
}

impl api::Model for Model<'_> {
    type Term = cvc5::Term;

    fn value(&self, term: Self::Term) -> Option<Self::Term> {
        Some(self.solver.cvc5solver.get_value(term))
    }
}

impl api::Manager for Manager {
    type ALL = ALL;
    type Backend = Cvc5;
    type Solver = cvc5::Solver;
    type FuncDecl = cvc5::Term;
    type Sort = cvc5::Sort;
    type Term = cvc5::Term;
    const FUNC_DEF_SUPPORTED: bool = true;

    fn backend(&self) -> &'static Self::Backend {
        &Cvc5
    }

    fn uninterpreted_sort(&self, name: &str) -> Result<cvc5::Sort> {
        Ok(self.cvc5manager.mk_uninterpreted_sort(name))
    }

    fn func_decl(
        &self,
        _solver: &cvc5::Solver,
        name: &str,
        sorts: &[cvc5::Sort],
        range: cvc5::Sort,
    ) -> Result<cvc5::Term> {
        if sorts.is_empty() {
            Ok(self.cvc5manager.mk_const(range, name))
        } else {
            Ok(self
                .cvc5manager
                .mk_const(self.cvc5manager.mk_fun_sort(sorts, range), name))
        }
    }

    fn func_def(
        &self,
        solver: &cvc5::Solver,
        name: &str,
        _sorts: &[cvc5::Sort],
        range: cvc5::Sort,
        variables: &[cvc5::Term],
        body: cvc5::Term,
    ) -> Result<cvc5::Term> {
        Ok(solver.define_fun(name, variables, range, body, false))
    }

    fn variable(&self, name: &str, sort: cvc5::Sort) -> Result<cvc5::Term> {
        Ok(self.cvc5manager.mk_var(sort, name))
    }

    fn application(&self, func: &cvc5::Term, arguments: &[cvc5::Term]) -> Result<cvc5::Term> {
        if arguments.is_empty() {
            return Ok(*func);
        }

        let mut args = Vec::new();
        args.push(*func);
        args.extend(arguments.iter().cloned());

        Ok(self.cvc5manager.mk_term(cvc5::Kind::ApplyUf, &args))
    }

    fn constant(&self, cnst: &smt::Constant) -> Result<cvc5::Term> {
        match cnst {
            smt::Constant::Integer { value, .. } => {
                Ok(self.cvc5manager.mk_integer(&value.to_string()))
            }
            smt::Constant::Rational { value, .. } => {
                Ok(self.cvc5manager.mk_real(&value.to_string()))
            }
        }
    }

    fn quantified(
        &self,
        quantifier: smt::Quantifier,
        variables: &[cvc5::Term],
        body: cvc5::Term,
    ) -> Result<cvc5::Term> {
        let varlist = self
            .cvc5manager
            .mk_term(cvc5::Kind::VariableList, variables);
        let kind = match quantifier {
            smt::Quantifier::Forall => cvc5::Kind::Forall,
            smt::Quantifier::Exists => cvc5::Kind::Exists,
        };

        Ok(self.cvc5manager.mk_term(kind, &[varlist, body]))
    }

    fn sort(
        &self,
        sort: <Self::ALL as LogicEx>::Sort<'_>,
        to_sort: impl Fn(&smt::SortArgument) -> Result<cvc5::Sort>,
        _to_value: impl Fn(&smt::SortArgument) -> Result<&smt::Integer>,
    ) -> Result<cvc5::Sort> {
        Ok(match sort {
            ALL_Sort::Core(sort) => match sort {
                theories::CoreSort::Bool => self.cvc5manager.get_boolean_sort(),
            },
            ALL_Sort::Ints(sort) => match sort {
                theories::IntsSort::Int => self.cvc5manager.get_integer_sort(),
            },
            ALL_Sort::Reals(sort) => match sort {
                theories::RealsSort::Real => self.cvc5manager.get_real_sort(),
            },
            ALL_Sort::RealsInts(_) => unreachable!(),
            ALL_Sort::Arrays(sort) => match sort {
                theories::ArraysSort::Array(index, range) => {
                    let index = to_sort(index)?;
                    let range = to_sort(range)?;

                    self.cvc5manager.mk_array_sort(index, range)
                }
            },
        })
    }

    fn atom(
        &self,
        atom: <Self::ALL as LogicEx>::Atom<'_>,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<cvc5::Term>>,
    ) -> Result<cvc5::Term> {
        match atom {
            ALL_Atom::Core(atom) => self.core_atom_to_cvc5(atom, to_term, to_terms),
            ALL_Atom::Ints(atom) => self.ints_atom_to_cvc5(atom, to_term, to_terms),
            ALL_Atom::Reals(atom) => self.reals_atom_to_cvc5(atom, to_term, to_terms),
            ALL_Atom::RealsInts(atom) => self.reals_ints_atom_to_cvc5(atom, to_term),
            ALL_Atom::Arrays(atom) => self.arrays_atom_to_cvc5(atom, to_term),
        }
    }

    fn export(
        &self,
        term: cvc5::Term,
        pool: &dyn smt::TermPool,
        to_func: impl Clone + Fn(cvc5::Term) -> Option<smt::UserFunction>,
        to_sort: impl Clone + Fn(cvc5::Sort) -> Option<smt::Sort>,
    ) -> Option<smt::Term> {
        use smt::theories::*;

        match self.cvc5manager.get_term_kind(term) {
            cvc5::Kind::Constant => to_func(term).map(|f| f.into_term_in(pool)),
            cvc5::Kind::Variable => to_func(term).map(|f| f.into_term_in(pool)),
            cvc5::Kind::ApplyUf => {
                let mut children = Vec::new();
                let head = to_func(self.cvc5manager.get_term_child(term, 0))?;
                for child in 1..self.cvc5manager.get_term_num_children(term) {
                    children.push(self.export(
                        self.cvc5manager.get_term_child(term, child),
                        pool,
                        to_func.clone(),
                        to_sort.clone(),
                    )?)
                }

                Some(smt::term!(#head #(#children)*).into_term_in(pool))
            }
            cvc5::Kind::ConstBoolean => {
                if self.cvc5manager.get_boolean_value(term).unwrap() {
                    Some(Core::True().into_term_in(pool))
                } else {
                    Some(Core::False().into_term_in(pool))
                }
            }
            cvc5::Kind::ConstRational => Some(
                smt::Constant::Rational {
                    value: Arc::new(self.cvc5manager.get_real_value(term).unwrap()),
                    span: None,
                }
                .into_term_in(pool),
            ),
            cvc5::Kind::ConstInteger => Some(
                smt::Constant::Integer {
                    value: Arc::new(self.cvc5manager.get_integer_value(term).unwrap()),
                    span: None,
                }
                .into_term_in(pool),
            ),
            cvc5::Kind::Forall | cvc5::Kind::Exists => todo!(),
            _ => self.export_app(term, pool, to_func, to_sort),
        }
    }
}

impl Manager {
    fn core_atom_to_cvc5(
        &self,
        atom: theories::CoreAtom,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<cvc5::Term>>,
    ) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::CoreAtom::True => self.cvc5manager.mk_boolean(true),
            theories::CoreAtom::False => self.cvc5manager.mk_boolean(false),
            theories::CoreAtom::Not(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Not, &[arg])
            }
            theories::CoreAtom::Implies(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Implies, &args)
            }
            theories::CoreAtom::And(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::And, &args)
            }
            theories::CoreAtom::Or(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Or, &args)
            }
            theories::CoreAtom::Xor(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Xor, &args)
            }
            theories::CoreAtom::Equals(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Equal, &args)
            }
            theories::CoreAtom::Distinct(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Distinct, &args)
            }
            theories::CoreAtom::Ite(cond, then, else_) => {
                let cond = to_term(cond)?;
                let then = to_term(then)?;
                let else_ = to_term(else_)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::Ite, &[cond, then, else_])
            }
        })
    }

    fn ints_atom_to_cvc5(
        &self,
        atom: theories::IntsAtom,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<cvc5::Term>>,
    ) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::IntsAtom::Unary_minus(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Neg, &[arg])
            }
            theories::IntsAtom::Minus(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Sub, &args)
            }
            theories::IntsAtom::Plus(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Add, &args)
            }
            theories::IntsAtom::Mult(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Mult, &args)
            }
            theories::IntsAtom::Div(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::IntsDivision, &args)
            }
            theories::IntsAtom::Mod_(left, right) => {
                let left = to_term(left)?;
                let right = to_term(right)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::IntsModulus, &[left, right])
            }
            theories::IntsAtom::Abs(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Abs, &[arg])
            }
            theories::IntsAtom::Le(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Leq, &args)
            }
            theories::IntsAtom::Lt(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Lt, &args)
            }
            theories::IntsAtom::Ge(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Geq, &args)
            }
            theories::IntsAtom::Gt(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Gt, &args)
            }
        })
    }

    fn reals_atom_to_cvc5(
        &self,
        atom: theories::RealsAtom,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
        to_terms: impl Fn(&[smt::Term]) -> Result<Vec<cvc5::Term>>,
    ) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::RealsAtom::Unary_minus(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::Neg, &[arg])
            }
            theories::RealsAtom::Minus(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Sub, &args)
            }
            theories::RealsAtom::Plus(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Add, &args)
            }
            theories::RealsAtom::Mult(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Mult, &args)
            }
            theories::RealsAtom::Div(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Division, &args)
            }
            theories::RealsAtom::Le(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Leq, &args)
            }
            theories::RealsAtom::Lt(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Lt, &args)
            }
            theories::RealsAtom::Ge(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Geq, &args)
            }
            theories::RealsAtom::Gt(args) => {
                let args = to_terms(args)?;
                self.cvc5manager.mk_term(cvc5::Kind::Gt, &args)
            }
        })
    }

    fn reals_ints_atom_to_cvc5(
        &self,
        atom: theories::RealsIntsAtom,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
    ) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::RealsIntsAtom::To_real(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::ToReal, &[arg])
            }
            theories::RealsIntsAtom::To_int(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::ToInteger, &[arg])
            }
            theories::RealsIntsAtom::Is_int(arg) => {
                let arg = to_term(arg)?;
                self.cvc5manager.mk_term(cvc5::Kind::IsInteger, &[arg])
            }
        })
    }

    fn arrays_atom_to_cvc5(
        &self,
        atom: theories::ArraysAtom,
        to_term: impl Fn(&smt::Term) -> Result<cvc5::Term>,
    ) -> Result<cvc5::Term> {
        Ok(match atom {
            theories::ArraysAtom::Select(array, index) => {
                let array = to_term(array)?;
                let index = to_term(index)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::Select, &[array, index])
            }
            theories::ArraysAtom::Store(array, index, elem) => {
                let array = to_term(array)?;
                let index = to_term(index)?;
                let elem = to_term(elem)?;

                self.cvc5manager
                    .mk_term(cvc5::Kind::Store, &[array, index, elem])
            }
        })
    }

    fn export_app(
        &self,
        term: cvc5::Term,
        pool: &dyn smt::TermPool,
        to_func: impl Clone + Fn(cvc5::Term) -> Option<smt::UserFunction>,
        to_sort: impl Clone + Fn(cvc5::Sort) -> Option<smt::Sort>,
    ) -> Option<smt::Term> {
        use smt::theories::*;

        let mut intargs = true;
        let mut realargs = true;

        let numchildren = self.cvc5manager.get_term_num_children(term);
        let mut children = Vec::with_capacity(numchildren);
        for child in 0..numchildren {
            let child = self.cvc5manager.get_term_child(term, child);
            let sort = self.cvc5manager.get_term_sort(child);

            intargs = intargs && self.cvc5manager.sort_is_integer(sort);
            realargs = realargs && self.cvc5manager.sort_is_real(sort);

            children.push(self.export(child, pool, to_func.clone(), to_sort.clone())?);
        }

        let head = match self.cvc5manager.get_term_kind(term) {
            cvc5::Kind::Equal => Core::equals(),
            cvc5::Kind::Distinct => Core::distinct(),
            cvc5::Kind::Not => Core::not(),
            cvc5::Kind::And => Core::and(),
            cvc5::Kind::Implies => Core::implies(),
            cvc5::Kind::Or => Core::or(),
            cvc5::Kind::Xor => Core::xor(),
            cvc5::Kind::Ite => Core::ite(),
            cvc5::Kind::Add if intargs => Ints::plus(),
            cvc5::Kind::Add if realargs => Reals::plus(),
            cvc5::Kind::Mult if intargs => Ints::mult(),
            cvc5::Kind::Mult if realargs => Reals::mult(),
            cvc5::Kind::Sub if intargs => Ints::minus(),
            cvc5::Kind::Sub if realargs => Reals::minus(),
            cvc5::Kind::Neg if intargs => Ints::unary_minus(),
            cvc5::Kind::Neg if realargs => Reals::unary_minus(),
            cvc5::Kind::Division => Reals::div(),
            cvc5::Kind::IntsDivision => Ints::div(),
            cvc5::Kind::IntsModulus => Ints::mod_(),
            cvc5::Kind::Abs => Ints::abs(),
            cvc5::Kind::Lt if intargs => Ints::lt(),
            cvc5::Kind::Lt if realargs => Reals::lt(),
            cvc5::Kind::Leq if intargs => Ints::le(),
            cvc5::Kind::Leq if realargs => Reals::le(),
            cvc5::Kind::Gt if intargs => Ints::gt(),
            cvc5::Kind::Gt if realargs => Reals::gt(),
            cvc5::Kind::Geq if intargs => Ints::ge(),
            cvc5::Kind::Geq if realargs => Reals::ge(),
            cvc5::Kind::IsInteger => RealsInts::is_int(),
            cvc5::Kind::ToInteger => RealsInts::to_int(),
            cvc5::Kind::ToReal => RealsInts::to_real(),
            cvc5::Kind::Select => Arrays::select(),
            cvc5::Kind::Store => Arrays::store(),
            _ => return None,
        };

        Some(smt::term!(#head #(#children)*).into_term_in(pool))
    }
}
