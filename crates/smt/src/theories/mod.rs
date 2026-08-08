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
// AUTHORS OR COPYRIGHT HOLDERS BE IntsBLE FOR ANY CLAIM, DAMAGES OR OTHER
// IntsBILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//

//! Declaration and usage of SMT-LIBv2 theories.
//!
//! This module contains everything regarding the declaration and usage of *theories* understood as
//! in the terminology of SMT-LIBv2.
//!
//! Most of the types declared in this module, except [CombinedTheory], are theories declared
//! through the [theory] macro, so one may want to look at its documentation as well.
//!
//! Each theory type is a unit struct (e.g. declared as `pub struct Ints;`, so it is instantiated as
//! `Ints`, not `Ints {}`) and exposes a set of associated functions, one for each symbol provided
//! by the theory. Function and constant symbols (e.g. [Ints::plus()] or [Core::True()] are
//! represented by returning a [Primitive] object. Sorts (e.g. [Ints::Int()]) return a [Sort].
//!
//! For parametric sorts (e.g. `(Array X Y)`) the corresponding functions accept a suitable number
//! of [sort arguments](SortArgument), so `(Array Int Int)` would be represented by
//! `Arrays::Array(Ints::Int(), Ints::Int())`. To access the [Function] corresponding to the sort
//! constructor `(Array X Y)` itself, one can write `Arrays::Array.to_constructor()` if the
//! [SortConstructor] trait is in scope.
//!
//! Theories are usually combined in a [Logic](logics::Logic), and the logic is what is set when
//! instantiating a [Solver]. When a logic is set to a solver, its symbols become in scope when
//! the solver applies [name resolution](Term::resolve()) to terms (e.g. those constructed with the
//! [term] macro). Therefore, in common usage of the framework, elements in this module should
//! rarely need to be mentioned directly.
//!
//! Instead, people implementing new *backends* will need to access this module quite
//! often. We refer to the documentation on [how to write a new backend](crate::backend) for
//! details.

use crate::*;
use formally::support::*;

mod macros;
mod standard;

pub use standard::*;

/// A trait for types representing SMT-LIBv2 theories.
///
/// The purpose of a theory object is that of providing an [environment](Env) providing the symbols
/// that the theory has to provide. Therefore, the trait expose two methods
/// ([functions()](Theory::functions()) and [sorts()](crate::theories::Theory::sorts()) to return
/// the corresponding function and sort scopes.
///
/// Implementing this trait directly is quite rare, since theories are usually better declared
/// using the [theory] macro.
pub trait Theory {
    fn functions(&self) -> Scope<Function>;

    fn sorts(&self) -> Scope<Function>;

    fn env(&self) -> Env {
        Env {
            functions: self.functions(),
            sorts: self.sorts(),
        }
    }
}

/// An instance of [Theory] combining multiple theories together.
pub struct CombinedTheory {
    functions: Scope<Function>,
    sorts: Scope<Function>,
}

impl CombinedTheory {
    /// Create a theory combining the given theories.
    pub fn new(theories: &[&dyn Theory]) -> CombinedTheory {
        let mut functions = Scope::new();
        let mut sorts = Scope::new();

        for theory in theories {
            functions.merge(&theory.functions());
            sorts.merge(&theory.sorts());
        }

        CombinedTheory { functions, sorts }
    }
}

impl Theory for CombinedTheory {
    fn functions(&self) -> Scope<Function> {
        self.functions.clone()
    }
    fn sorts(&self) -> Scope<Function> {
        self.sorts.clone()
    }
}

static SORT_DECL: PrimitiveData = PrimitiveData {
    name: Identifier::new("Sort"),
    parameters: Vec::new(),
    domain: Vec::new(),
    range: Sort::sort(),
    associativity: None,
};

impl Sort {
    /// The sort of sorts.
    ///
    /// [Sort::sort()] returns a special sort, not provided by any theory, which is the sort of
    /// terms representing sorts. In other words, a sort term such as `(Array Int Real)` has
    /// sort [Sort::sort()].
    /// ```
    /// # mod formally {
    /// #     pub extern crate formally_support as support;
    /// #     pub extern crate formally_smt as smt;
    /// # }
    /// # use formally::{smt::*, support::*};
    /// # fn main() -> Result<()> {
    /// let mut solver = Solver::new(&Config::default().logic("ALIA"))?;
    /// let array = term!(Array Int Int); // construct the term
    /// let array = array.resolve(&solver.env(), Role::Sort)?; // resolve the names
    /// let sort = array.type_check(solver.context())?; // type-check the term
    ///
    /// assert!(Sort::equal(&sort, &Sort::sort())); // the resulting sort is `Sort::sort()`
    /// # Ok(())
    /// # }
    /// ```
    #[allow(clippy::self_named_constructors)]
    pub const fn sort() -> Sort {
        Sort {
            head: Function::Primitive(Primitive(Nominal(SArc::Static(&SORT_DECL)))),
            arguments: Vec::new(),
            span: None,
        }
    }
}

/// Trait for function types returning sorts.
///
/// Any `Fn` type accepting references to [SortArgument] and returning [Sort] (currently up to six
/// arguments) implements this trait.
///
/// The [constructor()](SortConstructor::to_constructor()) method can be used to get the [Function]
/// corresponding to a sort constructor. For example, the sort `(Array Int Int)` is represented
/// by `Arrays::Array(Ints::Int(), Ints::Int())`, but the [Function] corresponding to the sort
/// constructor `(Array X Y)` is `Arrays::Array.to_constructor()`. This is mainly needed in
/// backends, so we refer to the documentation about [how to write a new backend](backend).
pub trait SortConstructor<const ARITY: usize> {
    /// Get the [Function] associated with this sort constructor.
    fn to_constructor(&self) -> Function;
}

impl<F: Fn() -> Sort> SortConstructor<0> for F {
    fn to_constructor(&self) -> Function {
        self().head
    }
}

impl<F: Fn(&SortArgument) -> Sort> SortConstructor<1> for F {
    fn to_constructor(&self) -> Function {
        self(&SortArgument::Sort(Sort::sort())).head
    }
}

impl<F: Fn(&SortArgument, &SortArgument) -> Sort> SortConstructor<2> for F {
    fn to_constructor(&self) -> Function {
        self(
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
        )
        .head
    }
}

impl<F: Fn(&SortArgument, &SortArgument, &SortArgument) -> Sort> SortConstructor<3> for F {
    fn to_constructor(&self) -> Function {
        self(
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
        )
        .head
    }
}

impl<F: Fn(&SortArgument, &SortArgument, &SortArgument, &SortArgument) -> Sort> SortConstructor<4>
    for F
{
    fn to_constructor(&self) -> Function {
        self(
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
        )
        .head
    }
}

impl<F: Fn(&SortArgument, &SortArgument, &SortArgument, &SortArgument, &SortArgument) -> Sort>
    SortConstructor<5> for F
{
    fn to_constructor(&self) -> Function {
        self(
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
        )
        .head
    }
}

impl<
    F: Fn(
        &SortArgument,
        &SortArgument,
        &SortArgument,
        &SortArgument,
        &SortArgument,
        &SortArgument,
    ) -> Sort,
> SortConstructor<6> for F
{
    fn to_constructor(&self) -> Function {
        self(
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
            &SortArgument::Sort(Sort::sort()),
        )
        .head
    }
}
