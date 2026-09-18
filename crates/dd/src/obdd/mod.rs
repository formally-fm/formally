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

//! Concurrent ordered binary decision diagrams.
//!
//! This module provides a concurrent implementation of basic ordered binary decision diagrams
//! (OBDDs). Concurrent here means that starting from the same [Manager], diagrams can be freely
//! created and combined in multiple threads keeping canonicity and minimality.
//!
//! The API is very simple. A [Manager] is created from which [variables](Var) can be obtained,
//! which can be combined with Boolean operators to form more complex Boolean functions.
//! Every method of [Manager] takes `&self` and [Manager] is [Send] and [Sync], so everything can be
//! done concurrently from multiple threads.
//!
//! See [Manager] and [BDD] as starting points for the API.

mod inner;
mod order;

use crate::formally;
use formally::support::Nominal;

use itertools::Itertools;
use parking_lot::RwLock;

use std::{
    cmp::{self, max, min},
    fmt::{Debug, Formatter},
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
};

use inner::{Inner, SlotID};
pub use order::Level;
use order::VarID;

/// A variable.
///
/// Variables are obtained by [Manager::add_var()] and [Manager::add_vars()], which create variables
/// positioned at the bottom of the current variable order, or [Manager::add_var_after()] and
/// [Manager::add_vars_after()], which create variables positioned after a specific other variables
/// in the variable order. [Var] is a cheap [Copy] handle. Combining [Var]s with Boolean operators
/// (the bitwise ones, because Rust does not allow to overload `&&` and `||`) produces [BDD]
/// handles. Variables can be compared with `<` and similar operators, which compare their position
/// in the variable order.
///
/// Note that [Var] borrows its [Manager], so their lifetime is tied to the latter's.
///
/// Example:
/// ```
/// # mod formally {
/// #     pub extern crate formally_dd as dd;
/// # }
/// use formally::dd::obdd::Manager;
///
/// # fn main() {
/// let manager = Manager::new();
/// let p = manager.add_var();
/// let q = manager.add_var();
///
/// assert!(p < q);
///
/// let b = p & !p;
/// assert_eq!(b, false);
/// # }
/// ```
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Var<'m> {
    var: VarID,
    manager: Nominal<&'m Manager>,
}

impl Debug for Var<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Var({})", self.var.index())
    }
}

impl<'m> Var<'m> {
    fn new(var: VarID, manager: &'m Manager) -> Var<'m> {
        Var {
            var,
            manager: Nominal(manager),
        }
    }

    /// Return a reference to the [Manager] that created the variable.
    pub fn manager(&self) -> &'m Manager {
        self.manager.into_inner()
    }

    /// Return the *level*, i.e. the position in the variable order, of the variable.
    pub fn level(&self) -> Level {
        self.manager.inner.read().level_of(Some(self.var))
    }

    /// Return the next variable in the variable order.
    ///
    /// Return the variable that is positioned immediately after the current one in the variable
    /// order, or [None] if the variable is the last one.
    pub fn next(&self) -> Option<Var<'m>> {
        let inner = self.manager.inner.read();
        inner
            .var_at(inner.level_of(Some(self.var)) + 1)
            .map(|id| Var::new(id, self.manager()))
    }
}

impl PartialOrd for Var<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Var<'_> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        assert_eq!(
            self.manager, other.manager,
            "attempt to compare two `Var`s from different `Manager`s"
        );
        let inner = self.manager.inner.read();
        inner
            .level_of(Some(self.var))
            .cmp(&inner.level_of(Some(other.var)))
    }
}

/// The BDD manager.
///
/// [Manager] handles the lifetime of the diagrams produced through it and keeps track of all the
/// structures needed to ensure canonicity of the diagrams.
///
/// An instance of [Manager] is basically used only to obtain [variables](Var) through
/// [add_var()](Manager::add_var()), [add_vars()](Manager::add_vars()),
/// [add_var_after()](Manager::add_var_after()), or [add_vars_after()](Manager::add_vars_after()),
/// which then can be combined to obtain [BDD]s using operators, although methods are also provided
/// for convenience.
///
/// Note that [Manager] is [Send] and [Sync] and all methods take `&self`, so every operation can be
/// freely done concurrently on multiple threads.
///
/// Example:
/// ```
/// # mod formally {
/// #     pub extern crate formally_dd as dd;
/// # }
/// use formally::dd::obdd::Manager;
///
/// # fn main() {
/// let manager = Manager::new();
/// let p = manager.add_var();
/// let q = manager.add_var();
///
/// assert!(p < q);
///
/// let b = p & !p;
/// assert_eq!(b, false);
/// # }
/// ```
///
/// [Manager] keeps track of the current variable order against which the BDDs are constructed.
/// The [swap()](Manager::swap()) and [swap_adjacent()](Manager::swap_adjacent()) methods are
/// available to reorder the variables.
#[derive(Default)]
pub struct Manager {
    inner: RwLock<Inner>,
}

impl Debug for Manager {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Manager {{ ... }}")
    }
}

impl Manager {
    /// Create a new empty [Manager].
    pub fn new() -> Manager {
        Manager::default()
    }

    /// Create a new [variable](Var) positioned at the bottom of the current variable order.
    pub fn add_var(&self) -> Var<'_> {
        Var::new(self.inner.write().add_var(), self)
    }

    /// Create a new [variable](Var) positioned immediately after the given one in the current
    /// variable order.
    pub fn add_var_after(&self, preceeding: Var<'_>) -> Var<'_> {
        Var::new(self.inner.write().add_var_after(preceeding.var), self)
    }

    /// Create a given number of [variables](Var) positioned at the bottom of the current variable
    /// order.
    pub fn add_vars(&self, n: u32) -> Vec<Var<'_>> {
        let vars = self.inner.write().add_vars(n);

        vars.into_iter().map(|v| Var::new(v, self)).collect()
    }

    /// Create a given number of [variables](Var) positioned immediately after the given one in the
    /// current variable order.
    pub fn add_vars_after(&self, preceeding: Var<'_>, n: u32) -> Vec<Var<'_>> {
        let ids = self.inner.write().add_vars_after(preceeding.var, n);

        let mut vars = Vec::with_capacity(n as usize);
        for id in ids {
            vars.push(Var::new(id, self))
        }

        vars
    }

    /// Return the number of variables currently managed by this [Manager].
    pub fn n_vars(&self) -> u32 {
        self.inner.read().n_vars()
    }

    /// Return an iterator to all the variables currently managed by this [Manager].
    pub fn vars(&self) -> impl ExactSizeIterator<Item = Var<'_>> {
        let n = self.n_vars();
        (0..n).into_iter().map(|i| Var::new(VarID(i), self))
    }

    /// Return the [variable](Var) positioned at the given level of the current variable order, or
    /// [None] if there is no such variable.
    pub fn var_at(&self, level: Level) -> Option<Var<'_>> {
        self.inner.read().var_at(level).map(|v| Var::new(v, self))
    }

    /// Swap the position in the variable order of the given variable with the one positioned
    /// immediately after it.
    pub fn swap_adjacent(&self, var: Var<'_>) {
        let mut inner = self.inner.write();
        let level = inner.level_of(Some(var.var));
        inner.swap(level);
    }

    /// Swap the position of two variables in the current variable order.
    pub fn swap(&self, v1: Var<'_>, v2: Var<'_>) {
        if v1 == v2 {
            return;
        }

        let mut inner = self.inner.write();
        let l1 = inner.level_of(Some(v1.var));
        let l2 = inner.level_of(Some(v2.var));

        let min = min(l1, l2);
        let max = max(l1, l2);
        let distance = (max - min) as u32;

        for i in 0..distance {
            inner.swap(min + i)
        }

        for i in (0..distance - 1).rev() {
            inner.swap(min + i)
        }
    }

    /// Intern a [Node] creating a new [BDD] from it.
    pub fn make<'m>(&'m self, node: Node<'m>) -> BDD<'m> {
        let inner = self.inner.read();
        let id = inner.make(inner::Node {
            var: node.var.var,
            high: node.high.id,
            low: node.low.id,
        });
        BDD::new(&inner, id, self)
    }

    /// Reclaim memory by discarding nodes that are not transitively referenced by any live [BDD]
    /// handle.
    pub fn reclaim(&self) {
        self.inner.write().reclaim();
    }

    /// Return the [BDD] corresponding to the [true] function.
    pub fn top(&self) -> BDD<'_> {
        BDD {
            id: SlotID::TOP,
            manager: Nominal(self),
        }
    }

    /// Return the [BDD] corresponding to the [false] function.
    pub fn bottom(&self) -> BDD<'_> {
        BDD {
            id: SlotID::BOTTOM,
            manager: Nominal(self),
        }
    }

    /// Negate a [BDD].
    pub fn not<'m>(&'m self, arg: impl Into<BDD<'m>>) -> BDD<'m> {
        self.ite(arg, self.bottom(), self.top())
    }

    /// Return the conjunction of the given iterator of [BDD]s.
    pub fn and<'m>(&'m self, args: impl IntoIterator<Item = impl Into<BDD<'m>>>) -> BDD<'m> {
        args.into_iter()
            .fold(self.top(), |acc, arg| self.ite(acc, arg, self.bottom()))
    }

    /// Return the disjunction of the given iterator of [BDD]s.
    pub fn or<'m>(&'m self, args: impl IntoIterator<Item = impl Into<BDD<'m>>>) -> BDD<'m> {
        args.into_iter()
            .fold(self.bottom(), |acc, arg| self.ite(acc, self.top(), arg))
    }

    /// Return the exclusive disjunction of the given iterator of [BDD]s.
    pub fn xor<'m>(&'m self, args: impl IntoIterator<Item = impl Into<BDD<'m>>>) -> BDD<'m> {
        args.into_iter().fold(self.bottom(), |acc, arg| {
            self.ite(acc, self.not(arg), self.bottom())
        })
    }

    /// Return the implication between the two given [BDD]s.
    pub fn implies<'m>(&'m self, left: impl Into<BDD<'m>>, right: impl Into<BDD<'m>>) -> BDD<'m> {
        self.ite(left, right, self.top())
    }

    /// Return the existential quantification of the given [variable](Var) over the given [BDD].
    pub fn exists<'m>(&'m self, var: Var<'m>, body: impl Into<BDD<'m>>) -> BDD<'m> {
        let body = body.into();
        self.or([self.restrict(var, &body), self.restrict(!var, body)])
    }

    /// Return the universal quantification of the given [variable](Var) over the given [BDD].
    pub fn forall<'m>(&'m self, var: Var<'m>, body: impl Into<BDD<'m>>) -> BDD<'m> {
        self.not(self.exists(var, self.not(body)))
    }

    /// Return the restriction of the given [BDD] over the given [literal](Lit).
    pub fn restrict<'m>(&'m self, lit: impl Into<Lit<'m>>, body: impl Into<BDD<'m>>) -> BDD<'m> {
        let lit = lit.into();
        let body = body.into();
        assert_eq!(
            Nominal(lit.manager()),
            Nominal(body.manager()),
            "restrict() called on Lit and BDD from different managers"
        );

        let inner = self.inner.read();
        let restrict = inner.restrict(lit.var().var, lit.value(), body.id);

        BDD::new(&inner, restrict, lit.manager())
    }

    /// Return the conditional if-then-else function `ite(guard, then, else_)`.
    pub fn ite<'m>(
        &'m self,
        guard: impl Into<BDD<'m>>,
        then: impl Into<BDD<'m>>,
        else_: impl Into<BDD<'m>>,
    ) -> BDD<'m> {
        let guard = guard.into();
        let then = then.into();
        let else_ = else_.into();

        assert!(
            [Nominal(self), guard.manager, then.manager, else_.manager]
                .into_iter()
                .all_equal(),
            "BDD operation called on BDDs from different managers"
        );

        let inner = self.inner.read();
        let ite = inner.ite(guard.id, then.id, else_.id);

        BDD::new(&inner, ite, guard.manager())
    }
}

/// Return the conditional if-then-else function `ite(guard, then, else_)`.
pub fn ite<'m>(
    guard: impl Into<BDD<'m>>,
    then: impl Into<BDD<'m>>,
    else_: impl Into<BDD<'m>>,
) -> BDD<'m> {
    let guard = guard.into();

    guard.manager.ite(guard, then, else_)
}

/// Return the restriction of the given [BDD] over the given [literal](Lit).
pub fn restrict<'m>(lit: impl Into<Lit<'m>>, body: impl Into<BDD<'m>>) -> BDD<'m> {
    let lit = lit.into();
    lit.manager().restrict(lit, body)
}

/// Return the existential quantification of the given [variable](Var) over the given [BDD].
pub fn exists<'m>(vars: impl IntoIterator<Item = Var<'m>>, body: impl Into<BDD<'m>>) -> BDD<'m> {
    vars.into_iter()
        .fold(body.into(), |acc, var| var.manager().exists(var, acc))
}

/// Return the universal quantification of the given [variable](Var) over the given [BDD].
pub fn forall<'m>(vars: impl IntoIterator<Item = Var<'m>>, body: impl Into<BDD<'m>>) -> BDD<'m> {
    vars.into_iter()
        .fold(body.into(), |acc, var| var.manager().forall(var, acc))
}

/// Return the implication between the two given [BDD]s.
pub fn implies<'m>(left: impl Into<BDD<'m>>, right: impl Into<BDD<'m>>) -> BDD<'m> {
    let left = left.into();
    let right = right.into();
    left.manager.implies(left, right)
}

/// A literal.
///
/// A literal represent a variable or its negation. It is the result of negating a [Var] with the
/// negation operator and can be combined with other variables or [BDD]s with logical operators.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum Lit<'m> {
    /// An asserted variable.
    Positive(Var<'m>),
    /// A negated variable.
    Negative(Var<'m>),
}

impl<'m> Lit<'m> {
    /// Return the inner [variable](Var) of this literal.
    pub fn var(&self) -> Var<'m> {
        match self {
            Lit::Positive(var) => *var,
            Lit::Negative(var) => *var,
        }
    }

    /// Return whether the literal is asserted or negated.
    pub fn value(&self) -> bool {
        match self {
            Lit::Positive(_) => true,
            Lit::Negative(_) => false,
        }
    }

    /// Return the [Manager] used to create the inner variable of this literal.
    pub fn manager(&self) -> &'m Manager {
        self.var().manager()
    }
}

impl<'m> From<Var<'m>> for Lit<'m> {
    fn from(var: Var<'m>) -> Self {
        Lit::Positive(var)
    }
}

/// A BDD tree.
///
/// [Tree]s are obtained with the [BDD::tree()] method and are used to inspect the inner structure
/// of a given [BDD], in cases where structural instead of logical manipulations are needed.
///
/// A [Tree] can be either a terminal or a [Node]. The latter can be interned again as a [BDD] using
/// [Manager::make()].
#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Tree<'m> {
    /// A terminal BDD.
    Terminal(bool),
    /// An internal BDD node.
    Node(Node<'m>),
}

/// A BDD node.
///
/// [Node]s are obtained from [Tree]s via the [BDD::tree()] method and are used to inspect the inner
/// structure of a given [BDD], in cases where structural instead of logical manipulations are
/// needed.
///
/// A [Node] can be interned again as a [BDD] using [Manager::make()].
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Node<'m> {
    pub var: Var<'m>,
    pub high: BDD<'m>,
    pub low: BDD<'m>,
}

/// A handle to a BDD.
///
/// [BDD] is the main type used to manipulate diagrams in this API. [BDD]s are obtained by
/// combining [variables](Var) with logical operators. A [BDD] is a lightweight reference-counted
/// handle to the internal BDD node managed by the [Manager].
///
/// The internal structure of the [BDD] can be inspected using the [BDD::tree()] method.
///
/// Example:
/// ```
/// # mod formally {
/// #     pub extern crate formally_dd as dd;
/// # }
/// use formally::dd::obdd::{implies, Manager};
///
/// # fn main() {
/// let manager = Manager::new();
/// let p = manager.add_var();
/// let q = manager.add_var();
///
/// let ponens = implies(implies(p, q) & p, q);
/// assert_eq!(ponens, true);
/// # }
/// ```
#[derive(Hash, PartialEq, Eq)]
pub struct BDD<'m> {
    id: SlotID,
    manager: Nominal<&'m Manager>,
}

impl<'m> Clone for BDD<'m> {
    fn clone(&self) -> Self {
        BDD::new(&self.manager().inner.read(), self.id, self.manager())
    }
}

impl Drop for BDD<'_> {
    fn drop(&mut self) {
        self.manager.inner.read().dec_ref(self.id);
    }
}

impl<'m> BDD<'m> {
    fn new(inner: &Inner, id: SlotID, manager: &'m Manager) -> BDD<'m> {
        BDD {
            id: inner.inc_ref(id),
            manager: Nominal(manager),
        }
    }

    /// Return the [Manager] that is handling the lifetime of this [BDD].
    pub fn manager(&self) -> &'m Manager {
        self.manager.into_inner()
    }

    /// Return a [Tree] to inspect the internal structure of this [BDD].
    pub fn tree(&self) -> Tree<'m> {
        let inner = self.manager().inner.read();
        let tree = inner.tree(self.id);

        match tree {
            inner::Tree::Terminal(value) => Tree::Terminal(value),
            inner::Tree::Node(node) => Tree::Node(Node {
                var: Var::new(node.var, self.manager()),
                high: BDD::new(&inner, node.high, self.manager()),
                low: BDD::new(&inner, node.low, self.manager()),
            }),
        }
    }
}

impl Debug for BDD<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "BDD({})", self.id.0)
    }
}

impl<'m> From<&BDD<'m>> for BDD<'m> {
    fn from(bdd: &BDD<'m>) -> Self {
        bdd.clone()
    }
}

impl<'m> From<&Var<'m>> for BDD<'m> {
    fn from(var: &Var<'m>) -> Self {
        BDD::from(*var)
    }
}

impl<'m> From<Var<'m>> for BDD<'m> {
    fn from(var: Var<'m>) -> Self {
        BDD::from(Lit::from(var))
    }
}

impl<'m> From<&Lit<'m>> for BDD<'m> {
    fn from(lit: &Lit<'m>) -> Self {
        BDD::from(*lit)
    }
}

impl<'m> From<Lit<'m>> for BDD<'m> {
    fn from(lit: Lit<'m>) -> Self {
        match lit {
            Lit::Positive(var) => {
                let manager = var.manager();
                let inner = manager.inner.read();
                let node = inner.make(inner::Node {
                    var: var.var,
                    high: SlotID::TOP,
                    low: SlotID::BOTTOM,
                });
                BDD::new(&inner, node, manager)
            }
            Lit::Negative(var) => {
                let manager = var.manager();
                let inner = manager.inner.read();
                let node = inner.make(inner::Node {
                    var: var.var,
                    high: SlotID::BOTTOM,
                    low: SlotID::TOP,
                });
                BDD::new(&inner, node, manager)
            }
        }
    }
}

impl<'m> PartialEq<bool> for BDD<'m> {
    fn eq(&self, other: &bool) -> bool {
        match self.manager.inner.read().tree(self.id) {
            inner::Tree::Terminal(b) => b == *other,
            inner::Tree::Node(_) => false,
        }
    }
}

impl<'m> Not for BDD<'m> {
    type Output = BDD<'m>;

    fn not(self) -> Self::Output {
        self.manager.not(self)
    }
}

impl<'m> Not for Var<'m> {
    type Output = Lit<'m>;

    fn not(self) -> Self::Output {
        Lit::Negative(self)
    }
}

impl<'m> Not for &BDD<'m> {
    type Output = BDD<'m>;

    fn not(self) -> Self::Output {
        self.manager.not(self)
    }
}

impl<'m> Not for &Var<'m> {
    type Output = Lit<'m>;

    fn not(self) -> Self::Output {
        Lit::Negative(*self)
    }
}

impl<'m> Not for Lit<'m> {
    type Output = Lit<'m>;

    fn not(self) -> Self::Output {
        match self {
            Lit::Positive(var) => Lit::Negative(var),
            Lit::Negative(var) => Lit::Positive(var),
        }
    }
}

impl<'m> Not for &Lit<'m> {
    type Output = Lit<'m>;

    fn not(self) -> Self::Output {
        (*self).not()
    }
}

impl<'m, T: Into<BDD<'m>>> BitAnd<T> for BDD<'m> {
    type Output = BDD<'m>;

    fn bitand(self, rhs: T) -> Self::Output {
        self.manager.and([self, rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitAnd<T> for Var<'m> {
    type Output = BDD<'m>;

    fn bitand(self, rhs: T) -> Self::Output {
        self.manager.and([BDD::from(self), rhs.into()])
    }
}
impl<'m, T: Into<BDD<'m>>> BitAnd<T> for &BDD<'m> {
    type Output = BDD<'m>;

    fn bitand(self, rhs: T) -> Self::Output {
        self.manager.and([self, &rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitAnd<T> for &Var<'m> {
    type Output = BDD<'m>;

    fn bitand(self, rhs: T) -> Self::Output {
        self.manager.and([BDD::from(self), rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitAndAssign<T> for BDD<'m> {
    fn bitand_assign(&mut self, rhs: T) {
        *self = &*self & rhs.into();
    }
}

impl<'m, T: Into<BDD<'m>>> BitOr<T> for BDD<'m> {
    type Output = BDD<'m>;

    fn bitor(self, rhs: T) -> Self::Output {
        self.manager.or([self, rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitOr<T> for Var<'m> {
    type Output = BDD<'m>;

    fn bitor(self, rhs: T) -> Self::Output {
        self.manager.or([BDD::from(self), rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitOr<T> for &BDD<'m> {
    type Output = BDD<'m>;

    fn bitor(self, rhs: T) -> Self::Output {
        self.manager.or([self, &rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitOr<T> for &Var<'m> {
    type Output = BDD<'m>;

    fn bitor(self, rhs: T) -> Self::Output {
        self.manager.or([BDD::from(self), rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitOrAssign<T> for BDD<'m> {
    fn bitor_assign(&mut self, rhs: T) {
        *self = &*self | rhs.into();
    }
}

impl<'m, T: Into<BDD<'m>>> BitXor<T> for BDD<'m> {
    type Output = BDD<'m>;

    fn bitxor(self, rhs: T) -> Self::Output {
        self.manager.xor([self, rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitXor<T> for Var<'m> {
    type Output = BDD<'m>;

    fn bitxor(self, rhs: T) -> Self::Output {
        self.manager.xor([BDD::from(self), rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitXor<T> for &BDD<'m> {
    type Output = BDD<'m>;

    fn bitxor(self, rhs: T) -> Self::Output {
        self.manager.xor([self, &rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitXor<T> for &Var<'m> {
    type Output = BDD<'m>;

    fn bitxor(self, rhs: T) -> Self::Output {
        self.manager.xor([BDD::from(self), rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitXorAssign<T> for BDD<'m> {
    fn bitxor_assign(&mut self, rhs: T) {
        *self = &*self ^ rhs.into();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn order() {
        let manager = Manager::new();

        let first = manager.add_var();
        let third = manager.add_var();
        assert!(first < third);

        let middle = manager.add_var_after(first);
        assert!(first < middle);
        assert!(middle < third);

        let seq = manager.add_vars_after(third, 4);

        for (v1, v2) in seq.into_iter().tuple_windows() {
            assert!(third < v1);
            assert!(v1 < v2);
        }

        manager.swap_adjacent(first);
        assert!(middle < first);

        manager.swap_adjacent(first);
        assert!(third < first);

        for var in manager.vars() {
            assert_eq!(Some(var), manager.var_at(var.level()))
        }

        manager.swap(first, middle);
        assert!(first < middle);
        assert!(third < middle);
    }

    #[test]
    fn obdds() {
        let manager = Manager::new();
        let p = manager.add_var();
        let q = manager.add_var();

        std::thread::scope(|scope| {
            scope.spawn(|| {
                let tautology = p | !p;
                let ponens = implies(implies(p, q) & p, q);
                let not = implies(p, q) & p & !q;
                let something = p & q;
                let xor = (p ^ q) & &something;

                manager.reclaim();

                assert_eq!(tautology, true);
                assert_eq!(ponens, true);
                assert_eq!(not, false);
                assert_ne!(something, true);
                assert_ne!(something, false);
                assert_eq!(xor, false);
            });

            scope.spawn(|| {
                let something = p & q;

                manager.swap(p, q);

                let xor = (p ^ q) & &something;

                assert_ne!(something, true);
                assert_ne!(something, false);
                assert_eq!(xor, false);
            });

            scope.spawn(|| {
                let w = manager.add_var();
                let something = p & (q | w);

                manager.swap(p, w);

                let ep = exists([p], &something);
                let ap = forall([p], &something);

                assert_ne!(ep, true);
                assert_ne!(ep, false);
                assert_eq!(ap, false);
            });
        });
    }
}
