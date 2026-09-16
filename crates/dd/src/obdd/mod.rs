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

mod inner;

use crate::formally;
use formally::support::Nominal;

use itertools::Itertools;
use parking_lot::RwLock;

use std::{
    cmp::{self, max, min},
    fmt::{Debug, Formatter},
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
};

pub use inner::Level;
use inner::{Inner, SlotID, VarID};

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Var<'m> {
    var: VarID,
    manager: Nominal<&'m Manager>,
}

impl<'m> Var<'m> {
    fn new(var: VarID, manager: &'m Manager) -> Var<'m> {
        Var {
            var,
            manager: Nominal(manager),
        }
    }

    pub fn manager(&self) -> &'m Manager {
        self.manager.into_inner()
    }

    pub fn level(&self) -> Level {
        self.manager.inner.read().level(Some(self.var))
    }

    pub fn next(&self) -> Option<Var<'m>> {
        let inner = self.manager.inner.read();
        inner
            .at_level(inner.level(Some(self.var)) + 1)
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
            .level(Some(self.var))
            .cmp(&inner.level(Some(other.var)))
    }
}

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
    pub fn new() -> Manager {
        Manager::default()
    }

    pub fn var(&self) -> Var<'_> {
        Var::new(self.inner.write().vars(1)[0], self)
    }

    pub fn var_after(&self, preceeding: Var<'_>) -> Var<'_> {
        let mut inner = self.inner.write();

        Var::new(inner.vars_after(preceeding.var, 1)[0], self)
    }

    pub fn vars(&self, n: u32) -> Vec<Var<'_>> {
        let vars = self.inner.write().vars(n);

        vars.into_iter().map(|v| Var::new(v, self)).collect()
    }

    pub fn vars_after(&self, preceeding: Var<'_>, n: u32) -> Vec<Var<'_>> {
        let ids = self.inner.write().vars_after(preceeding.var, n);

        let mut vars = Vec::with_capacity(n as usize);
        for id in ids {
            vars.push(Var::new(id, self))
        }

        vars
    }

    pub fn swap_adjacent(&self, var: Var<'_>) {
        let mut inner = self.inner.write();
        let level = inner.level(Some(var.var));
        inner.swap(level);
    }

    pub fn swap(&self, v1: Var<'_>, v2: Var<'_>) {
        if v1 == v2 {
            return;
        }

        let mut inner = self.inner.write();
        let l1 = inner.level(Some(v1.var));
        let l2 = inner.level(Some(v2.var));

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
    
    pub fn make<'m>(&'m self, node: Node<'m>) -> BDD<'m> {
        let id = self.inner.read().make(inner::Node {
            var: node.var.var,
            high: node.high.id,
            low: node.low.id,
        });
        BDD::new(id, self)
    }

    pub fn top(&self) -> BDD<'_> {
        BDD::new(SlotID::TOP, self)
    }

    pub fn bottom(&self) -> BDD<'_> {
        BDD::new(SlotID::BOTTOM, self)
    }

    pub fn not<'m>(&'m self, arg: impl Into<BDD<'m>>) -> BDD<'m> {
        self.ite(arg, self.bottom(), self.top())
    }

    pub fn and<'m>(&'m self, args: impl IntoIterator<Item = impl Into<BDD<'m>>>) -> BDD<'m> {
        args.into_iter()
            .fold(self.top(), |acc, arg| self.ite(acc, arg, self.bottom()))
    }

    pub fn or<'m>(&'m self, args: impl IntoIterator<Item = impl Into<BDD<'m>>>) -> BDD<'m> {
        args.into_iter()
            .fold(self.bottom(), |acc, arg| self.ite(acc, self.top(), arg))
    }

    pub fn xor<'m>(&'m self, args: impl IntoIterator<Item = impl Into<BDD<'m>>>) -> BDD<'m> {
        args.into_iter().fold(self.bottom(), |acc, arg| {
            self.ite(acc, self.not(arg), self.bottom())
        })
    }

    pub fn implies<'m>(&'m self, left: impl Into<BDD<'m>>, right: impl Into<BDD<'m>>) -> BDD<'m> {
        self.ite(left, right, self.top())
    }

    pub fn exists<'m>(&'m self, var: Var<'m>, body: impl Into<BDD<'m>>) -> BDD<'m> {
        let body = body.into();
        self.or([self.restrict(var, &body), self.restrict(!var, body)])
    }

    pub fn forall<'m>(&'m self, var: Var<'m>, body: impl Into<BDD<'m>>) -> BDD<'m> {
        self.not(self.exists(var, self.not(body)))
    }

    pub fn restrict<'m>(&'m self, lit: impl Into<Lit<'m>>, body: impl Into<BDD<'m>>) -> BDD<'m> {
        let lit = lit.into();
        let body = body.into();
        assert_eq!(
            Nominal(lit.manager()),
            Nominal(body.manager()),
            "restrict() called on Lit and BDD from different managers"
        );

        let restrict = self
            .inner
            .read()
            .restrict(lit.var().var, lit.value(), body.id);

        BDD::new(restrict, lit.manager())
    }

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

        let ite = self.inner.read().ite(guard.id, then.id, else_.id);

        BDD::new(ite, guard.manager())
    }
}

pub fn ite<'m>(
    guard: impl Into<BDD<'m>>,
    then: impl Into<BDD<'m>>,
    else_: impl Into<BDD<'m>>,
) -> BDD<'m> {
    let guard = guard.into();

    guard.manager.ite(guard, then, else_)
}

pub fn restrict<'m>(lit: impl Into<Lit<'m>>, body: impl Into<BDD<'m>>) -> BDD<'m> {
    let lit = lit.into();
    lit.manager().restrict(lit, body)
}

pub fn exists<'m>(vars: impl IntoIterator<Item = Var<'m>>, body: impl Into<BDD<'m>>) -> BDD<'m> {
    vars.into_iter()
        .fold(body.into(), |acc, var| var.manager().exists(var, acc))
}

pub fn forall<'m>(vars: impl IntoIterator<Item = Var<'m>>, body: impl Into<BDD<'m>>) -> BDD<'m> {
    vars.into_iter()
        .fold(body.into(), |acc, var| var.manager().forall(var, acc))
}

pub fn implies<'m>(left: impl Into<BDD<'m>>, right: impl Into<BDD<'m>>) -> BDD<'m> {
    let left = left.into();
    let right = right.into();
    left.manager.implies(left, right)
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum Lit<'m> {
    Positive(Var<'m>),
    Negative(Var<'m>),
}

impl<'m> Lit<'m> {
    pub fn var(&self) -> Var<'m> {
        match self {
            Lit::Positive(var) => *var,
            Lit::Negative(var) => *var,
        }
    }

    pub fn value(&self) -> bool {
        match self {
            Lit::Positive(_) => true,
            Lit::Negative(_) => false,
        }
    }

    pub fn manager(&self) -> &'m Manager {
        self.var().manager()
    }
}

impl<'m> From<Var<'m>> for Lit<'m> {
    fn from(var: Var<'m>) -> Self {
        Lit::Positive(var)
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Tree<'m> {
    Terminal(bool),
    Node(Node<'m>)
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Node<'m> {
    pub var: Var<'m>,
    pub high: BDD<'m>,
    pub low: BDD<'m>
}

#[derive(Hash, PartialEq, Eq)]
pub struct BDD<'m> {
    id: SlotID,
    manager: Nominal<&'m Manager>,
}

impl<'m> Clone for BDD<'m> {
    fn clone(&self) -> Self {
        BDD::new(self.id, self.manager())
    }
}

impl Drop for BDD<'_> {
    fn drop(&mut self) {
        self.manager.inner.read().dec_ref(self.id);
    }
}

impl<'m> BDD<'m> {
    fn new(id: SlotID, manager: &'m Manager) -> BDD<'m> {
        BDD {
            id: manager.inner.read().inc_ref(id),
            manager: Nominal(manager),
        }
    }

    pub fn manager(&self) -> &'m Manager {
        self.manager.into_inner()
    }

    pub fn tree(&self) -> Tree<'m> {
        let tree = self.manager().inner.read().tree(self.id);
        
        match tree {
            inner::Tree::Terminal(value) => Tree::Terminal(value),
            inner::Tree::Node(node) => Tree::Node(Node {
                var: Var::new(node.var, self.manager()),
                high: BDD::new(node.high, self.manager()),
                low: BDD::new(node.low, self.manager()),
            })
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
                let node = manager.inner.read().make(inner::Node {
                    var: var.var,
                    high: SlotID::TOP,
                    low: SlotID::BOTTOM,
                });
                BDD::new(node, manager)
            }
            Lit::Negative(var) => {
                let manager = var.manager();
                let node = manager.inner.read().make(inner::Node {
                    var: var.var,
                    high: SlotID::BOTTOM,
                    low: SlotID::TOP,
                });
                BDD::new(node, manager)
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

        let first = manager.var();
        let second = manager.var();
        let middle = manager.var_after(first);
        let seq = manager.vars_after(second, 4);

        assert!(first < second);
        assert!(first < middle);
        assert!(middle < second);

        for (v1, v2) in seq.into_iter().tuple_windows() {
            assert!(second < v1);
            assert!(v1 < v2);
        }

        manager.swap_adjacent(first);
        assert!(middle < first);

        manager.swap_adjacent(first);
        assert!(second < first);

        manager.swap(first, middle);
        assert!(first < middle);
        assert!(second < middle);
    }

    #[test]
    fn obdds() {
        let manager = Manager::new();
        let p = manager.var();
        let q = manager.var();

        std::thread::scope(|scope| {
            scope.spawn(|| {
                let tautology = p | !p;
                let ponens = implies(implies(p, q) & p, q);
                let not = implies(p, q) & p & !q;
                let something = p & q;
                let xor = (p ^ q) & &something;

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
                let w = manager.var();
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
