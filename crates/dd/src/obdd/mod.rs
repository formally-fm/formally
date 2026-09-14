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
    cmp,
    fmt::{Debug, Formatter},
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
};

use inner::{Inner, NodeID, VarID};

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
        let level = inner.level(Some(preceeding.var));

        Var::new(inner.vars_after(level, 1)[0], self)
    }

    pub fn vars(&self, n: u32) -> Vec<Var<'_>> {
        let vars = self.inner.write().vars(n);

        vars.into_iter().map(|v| Var::new(v, self)).collect()
    }

    pub fn vars_after(&self, preceeding: Var<'_>, n: u32) -> Vec<Var<'_>> {
        let ids = {
            let mut inner = self.inner.write();
            let level = inner.level(Some(preceeding.var));
            inner.vars_after(level, n)
        };

        let mut vars = Vec::with_capacity(n as usize);
        for id in ids {
            vars.push(Var::new(id, self))
        }

        vars
    }

    pub fn top(&self) -> BDD<'_> {
        BDD::new(NodeID::TOP, self)
    }

    pub fn bottom(&self) -> BDD<'_> {
        BDD::new(NodeID::BOTTOM, self)
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

pub fn implies<'m>(left: impl Into<BDD<'m>>, right: impl Into<BDD<'m>>) -> BDD<'m> {
    let left = left.into();
    let right = right.into();
    left.manager.implies(left, right)
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct BDD<'m> {
    id: NodeID,
    manager: Nominal<&'m Manager>,
}

impl<'m> BDD<'m> {
    fn new(id: NodeID, manager: &'m Manager) -> BDD<'m> {
        BDD {
            id,
            manager: Nominal(manager),
        }
    }

    pub fn manager(&self) -> &'m Manager {
        self.manager.into_inner()
    }
}

impl Debug for BDD<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "BDD({})", self.id.0)
    }
}

impl<'m> From<Var<'m>> for BDD<'m> {
    fn from(var: Var<'m>) -> Self {
        let manager = var.manager();
        let node = manager.inner.read().make(inner::Tree::Node(inner::Node {
            var: var.var,
            high: NodeID::TOP,
            low: NodeID::BOTTOM,
        }));
        BDD::new(node, manager)
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
    type Output = BDD<'m>;

    fn not(self) -> Self::Output {
        self.manager.not(self)
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

impl<'m, T: Into<BDD<'m>>> BitAndAssign<T> for BDD<'m> {
    fn bitand_assign(&mut self, rhs: T) {
        *self = *self & rhs.into();
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

impl<'m, T: Into<BDD<'m>>> BitOrAssign<T> for BDD<'m> {
    fn bitor_assign(&mut self, rhs: T) {
        *self = *self | rhs.into();
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

impl<'m, T: Into<BDD<'m>>> BitXorAssign<T> for BDD<'m> {
    fn bitxor_assign(&mut self, rhs: T) {
        *self = *self ^ rhs.into();
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
        let seq = manager.vars_after(middle, 4);
        
        assert!(first < second);
        assert!(first < middle);
        assert!(middle < second);
        
        for (v1, v2) in seq.into_iter().tuple_windows() {
            assert!(middle < v1);
            assert!(v1 < v2);
            assert!(v2 < second);
        }
    } 
    
    #[test]
    fn obdds() {
        let manager = Manager::new();
        let p = manager.var();
        let q = manager.var();
    
        let tautology = p | !p;
        let ponens = implies(implies(p, q) & p, q);
        let not = implies(p, q) & p & !q;
        let something = p | q;
        let xor = (p ^ q) & p & q;
    
        assert_eq!(tautology, true);
        assert_eq!(ponens, true);
        assert_eq!(not, false);
        assert_ne!(something, true);
        assert_ne!(something, false);
        assert_eq!(xor, false);
    }
    
}
