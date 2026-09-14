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

use crate::formally;
use formally::support::Nominal;

use dashmap::DashMap;
use itertools::Itertools;
use parking_lot::RwLock;

use std::{
    cmp,
    fmt::{Debug, Formatter},
    num::NonZero,
    ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
    sync::atomic::{AtomicU32, Ordering},
};

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
struct VarID(NonZero<u32>);

impl VarID {
    fn from_index(index: usize) -> VarID {
        VarID(NonZero::new((index + 1) as u32).unwrap())
    }

    fn into_index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

#[derive(Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Level(u32);

impl Level {
    pub const MIN: Level = Level(0);
    pub const MAX: Level = Level(u32::MAX);
}

impl Add<u32> for Level {
    type Output = Level;

    fn add(self, rhs: u32) -> Level {
        Level(self.0 + rhs)
    }
}

impl AddAssign<u32> for Level {
    fn add_assign(&mut self, rhs: u32) {
        *self = *self + rhs
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum Tree {
    Terminal(bool),
    Node(Node),
}

impl Tree {
    pub fn var(&self) -> Option<VarID> {
        match *self {
            Tree::Terminal(_) => None,
            Tree::Node(node) => Some(node.var),
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
struct Node {
    var: VarID,
    high: NodeID,
    low: NodeID,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
struct NodeID(u32);

impl Default for NodeID {
    fn default() -> Self {
        NodeID(2)
    }
}

impl NodeID {
    const TOP: NodeID = NodeID(1);
    const BOTTOM: NodeID = NodeID(0);
}

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
            .position(Some(self.var))
            .cmp(&inner.position(Some(other.var)))
    }
}

struct Inner {
    order: Vec<Level>,
    next_level: Level,
    nodes: DashMap<NodeID, Node>,
    next_node: AtomicU32,
    unique: DashMap<Node, NodeID>,
    ite_cache: DashMap<IteKey, NodeID>,
}

impl Default for Inner {
    fn default() -> Self {
        Inner {
            order: Vec::default(),
            next_level: Level::default(),
            nodes: DashMap::default(),
            next_node: AtomicU32::new(2),
            unique: DashMap::default(),
            ite_cache: DashMap::default(),
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
struct IteKey(NodeID, NodeID, NodeID);

impl Inner {
    fn var(&mut self) -> VarID {
        let var = VarID::from_index(self.order.len());

        self.order.push(self.next_level);
        self.next_level += 1;

        var
    }

    fn position(&self, var: Option<VarID>) -> Level {
        match var {
            None => Level::MAX,
            Some(var) => *self
                .order
                .get(var.into_index())
                .expect("use of a non-existent Var, probably from a different Manager"),
        }
    }

    fn tree(&self, id: NodeID) -> Tree {
        match id {
            NodeID::TOP => Tree::Terminal(true),
            NodeID::BOTTOM => Tree::Terminal(false),
            id => {
                Tree::Node(*self.nodes.get(&id).expect(
                    "use of a non-existent BDD, probably survived after a garbage collection",
                ))
            }
        }
    }

    fn make(&self, tree: Tree) -> NodeID {
        match tree {
            Tree::Terminal(true) => NodeID::TOP,
            Tree::Terminal(false) => NodeID::BOTTOM,
            Tree::Node(node) => {
                if node.high == node.low {
                    return node.high;
                }

                match self.unique.entry(node) {
                    dashmap::Entry::Occupied(entry) => *entry.get(),
                    dashmap::Entry::Vacant(entry) => {
                        let id = {
                            let id = self.next_node.fetch_add(1, Ordering::Relaxed);
                            assert_ne!(id, u32::MAX, "maximum number of BDD nodes reached");
                            NodeID(id)
                        };

                        self.nodes.insert(id, node);

                        entry.insert_entry(id);
                        id
                    }
                }
            }
        }
    }

    fn ite(&self, guard: NodeID, then: NodeID, else_: NodeID) -> NodeID {
        if then == else_ {
            return then;
        }

        let g = self.tree(guard);

        match g {
            Tree::Terminal(true) => then,
            Tree::Terminal(false) => else_,
            Tree::Node(node) => {
                if let Some(t) = self.ite_cache.get(&IteKey(guard, then, else_)) {
                    return *t;
                }

                let t = self.tree(then);
                let e = self.tree(else_);

                let var = [Some(node.var), t.var(), e.var()]
                    .into_iter()
                    .min_by_key(|var| self.position(*var))
                    .unwrap()
                    .unwrap();

                fn cofactors(tree: Tree, id: NodeID, var: VarID) -> (NodeID, NodeID) {
                    match tree {
                        Tree::Node(node) if node.var == var => (node.low, node.high),
                        _ => (id, id),
                    }
                }

                let (g0, g1) = cofactors(g, guard, var);
                let (t0, t1) = cofactors(t, then, var);
                let (e0, e1) = cofactors(e, else_, var);

                let result = self.make(Tree::Node(Node {
                    var,
                    high: self.ite(g1, t1, e1),
                    low: self.ite(g0, t0, e0),
                }));

                self.ite_cache
                    .insert(IteKey(guard, then, else_), result)
                    .unwrap_or(result)
            }
        }
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
        Var::new(self.inner.write().var(), self)
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
        let node = manager.inner.read().make(Tree::Node(Node {
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
            Tree::Terminal(b) => b == *other,
            Tree::Node(_) => false,
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
        self.manager.or([self, rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitXor<T> for Var<'m> {
    type Output = BDD<'m>;

    fn bitxor(self, rhs: T) -> Self::Output {
        self.manager.or([BDD::from(self), rhs.into()])
    }
}

impl<'m, T: Into<BDD<'m>>> BitXorAssign<T> for BDD<'m> {
    fn bitxor_assign(&mut self, rhs: T) {
        *self = *self ^ rhs.into();
    }
}

#[test]
pub fn obdds() {
    let manager = Manager::new();
    let p = manager.var();
    let q = manager.var();

    let tautology = p | !p;
    let ponens = implies(implies(p, q) & p, q);
    let not = implies(p, q) & p & !q;
    let something = p | q;

    assert_eq!(tautology, true);
    assert_eq!(ponens, true);
    assert_eq!(not, false);
    assert_ne!(something, true);
    assert_ne!(something, false);
}
