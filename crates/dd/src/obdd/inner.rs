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

use std::{
    num::NonZero,
    ops::{Add, AddAssign},
    sync::atomic::{AtomicU32, Ordering},
};

use dashmap::DashMap;
use smallvec::SmallVec;

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub(super) struct VarID(NonZero<u32>);

impl VarID {
    pub fn from_index(index: usize) -> VarID {
        VarID(NonZero::new((index + 1) as u32).unwrap())
    }

    pub fn into_index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

#[derive(Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Level(u32);

impl Level {
    const MAX: Level = Level(u32::MAX);
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
pub(super) enum Tree {
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
pub(super) struct Node {
    pub var: VarID,
    pub high: NodeID,
    pub low: NodeID,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub(super) struct NodeID(pub u32);

impl Default for NodeID {
    fn default() -> Self {
        NodeID(2)
    }
}

impl NodeID {
    pub const TOP: NodeID = NodeID(1);
    pub const BOTTOM: NodeID = NodeID(0);
}

pub(super) struct Inner {
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
    pub fn vars(&mut self, n: u32) -> SmallVec<[VarID; 8]> {
        let first = self.next_level.0;
        let last = self.next_level.0 + n;
        self.next_level += n;

        let mut vars = SmallVec::new();
        self.order.reserve(n as usize);
        for level in first..last {
            vars.push(VarID::from_index(self.order.len()));
            self.order.push(Level(level));
        }

        vars
    }

    pub fn vars_after(&mut self, preceeding: Level, n: u32) -> SmallVec<[VarID; 8]> {
        for level in &mut self.order {
            if *level > preceeding {
                *level += n;
            }
        }

        let first = preceeding.0 + 1;
        let last = first + n;
        self.next_level += n;

        let mut vars = SmallVec::new();
        self.order.reserve(n as usize);
        for level in first..last {
            vars.push(VarID::from_index(self.order.len()));
            self.order.push(Level(level));
        }

        vars
    }

    pub fn level(&self, var: Option<VarID>) -> Level {
        match var {
            None => Level::MAX,
            Some(var) => *self
                .order
                .get(var.into_index())
                .expect("use of a non-existent Var, probably from a different Manager"),
        }
    }

    pub fn tree(&self, id: NodeID) -> Tree {
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

    pub fn make(&self, tree: Tree) -> NodeID {
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

    pub fn ite(&self, guard: NodeID, then: NodeID, else_: NodeID) -> NodeID {
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
                    .min_by_key(|var| self.level(*var))
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
