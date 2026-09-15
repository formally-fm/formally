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

use dashmap::{DashMap, DashSet};
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
    pub high: SlotID,
    pub low: SlotID,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub(super) struct Slot {
    node: Node,
    refs: u32,
}

impl Slot {
    fn new(node: Node) -> Slot {
        Slot { node, refs: 0 }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub(super) struct SlotID(pub u32);

impl Default for SlotID {
    fn default() -> Self {
        SlotID(2)
    }
}

impl SlotID {
    pub const TOP: SlotID = SlotID(1);
    pub const BOTTOM: SlotID = SlotID(0);
}

struct VarInfo {
    level: Level,
    next: Option<VarID>,
    slots: DashSet<SlotID>,
}

impl VarInfo {
    fn new(level: Level, next: Option<VarID>) -> VarInfo {
        VarInfo {
            level,
            next,
            slots: DashSet::default(),
        }
    }
}

pub(super) struct Inner {
    order: Vec<VarInfo>,
    next_level: Level,
    slots: DashMap<SlotID, Slot>,
    next_node: AtomicU32,
    unique: DashMap<Node, SlotID>,
    ite_cache: DashMap<IteKey, SlotID>,
}

impl Default for Inner {
    fn default() -> Self {
        Inner {
            order: Vec::default(),
            next_level: Level::default(),
            slots: DashMap::default(),
            next_node: AtomicU32::new(2),
            unique: DashMap::default(),
            ite_cache: DashMap::default(),
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
struct IteKey(SlotID, SlotID, SlotID);

impl Inner {
    pub fn vars(&mut self, n: u32) -> SmallVec<[VarID; 8]> {
        if n == 0 {
            return SmallVec::new();
        }

        let first = self.next_level.0;
        let last = self.next_level.0 + n;
        self.next_level += n;

        let new = VarID::from_index(self.order.len());
        if let Some(last) = self.order.last_mut() {
            last.next = Some(new);
        }

        let mut vars = SmallVec::new();
        self.order.reserve(n as usize);
        for level in first..last {
            vars.push(VarID::from_index(self.order.len()));
            let next = if level + 1 < last {
                Some(VarID::from_index(self.order.len() + 1))
            } else {
                None
            };
            self.order.push(VarInfo::new(Level(level), next));
        }

        vars
    }

    pub fn vars_after(&mut self, prec: VarID, n: u32) -> SmallVec<[VarID; 8]> {
        if n == 0 {
            return SmallVec::new();
        }

        let preclevel = self.level(Some(prec));
        let next = self.order[prec.into_index()].next;
        for VarInfo { level, .. } in &mut self.order {
            if *level > preclevel {
                *level += n;
            }
        }

        let first = preclevel.0 + 1;
        let last = first + n;
        self.next_level += n;

        let mut vars = SmallVec::new();
        self.order.reserve(n as usize);
        for level in first..last {
            vars.push(VarID::from_index(self.order.len()));
            let next = if level + 1 < last {
                Some(VarID::from_index(self.order.len() + 1))
            } else {
                next
            };
            self.order.push(VarInfo::new(Level(level), next));
        }

        self.order[prec.into_index()].next = Some(vars[0]);

        vars
    }

    pub fn level(&self, var: Option<VarID>) -> Level {
        match var {
            None => Level::MAX,
            Some(var) => self
                .order
                .get(var.into_index())
                .map(|v| v.level)
                .expect("use of a non-existent Var, probably from a different Manager"),
        }
    }

    pub fn next(&self, var: VarID) -> Option<VarID> {
        self.order[var.into_index()].next
    }

    pub fn tree(&self, id: SlotID) -> Tree {
        match id {
            SlotID::TOP => Tree::Terminal(true),
            SlotID::BOTTOM => Tree::Terminal(false),
            id => Tree::Node(
                self.slots
                    .get(&id)
                    .map(|s| s.node)
                    .expect("use of a non-existent SlotID"),
            ),
        }
    }

    pub fn inc_ref(&self, id: SlotID) -> SlotID {
        if id == SlotID::TOP || id == SlotID::BOTTOM {
            return id;
        }

        self.slots.get_mut(&id).unwrap().refs += 1;
        id
    }

    pub fn dec_ref(&self, id: SlotID) {
        if id == SlotID::TOP || id == SlotID::BOTTOM {
            return;
        }

        let dashmap::Entry::Occupied(mut e) = self.slots.entry(id) else {
            panic!("use of non-existent SlotID")
        };

        let slot = e.get_mut();
        if slot.refs > 0 {
            slot.refs -= 1;
        }
        if slot.refs == 0 {
            self.dec_ref(slot.node.high);
            self.dec_ref(slot.node.low);
            self.unique.remove(&slot.node);
            self.order[slot.node.var.into_index()].slots.remove(&id);
            e.remove();
        }
    }

    pub fn make(&self, node: Node) -> SlotID {
        if node.high == node.low {
            return node.high;
        }

        match self.unique.entry(node) {
            dashmap::Entry::Occupied(entry) => *entry.get(),
            dashmap::Entry::Vacant(entry) => {
                let id = {
                    let id = self.next_node.fetch_add(1, Ordering::Relaxed);
                    assert_ne!(id, u32::MAX, "maximum number of BDD nodes reached");
                    SlotID(id)
                };

                self.inc_ref(node.high);
                self.inc_ref(node.low);
                self.slots.insert(id, Slot::new(node));
                self.order[node.var.into_index()].slots.insert(id);

                entry.insert_entry(id);
                id
            }
        }
    }

    fn ite_cache(&self, key: IteKey) -> Option<SlotID> {
        match self.ite_cache.entry(key) {
            dashmap::Entry::Occupied(e) if self.slots.contains_key(e.get()) => Some(*e.get()),
            dashmap::Entry::Occupied(e) => {
                e.remove();
                None
            }
            dashmap::Entry::Vacant(_) => None,
        }
    }

    fn cofactors(&self, tree: Tree, id: SlotID, var: VarID) -> (SlotID, SlotID) {
        match tree {
            Tree::Node(node) if node.var == var => (node.low, node.high),
            _ => (id, id),
        }
    }

    pub fn ite(&self, guard: SlotID, then: SlotID, else_: SlotID) -> SlotID {
        if then == else_ {
            return then;
        }

        let g = self.tree(guard);

        match g {
            Tree::Terminal(true) => then,
            Tree::Terminal(false) => else_,
            Tree::Node(node) => {
                let key = IteKey(guard, then, else_);
                if let Some(t) = self.ite_cache(key) {
                    return t;
                }

                let t = self.tree(then);
                let e = self.tree(else_);

                let var = [Some(node.var), t.var(), e.var()]
                    .into_iter()
                    .min_by_key(|var| self.level(*var))
                    .unwrap()
                    .unwrap();

                let (g0, g1) = self.cofactors(g, guard, var);
                let (t0, t1) = self.cofactors(t, then, var);
                let (e0, e1) = self.cofactors(e, else_, var);

                let result = self.make(Node {
                    var,
                    high: self.ite(g1, t1, e1),
                    low: self.ite(g0, t0, e0),
                });

                self.ite_cache.insert(key, result).unwrap_or(result)
            }
        }
    }

    // FIXME: swapping levels instead of swapping variables
    //
    // This allows to implement arbitrary swaps easily:
    // - requires to maintain a backref table from levels to variables
    // - it does not need the `next` field in VarInfo anymore
    pub fn swap(&mut self, var: VarID) {
        let index = var.into_index();
        let Some(next) = self.order[index].next else {
            return;
        };

        for id in std::mem::take(&mut self.order[index].slots) {
            let node = &mut self.slots.get_mut(&id).unwrap().node;

            let high = self.tree(node.high);
            let low = self.tree(node.low);

            if high.var() != Some(next) && low.var() != Some(next) {
                self.order[index].slots.insert(id);
                continue;
            }

            self.unique.remove(node);

            let (h0, h1) = self.cofactors(high, node.high, next);
            let (l0, l1) = self.cofactors(low, node.low, next);

            let high = self.make(Node {
                var,
                high: h1,
                low: l1,
            });

            let low = self.make(Node {
                var,
                high: h0,
                low: l0,
            });

            assert_ne!(high, low);

            self.inc_ref(high);
            self.inc_ref(low);
            *node = Node {
                var: next,
                high,
                low,
            };
            self.unique.insert(*node, id);
            self.order[next.into_index()].slots.insert(id);
        }

        let temp = self.order[var.into_index()].level;
        self.order[var.into_index()].level = self.order[next.into_index()].level;
        self.order[next.into_index()].level = temp;

        self.order[var.into_index()].next = self.order[next.into_index()].next;
        self.order[next.into_index()].next = Some(var);
    }
}
