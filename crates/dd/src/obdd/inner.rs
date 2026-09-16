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

use dashmap::{DashMap, DashSet};
use smallvec::SmallVec;
use std::{
    ops::{Add, AddAssign, Sub},
    sync::atomic::{AtomicU32, Ordering},
};

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub(super) struct VarID(u32);

impl VarID {
    pub fn from_index(index: usize) -> VarID {
        VarID(index as u32)
    }

    pub fn into_index(self) -> usize {
        self.0 as usize
    }
}

/// The position of a [variable](super::Var) in the variable order.
///
/// [Level] is an opaque value representing the position of a [variable](super::Var) in the current
/// variable order. [Level]s can be compared among each other, subtracted to obtain their distance
/// and added to an unsigned integer to step through the order.
#[derive(Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Level(u32);

impl Level {
    const MAX: Level = Level(u32::MAX);

    fn into_index(self) -> usize {
        self.0 as usize
    }
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

impl Sub for Level {
    type Output = i64;

    fn sub(self, rhs: Self) -> i64 {
        self.0 as i64 - rhs.0 as i64
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
    
    pub fn is_terminal(&self) -> bool {
        *self == SlotID::TOP || *self == SlotID::BOTTOM
    }
}

#[derive(Default)]
struct VarInfo {
    slots: DashSet<SlotID>,
}

pub(super) struct Inner {
    order: Vec<Level>,
    levels: Vec<VarID>,
    varinfo: Vec<VarInfo>,
    slots: DashMap<SlotID, Slot>,
    next_node: AtomicU32,
    unique: DashMap<Node, SlotID>,
    ite_cache: DashMap<IteKey, SlotID>,
}

impl Default for Inner {
    fn default() -> Self {
        Inner {
            order: Vec::default(),
            levels: Vec::default(),
            varinfo: Vec::default(),
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
    pub fn add_vars(&mut self, n: u32) -> SmallVec<[VarID; 8]> {
        if n == 0 {
            return SmallVec::new();
        }

        let next_level = self.levels.len() as u32;

        let first = next_level;
        let last = next_level + n;

        let mut vars = SmallVec::new();
        self.order.reserve(n as usize);
        for level in first..last {
            let var = VarID::from_index(self.order.len());
            vars.push(var);
            self.levels.push(var);
            self.order.push(Level(level));
            self.varinfo.push(VarInfo::default())
        }

        vars
    }

    pub fn add_vars_after(&mut self, prec: VarID, n: u32) -> SmallVec<[VarID; 8]> {
        if n == 0 {
            return SmallVec::new();
        }

        self.order.reserve(n as usize);
        self.levels.reserve(n as usize);

        let preclevel = self.level(Some(prec));
        for level in &mut self.order {
            if *level > preclevel {
                *level += n;
            }
        }

        let first = preclevel.0 + 1;
        let last = first + n;

        let mut vars = SmallVec::new();
        for level in first..last {
            let var = VarID::from_index(self.order.len());
            vars.push(var);
            self.levels.push(var);
            self.order.push(Level(level));
            self.varinfo.push(VarInfo::default());
        }

        let mut levels = Vec::new();
        levels.resize(self.order.len(), None);

        for index in 0..self.order.len() {
            levels[self.order[index].into_index()] = Some(VarID::from_index(index));
        }

        self.levels.clear();
        self.levels.extend(levels.into_iter().map(|v| v.unwrap()));

        vars
    }

    pub fn n_vars(&self) -> usize {
        self.order.len()
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

    pub fn at_level(&self, level: Level) -> Option<VarID> {
        self.levels.get(level.into_index()).copied()
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
    }

    fn collect(&mut self) -> Vec<SlotID> {
        let mut orphans = Vec::new();
        for s in self.slots.iter() {
            if s.refs == 0 {
                orphans.push(*s.key())
            }
        }

        orphans
    }

    pub fn reclaim(&mut self) {
        let mut orphans = self.collect();
        while !orphans.is_empty() {
            for id in std::mem::take(&mut orphans) {
                
                let Some(slot) = self.slots.get_mut(&id) else {
                    unreachable!()
                };

                self.unique.remove(&slot.node);
                self.varinfo[slot.node.var.into_index()].slots.remove(&id);
                if !slot.node.high.is_terminal() {
                    self.slots.get_mut(&slot.node.high).unwrap().refs -= 1;
                }
                if !slot.node.low.is_terminal() {
                    self.slots.get_mut(&slot.node.low).unwrap().refs -= 1;
                }
                drop(slot);
                
                self.slots.remove(&id);
            }
            orphans = self.collect();
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
                    let id = self.next_node.fetch_add(1, Ordering::AcqRel);
                    assert_ne!(id, u32::MAX, "maximum number of BDD nodes reached");
                    SlotID(id)
                };

                self.inc_ref(node.high);
                self.inc_ref(node.low);
                self.slots.insert(id, Slot::new(node));
                self.varinfo[node.var.into_index()].slots.insert(id);

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

                self.ite_cache.insert(key, result);

                result
            }
        }
    }

    pub fn restrict(&self, var: VarID, value: bool, body: SlotID) -> SlotID {
        match self.tree(body) {
            Tree::Terminal(true) => SlotID::TOP,
            Tree::Terminal(false) => SlotID::BOTTOM,
            Tree::Node(node) if node.var == var && value => node.high,
            Tree::Node(node) if node.var == var && !value => node.low,
            Tree::Node(node) if self.level(Some(node.var)) < self.level(Some(var)) => {
                self.make(Node {
                    var: node.var,
                    high: self.restrict(var, value, node.high),
                    low: self.restrict(var, value, node.low),
                })
            }
            Tree::Node(_) => body,
        }
    }

    pub fn swap(&mut self, level: Level) {
        let var = self.levels[level.into_index()];
        let index = var.into_index();
        let Some(next) = self.at_level(level + 1) else {
            return;
        };

        for id in std::mem::take(&mut self.varinfo[index].slots) {
            let node = self.slots.get_mut(&id).unwrap().node;

            let high = self.tree(node.high);
            let low = self.tree(node.low);

            if high.var() != Some(next) && low.var() != Some(next) {
                self.varinfo[index].slots.insert(id);
                continue;
            }

            self.unique.remove(&node);

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
            let node = &mut self.slots.get_mut(&id).unwrap().node;
            *node = Node {
                var: next,
                high,
                low,
            };
            self.unique.insert(*node, id);
            self.varinfo[next.into_index()].slots.insert(id);
        }

        self.order.swap(var.into_index(), next.into_index());
        self.levels
            .swap(level.into_index(), (level + 1).into_index());
    }
}
