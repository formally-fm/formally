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

use std::ops::{Add, AddAssign, Sub};

/// The position of a [variable](Var) in the variable order.
///
/// [Level] is an opaque value representing the position of a [variable](Var) in the current
/// variable order. [Level]s can be compared among each other, subtracted to obtain their distance
/// and added to an unsigned integer to step through the order.
#[derive(Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Level(u32);

impl Level {
    /// The maximum possible level.
    pub const MAX: Level = Level(u32::MAX);

    pub fn index(&self) -> usize {
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
pub(super) struct VarID(pub(super) u32);

impl VarID {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Default, Clone)]
pub struct Order {
    var_to_level: Vec<Level>,
    level_to_var: Vec<VarID>,
}

impl Order {
    pub fn size(&self) -> u32 {
        self.var_to_level.len() as u32
    }

    pub fn level_of(&self, var: VarID) -> Level {
        self.var_to_level[var.index()]
    }

    pub fn var_at(&self, level: Level) -> Option<VarID> {
        self.level_to_var.get(level.index()).copied()
    }

    #[expect(unused)]
    pub fn next_of(&self, var: VarID) -> Option<VarID> {
        self.var_at(self.level_of(var) + 1)
    }

    #[expect(unused)]
    pub fn first(&self) -> Option<VarID> {
        if self.size() == 0 {
            return None;
        }
        self.level_to_var.first().copied()
    }

    #[expect(unused)]
    pub fn last(&self) -> Option<VarID> {
        if self.size() == 0 {
            return None;
        }
        self.level_to_var.last().copied()
    }

    pub fn swap(&mut self, v1: VarID, v2: VarID) {
        let l1 = self.level_of(v1);
        let l2 = self.level_of(v2);

        self.var_to_level.swap(v1.index(), v2.index());
        self.level_to_var.swap(l1.index(), l2.index());
    }

    pub fn add_var(&mut self) -> VarID {
        assert!(
            self.size() < u32::MAX,
            "maximum number of variables reached"
        );

        let new = VarID(self.size());
        let level = Level(self.size());

        self.var_to_level.push(level);
        self.level_to_var.push(new);

        new
    }

    pub fn add_var_after(&mut self, level: Level) -> VarID {
        assert!(
            self.size() < u32::MAX,
            "maximum number of variables reached"
        );

        assert!(level < Level(self.size()), "non-existent Level");

        let new = VarID(self.size());
        for l in (level.index() + 1)..self.var_to_level.len() {
            self.var_to_level[self.level_to_var[l].index()] += 1;
        }
        self.var_to_level.push(level + 1);
        self.level_to_var.insert(level.index() + 1, new);

        new
    }

    pub fn add_vars(&mut self, n: u32) -> Vec<VarID> {
        self.var_to_level.reserve(n as usize);
        self.level_to_var.reserve(n as usize);

        let mut vars = Vec::with_capacity(n as usize);
        for _ in 0..n {
            vars.push(self.add_var())
        }

        vars
    }

    pub fn add_vars_after(&mut self, level: Level, n: u32) -> Vec<VarID> {
        assert!(
            self.size() < u32::MAX - n,
            "maximum number of variables reached"
        );

        assert!(level < Level(self.size()), "non-existent Level");

        let pos = level.index() + 1;

        let vars: Vec<_> = (self.size()..self.size() + n).map(VarID).collect();
        for l in pos..self.var_to_level.len() {
            self.var_to_level[self.level_to_var[l].index()] += n;
        }
        for l in pos..(pos + n as usize) {
            self.var_to_level.push(Level(l as u32));
        }
        self.level_to_var.splice(pos..pos, vars.iter().copied());

        vars
    }
}
