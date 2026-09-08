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
    fmt::{Debug, Formatter},
    num::NonZero,
    ops::Not,
};

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Var(pub(super) NonZero<u32>);

impl Debug for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Var({})", self.0)
    }
}

impl Not for Var {
    type Output = Lit;

    fn not(self) -> Lit {
        !Lit::from(self)
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Lit(NonZero<i32>);

impl From<Var> for Lit {
    fn from(var: Var) -> Self {
        Lit(var.0.cast_signed())
    }
}

impl Not for Lit {
    type Output = Lit;

    fn not(self) -> Lit {
        Lit(-self.0)
    }
}

impl Lit {
    pub fn var(self) -> Var {
        Var(self.0.unsigned_abs())
    }

    pub fn value(self) -> bool {
        self.0.is_positive()
    }
}

#[derive(Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Position(u64);

#[derive(Clone)]
pub struct Order {
    positions: Vec<Position>,
    subsequents: Vec<Position>,
    max: Option<Var>,
}

impl Default for Order {
    fn default() -> Self {
        Order {
            positions: vec![Position(0)],
            subsequents: vec![Position(u64::MAX)],
            max: None,
        }
    }
}

impl Order {
    pub fn new() -> Order {
        Order::default()
    }

    pub fn var_after(&mut self, previous: impl Into<Option<Var>>) -> Var {
        let previous = previous.into();
        let prev_pos = self.position(previous);
        let prev_sub = match previous {
            None => &mut self.subsequents[0],
            Some(var) => &mut self.subsequents[var.0.get() as usize],
        };

        let position = Position(prev_pos.0 + ((prev_sub.0 - prev_pos.0) / 2));

        assert!(position > prev_pos);

        let subsequent = *prev_sub;

        *prev_sub = position;

        let var = Var(NonZero::new(self.positions.len() as u32).unwrap());
        self.positions.push(position);
        self.subsequents.push(subsequent);

        if position > self.position(self.max) {
            self.max = Some(var)
        }

        var
    }

    pub fn max(&self) -> Option<Var> {
        self.max
    }

    pub fn var(&mut self) -> Var {
        self.var_after(self.max)
    }

    pub fn position(&self, var: impl Into<Option<Var>>) -> Position {
        match var.into() {
            None => self.positions[0],
            Some(var) => self.positions[var.0.get() as usize],
        }
    }
}

#[test]
pub fn order() {
    let mut order = Order::new();
    let first = order.var();
    let second = order.var_after(first);

    assert!(order.position(first) < order.position(second));

    let middle = order.var_after(first);
    assert!(order.position(first) < order.position(middle));
    assert!(order.position(middle) < order.position(second));

    let max = order.var();
    assert!(order.position(second) < order.position(max));
}
