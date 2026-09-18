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

use super::*;
use std::{
    fmt::{Display, Formatter},
    hash::{Hash, Hasher},
    iter::zip,
};

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
struct Literal(VarID, bool);

#[derive(Clone)]
pub struct Model<'m> {
    manager: &'m Manager,
    literals: Vec<Literal>,
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.1 {
            write!(f, "{}", self.0.index())
        } else {
            write!(f, "not {}", self.0.index())
        }
    }
}

impl Display for Model<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.literals.iter().map(|l| l.to_string()).join(", ")
        )
    }
}

impl Hash for Model<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.literals.hash(state)
    }
}

impl PartialEq for Model<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.literals.eq(&other.literals)
    }
}

impl<'m, const N: usize> PartialEq<[Lit<'m>; N]> for Model<'m> {
    fn eq(&self, other: &[Lit<'m>; N]) -> bool {
        if self.literals.len() != other.len() {
            return false;
        }

        for (literal, lit) in zip(self.literals.iter().copied(), other.iter().copied()) {
            if literal.0 != lit.var().var || literal.1 != lit.value() {
                return false
            }
        }
        
        true
    }
}

impl Eq for Model<'_> {}

impl<'m> Model<'m> {
    pub(super) fn new(manager: &'m Manager) -> Model<'m> {
        Model {
            manager,
            literals: Vec::new(),
        }
    }

    pub fn get(&self, var: Var<'_>) -> Option<bool> {
        self.literals
            .binary_search_by_key(&var, |lit| Var::new(lit.0, self.manager))
            .ok()
            .map(|i| self.literals[i].1)
    }

    pub fn set(&mut self, var: Var<'_>, value: impl Into<Option<bool>>) {
        let result = self
            .literals
            .binary_search_by_key(&var, |lit| Var::new(lit.0, self.manager));

        match (result, value.into()) {
            (Ok(index), None) => {
                self.literals.remove(index);
            }
            (Ok(index), Some(value)) => self.literals[index] = Literal(var.var, value),
            (Err(index), Some(value)) => self.literals.insert(index, Literal(var.var, value)),
            (Err(_), None) => {}
        }
    }

    pub fn pop(&mut self) {
        self.literals.pop();
    }
}

#[derive(Default, Clone, Copy, Hash, PartialEq, Eq)]
enum State {
    #[default]
    Enter,
    LowVisited,
    HighVisited,
}

#[derive(Clone, Copy)]
struct Frame {
    slot: SlotID,
    state: State,
}

#[derive(Clone)]
pub struct ModelIterator<'m> {
    stack: Vec<Frame>,
    model: Model<'m>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Advance {
    Continue,
    Stop,
}

impl<'m> ModelIterator<'m> {
    pub(super) fn new(manager: &'m Manager, root: BDD<'m>) -> Self {
        ModelIterator {
            stack: vec![Frame {
                slot: root.id,
                state: State::Enter,
            }],
            model: Model::new(manager),
        }
    }

    fn advance(&mut self) -> Advance {
        let Some(top) = self.stack.last() else {
            return Advance::Stop;
        };

        let tree = self.model.manager.inner.read().tree(top.slot);

        match tree {
            inner::Tree::Terminal(true) => Advance::Stop,
            inner::Tree::Terminal(false) => {
                self.stack.pop();
                Advance::Continue
            }
            inner::Tree::Node(node) => {
                let var = Var::new(node.var, self.model.manager);
                match top.state {
                    State::Enter => {
                        self.model.set(var, false);
                        self.stack.last_mut().unwrap().state = State::LowVisited;
                        self.stack.push(Frame {
                            slot: node.low,
                            state: State::Enter,
                        });
                    }
                    State::LowVisited => {
                        self.model.set(var, true);
                        self.stack.last_mut().unwrap().state = State::HighVisited;
                        self.stack.push(Frame {
                            slot: node.high,
                            state: State::Enter,
                        });
                    }
                    State::HighVisited => {
                        self.model.set(var, None);
                        self.stack.pop();
                    }
                }
                Advance::Continue
            }
        }
    }
}

impl<'m> Iterator for ModelIterator<'m> {
    type Item = Model<'m>;

    fn next(&mut self) -> Option<Model<'m>> {
        while self.advance() == Advance::Continue {}

        if !self.stack.is_empty() {
            self.stack.pop();
            Some(self.model.clone())
        } else {
            None
        }
    }
}
