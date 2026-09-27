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

/// A partial truth assignment for a [BDD]
///
/// [Model] represents a partial truth assignment to the variables managed by a [Manager]. Each
/// variable can be either `true`, `false` or not set.
///
/// [Model]s can be obtained by iterating over all the satisfying assignments of a [BDD] using
/// the [BDD::models()] method.
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
/// let xor = p ^ q;
///
/// for model in xor.models() {
///     println!("model: {model}")
/// }
/// # }
/// ```
#[derive(Clone)]
pub struct Model {
    inner: Arc<RwLock<Inner>>,
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

impl Display for Model {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.literals.iter().map(|l| l.to_string()).join(", ")
        )
    }
}

impl Hash for Model {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.literals.hash(state)
    }
}

impl PartialEq for Model {
    fn eq(&self, other: &Self) -> bool {
        self.literals.eq(&other.literals)
    }
}

impl<'m, const N: usize> PartialEq<[Lit; N]> for Model {
    fn eq(&self, other: &[Lit; N]) -> bool {
        if self.literals.len() != other.len() {
            return false;
        }

        for (literal, lit) in zip(self.literals.iter().copied(), other.iter().cloned()) {
            if literal.0 != lit.var().var || literal.1 != lit.value() {
                return false;
            }
        }

        true
    }
}

impl Eq for Model {}

impl Model {
    pub(super) fn new(inner: Arc<RwLock<Inner>>) -> Model {
        Model {
            inner: inner.clone(),
            literals: Vec::new(),
        }
    }

    /// Get the truth value (if any) of a variable in this model.
    pub fn get(&self, var: Var) -> Option<bool> {
        self.literals
            .binary_search_by_key(&var, |lit| Var::new(lit.0, self.inner.clone()))
            .ok()
            .map(|i| self.literals[i].1)
    }

    /// Set the truth value of a variable in this model.
    pub fn set(&mut self, var: Var, value: impl Into<Option<bool>>) {
        let result = self
            .literals
            .binary_search_by_key(&var, |lit| Var::new(lit.0, self.inner.clone()));

        match (result, value.into()) {
            (Ok(index), None) => {
                self.literals.remove(index);
            }
            (Ok(index), Some(value)) => self.literals[index] = Literal(var.var, value),
            (Err(index), Some(value)) => self.literals.insert(index, Literal(var.var, value)),
            (Err(_), None) => {}
        }
    }

    /// Unsets the truth value of the last variable in the variable order currently set in this
    /// model.
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

impl Frame {
    fn new(inner: &Inner, slot: SlotID) -> Frame {
        inner.inc_ref(slot);
        Frame {
            slot,
            state: State::Enter,
        }
    }

    fn release(&self, inner: &Inner) {
        inner.dec_ref(self.slot)
    }
}

/// An iterator over the satisfying assignments of a [BDD].
///
/// The [next()](ModelIterator::next()) method panics if the variable order of the underlying
/// [Manager] changed after the construction of the iterator.
#[derive(Clone)]
pub struct ModelIterator {
    stack: Vec<Frame>,
    model: Model,
    seq: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Advance {
    Continue,
    Stop,
}

impl Drop for ModelIterator {
    fn drop(&mut self) {
        let inner = self.model.inner.read();
        while !self.stack.is_empty() {
            self.stack.pop().inspect(|f| f.release(&inner));
        }
    }
}

impl<'m> ModelIterator {
    pub(super) fn new(inner: Arc<RwLock<Inner>>, root: BDD) -> Self {
        let inner = inner.read();
        ModelIterator {
            stack: vec![Frame {
                slot: inner.inc_ref(root.id),
                state: State::Enter,
            }],
            model: Model::new(inner.arc()),
            seq: inner.seq(),
        }
    }

    fn advance(&mut self) -> Advance {
        let Some(top) = self.stack.last() else {
            return Advance::Stop;
        };

        let inner = self.model.inner.clone();
        let inner = inner.read();
        assert_eq!(
            self.seq,
            inner.seq(),
            "OBDD variable order changed while iterating over models"
        );
        let tree = inner.tree(top.slot);

        match tree {
            inner::Tree::Terminal(true) => Advance::Stop,
            inner::Tree::Terminal(false) => {
                self.stack.pop().inspect(|f| f.release(&inner));
                Advance::Continue
            }
            inner::Tree::Node(node) => {
                let var = Var::new(node.var, self.model.inner.clone());
                match top.state {
                    State::Enter => {
                        self.model.set(var, false);
                        self.stack.last_mut().unwrap().state = State::LowVisited;
                        self.stack.push(Frame::new(&inner, node.low));
                    }
                    State::LowVisited => {
                        self.model.set(var, true);
                        self.stack.last_mut().unwrap().state = State::HighVisited;
                        self.stack.push(Frame::new(&inner, node.high));
                    }
                    State::HighVisited => {
                        self.model.set(var, None);
                        self.stack.pop().inspect(|f| f.release(&inner));
                    }
                }
                Advance::Continue
            }
        }
    }
}

impl<'m> Iterator for ModelIterator {
    type Item = Model;

    fn next(&mut self) -> Option<Model> {
        while self.advance() == Advance::Continue {}

        if !self.stack.is_empty() {
            self.stack.pop();
            Some(self.model.clone())
        } else {
            None
        }
    }
}
