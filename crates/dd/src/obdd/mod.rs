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

mod vars;

pub use vars::*;

use std::{cell::RefCell, collections::HashMap};

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TreeID(u32);

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum Edge {
    Top,
    Bottom,
    Tree(TreeID),
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Tree {
    pub var: Var,
    pub top: Edge,
    pub bottom: Edge,
}

impl From<Var> for Tree {
    fn from(var: Var) -> Self {
        Tree::from(Lit::from(var))
    }
}

impl From<Lit> for Tree {
    fn from(lit: Lit) -> Tree {
        if lit.value() {
            Tree {
                var: lit.var(),
                top: Edge::Top,
                bottom: Edge::Bottom,
            }
        } else {
            Tree {
                var: lit.var(),
                top: Edge::Bottom,
                bottom: Edge::Top,
            }
        }
    }
}

#[derive(Clone)]
pub struct Forest {
    trees: RefCell<Vec<Tree>>,
    cache: RefCell<HashMap<Tree, TreeID>>,
    order: Order,
}

impl Default for Forest {
    fn default() -> Self {
        Forest::new()
    }
}

impl Forest {
    pub fn new() -> Forest {
        Forest {
            trees: RefCell::default(),
            cache: RefCell::default(),
            order: Order::default(),
        }
    }

    pub fn var(&mut self) -> Var {
        self.order.var()
    }

    pub fn var_after(&mut self, previous: Var) -> Var {
        self.order.var_after(Some(previous))
    }
    
    pub fn order(&self) -> &Order {
        &self.order
    }

    pub fn id(&self, tree: Tree) -> TreeID {
        if let Some(id) = self.cache.borrow().get(&tree) {
            return *id;
        }

        let mut trees = self.trees.borrow_mut();
        let mut cache = self.cache.borrow_mut();

        let id = TreeID(trees.len() as u32);
        trees.push(tree);
        cache.insert(tree, id);

        id
    }

    pub fn tree(&self, id: TreeID) -> Tree {
        self.trees.borrow()[id.0 as usize]
    }
}
