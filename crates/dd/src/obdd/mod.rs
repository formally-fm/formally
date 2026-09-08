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

use std::{cell::RefCell, collections::HashMap, fmt::Debug};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TreeID(u32);

impl TreeID {
    pub const fn top() -> TreeID {
        TreeID(0)
    }

    pub const fn bottom() -> TreeID {
        TreeID(1)
    }

    pub fn boolean(value: bool) -> TreeID {
        if value { Self::top() } else { Self::bottom() }
    }

    pub fn to_bool(&self) -> Option<bool> {
        if *self == Self::top() {
            Some(true)
        } else if *self == Self::bottom() {
            Some(false)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Node {
    pub var: Var,
    pub top: TreeID,
    pub bottom: TreeID,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Tree {
    Boolean(bool),
    Node(Node),
}

impl Tree {
    pub fn to_bool(&self) -> Option<bool> {
        match *self {
            Tree::Boolean(b) => Some(b),
            Tree::Node(_) => None,
        }
    }
}

impl From<Var> for Tree {
    fn from(var: Var) -> Self {
        Tree::from(Lit::from(var))
    }
}

impl From<Lit> for Tree {
    fn from(lit: Lit) -> Tree {
        Tree::Node(Node {
            var: lit.var(),
            top: TreeID::boolean(lit.value()),
            bottom: TreeID::boolean(!lit.value()),
        })
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum BinOp {
    And,
    Or,
    Xor,
    Implies,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
struct BinOpEntry(BinOp, TreeID, TreeID);

#[derive(Clone)]
pub struct Forest {
    trees: RefCell<Vec<Tree>>,
    tree_to_id: RefCell<HashMap<Tree, TreeID>>,
    binop_cache: RefCell<HashMap<BinOpEntry, TreeID>>,
    order: Order,
}

impl Default for Forest {
    fn default() -> Self {
        Forest::new()
    }
}

impl Forest {
    pub fn new() -> Forest {
        let trees = vec![Tree::Boolean(true), Tree::Boolean(false)];
        let mut tree_to_id = HashMap::new();
        tree_to_id.insert(Tree::Boolean(true), TreeID::top());
        tree_to_id.insert(Tree::Boolean(false), TreeID::bottom());

        Forest {
            trees: RefCell::new(trees),
            tree_to_id: RefCell::new(tree_to_id),
            binop_cache: RefCell::default(),
            order: Order::default(),
        }
    }

    pub fn var(&mut self) -> TreeID {
        let var = self.order.var();
        self.id(Tree::from(var))
    }

    pub fn var_after(&mut self, previous: Var) -> TreeID {
        let var = self.order.var_after(Some(previous));
        self.id(Tree::from(var))
    }

    pub fn order(&self) -> &Order {
        &self.order
    }

    pub fn id(&self, tree: Tree) -> TreeID {
        if let Some(id) = self.tree_to_id.borrow().get(&tree) {
            return *id;
        }

        if let Tree::Node(node) = tree
            && node.top == node.bottom
        {
            return node.top;
        }

        let mut trees = self.trees.borrow_mut();
        let mut cache = self.tree_to_id.borrow_mut();

        let id = TreeID(trees.len() as u32);
        trees.push(tree);
        cache.insert(tree, id);

        id
    }

    pub fn tree(&self, id: TreeID) -> Tree {
        self.trees.borrow()[id.0 as usize]
    }

    pub fn not(&self, arg: TreeID) -> TreeID {
        self.apply(BinOp::Xor, arg, TreeID::top())
    }

    pub fn and(&self, args: impl IntoIterator<Item = TreeID>) -> TreeID {
        args.into_iter()
            .fold(TreeID::top(), |acc, t| self.apply(BinOp::And, acc, t))
    }

    pub fn or(&self, args: impl IntoIterator<Item = TreeID>) -> TreeID {
        args.into_iter()
            .fold(TreeID::top(), |acc, t| self.apply(BinOp::Or, acc, t))
    }

    pub fn xor(&self, args: impl IntoIterator<Item = TreeID>) -> TreeID {
        args.into_iter()
            .fold(TreeID::top(), |acc, t| self.apply(BinOp::Xor, acc, t))
    }

    pub fn implies(&self, left: TreeID, right: TreeID) -> TreeID {
        self.apply(BinOp::Implies, left, right)
    }

    pub fn apply(&self, binop: BinOp, left: TreeID, right: TreeID) -> TreeID {
        if let Some(id) = self
            .binop_cache
            .borrow()
            .get(&BinOpEntry(binop, left, right))
        {
            return *id;
        }

        let l = self.tree(left);
        let r = self.tree(right);

        let order = self.order();
        let result = match (l, r) {
            (Tree::Node(l), Tree::Node(r)) => {
                if l.var == r.var {
                    self.id(Tree::Node(Node {
                        var: l.var,
                        top: self.apply(binop, l.top, r.top),
                        bottom: self.apply(binop, l.bottom, r.bottom),
                    }))
                } else if order.position(l.var) < order.position(r.var) {
                    self.id(Tree::Node(Node {
                        var: l.var,
                        top: self.apply(binop, l.top, right),
                        bottom: self.apply(binop, l.bottom, right),
                    }))
                } else {
                    self.id(Tree::Node(Node {
                        var: r.var,
                        top: self.apply(binop, left, r.top),
                        bottom: self.apply(binop, left, r.bottom),
                    }))
                }
            }
            (Tree::Node(l), Tree::Boolean(r)) => self.id(Tree::Node(Node {
                var: l.var,
                top: self.apply(binop, l.top, TreeID::boolean(r)),
                bottom: self.apply(binop, l.bottom, TreeID::boolean(r)),
            })),
            (Tree::Boolean(l), Tree::Node(r)) => self.id(Tree::Node(Node {
                var: r.var,
                top: self.apply(binop, TreeID::boolean(l), r.top),
                bottom: self.apply(binop, TreeID::boolean(l), r.bottom),
            })),
            (Tree::Boolean(l), Tree::Boolean(r)) => match binop {
                BinOp::And => TreeID::boolean(l && r),
                BinOp::Or => TreeID::boolean(l || r),
                BinOp::Xor => TreeID::boolean(l ^ r),
                BinOp::Implies => TreeID::boolean(!l || r),
            },
        };

        self.binop_cache
            .borrow_mut()
            .insert(BinOpEntry(binop, left, right), result);

        result
    }

    pub fn model(&self) -> Option<HashMap<Var, bool>> {
        todo!()
    }
}

#[test]
pub fn apply() {
    let mut forest = Forest::new();
    let p = forest.var();
    let q = forest.var();

    let contradiction = forest.and([forest.implies(p, q), p, forest.not(q)]);

    assert_eq!(contradiction.to_bool(), Some(false));

    let validity = forest.implies(forest.and([forest.implies(p, q), p]), q);

    assert_eq!(validity.to_bool(), Some(true));
}
