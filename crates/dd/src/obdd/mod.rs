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

    pub fn var(&self) -> Option<Var> {
        match *self {
            Tree::Boolean(_) => None,
            Tree::Node(node) => Some(node.var),
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
struct IteEntry(TreeID, TreeID, TreeID);

#[derive(Clone)]
pub struct Forest {
    trees: RefCell<Vec<Tree>>,
    tree_to_id: RefCell<HashMap<Tree, TreeID>>,
    ite_cache: RefCell<HashMap<IteEntry, TreeID>>,
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
            ite_cache: RefCell::default(),
            order: Order::default(),
        }
    }

    pub fn var(&mut self) -> TreeID {
        let var = self.order.var();
        self.id(Tree::from(var))
    }

    pub fn var_after(&mut self, previous: Var) -> TreeID {
        let var = self.order.var_after(previous);
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
        self.ite(arg, TreeID::bottom(), TreeID::top())
    }

    pub fn and(&self, args: impl IntoIterator<Item = TreeID>) -> TreeID {
        args.into_iter()
            .fold(TreeID::top(), |acc, t| self.ite(acc, t, TreeID::bottom()))
    }

    pub fn or(&self, args: impl IntoIterator<Item = TreeID>) -> TreeID {
        args.into_iter()
            .fold(TreeID::top(), |acc, t| self.ite(acc, TreeID::top(), t))
    }

    pub fn xor(&self, args: impl IntoIterator<Item = TreeID>) -> TreeID {
        args.into_iter()
            .fold(TreeID::top(), |acc, t| self.ite(acc, self.not(t), t))
    }

    pub fn implies(&self, left: TreeID, right: TreeID) -> TreeID {
        self.ite(left, right, TreeID::top())
    }

    pub fn ite(&self, guard: TreeID, then: TreeID, else_: TreeID) -> TreeID {
        if then == else_ {
            return then;
        }

        let g = self.tree(guard);
        let t = self.tree(then);
        let e = self.tree(else_);

        match g {
            Tree::Boolean(true) => then,
            Tree::Boolean(false) => else_,
            Tree::Node(node) => {
                if let Some(t) = self.ite_cache.borrow().get(&IteEntry(guard, then, else_)) {
                    return *t;
                }

                let var = [Some(node.var), t.var(), e.var()]
                    .into_iter()
                    .min_by_key(|var| self.order().position(*var))
                    .unwrap()
                    .unwrap();
                
                fn cofactors(tree: Tree, id: TreeID, var: Var) -> (TreeID, TreeID) {
                    match tree {
                        Tree::Node(node) if node.var == var => (node.bottom, node.top),
                        _ => (id, id),
                    }
                }

                let (g0, g1) = cofactors(g, guard, var);
                let (t0, t1) = cofactors(t, then, var);
                let (e0, e1) = cofactors(e, else_, var);

                let top = self.ite(g1, t1, e1);
                let bottom = self.ite(g0, t0, e0);

                let result = self.id(Tree::Node(Node { var, top, bottom }));

                self.ite_cache
                    .borrow_mut()
                    .insert(IteEntry(guard, then, else_), result);

                result
            }
        }
    }

    pub fn restrict(&self, lit: Lit, tree: TreeID) -> TreeID {
        match self.tree(tree) {
            Tree::Boolean(_) => tree,
            Tree::Node(node) => {
                if node.var == lit.var() {
                    if lit.value() { node.top } else { node.bottom }
                } else {
                    self.id(Tree::Node(Node {
                        var: node.var,
                        top: self.restrict(lit, node.top),
                        bottom: self.restrict(lit, node.bottom),
                    }))
                }
            }
        }
    }

    pub fn exists(&self, var: Var, tree: TreeID) -> TreeID {
        self.or([
            self.restrict(Lit::from(var), tree),
            self.restrict(!Lit::from(var), tree),
        ])
    }

    pub fn forall(&self, var: Var, tree: TreeID) -> TreeID {
        self.not(self.exists(var, self.not(tree)))
    }

    pub fn model(&self) -> Option<HashMap<Var, bool>> {
        todo!()
    }
}

#[test]
pub fn ite() {
    let mut forest = Forest::new();
    let p = forest.var();
    let q = forest.var();

    let contradiction = forest.and([forest.implies(p, q), p, forest.not(q)]);

    assert_eq!(contradiction.to_bool(), Some(false));

    let validity = forest.implies(forest.and([forest.implies(p, q), p]), q);

    assert_eq!(validity.to_bool(), Some(true));
}
