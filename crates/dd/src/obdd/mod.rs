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

use crate::formally;
use formally::support::Nominal;
use std::fmt::Formatter;
use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::Debug,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref, Not},
};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct TreeID(u32);

impl TreeID {
    const TOP: TreeID = TreeID(0);
    const BOTTOM: TreeID = TreeID(1);
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct OBDD<'f>(TreeID, Nominal<&'f Forest>);

impl<'f> OBDD<'f> {
    pub fn to_bool(&self) -> Option<bool> {
        match self.0 {
            TreeID::TOP => Some(true),
            TreeID::BOTTOM => Some(false),
            _ => None,
        }
    }

    pub fn forest(&self) -> &'f Forest {
        self.1.into_inner()
    }
}

impl<'f> Not for OBDD<'f> {
    type Output = OBDD<'f>;

    fn not(self) -> Self::Output {
        self.forest().not(self)
    }
}

impl<'f> BitAnd for OBDD<'f> {
    type Output = OBDD<'f>;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.forest().and([self, rhs])
    }
}

impl<'f> BitAndAssign for OBDD<'f> {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = self.forest().and([*self, rhs])
    }
}

impl<'f> BitOr for OBDD<'f> {
    type Output = OBDD<'f>;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.forest().or([self, rhs])
    }
}

impl<'f> BitOrAssign for OBDD<'f> {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.forest().or([*self, rhs])
    }
}

impl<'f> BitXor for OBDD<'f> {
    type Output = OBDD<'f>;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.forest().xor([self, rhs])
    }
}

impl<'f> BitXorAssign for OBDD<'f> {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = self.forest().xor([*self, rhs])
    }
}

pub fn implies<'f>(o1: OBDD<'f>, o2: OBDD<'f>) -> OBDD<'f> {
    o1.forest().implies(o1, o2)
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct NodeData {
    var: Var,
    top: TreeID,
    bottom: TreeID,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
enum TreeData {
    Boolean(bool),
    Node(NodeData),
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Node<'f> {
    var: Var,
    top: OBDD<'f>,
    bottom: OBDD<'f>,
}

impl From<Node<'_>> for NodeData {
    fn from(node: Node<'_>) -> Self {
        NodeData {
            var: node.var,
            top: node.top.0,
            bottom: node.bottom.0,
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Tree<'f> {
    Boolean(bool),
    Node(Node<'f>),
}

impl From<Tree<'_>> for TreeData {
    fn from(tree: Tree<'_>) -> Self {
        match tree {
            Tree::Boolean(b) => TreeData::Boolean(b),
            Tree::Node(n) => TreeData::Node(NodeData::from(n)),
        }
    }
}

impl<'f> Tree<'f> {
    pub fn var(&self) -> Option<Var> {
        match *self {
            Tree::Boolean(_) => None,
            Tree::Node(node) => Some(node.var),
        }
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
    trees: RefCell<Vec<TreeData>>,
    tree_to_id: RefCell<HashMap<TreeData, TreeID>>,
    ite_cache: RefCell<HashMap<IteEntry, TreeID>>,
    order: RefCell<Order>,
}

impl Default for Forest {
    fn default() -> Self {
        Forest::new()
    }
}

impl Debug for Forest {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Forest {{ ... }}")
    }
}

impl Forest {
    pub fn new() -> Forest {
        let trees = vec![TreeData::Boolean(true), TreeData::Boolean(false)];
        let mut tree_to_id = HashMap::new();
        tree_to_id.insert(TreeData::Boolean(true), TreeID::TOP);
        tree_to_id.insert(TreeData::Boolean(false), TreeID::BOTTOM);

        Forest {
            trees: RefCell::new(trees),
            tree_to_id: RefCell::new(tree_to_id),
            ite_cache: RefCell::default(),
            order: RefCell::default(),
        }
    }

    pub fn var(&self) -> OBDD<'_> {
        let var = self.order.borrow_mut().var();
        self.id(Tree::Node(Node {
            var,
            top: self.top(),
            bottom: self.bottom(),
        }))
    }

    pub fn var_after<'s>(&'s self, prev: OBDD<'s>) -> OBDD<'s> {
        let prev = self.tree(prev);
        let var = match prev.var() {
            None => self.order.borrow_mut().var(),
            Some(var) => self.order.borrow_mut().var_after(var),
        };
        self.id(Tree::Node(Node {
            var,
            top: self.top(),
            bottom: self.bottom(),
        }))
    }

    pub fn order(&self) -> impl Deref<Target = Order> {
        self.order.borrow()
    }

    pub fn id<'s>(&'s self, tree: Tree<'s>) -> OBDD<'s> {
        if let Some(id) = self.tree_to_id.borrow().get(&TreeData::from(tree)) {
            return OBDD(*id, Nominal(self));
        }

        if let Tree::Node(node) = tree
            && node.top == node.bottom
        {
            return node.top;
        }

        let mut trees = self.trees.borrow_mut();
        let mut cache = self.tree_to_id.borrow_mut();

        let id = TreeID(trees.len() as u32);
        let data = TreeData::from(tree);
        trees.push(data);
        cache.insert(data, id);

        OBDD(id, Nominal(self))
    }

    pub fn tree(&self, id: OBDD) -> Tree<'_> {
        let data = self.trees.borrow()[id.0.0 as usize];
        match data {
            TreeData::Boolean(b) => Tree::Boolean(b),
            TreeData::Node(node) => Tree::Node(Node {
                var: node.var,
                top: OBDD(node.top, Nominal(self)),
                bottom: OBDD(node.bottom, Nominal(self)),
            }),
        }
    }

    pub fn top(&self) -> OBDD<'_> {
        OBDD(TreeID::TOP, Nominal(self))
    }

    pub fn bottom(&self) -> OBDD<'_> {
        OBDD(TreeID::BOTTOM, Nominal(self))
    }

    pub fn not<'s>(&'s self, arg: OBDD<'s>) -> OBDD<'s> {
        self.ite(arg, self.bottom(), self.top())
    }

    pub fn and<'s>(&'s self, args: impl IntoIterator<Item = OBDD<'s>>) -> OBDD<'s> {
        args.into_iter()
            .fold(self.top(), |acc, t| self.ite(acc, t, self.bottom()))
    }

    pub fn or<'s>(&'s self, args: impl IntoIterator<Item = OBDD<'s>>) -> OBDD<'s> {
        args.into_iter()
            .fold(self.top(), |acc, t| self.ite(acc, self.top(), t))
    }

    pub fn xor<'s>(&'s self, args: impl IntoIterator<Item = OBDD<'s>>) -> OBDD<'s> {
        args.into_iter()
            .fold(self.top(), |acc, t| self.ite(acc, self.not(t), t))
    }

    pub fn implies<'s>(&'s self, left: OBDD<'s>, right: OBDD<'s>) -> OBDD<'s> {
        self.ite(left, right, self.top())
    }

    pub fn ite<'s>(&'s self, guard: OBDD<'s>, then: OBDD<'s>, else_: OBDD<'s>) -> OBDD<'s> {
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
                if let Some(t) = self
                    .ite_cache
                    .borrow()
                    .get(&IteEntry(guard.0, then.0, else_.0))
                {
                    return OBDD(*t, Nominal(self));
                }

                let var = [Some(node.var), t.var(), e.var()]
                    .into_iter()
                    .min_by_key(|var| self.order().position(*var))
                    .unwrap()
                    .unwrap();

                fn cofactors<'f>(tree: Tree<'f>, id: OBDD<'f>, var: Var) -> (OBDD<'f>, OBDD<'f>) {
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
                    .insert(IteEntry(guard.0, then.0, else_.0), result.0);

                result
            }
        }
    }

    pub fn restrict<'s>(&'s self, lit: Lit, tree: OBDD<'s>) -> OBDD<'s> {
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

    pub fn exists<'s>(&'s self, var: Var, tree: OBDD<'s>) -> OBDD<'s> {
        self.or([
            self.restrict(Lit::from(var), tree),
            self.restrict(!Lit::from(var), tree),
        ])
    }

    pub fn forall<'s>(&'s self, var: Var, tree: OBDD<'s>) -> OBDD<'s> {
        self.not(self.exists(var, self.not(tree)))
    }

    pub fn model(&self) -> Option<HashMap<Var, bool>> {
        todo!()
    }
}

#[test]
pub fn ite() {
    let forest = Forest::new();
    let p = forest.var();
    let q = forest.var_after(p);

    let contradiction = implies(p, q) & p & !q;

    assert_eq!(contradiction.to_bool(), Some(false));

    let validity = implies(implies(p, q) & p, q);

    assert_eq!(validity.to_bool(), Some(true));
}
