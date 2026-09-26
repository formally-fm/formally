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

use bitvec::vec::BitVec;
use dashmap::{DashMap, Entry};
use std::ops::BitOrAssign;
use std::{
    hash::Hash,
    ops::{Deref, DerefMut},
};

#[derive(Clone)]
pub struct SyncBiMap<K: Hash + Eq, I: Hash + Eq> {
    key_to_index: DashMap<K, I>,
    index_to_key: DashMap<I, K>,
}

impl<K: Hash + Eq, I: Hash + Eq> Default for SyncBiMap<K, I> {
    fn default() -> Self {
        SyncBiMap::new()
    }
}

impl<K: Hash + Eq, I: Hash + Eq> SyncBiMap<K, I> {
    pub fn new() -> Self {
        SyncBiMap {
            key_to_index: DashMap::new(),
            index_to_key: DashMap::new(),
        }
    }

    pub fn size(&self) -> usize {
        self.index_to_key.len()
    }
}

impl<K: Clone + Hash + Eq, I: Clone + Hash + Eq> SyncBiMap<K, I> {
    pub fn by_index(&self, index: &I) -> Option<K> {
        self.index_to_key.get(index).as_deref().cloned()
    }

    pub fn by_key(&self, key: &K) -> Option<I> {
        self.key_to_index.get(key).as_deref().cloned()
    }

    pub fn by_key_or_insert<F>(&self, key: K, f: F) -> I
    where
        F: FnOnce() -> I,
    {
        match self.key_to_index.entry(key) {
            Entry::Occupied(entry) => entry.get().clone(),
            Entry::Vacant(entry) => {
                let index = f();
                self.index_to_key.insert(index.clone(), entry.key().clone());
                entry.insert(index.clone());
                index
            }
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = K> {
        self.key_to_index.iter().map(|r| r.key().clone())
    }

    pub fn indexes(&self) -> impl Iterator<Item = I> {
        self.index_to_key.iter().map(|r| r.key().clone())
    }

    pub fn iter(&self) -> impl Iterator<Item = (K, I)> {
        self.key_to_index.iter().map(|r| {
            let (k, i) = r.pair();
            (k.clone(), i.clone())
        })
    }
}

#[derive(Default, Clone, Hash, PartialEq, Eq)]
pub struct BitSet {
    bits: BitVec,
}

impl BitSet {
    pub fn new() -> BitSet {
        BitSet::default()
    }

    pub fn with_capacity(capacity: usize) -> BitSet {
        BitSet {
            bits: BitVec::with_capacity(capacity),
        }
    }

    pub fn set(&mut self, index: usize, value: bool) {
        if index >= self.bits.len() {
            self.bits.resize(index + 1, false);
        }
        self.bits.set(index, value);
    }

    pub fn get(&self, index: usize) -> bool {
        index < self.bits.len() && self.bits[index]
    }
}

impl BitOrAssign for BitSet {
    fn bitor_assign(&mut self, rhs: Self) {
        if self.len() < rhs.len() {
            self.bits.resize(rhs.len(), false);
        }
        self.bits |= rhs.bits
    }
}

impl Deref for BitSet {
    type Target = BitVec;

    fn deref(&self) -> &BitVec {
        &self.bits
    }
}

impl DerefMut for BitSet {
    fn deref_mut(&mut self) -> &mut BitVec {
        &mut self.bits
    }
}
