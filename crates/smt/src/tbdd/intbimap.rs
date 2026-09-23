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

use std::{collections::HashMap, fmt::Debug, hash::Hash};

use dashmap::{DashMap, Entry};

#[derive(Clone)]
pub struct IntBiMap<K: Hash + Eq, I> {
    key_to_index: DashMap<K, I>,
    index_to_key: boxcar::Vec<K>,
}

impl<K: Hash + Eq, I> Default for IntBiMap<K, I> {
    fn default() -> Self {
        IntBiMap::new()
    }
}

pub trait IntBiMapIndex:
    Clone + TryInto<usize, Error: Debug> + TryFrom<usize, Error: Debug>
{
}
impl<T: Clone + TryInto<usize, Error: Debug> + TryFrom<usize, Error: Debug>> IntBiMapIndex for T {}

impl<K: Hash + Eq, I> IntBiMap<K, I> {
    pub fn new() -> Self {
        IntBiMap {
            key_to_index: DashMap::new(),
            index_to_key: boxcar::Vec::new(),
        }
    }

    pub fn size(&self) -> usize {
        self.index_to_key.count()
    }
}

impl<K: Clone + Hash + Eq, I: IntBiMapIndex> IntBiMap<K, I> {
    pub fn by_index(&self, index: I) -> Option<&K> {
        let index: usize = index.try_into().ok()?;
        self.index_to_key.get(index)
    }

    pub fn by_key(&self, key: &K) -> Option<I> {
        self.key_to_index.get(key).as_deref().cloned()
    }

    pub fn by_key_or_insert(&self, key: K) -> I {
        match self.key_to_index.entry(key) {
            Entry::Occupied(entry) => entry.get().clone(),
            Entry::Vacant(entry) => {
                let id: I = self
                    .index_to_key
                    .push(entry.key().clone())
                    .try_into()
                    .unwrap();
                entry.insert(id.clone());

                id
            }
        }
    }
}
