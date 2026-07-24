// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::key::{cmp_keys, DiscrKey};

#[derive(Clone, Debug)]
pub(crate) struct Trie<T> {
    values: Vec<T>,
    children: Vec<(DiscrKey, Trie<T>)>,
}

impl<T> Default for Trie<T> {
    fn default() -> Self {
        Trie {
            values: Vec::new(),
            children: Vec::new(),
        }
    }
}

impl<T> Trie<T> {
    pub(crate) fn insert_path(&mut self, path: &[DiscrKey], value: T) {
        if let Some((key, rest)) = path.split_first() {
            match self
                .children
                .binary_search_by(|(existing, _)| cmp_keys(existing, key))
            {
                Ok(index) => self.children[index].1.insert_path(rest, value),
                Err(index) => {
                    let mut child = Trie::default();
                    child.insert_path(rest, value);
                    self.children.insert(index, (key.clone(), child));
                }
            }
            return;
        }

        self.values.push(value);
    }

    pub(crate) fn match_path(&self, path: &[DiscrKey], out: &mut Vec<T>)
    where
        T: Clone,
    {
        if let Some((key, rest)) = path.split_first() {
            self.visit_child(key, rest, out);
            if !matches!(key, DiscrKey::Star) {
                self.visit_child(&DiscrKey::Star, rest, out);
            }
            if !matches!(key, DiscrKey::Other) {
                self.visit_child(&DiscrKey::Other, rest, out);
            }
            return;
        }

        out.extend(self.values.iter().cloned());
    }

    pub(crate) fn collect_all(&self, out: &mut Vec<T>)
    where
        T: Clone,
    {
        out.extend(self.values.iter().cloned());
        for (_, child) in &self.children {
            child.collect_all(out);
        }
    }

    fn visit_child(&self, key: &DiscrKey, rest: &[DiscrKey], out: &mut Vec<T>)
    where
        T: Clone,
    {
        if let Ok(index) = self
            .children
            .binary_search_by(|(existing, _)| cmp_keys(existing, key))
        {
            self.children[index].1.match_path(rest, out);
        }
    }
}
