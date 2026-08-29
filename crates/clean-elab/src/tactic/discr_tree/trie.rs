// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::key::{cmp_keys, subtree_key_count, DiscrKey};

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
            // A stored `Star`/`Other` is a WHOLE-SUBTERM placeholder (the
            // pattern side emits it with none of the subterm's children), so
            // descending into one must skip the query's complete leading
            // subtree — arity-aware — not a single key. Skipping one key made
            // every star lemma invisible at any position whose corresponding
            // argument was compound: `Nat.succ ?n` (path `[succ, *]`) was
            // offered at `Nat.succ n` but NOT at
            // `Nat.succ (List.length l)` (path `[succ, length, ..]`), which
            // starved `simp`'s closing rewrite under `import Init` (g_simp
            // probe 27).
            let after_subtree = &path[subtree_key_count(path)..];
            if !matches!(key, DiscrKey::Star) {
                self.visit_child(&DiscrKey::Star, after_subtree, out);
            }
            if !matches!(key, DiscrKey::Other) {
                self.visit_child(&DiscrKey::Other, after_subtree, out);
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
