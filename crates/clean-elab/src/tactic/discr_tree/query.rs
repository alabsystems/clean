// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use clean_kernel::{Expr, ExprKind};

use super::key::{DiscrKey, IndexMode, Match};
use super::path::{is_trivially_generic_path, mk_path};
use super::trie::Trie;
use crate::tactic::{Goal, ProofState};

/// Longest key path the tree will index or descend. Trie recursion depth is
/// bounded by path length, and `mk_path` flattens expressions structurally —
/// an imported lemma (or goal) carrying a structurally-expanded numeral
/// (nested `Nat.succ` chains) can flatten to a path of millions of keys,
/// which overflowed the stack under real `import Init` once the typed
/// simpExtension decoder made ~10k entries live. Over-long lemma paths are
/// refused at insert (`insert_if_specific` → `false` → the caller's
/// always-scanned unindexed bucket, so the lemma stays fully usable);
/// over-long query paths skip the trie (the unindexed bucket still runs, so
/// this only narrows candidates for pathological goals, never soundness).
const MAX_INDEX_PATH_KEYS: usize = 512;

#[derive(Clone, Debug, Default)]
pub(crate) struct DiscrTree<T> {
    root: HashMap<DiscrKey, Trie<T>>,
}

impl<T> DiscrTree<T> {
    pub(crate) fn is_empty(&self) -> bool {
        self.root.is_empty()
    }

    pub(crate) fn insert_if_specific(
        &mut self,
        state: &ProofState,
        goal: &Goal,
        expr: &Expr,
        mode: IndexMode,
        value: T,
    ) -> bool {
        let path = mk_path(state, goal, expr, mode);
        self.insert_path_if_specific(&path, value)
    }

    /// Insert a value under an already-computed key path (same refusal rules
    /// as [`Self::insert_if_specific`]). Lets callers that also need the path
    /// for their own bookkeeping (e.g. `SimpLemmaSet`'s unindexed head-const
    /// buckets) run `mk_path` — whose per-node `whnf` is expensive — once.
    /// The `MAX_INDEX_PATH_KEYS` refusal lives HERE so every insertion route
    /// (wrapper or precomputed-path) gets the over-long-path protection.
    pub(crate) fn insert_path_if_specific(&mut self, path: &[DiscrKey], value: T) -> bool {
        if path.is_empty() || path.len() > MAX_INDEX_PATH_KEYS || is_trivially_generic_path(path) {
            return false;
        }

        let (root_key, rest) = path.split_first().expect("path checked non-empty");
        self.root
            .entry(root_key.clone())
            .or_default()
            .insert_path(rest, value);
        true
    }
}

impl<T> DiscrTree<T>
where
    T: Clone,
{
    pub(crate) fn get_match_with_extra(
        &self,
        state: &ProofState,
        goal: &Goal,
        expr: &Expr,
    ) -> Vec<Match<T>> {
        let mut current = expr.clone();
        let mut extra_args = 0;
        let mut matches = Vec::new();

        loop {
            let path = mk_path(state, goal, &current, IndexMode::Normal);
            matches.extend(
                self.get_match_by_path(&path)
                    .into_iter()
                    .map(|value| Match { value, extra_args }),
            );

            let ExprKind::App(function, _) = current.kind() else {
                break;
            };
            current = function.as_ref().clone();
            extra_args += 1;
        }

        matches
    }

    pub(crate) fn get_match_liberal(&self, state: &ProofState, goal: &Goal, expr: &Expr) -> Vec<T> {
        let path = mk_path(state, goal, expr, IndexMode::Normal);
        let Some(root_key) = path.first() else {
            return Vec::new();
        };

        let mut matches = Vec::new();
        self.collect_root_bucket(&DiscrKey::Star, &mut matches);
        self.collect_root_bucket(&DiscrKey::Other, &mut matches);
        if !matches!(root_key, DiscrKey::Star | DiscrKey::Other) {
            self.collect_root_bucket(root_key, &mut matches);
        }
        matches
    }

    fn get_match_by_path(&self, path: &[DiscrKey]) -> Vec<T> {
        if path.len() > MAX_INDEX_PATH_KEYS {
            // No lemma with a path this long is ever indexed (see
            // MAX_INDEX_PATH_KEYS), and descending would recurse per key.
            return Vec::new();
        }
        let Some(root_key) = path.first() else {
            return Vec::new();
        };

        let mut matches = Vec::new();
        self.visit_root_key(root_key, &path[1..], &mut matches);
        if !matches!(root_key, DiscrKey::Star) {
            self.visit_root_key(&DiscrKey::Star, &path[1..], &mut matches);
        }
        if !matches!(root_key, DiscrKey::Other) {
            self.visit_root_key(&DiscrKey::Other, &path[1..], &mut matches);
        }
        matches
    }

    fn visit_root_key(&self, key: &DiscrKey, rest: &[DiscrKey], matches: &mut Vec<T>) {
        if let Some(trie) = self.root.get(key) {
            trie.match_path(rest, matches);
        }
    }

    fn collect_root_bucket(&self, key: &DiscrKey, matches: &mut Vec<T>) {
        if let Some(trie) = self.root.get(key) {
            trie.collect_all(matches);
        }
    }
}
