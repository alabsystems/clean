// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use clean_kernel::{Expr, ExprKind};

use super::key::{DiscrKey, IndexMode, Match};
use super::path::{is_trivially_generic_path, mk_path};
use super::trie::Trie;
use crate::tactic::{Goal, ProofState};

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
        if path.is_empty() || is_trivially_generic_path(&path) {
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
