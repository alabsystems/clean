// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type-directed discrimination tree for sub-10us type search.
//!
//! A discrimination tree (discrim tree) is a trie-like index where each path
//! from root to leaf corresponds to a flattened type expression. This enables
//! fast unification-based retrieval: given a query type, we walk the tree and
//! collect all leaves whose stored types unify with the query.
//!
//! ## Flattening
//!
//! Type expressions are flattened left-to-right depth-first into a sequence
//! of `DiscrimKey` values:
//!
//! - `App(fn, arg)` -> `[App, ...flatten(fn), ...flatten(arg)]`
//! - `Pi(_, ty, body)` -> `[Pi, ...flatten(ty), ...flatten(body)]`
//! - `Lam(_, ty, body)` -> `[Lam, ...flatten(ty), ...flatten(body)]`
//! - `Const(name_idx, _)` -> `[Const(name_idx)]`
//! - `BVar(idx)` -> `[BVar(idx)]`
//! - `Sort(_)` -> `[Sort]`
//! - `Star` matches any single subtree during search

use clean_kernel::flat::{FlatExpr, FlatTag};

use crate::shard::ShardReader;
use crate::types::{ConstantIdx, ExprIdx};

/// Alphabet for discrimination tree paths.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DiscrimKey {
    /// Application node — followed by flattened fn then flattened arg.
    App,
    /// Lambda node — followed by flattened ty then flattened body.
    Lam,
    /// Pi/forall node — followed by flattened ty then flattened body.
    Pi,
    /// Named constant (leaf). The u32 is the name index in the string table.
    Const(u32),
    /// Bound variable (leaf). The u32 is the de Bruijn index.
    BVar(u32),
    /// Sort/Type (leaf).
    Sort,
    /// Wildcard — matches any single subtree during search.
    Star,
}

/// A node in the discrimination tree.
#[derive(Clone, Debug)]
pub struct DiscrimNode {
    /// The key at this node.
    pub key: DiscrimKey,
    /// Indices into `DiscrimTree::nodes` for children.
    pub children: Vec<usize>,
    /// Constants whose type path ends at this node.
    pub leaves: Vec<ConstantIdx>,
}

/// Type-directed discrimination tree for fast type search.
///
/// The tree is stored as a flat `Vec<DiscrimNode>`. Node 0 is the root
/// (a sentinel with key `Star`). All paths from root to leaves correspond
/// to flattened type expressions.
pub struct DiscrimTree {
    nodes: Vec<DiscrimNode>,
}

impl DiscrimTree {
    /// Create an empty discrimination tree.
    pub fn new() -> Self {
        Self {
            nodes: vec![DiscrimNode {
                key: DiscrimKey::Star,
                children: Vec::new(),
                leaves: Vec::new(),
            }],
        }
    }

    /// Number of nodes in the tree (including root sentinel).
    #[inline]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the tree contains only the root sentinel (no indexed constants).
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.len() == 1 && self.nodes[0].children.is_empty()
    }

    /// Insert a constant indexed by its type expression.
    ///
    /// `type_exprs` is the full FlatExpr arena. `expr_idx` is the root of the
    /// type expression within that arena. `constant_idx` is the constant to
    /// associate with this type.
    pub fn insert(
        &mut self,
        type_exprs: &[FlatExpr],
        expr_idx: ExprIdx,
        constant_idx: ConstantIdx,
    ) {
        let path = flatten_expr(type_exprs, expr_idx);
        let mut current = 0; // root
        for key in &path {
            current = self.get_or_create_child(current, *key);
        }
        self.nodes[current].leaves.push(constant_idx);
    }

    /// Search for constants whose type unifies with the query.
    ///
    /// `query_exprs` is the full FlatExpr arena. `query_idx` is the root of
    /// the query type expression. `max_results` limits the number of results.
    ///
    /// The query may contain `Star` wildcards (any FlatExpr that isn't
    /// recognized or that is explicitly a wildcard placeholder). During search,
    /// `Star` in the query matches any subtree in the stored paths, and `Star`
    /// in the stored tree matches any subtree in the query.
    pub fn search(
        &self,
        query_exprs: &[FlatExpr],
        query_idx: ExprIdx,
        max_results: usize,
    ) -> Vec<ConstantIdx> {
        let path = flatten_expr(query_exprs, query_idx);
        let mut results = Vec::new();
        self.search_recursive(0, &path, 0, max_results, &mut results);
        results
    }

    /// Build a discrimination tree from all constants in a shard.
    pub fn build_from_shard(reader: &ShardReader) -> Self {
        let mut tree = Self::new();
        for (i, constant) in reader.constants.iter().enumerate() {
            let type_idx = constant.type_idx;
            if (type_idx as usize) < reader.exprs.len() {
                tree.insert(&reader.exprs, type_idx, i as ConstantIdx);
            }
        }
        tree
    }

    /// Scored search: returns `(constant_idx, relevance_score)` pairs.
    ///
    /// The relevance score is in `[0.0, 1.0]` and is based on match quality:
    /// - Exact matches score 1.0.
    /// - Wildcard matches reduce the score proportionally to how much of the
    ///   path was matched exactly vs via wildcards.
    pub fn search_generalized(&self, query: &[DiscrimKey], max_results: usize) -> Vec<(u32, f32)> {
        let mut results: Vec<(u32, f32)> = Vec::new();
        let total_keys = query.len().max(1) as f32;
        self.search_scored_recursive(0, query, 0, 0, total_keys, max_results, &mut results);
        // Sort by descending relevance, then ascending index for stability.
        results.sort_by(|a, b| {
            b.1.partial_cmp(&a.1)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then(a.0.cmp(&b.0))
        });
        results.truncate(max_results);
        results
    }

    /// Compute statistics about the tree structure.
    #[must_use]
    pub fn statistics(&self) -> DiscrimStats {
        let mut stats = DiscrimStats {
            node_count: self.nodes.len(),
            leaf_count: 0,
            max_depth: 0,
            depth_sum: 0,
            total_entries: 0,
        };
        self.stats_recursive(0, 0, &mut stats);
        stats
    }

    /// Merge another discrimination tree into this one, offsetting all constant
    /// indices by `offset`. Used for combining shard-level trees.
    pub fn merge(&mut self, other: &DiscrimTree, offset: u32) {
        // Walk the other tree and re-insert all paths with offset indices.
        self.merge_recursive(0, other, 0, offset);
    }

    fn stats_recursive(&self, node_idx: usize, depth: usize, stats: &mut DiscrimStats) {
        if depth > stats.max_depth {
            stats.max_depth = depth;
        }
        stats.depth_sum += depth;
        let leaf_count = self.nodes[node_idx].leaves.len();
        if leaf_count > 0 {
            stats.leaf_count += 1;
        }
        stats.total_entries += leaf_count;
        for &child_idx in &self.nodes[node_idx].children {
            self.stats_recursive(child_idx, depth + 1, stats);
        }
    }

    fn search_scored_recursive(
        &self,
        node_idx: usize,
        path: &[DiscrimKey],
        path_pos: usize,
        wildcards_used: usize,
        total_keys: f32,
        max_results: usize,
        results: &mut Vec<(u32, f32)>,
    ) {
        if results.len() >= max_results {
            return;
        }
        if path_pos >= path.len() {
            let exact_matches = (path.len() - wildcards_used) as f32;
            let score = exact_matches / total_keys;
            for &leaf in &self.nodes[node_idx].leaves {
                if results.len() >= max_results {
                    return;
                }
                results.push((leaf, score));
            }
            return;
        }
        let query_key = path[path_pos];
        for &child_idx in &self.nodes[node_idx].children {
            if results.len() >= max_results {
                return;
            }
            let child_key = self.nodes[child_idx].key;
            if query_key == DiscrimKey::Star {
                // Wildcard in query — count it.
                self.search_scored_recursive(
                    child_idx,
                    path,
                    path_pos + 1,
                    wildcards_used + 1,
                    total_keys,
                    max_results,
                    results,
                );
            } else if child_key == DiscrimKey::Star {
                // Wildcard in tree — count it.
                let skip = subtree_key_size(query_key);
                self.search_scored_recursive(
                    child_idx,
                    path,
                    path_pos + skip,
                    wildcards_used + 1,
                    total_keys,
                    max_results,
                    results,
                );
            } else if child_key == query_key {
                // Exact match — no wildcard cost.
                self.search_scored_recursive(
                    child_idx,
                    path,
                    path_pos + 1,
                    wildcards_used,
                    total_keys,
                    max_results,
                    results,
                );
            }
        }
    }

    fn merge_recursive(
        &mut self,
        self_node: usize,
        other: &DiscrimTree,
        other_node: usize,
        offset: u32,
    ) {
        // Copy leaves with offset.
        for &leaf in &other.nodes[other_node].leaves {
            self.nodes[self_node].leaves.push(leaf + offset);
        }
        // Recursively merge children.
        for &other_child in &other.nodes[other_node].children {
            let child_key = other.nodes[other_child].key;
            let self_child = self.get_or_create_child(self_node, child_key);
            self.merge_recursive(self_child, other, other_child, offset);
        }
    }

    /// Find or create a child of `parent` with the given key. Returns the
    /// child's index in `self.nodes`.
    fn get_or_create_child(&mut self, parent: usize, key: DiscrimKey) -> usize {
        // Search existing children.
        for &child_idx in &self.nodes[parent].children {
            if self.nodes[child_idx].key == key {
                return child_idx;
            }
        }
        // Create new child.
        let new_idx = self.nodes.len();
        self.nodes.push(DiscrimNode {
            key,
            children: Vec::new(),
            leaves: Vec::new(),
        });
        self.nodes[parent].children.push(new_idx);
        new_idx
    }

    /// Recursive search through the tree with wildcard support.
    ///
    /// `node_idx` is the current tree node. `path` is the flattened query.
    /// `path_pos` is our current position in the path. When we reach the end
    /// of the path, we collect leaves from the current node.
    fn search_recursive(
        &self,
        node_idx: usize,
        path: &[DiscrimKey],
        path_pos: usize,
        max_results: usize,
        results: &mut Vec<ConstantIdx>,
    ) {
        if results.len() >= max_results {
            return;
        }

        // If we've consumed the entire query path, collect leaves.
        if path_pos >= path.len() {
            for &leaf in &self.nodes[node_idx].leaves {
                if results.len() >= max_results {
                    return;
                }
                results.push(leaf);
            }
            return;
        }

        let query_key = path[path_pos];

        for &child_idx in &self.nodes[node_idx].children {
            if results.len() >= max_results {
                return;
            }

            let child_key = self.nodes[child_idx].key;

            // Case 1: Query has Star — match any single subtree in the tree.
            if query_key == DiscrimKey::Star {
                // Star matches a single subtree. We need to compute the
                // subtree size of the child's key to know how many positions
                // it occupies in the stored path, then skip that many.
                let skip = subtree_key_size(child_key);
                // The Star in the query consumes 1 position (the Star itself).
                // The child's subtree in the tree consumes `skip` positions
                // from its path. We advance past the Star in the query (1)
                // and must recursively skip the child's subtree.
                self.skip_and_search(
                    child_idx,
                    path,
                    path_pos + 1, // past the Star in the query
                    skip - 1,     // remaining positions to skip in the tree
                    max_results,
                    results,
                );
                continue;
            }

            // Case 2: Tree node has Star — matches any single subtree in query.
            if child_key == DiscrimKey::Star {
                let skip = subtree_key_size(query_key);
                // Skip past the query subtree, then continue from child.
                self.search_recursive(
                    child_idx,
                    path,
                    path_pos + skip, // skip the query subtree
                    max_results,
                    results,
                );
                continue;
            }

            // Case 3: Exact match.
            if child_key == query_key {
                self.search_recursive(child_idx, path, path_pos + 1, max_results, results);
            }
        }
    }

    /// Skip `remaining` subtree positions in the tree, then continue search.
    /// This is used when the query has a Star that must match a subtree in the tree.
    fn skip_and_search(
        &self,
        node_idx: usize,
        path: &[DiscrimKey],
        path_pos: usize,
        remaining: usize,
        max_results: usize,
        results: &mut Vec<ConstantIdx>,
    ) {
        if results.len() >= max_results {
            return;
        }
        if remaining == 0 {
            // Done skipping — continue normal search from this node.
            self.search_recursive(node_idx, path, path_pos, max_results, results);
            return;
        }
        // We must descend through `remaining` more key positions in the tree.
        for &child_idx in &self.nodes[node_idx].children {
            if results.len() >= max_results {
                return;
            }
            let child_key = self.nodes[child_idx].key;
            let child_subtree = subtree_key_size(child_key);
            if child_subtree <= remaining {
                self.skip_and_search(
                    child_idx,
                    path,
                    path_pos,
                    remaining - child_subtree,
                    max_results,
                    results,
                );
            }
        }
    }
}

impl Default for DiscrimTree {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics about a discrimination tree's structure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiscrimStats {
    /// Total number of nodes (including root sentinel).
    pub node_count: usize,
    /// Number of nodes that contain at least one leaf entry.
    pub leaf_count: usize,
    /// Maximum depth from root to any node.
    pub max_depth: usize,
    /// Sum of all depths (for computing average).
    pub depth_sum: usize,
    /// Total number of leaf entries across all nodes.
    pub total_entries: usize,
}

impl DiscrimStats {
    /// Average depth of nodes in the tree (0.0 for empty trees).
    #[must_use]
    pub fn avg_depth(&self) -> f64 {
        if self.node_count == 0 {
            0.0
        } else {
            self.depth_sum as f64 / self.node_count as f64
        }
    }
}

/// Flatten a type expression into a sequence of `DiscrimKey` values.
///
/// Traversal is left-to-right depth-first:
/// - `App(fn, arg)` -> `[App, ...flatten(fn), ...flatten(arg)]`
/// - `Pi(_, ty, body)` -> `[Pi, ...flatten(ty), ...flatten(body)]`
/// - `Lam(_, ty, body)` -> `[Lam, ...flatten(ty), ...flatten(body)]`
/// - `Const(name_idx, _)` -> `[Const(name_idx)]`
/// - `BVar(idx)` -> `[BVar(idx)]`
/// - `Sort(_)` -> `[Sort]`
/// - Everything else -> `[Star]` (treated as opaque)
pub(crate) fn flatten_expr(exprs: &[FlatExpr], root: ExprIdx) -> Vec<DiscrimKey> {
    let mut path = Vec::new();
    flatten_recursive(exprs, root, &mut path);
    path
}

fn flatten_recursive(exprs: &[FlatExpr], idx: ExprIdx, path: &mut Vec<DiscrimKey>) {
    let expr_idx = idx as usize;
    if expr_idx >= exprs.len() {
        path.push(DiscrimKey::Star);
        return;
    }
    let expr = &exprs[expr_idx];
    match expr.tag() {
        Ok(FlatTag::App) => {
            let fn_idx = expr.read_u32(0).unwrap_or(0);
            let arg_idx = expr.read_u32(4).unwrap_or(0);
            path.push(DiscrimKey::App);
            flatten_recursive(exprs, fn_idx, path);
            flatten_recursive(exprs, arg_idx, path);
        }
        Ok(FlatTag::Pi) => {
            // data[0] = binder_info, data[1..5] = ty_idx, data[5..9] = body_idx
            let ty_idx =
                u32::from_le_bytes([expr.data[1], expr.data[2], expr.data[3], expr.data[4]]);
            let body_idx =
                u32::from_le_bytes([expr.data[5], expr.data[6], expr.data[7], expr.data[8]]);
            path.push(DiscrimKey::Pi);
            flatten_recursive(exprs, ty_idx, path);
            flatten_recursive(exprs, body_idx, path);
        }
        Ok(FlatTag::Lam) => {
            let ty_idx =
                u32::from_le_bytes([expr.data[1], expr.data[2], expr.data[3], expr.data[4]]);
            let body_idx =
                u32::from_le_bytes([expr.data[5], expr.data[6], expr.data[7], expr.data[8]]);
            path.push(DiscrimKey::Lam);
            flatten_recursive(exprs, ty_idx, path);
            flatten_recursive(exprs, body_idx, path);
        }
        Ok(FlatTag::Const) => {
            let name_idx = expr.read_u32(0).unwrap_or(0);
            path.push(DiscrimKey::Const(name_idx));
        }
        Ok(FlatTag::BVar) => {
            let bvar_idx = expr.read_u32(0).unwrap_or(0);
            path.push(DiscrimKey::BVar(bvar_idx));
        }
        Ok(FlatTag::Sort) => {
            path.push(DiscrimKey::Sort);
        }
        _ => {
            // Let, LitNat, LitStr, Proj, FVar, or unknown — treat as opaque.
            path.push(DiscrimKey::Star);
        }
    }
}

/// The number of `DiscrimKey` positions a key occupies in a flattened path.
///
/// Leaf keys (Const, BVar, Sort, Star) occupy exactly 1 position.
/// Branch keys (App, Pi, Lam) occupy 1 + subtree sizes of their children.
/// Since we don't know the children at this point (we're looking at a single key),
/// branch keys return 1 here and the caller must account for children separately
/// via recursive descent.
///
/// For the skip logic during wildcard matching, a Star in the query must match
/// exactly one "subtree" in the tree. A subtree rooted at a leaf key is 1 node.
/// A subtree rooted at App/Pi/Lam is 1 node + 2 child subtrees. But since we
/// walk the tree node by node, we track the remaining count of child subtrees.
fn subtree_key_size(key: DiscrimKey) -> usize {
    match key {
        // Branch nodes: the key itself (1) + we need to skip 2 child subtrees.
        // Return 1 here; the caller handles the 2 children via recursive skip.
        DiscrimKey::App | DiscrimKey::Pi | DiscrimKey::Lam => 1,
        // Leaf nodes: exactly 1 position.
        DiscrimKey::Const(_) | DiscrimKey::BVar(_) | DiscrimKey::Sort | DiscrimKey::Star => 1,
    }
}

/// Parse a simple type query string into a sequence of `DiscrimKey` values.
///
/// The query language is a simplified arrow-type notation:
/// - `?` becomes `Star` (wildcard, matches any single subtree)
/// - `Name` becomes `Const(hash)` where hash is a simple FNV-1a-style hash
/// - `A → B` (or `A -> B`) becomes `[Pi, ...A, ...B]`
///
/// Example: `"? → ? → Nat"` becomes `[Pi, Star, Pi, Star, Const(hash_of_Nat)]`.
pub fn fingerprint_for_search(query_str: &str) -> Vec<DiscrimKey> {
    // Split on arrow operators, handling both `→` and `->`.
    let normalized = query_str.replace('→', "->");
    let parts: Vec<&str> = normalized.split("->").map(|s| s.trim()).collect();

    if parts.is_empty() {
        return Vec::new();
    }

    // Build right-associative Pi chain: A -> B -> C = Pi(A, Pi(B, C))
    fn token_to_key(token: &str) -> DiscrimKey {
        if token == "?" || token == "_" || token == "*" {
            DiscrimKey::Star
        } else {
            // Simple FNV-1a-like hash to u32 for the constant name.
            let hash = simple_name_hash(token);
            DiscrimKey::Const(hash)
        }
    }

    if parts.len() == 1 {
        return vec![token_to_key(parts[0])];
    }

    // Right-to-left: wrap in Pi nodes.
    let mut result = Vec::new();
    fn build_pi(parts: &[&str], result: &mut Vec<DiscrimKey>) {
        if parts.len() == 1 {
            if parts[0] == "?" || parts[0] == "_" || parts[0] == "*" {
                result.push(DiscrimKey::Star);
            } else {
                result.push(DiscrimKey::Const(simple_name_hash(parts[0])));
            }
            return;
        }
        result.push(DiscrimKey::Pi);
        // Domain
        let domain = parts[0];
        if domain == "?" || domain == "_" || domain == "*" {
            result.push(DiscrimKey::Star);
        } else {
            result.push(DiscrimKey::Const(simple_name_hash(domain)));
        }
        // Codomain (recursive)
        build_pi(&parts[1..], result);
    }

    build_pi(&parts, &mut result);
    result
}

/// Simple deterministic hash for constant names used in fingerprint search.
/// Uses FNV-1a to produce a u32 from a string.
pub(crate) fn simple_name_hash(name: &str) -> u32 {
    let mut hash: u32 = 0x811c_9dc5;
    for byte in name.as_bytes() {
        hash ^= *byte as u32;
        hash = hash.wrapping_mul(0x0100_0193);
    }
    hash
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardWriter;
    use crate::types::{
        AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem,
    };
    use clean_kernel::flat::{FlatExpr, FlatLevel};

    /// Helper: build a small FlatExpr arena with some named constants and Pi types.
    ///
    /// We create:
    ///   expr 0: Const("Nat", name_idx=0)
    ///   expr 1: Const("Bool", name_idx=1)
    ///   expr 2: BVar(0) — represents return in Pi body
    ///   expr 3: Pi(Nat, Nat) — type `Nat -> Nat`
    ///   expr 4: Pi(Nat, Bool) — type `Nat -> Bool`
    ///   expr 5: Pi(Bool, Bool) — type `Bool -> Bool`
    fn build_test_arena() -> (Vec<FlatExpr>, Vec<String>) {
        let mut exprs = Vec::new();
        let strings = vec!["Nat".to_string(), "Bool".to_string()];

        // 0: Const("Nat") — name_idx=0
        exprs.push(FlatExpr::const_ref(0, u32::MAX));
        // 1: Const("Bool") — name_idx=1
        exprs.push(FlatExpr::const_ref(1, u32::MAX));
        // 2: Const("Nat") again for Pi body
        exprs.push(FlatExpr::const_ref(0, u32::MAX));
        // 3: Pi(ty=0 (Nat), body=2 (Nat)) — Nat -> Nat
        exprs.push(FlatExpr::pi(0, 0, 2));
        // 4: Const("Bool") for Pi body
        exprs.push(FlatExpr::const_ref(1, u32::MAX));
        // 5: Pi(ty=0 (Nat), body=4 (Bool)) — Nat -> Bool
        exprs.push(FlatExpr::pi(0, 0, 4));
        // 6: Const("Bool") for Pi body
        exprs.push(FlatExpr::const_ref(1, u32::MAX));
        // 7: Pi(ty=1 (Bool), body=6 (Bool)) — Bool -> Bool
        exprs.push(FlatExpr::pi(0, 1, 6));

        (exprs, strings)
    }

    #[test]
    fn test_flatten_const() {
        let exprs = vec![FlatExpr::const_ref(42, u32::MAX)];
        let path = flatten_expr(&exprs, 0);
        assert_eq!(path, vec![DiscrimKey::Const(42)]);
    }

    #[test]
    fn test_flatten_pi() {
        let (exprs, _) = build_test_arena();
        // expr 3: Pi(ty=0 (Nat), body=2 (Nat))
        let path = flatten_expr(&exprs, 3);
        assert_eq!(
            path,
            vec![DiscrimKey::Pi, DiscrimKey::Const(0), DiscrimKey::Const(0)]
        );
    }

    #[test]
    fn test_flatten_app() {
        let exprs = vec![
            FlatExpr::const_ref(0, u32::MAX), // 0: Const(0)
            FlatExpr::const_ref(1, u32::MAX), // 1: Const(1)
            FlatExpr::app(0, 1),              // 2: App(0, 1)
        ];

        let path = flatten_expr(&exprs, 2);
        assert_eq!(
            path,
            vec![DiscrimKey::App, DiscrimKey::Const(0), DiscrimKey::Const(1)]
        );
    }

    #[test]
    fn test_insert_and_exact_search() {
        let (exprs, _) = build_test_arena();
        let mut tree = DiscrimTree::new();

        // Insert three constants with types Nat->Nat, Nat->Bool, Bool->Bool
        tree.insert(&exprs, 3, 0); // Nat -> Nat
        tree.insert(&exprs, 5, 1); // Nat -> Bool
        tree.insert(&exprs, 7, 2); // Bool -> Bool

        assert!(!tree.is_empty());
        assert!(tree.len() > 1);

        // Exact search for Nat -> Nat: should find constant 0
        let results = tree.search(&exprs, 3, 10);
        assert_eq!(results, vec![0]);

        // Exact search for Nat -> Bool: should find constant 1
        let results = tree.search(&exprs, 5, 10);
        assert_eq!(results, vec![1]);

        // Exact search for Bool -> Bool: should find constant 2
        let results = tree.search(&exprs, 7, 10);
        assert_eq!(results, vec![2]);
    }

    #[test]
    fn test_search_nat_arrow_wildcard() {
        let (exprs, _) = build_test_arena();
        let mut tree = DiscrimTree::new();

        tree.insert(&exprs, 3, 0); // Nat -> Nat
        tree.insert(&exprs, 5, 1); // Nat -> Bool
        tree.insert(&exprs, 7, 2); // Bool -> Bool

        // Build query for `Nat -> _` (Pi with ty=Nat, body=Star).
        // We need a FlatExpr arena for the query.
        let query_exprs = vec![
            // 0: Const("Nat") — name_idx=0
            FlatExpr::const_ref(0, u32::MAX),
            // 1: We need a "wildcard" expression. Use LitNat(0) which flattens to Star.
            FlatExpr::lit_nat(0),
            // 2: Pi(ty=0 (Nat), body=1 (Star))
            FlatExpr::pi(0, 0, 1),
        ];

        let mut results = tree.search(&query_exprs, 2, 10);
        results.sort();
        // Should find constants 0 (Nat->Nat) and 1 (Nat->Bool)
        assert_eq!(results, vec![0, 1]);
    }

    #[test]
    fn test_search_wildcard_arrow_bool() {
        let (exprs, _) = build_test_arena();
        let mut tree = DiscrimTree::new();

        tree.insert(&exprs, 3, 0); // Nat -> Nat
        tree.insert(&exprs, 5, 1); // Nat -> Bool
        tree.insert(&exprs, 7, 2); // Bool -> Bool

        // Build query for `_ -> Bool` (Pi with ty=Star, body=Bool).
        let query_exprs = vec![
            // 0: wildcard (LitNat flattens to Star)
            FlatExpr::lit_nat(0),
            // 1: Const("Bool") — name_idx=1
            FlatExpr::const_ref(1, u32::MAX),
            // 2: Pi(ty=0 (Star), body=1 (Bool))
            FlatExpr::pi(0, 0, 1),
        ];

        let mut results = tree.search(&query_exprs, 2, 10);
        results.sort();
        // Should find constants 1 (Nat->Bool) and 2 (Bool->Bool)
        assert_eq!(results, vec![1, 2]);
    }

    #[test]
    fn test_build_from_shard() {
        let mut writer = ShardWriter::new();

        // Strings
        let nat_name = writer.add_string("Nat");
        let bool_name = writer.add_string("Bool");
        let c0_name = writer.add_string("nat_to_nat");
        let c1_name = writer.add_string("nat_to_bool");
        let c2_name = writer.add_string("bool_to_bool");

        // Levels
        let l0 = writer.add_level(FlatLevel::zero());

        // Expressions: build arena like build_test_arena
        // 0: Const("Nat") — name_idx=0
        let e_nat = writer.add_expr(FlatExpr::const_ref(nat_name, u32::MAX));
        // 1: Const("Bool") — name_idx=1
        let _e_bool = writer.add_expr(FlatExpr::const_ref(bool_name, u32::MAX));
        // 2: Const("Nat") for Pi body
        let e_nat2 = writer.add_expr(FlatExpr::const_ref(nat_name, u32::MAX));
        // 3: Pi(Nat, Nat) — Nat -> Nat
        let pi_nat_nat = writer.add_expr(FlatExpr::pi(0, e_nat, e_nat2));
        // 4: Const("Bool") for Pi body
        let e_bool2 = writer.add_expr(FlatExpr::const_ref(bool_name, u32::MAX));
        // 5: Pi(Nat, Bool) — Nat -> Bool
        let pi_nat_bool = writer.add_expr(FlatExpr::pi(0, e_nat, e_bool2));
        // 6: Const("Bool") for Pi body
        let e_bool3 = writer.add_expr(FlatExpr::const_ref(bool_name, u32::MAX));
        // 7: Pi(Bool, Bool) — Bool -> Bool
        let pi_bool_bool = writer.add_expr(FlatExpr::pi(0, _e_bool, e_bool3));

        // Sort for value_idx
        let sort_e = writer.add_expr(FlatExpr::sort(l0));

        // Constants
        let mk_header = |name: u32, ty: u32| MathverseConstantHeader {
            name_idx: name,
            type_idx: ty,
            value_idx: sort_e,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        writer.add_constant(mk_header(c0_name, pi_nat_nat));
        writer.add_constant(mk_header(c1_name, pi_nat_bool));
        writer.add_constant(mk_header(c2_name, pi_bool_bool));

        // Write and read back
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        // Build the tree
        let tree = DiscrimTree::build_from_shard(&reader);
        assert!(!tree.is_empty());

        // Search for Nat -> _ using the reader's expression arena.
        // Build a query in a separate mini-arena.
        let query_exprs = vec![
            FlatExpr::const_ref(nat_name, u32::MAX), // 0: Nat
            FlatExpr::lit_nat(0),                    // 1: Star (wildcard)
            FlatExpr::pi(0, 0, 1),                   // 2: Pi(Nat, Star)
        ];

        let mut results = tree.search(&query_exprs, 2, 10);
        results.sort();
        // Constants 0 (nat_to_nat) and 1 (nat_to_bool) have types Nat->Nat and Nat->Bool
        assert_eq!(results, vec![0, 1]);

        // Search for _ -> Bool
        let query_exprs2 = vec![
            FlatExpr::lit_nat(0),                     // 0: Star
            FlatExpr::const_ref(bool_name, u32::MAX), // 1: Bool
            FlatExpr::pi(0, 0, 1),                    // 2: Pi(Star, Bool)
        ];

        let mut results2 = tree.search(&query_exprs2, 2, 10);
        results2.sort();
        // Constants 1 (nat_to_bool) and 2 (bool_to_bool)
        assert_eq!(results2, vec![1, 2]);
    }

    #[test]
    fn test_empty_tree() {
        let tree = DiscrimTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 1); // just root

        let exprs = vec![FlatExpr::const_ref(0, u32::MAX)];
        let results = tree.search(&exprs, 0, 10);
        assert!(results.is_empty());
    }

    #[test]
    fn test_max_results_limit() {
        let (exprs, _) = build_test_arena();
        let mut tree = DiscrimTree::new();

        // Insert same type for many constants
        for i in 0..100 {
            tree.insert(&exprs, 3, i); // Nat -> Nat
        }

        let results = tree.search(&exprs, 3, 5);
        assert_eq!(results.len(), 5);
    }

    #[test]
    fn test_sort_expression() {
        let exprs = vec![FlatExpr::sort(0)];
        let path = flatten_expr(&exprs, 0);
        assert_eq!(path, vec![DiscrimKey::Sort]);
    }

    #[test]
    fn test_bvar_expression() {
        let exprs = vec![FlatExpr::bvar(7)];
        let path = flatten_expr(&exprs, 0);
        assert_eq!(path, vec![DiscrimKey::BVar(7)]);
    }

    #[test]
    fn test_let_flattens_to_star() {
        let exprs = vec![FlatExpr::let_expr(0, 0, 0)];
        let path = flatten_expr(&exprs, 0);
        assert_eq!(path, vec![DiscrimKey::Star]);
    }

    #[test]
    fn test_lam_flatten() {
        let exprs = vec![
            FlatExpr::const_ref(0, u32::MAX), // 0: Const(0)
            FlatExpr::bvar(0),                // 1: BVar(0)
            FlatExpr::lam(0, 0, 1),           // 2: Lam(ty=0 (Const(0)), body=1 (BVar(0)))
        ];

        let path = flatten_expr(&exprs, 2);
        assert_eq!(
            path,
            vec![DiscrimKey::Lam, DiscrimKey::Const(0), DiscrimKey::BVar(0)]
        );
    }

    #[test]
    fn test_nested_pi() {
        // Pi(Nat, Pi(Bool, Nat)) — Nat -> Bool -> Nat
        let exprs = vec![
            FlatExpr::const_ref(0, u32::MAX), // 0: Const("Nat") name_idx=0
            FlatExpr::const_ref(1, u32::MAX), // 1: Const("Bool") name_idx=1
            FlatExpr::const_ref(0, u32::MAX), // 2: Const("Nat") name_idx=0 (for inner Pi body)
            FlatExpr::pi(0, 1, 2),            // 3: Pi(Bool, Nat) — inner
            FlatExpr::pi(0, 0, 3),            // 4: Pi(Nat, Pi(Bool, Nat)) — outer
        ];

        let path = flatten_expr(&exprs, 4);
        assert_eq!(
            path,
            vec![
                DiscrimKey::Pi,
                DiscrimKey::Const(0), // Nat
                DiscrimKey::Pi,       // inner Pi
                DiscrimKey::Const(1), // Bool
                DiscrimKey::Const(0), // Nat
            ]
        );
    }

    #[test]
    fn test_out_of_bounds_expr_idx() {
        let exprs = vec![FlatExpr::const_ref(0, u32::MAX)];
        // Index 99 is out of bounds — should flatten to Star.
        let path = flatten_expr(&exprs, 99);
        assert_eq!(path, vec![DiscrimKey::Star]);
    }

    // -- search_generalized --

    #[test]
    fn test_search_generalized_exact_match_score_1() {
        let (exprs, _) = build_test_arena();
        let mut tree = DiscrimTree::new();
        tree.insert(&exprs, 3, 0); // Nat -> Nat
        tree.insert(&exprs, 5, 1); // Nat -> Bool

        // Exact query for Nat -> Nat: path = [Pi, Const(0), Const(0)]
        let path = flatten_expr(&exprs, 3);
        let results = tree.search_generalized(&path, 10);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 0);
        assert!((results[0].1 - 1.0).abs() < f32::EPSILON);
    }

    #[test]
    fn test_search_generalized_wildcard_reduces_score() {
        let (exprs, _) = build_test_arena();
        let mut tree = DiscrimTree::new();
        tree.insert(&exprs, 3, 0); // Nat -> Nat

        // Query with wildcard: [Pi, Star, Const(0)] = ? -> Nat
        let query = vec![DiscrimKey::Pi, DiscrimKey::Star, DiscrimKey::Const(0)];
        let results = tree.search_generalized(&query, 10);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 0);
        // 2 out of 3 keys are exact, so score = 2/3
        assert!((results[0].1 - 2.0 / 3.0).abs() < 0.01);
    }

    #[test]
    fn test_search_generalized_max_results() {
        let (exprs, _) = build_test_arena();
        let mut tree = DiscrimTree::new();
        for i in 0..50 {
            tree.insert(&exprs, 3, i); // Nat -> Nat
        }
        let path = flatten_expr(&exprs, 3);
        let results = tree.search_generalized(&path, 5);
        assert_eq!(results.len(), 5);
    }

    // -- statistics --

    #[test]
    fn test_statistics_empty_tree() {
        let tree = DiscrimTree::new();
        let stats = tree.statistics();
        assert_eq!(stats.node_count, 1); // root
        assert_eq!(stats.leaf_count, 0);
        assert_eq!(stats.max_depth, 0);
        assert_eq!(stats.total_entries, 0);
    }

    #[test]
    fn test_statistics_populated_tree() {
        let (exprs, _) = build_test_arena();
        let mut tree = DiscrimTree::new();
        tree.insert(&exprs, 3, 0); // Nat -> Nat: path [Pi, Const(0), Const(0)]
        tree.insert(&exprs, 5, 1); // Nat -> Bool: path [Pi, Const(0), Const(1)]
        tree.insert(&exprs, 7, 2); // Bool -> Bool: path [Pi, Const(1), Const(1)]

        let stats = tree.statistics();
        assert!(stats.node_count > 1);
        assert_eq!(stats.total_entries, 3);
        assert!(stats.leaf_count >= 2); // at least 2 distinct leaf nodes
        assert!(stats.max_depth >= 3); // Pi -> Const -> Const
    }

    #[test]
    fn test_statistics_avg_depth() {
        let stats = DiscrimStats {
            node_count: 4,
            leaf_count: 2,
            max_depth: 3,
            depth_sum: 6, // e.g. depths 0, 1, 2, 3
            total_entries: 2,
        };
        assert!((stats.avg_depth() - 1.5).abs() < f64::EPSILON);
    }

    // -- merge --

    #[test]
    fn test_merge_two_trees() {
        let (exprs, _) = build_test_arena();

        let mut tree_a = DiscrimTree::new();
        tree_a.insert(&exprs, 3, 0); // Nat -> Nat

        let mut tree_b = DiscrimTree::new();
        tree_b.insert(&exprs, 5, 0); // Nat -> Bool (idx 0 in shard B)
        tree_b.insert(&exprs, 7, 1); // Bool -> Bool (idx 1 in shard B)

        // Merge B into A with offset 100.
        tree_a.merge(&tree_b, 100);

        // Search Nat -> Nat: should still find original constant 0.
        let path_nn = flatten_expr(&exprs, 3);
        let results = tree_a.search_generalized(&path_nn, 10);
        assert!(results.iter().any(|(idx, _)| *idx == 0));

        // Search Nat -> Bool: should find constant 100 (0 + offset).
        let path_nb = flatten_expr(&exprs, 5);
        let results = tree_a.search_generalized(&path_nb, 10);
        assert!(results.iter().any(|(idx, _)| *idx == 100));

        // Search Bool -> Bool: should find constant 101 (1 + offset).
        let path_bb = flatten_expr(&exprs, 7);
        let results = tree_a.search_generalized(&path_bb, 10);
        assert!(results.iter().any(|(idx, _)| *idx == 101));
    }

    #[test]
    fn test_merge_empty_into_populated() {
        let (exprs, _) = build_test_arena();
        let mut tree_a = DiscrimTree::new();
        tree_a.insert(&exprs, 3, 0);

        let tree_b = DiscrimTree::new();
        let stats_before = tree_a.statistics();
        tree_a.merge(&tree_b, 100);
        let stats_after = tree_a.statistics();

        assert_eq!(stats_before.total_entries, stats_after.total_entries);
    }

    // -- fingerprint_for_search --

    #[test]
    fn test_fingerprint_single_name() {
        let fp = fingerprint_for_search("Nat");
        assert_eq!(fp.len(), 1);
        assert!(matches!(fp[0], DiscrimKey::Const(_)));
    }

    #[test]
    fn test_fingerprint_wildcard() {
        let fp = fingerprint_for_search("?");
        assert_eq!(fp, vec![DiscrimKey::Star]);
    }

    #[test]
    fn test_fingerprint_simple_arrow() {
        let fp = fingerprint_for_search("Nat -> Bool");
        assert_eq!(fp.len(), 3);
        assert_eq!(fp[0], DiscrimKey::Pi);
        assert!(matches!(fp[1], DiscrimKey::Const(_))); // Nat
        assert!(matches!(fp[2], DiscrimKey::Const(_))); // Bool
                                                        // Nat and Bool should hash differently.
        assert_ne!(fp[1], fp[2]);
    }

    #[test]
    fn test_fingerprint_unicode_arrow() {
        let fp = fingerprint_for_search("? → ? → Nat");
        // ? -> (? -> Nat) = Pi(Star, Pi(Star, Const(nat)))
        assert_eq!(fp.len(), 5);
        assert_eq!(fp[0], DiscrimKey::Pi);
        assert_eq!(fp[1], DiscrimKey::Star);
        assert_eq!(fp[2], DiscrimKey::Pi);
        assert_eq!(fp[3], DiscrimKey::Star);
        assert!(matches!(fp[4], DiscrimKey::Const(_)));
    }

    #[test]
    fn test_fingerprint_deterministic() {
        let fp1 = fingerprint_for_search("Nat -> Bool -> Nat");
        let fp2 = fingerprint_for_search("Nat -> Bool -> Nat");
        assert_eq!(fp1, fp2);
    }
}
