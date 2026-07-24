// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Build a Tier-2 lineage graph from a `.mathverse` corpus.
//!
//! This is the "populate the lineage graph from the corpus" step: it turns
//! [`clean_cake::lineage::LineageGraph`] from a tested primitive into a structure that
//! holds **real corpus edges**. The nodes are statement identities (canonical
//! statement-hashes); the edges are [`EdgeKind::RewriteCanonical`] links between two
//! *distinct* statement-hashes that fold to the **same env-free Tier-1.5 rewrite-canonical
//! digest** ([`clean_cake::identity::structural_rewrite_digest`]) — i.e. "the same object
//! in a different form" (commutative-operand reorderings the exact statement-hash misses).
//!
//! Trust discipline (Tier 2 is evidence, NOT proof): every edge is `RewriteCanonical`
//! ([`clean_cake::lineage::Trust::Deterministic`]), so `same_class` clusters them for
//! search-space collapse but `soundly_equivalent` never crosses them — confirming true
//! sameness still needs `same_object` (defeq) or a kernel-checked `proved-iff`. This
//! builder records *candidate* equivalences only; it does not, and cannot, mint proofs.
//!
//! The headline number is the **search-space collapse**: how many distinct statements
//! commutativity merges *beyond* exact statement-hash dedup (`distinct_statements −
//! distinct_forms`).

use std::collections::{HashMap, HashSet};
use std::path::Path;

use clean_cake::lineage::{EdgeKind, LineageGraph};

use super::intake::collect_shard_paths;
use super::record::expr_canonical_digest;
use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardReader;
use crate::shard_reconstruct::reconstruct_expr_table_prefix;

/// Summary of a corpus lineage build.
#[derive(Debug, Clone)]
pub struct LineageStats {
    /// Shards scanned (sorted-path order).
    pub shards: usize,
    /// Constant headers visited.
    pub constants: u64,
    /// Distinct canonical statement-hashes (the exact-identity statement count).
    pub distinct_statements: usize,
    /// Distinct Tier-1.5 rewrite-canonical forms (after commutative folding). Always
    /// `<= distinct_statements`.
    pub distinct_forms: usize,
    /// `distinct_statements - distinct_forms`: statements merged by commutativity *beyond*
    /// exact-hash dedup — the search-space collapse this lineage buys.
    pub collapsed_by_commutativity: usize,
    /// `RewriteCanonical` edges recorded (one per distinct statement folded into an
    /// existing form's representative).
    pub rewrite_edges: usize,
    /// Nodes in the graph (statement-hashes that participate in at least one edge).
    pub lineage_nodes: usize,
    /// Connected components in the graph (= multi-member equivalence classes, since a
    /// node only exists by being on an edge).
    pub lineage_classes: usize,
}

/// Scan a `.mathverse` shard file or directory tree and build the corpus lineage graph
/// of rewrite-canonical equivalence classes.
///
/// # Errors
///
/// I/O failures or malformed shards.
pub fn build_corpus_lineage(input: &Path) -> MathverseResult<(LineageGraph, LineageStats)> {
    let shard_paths = collect_shard_paths(input)?;
    let mut graph = LineageGraph::new();
    // structural_rewrite_digest -> representative statement-hash (first seen for that form).
    let mut form_rep: HashMap<String, String> = HashMap::new();
    let mut distinct_statements: HashSet<String> = HashSet::new();
    let mut constants: u64 = 0;
    let mut rewrite_edges: usize = 0;

    for shard_path in &shard_paths {
        let bytes = std::fs::read(shard_path).map_err(MathverseError::Io)?;
        let reader = ShardReader::from_bytes(&bytes)?;
        let table = reconstruct_expr_table_prefix(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
        );
        for header in &reader.constants {
            constants += 1;
            let Some(type_) = table.get(header.type_idx as usize) else {
                continue;
            };
            let Ok(stmt) = expr_canonical_digest(type_) else {
                continue;
            };
            let sem = clean_cake::identity::structural_rewrite_digest(type_);
            distinct_statements.insert(stmt.clone());
            match form_rep.get(&sem) {
                None => {
                    form_rep.insert(sem, stmt);
                }
                Some(rep) if *rep != stmt => {
                    // A DISTINCT statement that folds to an existing form: an edge linking
                    // the two statement identities, justified by the shared Tier-1.5 digest.
                    graph.add_edge(rep, &stmt, EdgeKind::RewriteCanonical, sem);
                    rewrite_edges += 1;
                }
                Some(_) => {} // same statement-hash, same form: nothing new.
            }
        }
    }

    let distinct_statements = distinct_statements.len();
    let distinct_forms = form_rep.len();
    let lineage_nodes = graph.len().0;
    let lineage_classes = graph.class_count();
    let stats = LineageStats {
        shards: shard_paths.len(),
        constants,
        distinct_statements,
        distinct_forms,
        collapsed_by_commutativity: distinct_statements.saturating_sub(distinct_forms),
        rewrite_edges,
        lineage_nodes,
        lineage_classes,
    };
    Ok((graph, stats))
}

#[cfg(test)]
#[path = "lineage_build_tests.rs"]
mod tests;
