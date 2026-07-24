// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Coq adapter for the blocking-weight targeter** — ranks the Coq lane's
//! REJECTED constants by how much downstream cascade each one gates, so a KV
//! round attacks the top *gatekeepers* instead of chasing failure families by
//! name in the taxonomy (`designs/2026-07-05-coq-kv-failure-taxonomy.md`).
//!
//! # Inputs (Coq lane OUTPUT formats only — no driver code touched)
//!
//! - the per-library `.mathverse` shards a `coq-import` run wrote to
//!   `<out>/<lib>/coq_<lib>.mathverse` — every constant's fully-qualified name
//!   and the names it references through its type/value trees (the reject
//!   subgraph's nodes + edges); and
//! - the `<out>/<lib>/kernel-verified.json`
//!   [`KernelVerifiedManifest`](crate::verify::kernel_verified_manifest::KernelVerifiedManifest)
//!   sidecar — its `kernel_verified_names` are the ACCEPTED set; every other
//!   constant in the shards is REJECTED.
//!
//! Optionally, a `name -> reason` map (e.g. joined from the `coq-import --json`
//! report's `axiom_fallback_names_full` / `failed_names_full`, emitted under
//! `COQ_IMPORT_FULL_REASONS`) annotates each ranked gatekeeper with its kernel
//! rejection reason.
//!
//! # Model
//!
//! Coq constants are keyed by fully-qualified `String` name (unlike Isabelle's
//! `i64` serials), and that name order is NOT a topological order, so the adapter
//! computes one with [`topo_order`] before delegating the frontier arithmetic to
//! the shared [`frontier_weights`] core — byte-identical math to the Isabelle
//! lane, just over string ids.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::replay_infra::targets::{frontier_weights, topo_order};
use crate::shard::ShardReader;
use crate::shard_verify::discover_mathverse_files;
use crate::verify::kernel_verified_manifest::KernelVerifiedManifest;

/// Errors from Coq blocking-weight targeting.
#[derive(Debug, thiserror::Error)]
pub enum CoqTargetsError {
    /// Filesystem / shard-decode failure.
    #[error("coq-targets I/O on {path}: {source}")]
    Io {
        /// Path involved.
        path: PathBuf,
        /// Underlying error.
        source: std::io::Error,
    },
    /// A shard failed to decode.
    #[error("coq-targets shard decode {path}: {source}")]
    Shard {
        /// Shard path.
        path: PathBuf,
        /// Underlying decode error.
        source: crate::error::MathverseError,
    },
    /// The kernel-verified manifest failed to load.
    #[error("coq-targets manifest {path}: {source}")]
    Manifest {
        /// Manifest path.
        path: PathBuf,
        /// Underlying error.
        source: crate::error::MathverseError,
    },
}

/// The corpus dependency graph over a set of Coq `.mathverse` shards: every
/// constant name present, and the in-corpus names each references.
#[derive(Debug, Default)]
pub struct CoqCorpusGraph {
    /// Every constant name present across the shards.
    pub present: HashSet<String>,
    /// name → the in-corpus names it references through its type/value trees
    /// (deduped; only names that are themselves present are kept).
    pub deps_of: HashMap<String, Vec<String>>,
}

/// One gatekeeper row in the Coq targeting table.
#[derive(Debug, Clone)]
pub struct CoqGatekeeperRow {
    /// The primary constant's fully-qualified name.
    pub name: String,
    /// The rejection reason, joined from the optional reason map (empty absent).
    pub reason: String,
    /// Cascade weight: rejected constants whose frontier set includes this one.
    pub blocked: usize,
    /// Sole-blocked dependents (the guaranteed release when this is fixed).
    pub exclusive: usize,
}

/// The full Coq targeting result.
#[derive(Debug, Clone, Default)]
pub struct CoqTargetsReport {
    /// Constants present across the loaded shards.
    pub corpus_constants: usize,
    /// Constants present AND kernel-verified (accepted).
    pub accepted: usize,
    /// Constants present but not accepted (rejected).
    pub rejected: usize,
    /// Rejected frontier constants (all in-corpus rejected deps: none).
    pub primaries: usize,
    /// Gated cascade (`rejected - primaries`).
    pub cascade: usize,
    /// Reject edges dropped as back-edges of a dependency cycle (Coq mutual
    /// `Fixpoint`/`Inductive` blocks) — tallied, never panicking the pass.
    pub forward_edges: usize,
    /// Top gatekeepers, ranked by `(blocked desc, exclusive desc, name asc)`.
    pub rows: Vec<CoqGatekeeperRow>,
}

/// Extract one shard reader's `(name, dep_names)` rows, resolving the referenced
/// names against this shard's own string table. Mirrors
/// `ShardWriter::constant_axiom_dep_names` on the read side.
fn shard_constant_deps(reader: &ShardReader) -> Vec<(String, Vec<String>)> {
    let mut out = Vec::with_capacity(reader.constants.len());
    for c in &reader.constants {
        let Some(name) = reader.strings.get(c.name_idx as usize) else {
            continue;
        };
        if name.is_empty() {
            continue;
        }
        let mut dep_idx: Vec<u32> =
            crate::lean4::olean::alpha::extract_deps(&reader.exprs, c.type_idx);
        if c.has_value() {
            dep_idx.extend(crate::lean4::olean::alpha::extract_deps(
                &reader.exprs,
                c.value_idx,
            ));
        }
        dep_idx.sort_unstable();
        dep_idx.dedup();
        let dep_names: Vec<String> = dep_idx
            .iter()
            .filter_map(|&ni| reader.strings.get(ni as usize).cloned())
            .filter(|n| !n.is_empty())
            .collect();
        out.push((name.clone(), dep_names));
    }
    out
}

/// Scan every `.mathverse` shard under `shard_dir` into a [`CoqCorpusGraph`].
/// Cross-shard references resolve by name (each constant is defined in exactly
/// one shard, but referenced from many); a dep name kept in `deps_of` is
/// filtered to those PRESENT somewhere in the loaded shards.
///
/// # Errors
/// [`CoqTargetsError`] on read/decode failure.
pub fn build_graph_from_shard_dir(shard_dir: &Path) -> Result<CoqCorpusGraph, CoqTargetsError> {
    let files = discover_mathverse_files(shard_dir);
    // First pass: raw deps + presence.
    let mut raw: HashMap<String, Vec<String>> = HashMap::new();
    let mut present: HashSet<String> = HashSet::new();
    for path in files {
        let reader = ShardReader::from_file(&path).map_err(|source| CoqTargetsError::Shard {
            path: path.clone(),
            source,
        })?;
        for (name, deps) in shard_constant_deps(&reader) {
            present.insert(name.clone());
            // A name can appear in multiple shards (rare); keep the first
            // non-empty dep set, union additional ones deterministically.
            let entry = raw.entry(name).or_default();
            for d in deps {
                if !entry.contains(&d) {
                    entry.push(d);
                }
            }
        }
    }
    // Second pass: narrow each dep list to in-corpus names (a self-reference or
    // a reference to an out-of-corpus prelude constant does not gate).
    let mut deps_of: HashMap<String, Vec<String>> = HashMap::with_capacity(raw.len());
    for (name, deps) in raw {
        let kept: Vec<String> = deps
            .into_iter()
            .filter(|d| d != &name && present.contains(d))
            .collect();
        if !kept.is_empty() {
            deps_of.insert(name, kept);
        }
    }
    Ok(CoqCorpusGraph { present, deps_of })
}

/// Load the accepted (`kernel_verified_names`) set from a Coq
/// `kernel-verified.json` manifest.
///
/// # Errors
/// [`CoqTargetsError::Manifest`] on read/parse failure.
pub fn load_accepted_names(manifest: &Path) -> Result<HashSet<String>, CoqTargetsError> {
    let m: KernelVerifiedManifest =
        KernelVerifiedManifest::from_file(manifest).map_err(|source| {
            CoqTargetsError::Manifest {
                path: manifest.to_path_buf(),
                source,
            }
        })?;
    Ok(m.kernel_verified_names.into_iter().collect())
}

/// Compute the blocking-weight targeting report over an in-memory graph +
/// accepted set. Split from I/O so it is unit-testable on constructed graphs.
/// `reasons` (optional) joins a kernel rejection reason onto each gatekeeper;
/// `top` caps the returned rows (0 = all primaries).
#[must_use]
pub fn analyze(
    graph: &CoqCorpusGraph,
    accepted: &HashSet<String>,
    reasons: Option<&HashMap<String, String>>,
    top: usize,
) -> CoqTargetsReport {
    // Rejected = present \ accepted. Sorted for deterministic tie-breaks.
    let mut rejected: Vec<String> = graph
        .present
        .iter()
        .filter(|s| !accepted.contains(*s))
        .cloned()
        .collect();
    rejected.sort();

    let empty: Vec<String> = Vec::new();
    let deps_fn = |n: &String| graph.deps_of.get(n).unwrap_or(&empty).as_slice();

    // Coq names are not topo-ordered — build a dependency order first.
    let order = topo_order(&rejected, deps_fn);
    let frontier = frontier_weights(&order, deps_fn);

    let mut rows: Vec<CoqGatekeeperRow> = frontier
        .rows
        .iter()
        .map(|r| CoqGatekeeperRow {
            name: r.id.clone(),
            reason: reasons
                .and_then(|m| m.get(&r.id))
                .cloned()
                .unwrap_or_default(),
            blocked: r.blocked,
            exclusive: r.exclusive,
        })
        .collect();
    rows.sort_by(|a, b| {
        b.blocked
            .cmp(&a.blocked)
            .then(b.exclusive.cmp(&a.exclusive))
            .then(a.name.cmp(&b.name))
    });
    if top > 0 && rows.len() > top {
        rows.truncate(top);
    }

    let corpus_constants = graph.present.len();
    CoqTargetsReport {
        corpus_constants,
        accepted: corpus_constants - frontier.rejected,
        rejected: frontier.rejected,
        primaries: frontier.primaries,
        cascade: frontier.cascade,
        forward_edges: frontier.forward_edges,
        rows,
    }
}

/// End-to-end: scan the shard dir into a graph, load the manifest's accepted
/// set, optionally join a `name -> reason` map, and rank the top gatekeepers.
///
/// # Errors
/// [`CoqTargetsError`] on I/O, shard-decode, or manifest-load failure.
pub fn compute_coq_targets(
    shard_dir: &Path,
    manifest: &Path,
    reasons: Option<&HashMap<String, String>>,
    top: usize,
) -> Result<CoqTargetsReport, CoqTargetsError> {
    let graph = build_graph_from_shard_dir(shard_dir)?;
    let accepted = load_accepted_names(manifest)?;
    Ok(analyze(&graph, &accepted, reasons, top))
}

/// Join a `name -> reason` map from a `coq-import --json` report emitted with
/// `COQ_IMPORT_FULL_REASONS=1` (so the per-library `axiom_fallback_names_full`
/// and `failed_names_full` arrays are present). Missing arrays are skipped; a
/// name present in both keeps its fallback reason.
///
/// # Errors
/// [`CoqTargetsError::Io`] on read failure. A malformed JSON body yields an
/// empty map rather than an error (the report is a diagnostic, not a gate).
pub fn reasons_from_report_json(report: &Path) -> Result<HashMap<String, String>, CoqTargetsError> {
    let text = std::fs::read_to_string(report).map_err(|source| CoqTargetsError::Io {
        path: report.to_path_buf(),
        source,
    })?;
    let mut out: HashMap<String, String> = HashMap::new();
    let Ok(root) = serde_json::from_str::<serde_json::Value>(&text) else {
        return Ok(out);
    };
    let Some(libs) = root.as_object() else {
        return Ok(out);
    };
    for lib in libs.values() {
        for key in ["failed_names_full", "axiom_fallback_names_full"] {
            if let Some(arr) = lib.get(key).and_then(|v| v.as_array()) {
                for row in arr {
                    if let Some(pair) = row.as_array() {
                        if let (Some(n), Some(r)) = (
                            pair.first().and_then(|v| v.as_str()),
                            pair.get(1).and_then(|v| v.as_str()),
                        ) {
                            out.entry(n.to_string()).or_insert_with(|| r.to_string());
                        }
                    }
                }
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A hand-built Coq-style reject graph exercises the frontier arithmetic
    /// over STRING ids (with a non-topological name order): accepted =
    /// {"Init.eq"}. Rejected: "Aa" (deps Init.eq → primary), "Zz" (dep "Aa"),
    /// "Mm" (dep "Zz"). Even though "Aa" < "Mm" < "Zz" by name, the topo order
    /// puts "Aa" before "Zz" before "Mm". Frontier: Aa→{Aa}, Zz→{Aa}, Mm→{Aa}.
    /// blocked(Aa)=3, exclusive(Aa)=3.
    #[test]
    fn test_analyze_string_chain() {
        let mut graph = CoqCorpusGraph::default();
        for s in ["Init.eq", "Aa", "Zz", "Mm"] {
            graph.present.insert(s.to_string());
        }
        graph.deps_of.insert("Aa".into(), vec!["Init.eq".into()]);
        graph.deps_of.insert("Zz".into(), vec!["Aa".into()]);
        graph.deps_of.insert("Mm".into(), vec!["Zz".into()]);
        let accepted: HashSet<String> = ["Init.eq".to_string()].into_iter().collect();
        let report = analyze(&graph, &accepted, None, 0);

        assert_eq!(report.corpus_constants, 4);
        assert_eq!(report.accepted, 1);
        assert_eq!(report.rejected, 3, "Aa, Zz, Mm rejected");
        assert_eq!(report.primaries, 1, "only Aa is a frontier primary");
        assert_eq!(report.cascade, 2, "Zz, Mm gated");
        assert_eq!(
            report.forward_edges, 0,
            "topo order eliminates forward edges"
        );

        let aa = report.rows.iter().find(|r| r.name == "Aa").expect("Aa row");
        assert_eq!(aa.blocked, 3, "Aa gates Aa, Zz, Mm");
        assert_eq!(aa.exclusive, 3, "Aa solely gates all three");
        assert_eq!(report.rows[0].name, "Aa", "top gatekeeper");
    }

    /// Two independent primaries + a shared dependent split blocked vs exclusive.
    #[test]
    fn test_analyze_shared_dependent() {
        let mut graph = CoqCorpusGraph::default();
        for s in ["acc", "P1", "P2", "Shared"] {
            graph.present.insert(s.to_string());
        }
        // P1, P2 are primaries (dep only the accepted "acc"); Shared waits on both.
        graph.deps_of.insert("P1".into(), vec!["acc".into()]);
        graph.deps_of.insert("P2".into(), vec!["acc".into()]);
        graph
            .deps_of
            .insert("Shared".into(), vec!["P1".into(), "P2".into()]);
        let accepted: HashSet<String> = ["acc".to_string()].into_iter().collect();
        let report = analyze(&graph, &accepted, None, 0);

        assert_eq!(report.primaries, 2);
        let p1 = report.rows.iter().find(|r| r.name == "P1").expect("P1");
        assert_eq!(p1.blocked, 2, "P1 gates P1 + Shared");
        assert_eq!(
            p1.exclusive, 1,
            "Shared is co-blocked, so exclusive is P1 only"
        );
    }

    /// A dependency cycle (Coq mutual Fixpoint) is tolerated: the report is
    /// produced, one back-edge tallied, no panic.
    #[test]
    fn test_analyze_cycle_tolerated() {
        let mut graph = CoqCorpusGraph::default();
        for s in ["even", "odd"] {
            graph.present.insert(s.to_string());
        }
        graph.deps_of.insert("even".into(), vec!["odd".into()]);
        graph.deps_of.insert("odd".into(), vec!["even".into()]);
        let accepted: HashSet<String> = HashSet::new();
        let report = analyze(&graph, &accepted, None, 0);
        assert_eq!(report.rejected, 2);
        assert_eq!(report.forward_edges, 1, "one cycle back-edge dropped");
    }

    /// The reason map annotates a ranked gatekeeper.
    #[test]
    fn test_analyze_reason_join() {
        let mut graph = CoqCorpusGraph::default();
        for s in ["acc", "P1"] {
            graph.present.insert(s.to_string());
        }
        graph.deps_of.insert("P1".into(), vec!["acc".into()]);
        let accepted: HashSet<String> = ["acc".to_string()].into_iter().collect();
        let reasons: HashMap<String, String> =
            [("P1".to_string(), "universe inconsistency".to_string())]
                .into_iter()
                .collect();
        let report = analyze(&graph, &accepted, Some(&reasons), 0);
        let p1 = report.rows.iter().find(|r| r.name == "P1").expect("P1");
        assert_eq!(p1.reason, "universe inconsistency");
    }

    /// Reason join from a coq-import `--json` report body.
    #[test]
    fn test_reasons_from_report_json() {
        let dir = std::env::temp_dir().join(format!("coq_targets_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let report = dir.join("report.json");
        std::fs::write(
            &report,
            r#"{
              "stdlib": {
                "failed_names_full": [["Coq.foo", "kernel reject: mismatch"]],
                "axiom_fallback_names_full": [["Coq.bar", "value rejected"]]
              }
            }"#,
        )
        .expect("write report");
        let map = reasons_from_report_json(&report).expect("parse report");
        assert_eq!(
            map.get("Coq.foo").map(String::as_str),
            Some("kernel reject: mismatch")
        );
        assert_eq!(
            map.get("Coq.bar").map(String::as_str),
            Some("value rejected")
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}
