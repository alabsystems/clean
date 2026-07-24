// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Blocking-weight targeting** — rank every REJECTED corpus line by how much
//! cascade it transitively gates, so a round attacks the top *gatekeepers*
//! (the sole blockers of the largest downstream reject sets) instead of
//! attacking families by name.
//!
//! # Inputs
//!
//! - a serial-sorted Isabelle corpus (`main_v2.jsonl`-shape lines), and
//! - a replay [`ReplaySnapshot`](super::isabelle_pure_verify::snapshot::ReplaySnapshot):
//!   its [`Closure`](super::isabelle_pure_translate::Closure) keys are the
//!   ACCEPTED (`KernelVerified`) serials; every other present serial is REJECTED.
//!
//! # Model
//!
//! Over the reject subgraph (rejected nodes; an edge `x → d` for every in-corpus
//! proof dep `d` of `x` that is itself rejected):
//!
//! - A rejected line is a **PRIMARY** (a frontier gatekeeper) iff *all* of its
//!   in-corpus deps are accepted — i.e. it has no rejected dep. Primaries are
//!   the sinks of the reject subgraph: the lines a round can actually attack,
//!   because everything they need already verifies.
//! - Each rejected line's **frontier set** is the set of primaries reachable
//!   from it through rejected-only edges — the primaries it *waits on*. A
//!   primary's own frontier set is exactly itself.
//! - **blocked(p)** = the number of rejected lines whose frontier set contains
//!   `p` (`p` included). This is `p`'s cascade weight: fixing every gatekeeper a
//!   line waits on is necessary before that line can verify, and `p` is one of
//!   them.
//! - **exclusive(p)** = the number of rejected lines whose frontier set is
//!   *exactly* `{p}` (`p` included). These are `p`'s SOLE-blocked dependents:
//!   the guaranteed release when `p` is fixed (nothing else stands in their way).
//!
//! `exclusive(p) ≤ blocked(p)`, and both count `p` itself. `exclusive` is the
//! conservative, guaranteed-yield metric; `blocked` is the optimistic ceiling
//! (realized only if *all* co-blockers of the shared dependents also fall).
//!
//! # Cost
//!
//! The corpus is ~134k nodes / ~500k edges. The dep graph is a DAG in serial
//! order (proof deps reference earlier serials), so the frontier sets are built
//! in one ascending pass with a per-node primary bitset (`P` primaries →
//! `⌈P/64⌉` words each). At `P ≈ 3k` and `R ≈ 112k` rejected nodes that is
//! ~40 MB and a few hundred million word-ops — seconds.

use std::collections::{HashMap, HashSet};
use std::io::BufRead as _;
use std::path::{Path, PathBuf};

use super::isabelle_import::{leading_serial, thm_refs_public};
use crate::replay_infra::targets::frontier_weights;

/// Errors from blocking-weight targeting.
#[derive(Debug, thiserror::Error)]
pub enum IsabelleTargetsError {
    /// Filesystem failure on the corpus, snapshot, or dump.
    #[error("isabelle-targets I/O on {path}: {source}")]
    Io {
        /// Path involved.
        path: PathBuf,
        /// Underlying error.
        source: std::io::Error,
    },
    /// Loading the replay snapshot failed.
    #[error("isabelle-targets snapshot load: {0}")]
    Snapshot(String),
}

fn io_err(path: &Path) -> impl FnOnce(std::io::Error) -> IsabelleTargetsError + '_ {
    move |source| IsabelleTargetsError::Io {
        path: path.to_path_buf(),
        source,
    }
}

/// The `"name":"..."` field of a corpus line (after the serial key).
fn line_name(line: &str) -> Option<&str> {
    let at = line.find("\"name\":\"")? + "\"name\":\"".len();
    let rest = &line[at..];
    let end = rest.find('"')?;
    Some(&rest[..end])
}

/// The corpus dependency graph plus per-serial display metadata, indexed by the
/// leading serial. `deps_of` holds the raw (possibly out-of-corpus, possibly
/// duplicated) thm references — the graph builder filters and dedups.
#[derive(Debug, Default)]
pub struct CorpusGraph {
    /// Every serial present in the corpus.
    pub present: HashSet<i64>,
    /// serial → its raw proof-dep thm ids (superset; unfiltered).
    pub deps_of: HashMap<i64, Vec<i64>>,
    /// serial → its `"name"` field (only stored for rejected serials).
    pub names: HashMap<i64, String>,
}

/// One rejected line's reason + signature, joined from an `ISA_DUMP_REJECTS`
/// dump (`reason\tname\tsignature`).
#[derive(Debug, Clone, Default)]
pub struct DumpJoin {
    /// By-serial rows (`<anon.sN>` names resolve here).
    by_serial: HashMap<i64, (String, String)>,
    /// By-name rows (non-anon names).
    by_name: HashMap<String, (String, String)>,
}

impl DumpJoin {
    /// Parse an `ISA_DUMP_REJECTS` dump into a serial/name join table.
    ///
    /// # Errors
    /// [`IsabelleTargetsError::Io`] on read failure.
    pub fn load(dump: &Path) -> Result<Self, IsabelleTargetsError> {
        let mut join = DumpJoin::default();
        let reader = std::io::BufReader::new(std::fs::File::open(dump).map_err(io_err(dump))?);
        for line in reader.lines() {
            let line = line.map_err(io_err(dump))?;
            let mut cols = line.split('\t');
            let (Some(reason), Some(name)) = (cols.next(), cols.next()) else {
                continue;
            };
            let sig = cols.next().unwrap_or("").to_string();
            if let Some(serial) = name
                .strip_prefix("<anon.s")
                .and_then(|r| r.strip_suffix('>'))
                .and_then(|d| d.parse::<i64>().ok())
            {
                join.by_serial.insert(serial, (reason.to_string(), sig));
            } else {
                join.by_name
                    .insert(name.to_string(), (reason.to_string(), sig));
            }
        }
        Ok(join)
    }

    /// The `(reason, signature)` recorded for `serial` (by serial first, then by
    /// name), if any.
    fn lookup(&self, serial: i64, name: &str) -> Option<&(String, String)> {
        self.by_serial
            .get(&serial)
            .or_else(|| self.by_name.get(name))
    }
}

/// One gatekeeper row in the targeting table.
#[derive(Debug, Clone)]
pub struct GatekeeperRow {
    /// The primary's serial.
    pub serial: i64,
    /// Its `"name"` field (or `<anon.sN>` when unnamed).
    pub name: String,
    /// The rejection reason, joined from the dump (empty when no dump / no row).
    pub reason: String,
    /// The rejection signature, joined from the dump (empty when absent).
    pub signature: String,
    /// Cascade weight: rejected lines whose frontier set includes this primary
    /// (this primary counted).
    pub blocked: usize,
    /// Sole-blocked dependents: rejected lines whose frontier set is exactly
    /// this primary (this primary counted) — the guaranteed release.
    pub exclusive: usize,
}

/// The full targeting result.
#[derive(Debug, Clone, Default)]
pub struct TargetsReport {
    /// Corpus lines with a parseable leading serial.
    pub corpus_lines: usize,
    /// Serials present AND in the snapshot closure (accepted / KernelVerified).
    pub accepted: usize,
    /// Serials present but NOT in the closure (rejected).
    pub rejected: usize,
    /// Rejected frontier lines (all in-corpus deps accepted).
    pub primaries: usize,
    /// Rejected lines with at least one rejected in-corpus dep (the cascade
    /// gated by the primaries) — `rejected - primaries`.
    pub cascade: usize,
    /// Rejected edges ignored because the dep had a serial ≥ the referrer
    /// (forward reference / cycle — vanishing in a well-formed serial export).
    pub forward_edges: usize,
    /// Top gatekeepers, ranked by `(blocked desc, exclusive desc, serial asc)`.
    pub rows: Vec<GatekeeperRow>,
}

/// Load the accepted-serial set (closure keys) from a replay snapshot,
/// ignoring the translator fingerprint (a pure post-hoc analysis, never a
/// verdict source). Runs the decode on a big-stack thread — the registry JSON
/// blob is deeply recursive.
fn load_accepted(snapshot: &Path) -> Result<HashSet<i64>, IsabelleTargetsError> {
    let path = snapshot.to_path_buf();
    let handle = std::thread::Builder::new()
        .stack_size(2560 * 1024 * 1024)
        .spawn(move || {
            super::isabelle_pure_verify::snapshot::load_snapshot_retry(&path)
                .map(|snap| snap.closure.keys().copied().collect::<HashSet<i64>>())
                .map_err(|e| e.to_string())
        })
        .map_err(|e| IsabelleTargetsError::Snapshot(e.to_string()))?;
    handle
        .join()
        .map_err(|_| IsabelleTargetsError::Snapshot("snapshot-load thread panicked".to_string()))?
        .map_err(IsabelleTargetsError::Snapshot)
}

/// Scan `corpus` into a [`CorpusGraph`], recording names only for serials NOT
/// in `accepted` (the only ones the report displays). Returns the graph and the
/// count of lines with a parseable leading serial.
fn scan_corpus(
    corpus: &Path,
    accepted: &HashSet<i64>,
) -> Result<(CorpusGraph, usize), IsabelleTargetsError> {
    let mut graph = CorpusGraph::default();
    let mut corpus_lines = 0usize;
    let reader = std::io::BufReader::new(std::fs::File::open(corpus).map_err(io_err(corpus))?);
    let mut ref_buf: Vec<i64> = Vec::new();
    for line in reader.lines() {
        let line = line.map_err(io_err(corpus))?;
        let Some(serial) = leading_serial(&line) else {
            continue;
        };
        corpus_lines += 1;
        graph.present.insert(serial);
        ref_buf.clear();
        thm_refs_public(&line, &mut ref_buf);
        if !ref_buf.is_empty() {
            graph.deps_of.insert(serial, ref_buf.clone());
        }
        if !accepted.contains(&serial) {
            let name = line_name(&line).unwrap_or("").to_string();
            graph.names.insert(serial, name);
        }
    }
    Ok((graph, corpus_lines))
}

/// Build the [`CorpusGraph`] straight from a loaded corpus index — the
/// scan-free twin of [`scan_corpus`]. Iterates entries in FILE order so
/// duplicate-serial resolution (last write wins for `deps_of`/`names`) matches
/// the sequential scan exactly; the resulting graph is byte-identical.
fn graph_from_index(
    index: &super::isabelle_index::CorpusIndex,
    accepted: &HashSet<i64>,
) -> (CorpusGraph, usize) {
    let mut graph = CorpusGraph::default();
    for e in index.entries_in_file_order() {
        graph.present.insert(e.serial);
        if !e.deps.is_empty() {
            graph.deps_of.insert(e.serial, e.deps.clone());
        }
        if !accepted.contains(&e.serial) {
            graph.names.insert(e.serial, e.name.clone());
        }
    }
    (graph, index.entries.len())
}

/// Compute the blocking-weight targeting report from an in-memory graph +
/// accepted set. Split out from I/O so it is unit-testable on constructed
/// graphs. `top` caps the returned rows (0 = all primaries).
///
/// The frontier arithmetic (which rejected serials gate the most cascade) is the
/// lane-agnostic [`frontier_weights`] core; this adapter supplies the
/// ascending-serial DAG order (a topological order, since Isabelle proof deps
/// reference strictly-earlier serials) and joins names + dump reasons onto the
/// ranked primaries. The delegation is byte-identical to the former inline pass:
/// serial-ascending order makes the core's position-based forward-edge check
/// (`pos(dep) ≥ pos(node)`) coincide exactly with the old `dep_serial ≥
/// node_serial` test.
#[must_use]
pub fn analyze(
    graph: &CorpusGraph,
    accepted: &HashSet<i64>,
    dump: &DumpJoin,
    top: usize,
) -> TargetsReport {
    // Rejected = present \ accepted, in ascending serial order (DAG order).
    let mut rejected: Vec<i64> = graph
        .present
        .iter()
        .copied()
        .filter(|s| !accepted.contains(s))
        .collect();
    rejected.sort_unstable();

    let empty: Vec<i64> = Vec::new();
    let frontier = frontier_weights(&rejected, |s| {
        graph.deps_of.get(s).unwrap_or(&empty).as_slice()
    });

    // Join names + dump reasons onto the ranked primaries.
    let mut rows: Vec<GatekeeperRow> = frontier
        .rows
        .iter()
        .map(|r| {
            let serial = r.id;
            let name = graph
                .names
                .get(&serial)
                .filter(|n| !n.is_empty())
                .cloned()
                .unwrap_or_else(|| format!("<anon.s{serial}>"));
            let (reason, signature) = dump.lookup(serial, &name).cloned().unwrap_or_default();
            GatekeeperRow {
                serial,
                name,
                reason,
                signature,
                blocked: r.blocked,
                exclusive: r.exclusive,
            }
        })
        .collect();
    rows.sort_by(|a, b| {
        b.blocked
            .cmp(&a.blocked)
            .then(b.exclusive.cmp(&a.exclusive))
            .then(a.serial.cmp(&b.serial))
    });
    if top > 0 && rows.len() > top {
        rows.truncate(top);
    }

    TargetsReport {
        corpus_lines: 0, // filled by compute_targets
        accepted: accepted.len(),
        rejected: frontier.rejected,
        primaries: frontier.primaries,
        cascade: frontier.cascade,
        forward_edges: frontier.forward_edges,
        rows,
    }
}

/// End-to-end: load the snapshot's accepted set, scan the corpus into a graph,
/// optionally join a reject dump, and rank the top gatekeepers.
///
/// # Errors
/// [`IsabelleTargetsError`] on I/O or snapshot-load failure.
pub fn compute_targets(
    corpus: &Path,
    snapshot: &Path,
    dump: Option<&Path>,
    top: usize,
) -> Result<TargetsReport, IsabelleTargetsError> {
    let accepted = load_accepted(snapshot)?;
    // Prefer the `<corpus>.idx` sidecar (near-instant vs a full scan); the graph
    // it yields is byte-identical to `scan_corpus` (same `thm_refs_public` edges,
    // same names, same file-order duplicate resolution). Falls back to a scan —
    // with a stderr hint — when the sidecar is absent or stale.
    let (graph, corpus_lines) = match super::isabelle_index::try_load(corpus) {
        Some(index) => graph_from_index(&index, &accepted),
        None => scan_corpus(corpus, &accepted)?,
    };
    let join = match dump {
        Some(d) => DumpJoin::load(d)?,
        None => DumpJoin::default(),
    };
    let mut report = analyze(&graph, &accepted, &join, top);
    report.corpus_lines = corpus_lines;
    // `analyze` reports `accepted` as closure-key count; narrow to serials that
    // are actually present in the corpus so accepted + rejected = corpus_lines.
    report.accepted = corpus_lines - report.rejected;
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tiny hand-built reject graph exercises the frontier arithmetic:
    ///
    /// accepted = {1, 2}. Rejected: A=10 (deps 1,2 → primary), E=15 (dep 1 →
    /// primary), B=20 (dep 10), C=30 (dep 20), D=40 (deps 10,15).
    ///
    /// Frontier sets: A→{A}, E→{E}, B→{A}, C→{A}, D→{A,E}.
    /// blocked(A)=|{10,20,30,40}|=4, exclusive(A)=|{10,20,30}|=3.
    /// blocked(E)=|{15,40}|=2, exclusive(E)=|{15}|=1.
    #[test]
    fn test_analyze_frontier_weights() {
        let mut graph = CorpusGraph::default();
        for s in [1, 2, 10, 15, 20, 30, 40] {
            graph.present.insert(s);
        }
        graph.deps_of.insert(10, vec![1, 2]);
        graph.deps_of.insert(15, vec![1]);
        graph.deps_of.insert(20, vec![10]);
        graph.deps_of.insert(30, vec![20]);
        graph.deps_of.insert(40, vec![10, 15]);
        for s in [10, 15, 20, 30, 40] {
            graph.names.insert(s, format!("thm{s}"));
        }
        let accepted: HashSet<i64> = [1, 2].into_iter().collect();
        let report = analyze(&graph, &accepted, &DumpJoin::default(), 0);

        assert_eq!(report.rejected, 5, "10,15,20,30,40 rejected");
        assert_eq!(report.primaries, 2, "A=10 and E=15 are frontier primaries");
        assert_eq!(report.cascade, 3, "20,30,40 gated");

        let a = report.rows.iter().find(|r| r.serial == 10).expect("A row");
        assert_eq!(a.blocked, 4, "A gates 10,20,30,40");
        assert_eq!(a.exclusive, 3, "A solely gates 10,20,30 (not 40)");
        let e = report.rows.iter().find(|r| r.serial == 15).expect("E row");
        assert_eq!(e.blocked, 2, "E gates 15,40");
        assert_eq!(e.exclusive, 1, "E solely gates only itself");

        // Ranking: A (blocked 4) before E (blocked 2).
        assert_eq!(report.rows[0].serial, 10, "top gatekeeper is A");
        assert_eq!(report.rows[1].serial, 15);
    }

    /// Forward references (dep serial ≥ referrer) are dropped from the reject
    /// subgraph and tallied, never panicking the ascending pass.
    #[test]
    fn test_analyze_forward_ref_dropped() {
        let mut graph = CorpusGraph::default();
        for s in [1, 10, 20] {
            graph.present.insert(s);
        }
        graph.deps_of.insert(10, vec![1, 20]); // 20 is a forward ref
        graph.deps_of.insert(20, vec![1]);
        let accepted: HashSet<i64> = [1].into_iter().collect();
        let report = analyze(&graph, &accepted, &DumpJoin::default(), 0);
        assert_eq!(report.forward_edges, 1, "the 10→20 edge is forward");
        // With the forward edge dropped, both 10 and 20 are primaries.
        assert_eq!(report.primaries, 2);
        let ten = report.rows.iter().find(|r| r.serial == 10).expect("row 10");
        assert_eq!(ten.blocked, 1, "10 gates only itself");
        assert_eq!(ten.exclusive, 1);
    }

    /// The dump join surfaces reason + signature by `<anon.sN>` serial.
    #[test]
    fn test_dump_join_by_serial() {
        let dir = std::env::temp_dir().join(format!("isa_targets_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let dump = dir.join("krej.txt");
        std::fs::write(
            &dump,
            "kernel-reject\t<anon.s10>\tmismatch expected=fun got=Eq\n",
        )
        .expect("write dump");
        let join = DumpJoin::load(&dump).expect("load dump");
        let hit = join.lookup(10, "<anon.s10>").expect("row");
        assert_eq!(hit.0, "kernel-reject");
        assert_eq!(hit.1, "mismatch expected=fun got=Eq");
        let _ = std::fs::remove_dir_all(&dir);
    }
}
