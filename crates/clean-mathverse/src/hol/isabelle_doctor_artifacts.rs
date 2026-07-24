// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The artifact-coherence and storage ops-preflight checks (corpus↔index,
//! snapshot layout, `/tmp` durability, disk headroom). Split from
//! `isabelle_doctor_checks.rs` (the process/script checks) to keep each file
//! under the size cap; both are `mod` children of [`super`].

use std::path::{Path, PathBuf};

use super::super::isabelle_index;
use super::super::isabelle_pure_verify::snapshot::{
    self, SnapshotError, SnapshotHeaderInfo, SnapshotProvenance,
};
use super::{run_capture, BuildIdentity, Check, DoctorConfig, Status};

// ---------------------------------------------------------------------------
// Check 4: corpus / index coherence
// ---------------------------------------------------------------------------

pub(super) fn check_corpus_index(corpus: &Path) -> Check {
    let id = "corpus-index";
    let Ok(meta) = std::fs::metadata(corpus) else {
        return Check::new(
            id,
            Status::Fail,
            format!("corpus {} does not exist / is unreadable", corpus.display()),
        );
    };
    let corpus_len = meta.len();
    let idx = isabelle_index::index_path(corpus);
    if !idx.exists() {
        return Check::new(
            id,
            Status::Warn,
            format!(
                "no .idx sidecar for {} — slicing/verify-one will scan the full corpus; \
                 build one with `clean mathverse isabelle-index --corpus {}`",
                corpus.display(),
                corpus.display()
            ),
        );
    }
    let index = match isabelle_index::load_index(&idx) {
        Ok(index) => index,
        Err(e) => {
            return Check::new(
                id,
                Status::Fail,
                format!(
                    "corpus index {} failed to load ({e}) — corrupt sidecar; rebuild it",
                    idx.display()
                ),
            );
        }
    };
    if index.corpus_len != corpus_len {
        return Check::new(
            id,
            Status::Fail,
            format!(
                "index STALE: {} indexed {} bytes but corpus is now {} bytes — rebuild the \
                 index before importing",
                idx.display(),
                index.corpus_len,
                corpus_len
            ),
        );
    }
    let range = match (index.entries.first(), index.entries.last()) {
        (Some(a), Some(b)) => format!("serials {}..{}", a.serial, b.serial),
        _ => "no indexed serials".to_string(),
    };
    Check::new(
        id,
        Status::Pass,
        format!(
            "index coherent: {} lines, {range}, {} corpus bytes",
            index.entries.len(),
            corpus_len
        ),
    )
}

// ---------------------------------------------------------------------------
// Check 5: snapshot layout drift
// ---------------------------------------------------------------------------

pub(super) fn check_snapshot_layout(snapshot: &Path, build: &BuildIdentity) -> Check {
    let mut check = classify_snapshot_header(snapshot::inspect_snapshot_header(snapshot), snapshot);
    // Provenance pairing is INFORMATIONAL (the ENV-LAYOUT fingerprint match set by
    // `classify_snapshot_header` is the decisive resume-correctness signal); it
    // reports which binary built the snapshot vs. the running one so the operator
    // can rerun with the original binary or preserve it.
    let prov = snapshot::read_provenance_sidecar(snapshot);
    check
        .items
        .push(snapshot_pairing_item(prov.as_ref(), build));
    check
}

/// The 7-char short prefix of a SHA-like string (`"unknown"` passes through).
fn short_sha(s: &str) -> &str {
    &s[..s.len().min(7)]
}

/// Human pairing line for the snapshot-layout check: names the binary that BUILT
/// the snapshot (from the `<snap>.provenance.json` sidecar) against the running
/// one, with a MATCH / MISMATCH / UNVERIFIABLE git-SHA verdict. Degrades
/// gracefully to a "no sidecar" note. Pure over its inputs so it is unit-testable
/// with synthetic provenance.
pub(super) fn snapshot_pairing_item(
    prov: Option<&SnapshotProvenance>,
    build: &BuildIdentity,
) -> String {
    let current = build.short_sha().unwrap_or_else(|| "unknown".to_string());
    match prov {
        None => format!(
            "no provenance sidecar (<snap>.provenance.json) — cannot pair snapshot to its \
             builder binary (current binary {current}); degraded, regenerate/preserve to establish pairing"
        ),
        Some(p) => {
            let built = short_sha(&p.binary_git_sha);
            let verdict = match build.git_sha.as_deref() {
                Some(cur) if p.binary_git_sha != "unknown" && !p.binary_git_sha.is_empty() => {
                    if p.binary_git_sha == cur {
                        "MATCH"
                    } else {
                        "MISMATCH"
                    }
                }
                _ => "UNVERIFIABLE (sha unknown)",
            };
            format!(
                "snapshot built by {built} at {}, current binary {current} — {verdict}",
                p.binary_path
            )
        }
    }
}

/// Pure verdict over the snapshot header inspector's result — factored out so it
/// is testable with synthetic headers/errors and never re-parses the format.
pub(super) fn classify_snapshot_header(
    res: Result<SnapshotHeaderInfo, SnapshotError>,
    path: &Path,
) -> Check {
    let id = "snapshot-layout";
    match res {
        Ok(info) if !info.has_layout_fp => Check::new(
            id,
            Status::Warn,
            format!(
                "snapshot {} is v{} (pre-v6, no ENV-LAYOUT guard) — resume is riskier; a \
                 full replay under this binary is safest",
                path.display(),
                info.version
            ),
        ),
        Ok(info) if !info.layout_matches => Check::new(
            id,
            Status::Fail,
            format!(
                "snapshot {} ENV-LAYOUT DRIFT: built by a different binary layout \
                 (snapshot fp {}, this binary {}) — it will fail with LayoutDrift; \
                 regenerate with a full replay",
                path.display(),
                info.snapshot_fp_hex,
                info.loader_fp_hex
            ),
        ),
        Ok(info) => Check::new(
            id,
            Status::Pass,
            format!(
                "snapshot {} v{} layout matches this binary (fp {})",
                path.display(),
                info.version,
                info.loader_fp_hex
            ),
        ),
        Err(e) => Check::new(
            id,
            Status::Fail,
            format!("snapshot {} header unreadable/invalid: {e}", path.display()),
        ),
    }
}

// ---------------------------------------------------------------------------
// Check 6: durability (no /tmp)
// ---------------------------------------------------------------------------

pub(super) fn check_durability(cfg: &DoctorConfig) -> Check {
    let id = "durability";
    let mut candidates: Vec<(&str, &Path)> = vec![("ops-dir", cfg.ops_dir.as_path())];
    if let Some(c) = &cfg.corpus {
        candidates.push(("corpus", c.as_path()));
    }
    if let Some(s) = &cfg.snapshot {
        candidates.push(("snapshot", s.as_path()));
    }
    if let Some(l) = &cfg.verify_lock {
        candidates.push(("verify-lock", l.as_path()));
    }
    let offenders: Vec<String> = candidates
        .into_iter()
        .filter(|(_, p)| is_under_tmp(p))
        .map(|(label, p)| format!("{label}: {}", p.display()))
        .collect();
    if offenders.is_empty() {
        Check::new(
            id,
            Status::Pass,
            "all provided paths are on durable storage (none under /tmp)",
        )
    } else {
        Check::new(
            id,
            Status::Warn,
            format!(
                "{} path(s) under /tmp — the OS temp cleaner destroys corpora/snapshots; \
                 move them to durable storage",
                offenders.len()
            ),
        )
        .with_items(offenders)
    }
}

/// TRUE when `path` (raw or canonicalized) lives under `/tmp` or `/private/tmp`.
pub(super) fn is_under_tmp(path: &Path) -> bool {
    let raw = path.to_path_buf();
    let canon = std::fs::canonicalize(path).unwrap_or_else(|_| raw.clone());
    [raw, canon]
        .iter()
        .any(|p| p.starts_with("/tmp") || p.starts_with("/private/tmp"))
}

// ---------------------------------------------------------------------------
// Check 7: disk headroom
// ---------------------------------------------------------------------------

pub(super) fn check_disk_headroom(ops_dir: &Path, threshold_gib: u64) -> Check {
    let id = "disk-headroom";
    let target = existing_ancestor(ops_dir);
    let Some(out) = run_capture("df", &["-Pk", &target.to_string_lossy()]) else {
        return Check::new(
            id,
            Status::Warn,
            format!(
                "could not determine free space for {} (df unavailable)",
                target.display()
            ),
        );
    };
    let Some(avail_kib) = parse_df_avail_kib(&out) else {
        return Check::new(
            id,
            Status::Warn,
            format!("could not parse free space for {}", target.display()),
        );
    };
    let avail_gib = avail_kib / (1024 * 1024);
    if avail_gib < threshold_gib {
        Check::new(
            id,
            Status::Warn,
            format!(
                "low disk headroom: {avail_gib} GiB free on the ops volume (< {threshold_gib} \
                 GiB) — Isabelle corpora are 30–50 GB"
            ),
        )
    } else {
        Check::new(
            id,
            Status::Pass,
            format!("{avail_gib} GiB free on the ops volume (>= {threshold_gib} GiB threshold)"),
        )
    }
}

/// The `Available` (1 KiB blocks) field of POSIX `df -Pk` output: field index 3
/// of the first data row. Returns `None` when the output is malformed.
pub(super) fn parse_df_avail_kib(df_output: &str) -> Option<u64> {
    df_output
        .lines()
        .nth(1)
        .and_then(|row| row.split_whitespace().nth(3))
        .and_then(|f| f.parse::<u64>().ok())
}

/// The deepest existing ancestor of `path` (so `df` has a real directory to
/// stat even when the ops dir itself has not been created yet).
pub(super) fn existing_ancestor(path: &Path) -> PathBuf {
    let mut p = path;
    loop {
        if p.exists() {
            return p.to_path_buf();
        }
        match p.parent() {
            Some(parent) => p = parent,
            None => return PathBuf::from("."),
        }
    }
}
