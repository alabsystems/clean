// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Single-line verify** — the exemplar tweak-and-check diagnostic behind
//! `clean mathverse isabelle-verify-one`.
//!
//! The engine rounds lacked a way to re-check ONE corpus line against an
//! accepted state in seconds; the only loop was a 30-minute slice replay. This
//! module closes that: fetch exactly one line (by serial, via the
//! [`super::isabelle_index`] sidecar when present, else a scan), restore the
//! accepted env + closure + registries from a completed replay snapshot (or
//! build a minimal state), and run the REAL
//! [`verify_single_line`](super::isabelle_pure_verify::verify_single_line) on
//! it — the same `verify_one` the full driver runs, so the verdict is
//! bit-identical. Any env mutation is local to the process.
//!
//! When a line's `PThm` dependencies are not all in the snapshot's accepted
//! closure, `verify_one` cannot resolve them; the report names the exact missing
//! serials — that IS the diagnostic (fix the gatekeeper it waits on).

use std::path::{Path, PathBuf};

use super::isabelle_pure::parse_proven_theorem;
use super::isabelle_pure_verify::{
    snapshot::load_snapshot_retry, verify_single_line, SingleLineState,
};
use crate::shard::ShardWriter;

/// Kernel replay recursion is deep; run state-build + verify on a dedicated
/// big-stack thread so the diagnostic works regardless of `RUST_MIN_STACK`.
const VERIFY_STACK: usize = 2560 * 1024 * 1024;

/// Errors from the single-line verify diagnostic.
#[derive(Debug, thiserror::Error)]
pub enum VerifyOneError {
    /// Filesystem failure reading the corpus.
    #[error("isabelle-verify-one I/O on {path}: {source}")]
    Io {
        /// Path involved.
        path: PathBuf,
        /// Underlying error.
        source: std::io::Error,
    },
    /// The requested serial is not present in the corpus.
    #[error("serial {0} not found in corpus")]
    SerialNotFound(i64),
    /// The corpus line for the serial did not parse as a proven theorem.
    #[error("serial {0}: corpus line did not parse as a proven theorem")]
    ParseError(i64),
    /// Snapshot load failed.
    #[error("isabelle-verify-one snapshot load: {0}")]
    Snapshot(String),
    /// Building the minimal (no-snapshot) verify state failed.
    #[error("isabelle-verify-one state build: {0}")]
    StateBuild(String),
    /// The verify thread panicked.
    #[error("isabelle-verify-one: verify thread panicked")]
    ThreadPanic,
}

fn io_err(path: &Path) -> impl FnOnce(std::io::Error) -> VerifyOneError + '_ {
    move |source| VerifyOneError::Io {
        path: path.to_path_buf(),
        source,
    }
}

/// The outcome of verifying one corpus line, ready for the CLI to print.
#[derive(Debug, Clone, Default)]
pub struct VerifyOneReport {
    /// The verified line's serial.
    pub serial: i64,
    /// Its `"name"` (empty for anonymous nodes).
    pub name: String,
    /// TRUE iff clean's kernel accepted the proof with a foundational-only
    /// closure (`KernelVerified`), OR the line was already in the snapshot's
    /// accepted closure (see [`Self::already_accepted`]).
    pub verified: bool,
    /// TRUE when the target serial was ALREADY a `KernelVerified` closure entry
    /// in the restored snapshot — so it was reported as verified WITHOUT a
    /// re-check (re-adding its declaration would collide as a duplicate). The
    /// diagnostic is aimed at the rejected set, which is never in the closure.
    pub already_accepted: bool,
    /// The rejection reason tally (`reason -> count`), empty on accept.
    pub reasons: Vec<(String, usize)>,
    /// The fine-grained rejection-specifics tally (payload-bearing keys),
    /// populated because the diagnostic enables `reject_specifics` in its
    /// installed [`VerifyConfig`](super::isabelle_verify_config::VerifyConfig).
    pub specifics: Vec<(String, usize)>,
    /// The line's parsed proof `PThm` dependency serials (deduplicated).
    pub deps: Vec<i64>,
    /// The subset of `deps` NOT resolvable in the accepted closure — the crisp
    /// "this line waits on a rejected/absent gatekeeper" diagnostic.
    pub missing_deps: Vec<i64>,
    /// Whether the corpus index sidecar served the line fetch (vs a scan).
    pub used_index: bool,
    /// Whether an accepted-state snapshot was restored (vs a minimal state).
    pub used_snapshot: bool,
    /// Wall time of the state-build + verify step, in milliseconds.
    pub wall_ms: u128,
}

/// Fetch the (trimmed) corpus line for `serial`, via the `.idx` sidecar when
/// present, else a streaming scan. Returns the line plus whether the index was
/// used.
fn fetch_line(corpus: &Path, serial: i64) -> Result<(String, bool), VerifyOneError> {
    if let Some(index) = super::isabelle_index::try_load(corpus) {
        if let Some(entry) = index.get(serial) {
            let line = index
                .read_line(corpus, entry)
                .map_err(|e| VerifyOneError::Io {
                    path: corpus.to_path_buf(),
                    source: std::io::Error::other(e.to_string()),
                })?;
            return Ok((line, true));
        }
        return Err(VerifyOneError::SerialNotFound(serial));
    }
    // Scan fallback.
    use std::io::BufRead as _;
    let reader = std::io::BufReader::new(std::fs::File::open(corpus).map_err(io_err(corpus))?);
    for line in reader.lines() {
        let line = line.map_err(io_err(corpus))?;
        if super::isabelle_import::leading_serial(&line) == Some(serial) {
            return Ok((line, false));
        }
    }
    Err(VerifyOneError::SerialNotFound(serial))
}

/// The `"name":"..."` field of a corpus line.
fn line_name(line: &str) -> String {
    line.find("\"name\":\"")
        .map(|at| &line[at + "\"name\":\"".len()..])
        .and_then(|rest| rest.find('"').map(|end| rest[..end].to_string()))
        .unwrap_or_default()
}

/// Verify exactly one corpus line and return its full diagnostic report.
///
/// `snapshot` restores the accepted env + closure + registries (fingerprint
/// ignored — a diagnostic never mints a release verdict); `None` builds a
/// minimal state from the corpus. `modes`/`full` enable the per-escalation-mode
/// and full expected-vs-got traces (printed to stderr by `verify_one`) for this
/// serial.
///
/// # Errors
/// [`VerifyOneError`] on a missing serial, a parse failure, a snapshot/state
/// failure, or a worker-thread panic.
pub fn verify_one_line(
    corpus: &Path,
    serial: i64,
    snapshot: Option<&Path>,
    modes: bool,
    full: bool,
) -> Result<VerifyOneReport, VerifyOneError> {
    let (line, used_index) = fetch_line(corpus, serial)?;
    let thm = parse_proven_theorem(&line).map_err(|_| VerifyOneError::ParseError(serial))?;
    let name = line_name(&line);

    // Build THIS probe's verify config explicitly rather than mutating shared
    // process env (the historical `set_var` hazard): fine-grained specifics are
    // always useful for a single-line probe, and the per-line translation is
    // bounded exactly like the standing import driver (`isabelle-import` sets 8M)
    // so a pathological recorded proof is budget-cut and honestly rejected
    // instead of hanging the diagnostic — unless the caller already pinned an
    // explicit budget. Installed on the verify worker thread below, so it never
    // leaks into a co-hosted run.
    let mut probe_cfg = crate::hol::isabelle_verify_config::VerifyConfig::from_env();
    probe_cfg.reject_specifics = true;
    if probe_cfg.translate_node_budget.is_none() {
        probe_cfg.translate_node_budget = Some(8_000_000);
    }
    // Per-mode / full expected-vs-got traces target THIS serial (verify_one
    // matches name-or-serial). These stay env-driven diagnostic toggles (read by
    // `dump.rs`), but a scoped guard serializes them and restores any ambient
    // values after the worker joins or an error unwinds the call.
    let _diagnostic_env = if modes || full {
        let mut env = crate::process_env::ScopedEnv::new();
        if modes {
            env.set("ISA_DUMP_MODES", serial.to_string());
        }
        if full {
            env.set("ISA_DUMP_FULL", serial.to_string());
        }
        Some(env)
    } else {
        None
    };

    // Parsed-proof dependency serials (precise; the byte-scan superset lives in
    // the index and drives slice/targets, not this per-line resolution check).
    let mut deps: Vec<i64> = Vec::new();
    thm.proof.thm_deps(&mut deps);
    deps.sort_unstable();
    deps.dedup();

    let corpus_owned = corpus.to_path_buf();
    let snapshot_owned = snapshot.map(Path::to_path_buf);
    let deps_for_thread = deps.clone();

    // State-build + verify on a big-stack thread (deep kernel recursion).
    type ThreadOut = (
        bool,
        bool,
        Vec<(String, usize)>,
        Vec<(String, usize)>,
        Vec<i64>,
        u128,
    );
    let handle = std::thread::Builder::new()
        .stack_size(VERIFY_STACK)
        .spawn(move || -> Result<ThreadOut, VerifyOneError> {
            // Install this probe's config on the verify thread (the thread-local
            // where the translate/verify reads happen); dropped when the thread
            // returns, so it never touches another run.
            let _cfg = probe_cfg.install();
            let started = std::time::Instant::now();
            let mut state = match &snapshot_owned {
                Some(snap) => {
                    let s = load_snapshot_retry(snap)
                        .map_err(|e| VerifyOneError::Snapshot(e.to_string()))?;
                    SingleLineState::from_snapshot(s)
                }
                None => SingleLineState::minimal(&corpus_owned)
                    .map_err(|e| VerifyOneError::StateBuild(e.to_string()))?,
            };
            let missing: Vec<i64> = deps_for_thread
                .iter()
                .copied()
                .filter(|d| !state.closure_has(*d))
                .collect();
            // If the target serial is ALREADY in the accepted closure (a line the
            // snapshot verified), re-adding its kernel declaration would collide
            // (`DuplicateName`) and mis-report a spurious kernel-reject. It is
            // already KernelVerified — report that, don't re-run. Diagnostics are
            // for lines NOT in the closure (the rejected set), which never collide.
            if state.closure_has(serial) {
                let wall_ms = started.elapsed().as_millis();
                return Ok((true, true, Vec::new(), Vec::new(), missing, wall_ms));
            }
            let mut writer = ShardWriter::new();
            let out = verify_single_line(&thm, &mut state, &mut writer);
            let wall_ms = started.elapsed().as_millis();
            let reasons: Vec<(String, usize)> = out.rejection_reasons.into_iter().collect();
            let specifics: Vec<(String, usize)> = out.rejection_specifics.into_iter().collect();
            Ok((
                out.kernel_verified == 1,
                false,
                reasons,
                specifics,
                missing,
                wall_ms,
            ))
        })
        .map_err(|e| VerifyOneError::StateBuild(e.to_string()))?;

    let (verified, already_accepted, reasons, specifics, missing_deps, wall_ms) =
        handle.join().map_err(|_| VerifyOneError::ThreadPanic)??;

    Ok(VerifyOneReport {
        serial,
        name,
        verified,
        already_accepted,
        reasons,
        specifics,
        deps,
        missing_deps,
        used_index,
        used_snapshot: snapshot.is_some(),
        wall_ms,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::isabelle_import::leading_serial;

    const FIXTURE: &str =
        include_str!("../../tests/fixtures/isabelle/hol_foundational_closure.jsonl");

    fn write_fixture(dir: &Path) -> PathBuf {
        std::fs::create_dir_all(dir).expect("mk dir");
        let corpus = dir.join("corpus.jsonl");
        let mut lines: Vec<&str> = FIXTURE.lines().filter(|l| !l.trim().is_empty()).collect();
        lines.sort_by_key(|l| leading_serial(l).expect("serials"));
        std::fs::write(&corpus, lines.join("\n") + "\n").expect("write corpus");
        corpus
    }

    /// HOL.refl (serial 300) is a foundational leaf — it verifies from a minimal
    /// state (no snapshot, empty closure, no deps).
    #[test]
    fn test_verify_one_accepts_foundational_leaf() {
        let dir = std::env::temp_dir().join(format!("isa_vone_ok_{}", std::process::id()));
        let corpus = write_fixture(&dir);
        let report = verify_one_line(&corpus, 300, None, false, false).expect("verify");
        assert_eq!(report.name, "HOL.refl");
        assert!(
            report.verified,
            "HOL.refl must verify; reasons={:?}",
            report.reasons
        );
        assert!(report.missing_deps.is_empty(), "refl has no thm deps");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A missing serial is a crisp typed error, not a silent pass.
    #[test]
    fn test_verify_one_missing_serial_errors() {
        let dir = std::env::temp_dir().join(format!("isa_vone_miss_{}", std::process::id()));
        let corpus = write_fixture(&dir);
        let err = verify_one_line(&corpus, -424242, None, false, false)
            .expect_err("absent serial must error");
        assert!(matches!(err, VerifyOneError::SerialNotFound(-424242)));
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A non-leaf line verified minimally (empty closure) reports its unresolved
    /// dependencies as missing — the gatekeeper diagnostic.
    #[test]
    fn test_verify_one_reports_missing_deps_without_snapshot() {
        let dir = std::env::temp_dir().join(format!("isa_vone_dep_{}", std::process::id()));
        let corpus = write_fixture(&dir);
        // Find a corpus line WITH parsed thm deps.
        let target = FIXTURE
            .lines()
            .filter(|l| !l.trim().is_empty())
            .filter_map(|l| parse_proven_theorem(l).ok())
            .find_map(|t| {
                let mut d = Vec::new();
                t.proof.thm_deps(&mut d);
                (!d.is_empty()).then_some(t.serial)
            })
            .expect("a line with thm deps");
        let report = verify_one_line(&corpus, target, None, false, false).expect("verify");
        assert!(!report.deps.is_empty(), "target should have parsed deps");
        // With an empty (minimal) closure, every thm dep is unresolved — the
        // missing-dep set equals the full dep set (the gatekeeper diagnostic).
        assert_eq!(
            report.missing_deps.len(),
            report.deps.len(),
            "minimal state resolves no thm dep"
        );
        // Conservation: a line is either KernelVerified with no reject reason, or
        // rejected WITH a recorded reason (never a silent drop). This also
        // exercises the rejected-line report path.
        assert!(
            report.verified ^ !report.reasons.is_empty(),
            "verified XOR has-a-reject-reason: verified={} reasons={:?}",
            report.verified,
            report.reasons
        );
        assert!(
            !report.already_accepted,
            "minimal state has an empty closure"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}
