// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Ops preflight / health doctor** — the mechanized checklist behind
//! `clean mathverse isabelle-doctor`.
//!
//! Every check here encodes a *real* operational failure this import campaign
//! hit, so a re-import on a fresh or busy machine fails LOUD before burning
//! hours instead of silently producing an invalid grand run:
//!
//! 1. **Stale binary** — a chain script once picked a 5-day-old binary via
//!    `ls | head -1`. [`check_binary_identity`] reports the running binary's
//!    embedded git SHA + build time and compares it against the repo HEAD and
//!    the newest `crates/` commit.
//! 2. **Concurrent verify** — two simultaneous verifies silently corrupted the
//!    KV count (4,111 → 1,310). [`check_verify_busy`] probes the flock and scans
//!    for running verify processes.
//! 3. **Dead script refs** — an armed script referenced a launcher inside a
//!    since-deleted `.claude/worktrees/…` tree. [`check_dead_script_refs`] scans
//!    the ops dir's `*.sh` for absolute paths that no longer exist.
//! 4. **Corpus/index drift** — a `.jsonl` corpus and its `.idx` sidecar can
//!    diverge. [`check_corpus_index`] reuses the index's own staleness metadata.
//! 5. **Snapshot layout drift** — a snapshot built by an older binary layout
//!    fails with `LayoutDrift`. [`check_snapshot_layout`] reuses the snapshot
//!    module's header inspector.
//! 6. **Durability** — the macOS `/tmp` cleaner destroyed corpus v1.
//!    [`check_durability`] warns on any path under `/tmp`.
//! 7. **Disk headroom** — corpora are 30–50 GB. [`check_disk_headroom`] reports
//!    free space on the ops volume.
//!
//! Each check yields a [`Check`] with a [`Status`]; the process exit code is
//! `1` iff any check is [`Status::Fail`] (warnings never fail the gate).

use std::path::PathBuf;
use std::process::Command;

use serde::Serialize;

#[path = "isabelle_doctor_artifacts.rs"]
mod artifacts;
#[path = "isabelle_doctor_checks.rs"]
mod checks;
#[path = "isabelle_doctor_skew.rs"]
mod skew;
use artifacts::{check_corpus_index, check_disk_headroom, check_durability, check_snapshot_layout};
use checks::{check_binary_identity, check_dead_script_refs, check_verify_busy};
use skew::check_afp_skew;

/// A single check's severity. Ordered least → most severe so [`Status::worst`]
/// can fold a set of sub-verdicts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "UPPERCASE")]
pub enum Status {
    /// The check passed with nothing to flag.
    Pass,
    /// A soft problem the operator should know about, but not a hard stop.
    Warn,
    /// A hard blocker: running a grand import now risks an invalid result.
    Fail,
}

impl Status {
    /// The fixed-width label printed at the head of a human-readable check line.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Status::Pass => "PASS",
            Status::Warn => "WARN",
            Status::Fail => "FAIL",
        }
    }

    /// The more severe of `self` and `other`.
    #[must_use]
    pub fn worst(self, other: Status) -> Status {
        self.max(other)
    }
}

/// One check's outcome: a stable machine `id`, a severity, a one-line human
/// `summary`, and optional detail `items` (e.g. the broken references found).
#[derive(Debug, Clone, Serialize)]
pub struct Check {
    /// Stable machine identifier (`binary-identity`, `verify-busy`, …).
    pub id: &'static str,
    /// This check's severity.
    pub status: Status,
    /// One-line human summary.
    pub summary: String,
    /// Optional per-finding detail lines (empty for most checks).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub items: Vec<String>,
}

impl Check {
    fn new(id: &'static str, status: Status, summary: impl Into<String>) -> Self {
        Check {
            id,
            status,
            summary: summary.into(),
            items: Vec::new(),
        }
    }

    fn with_items(mut self, items: Vec<String>) -> Self {
        self.items = items;
        self
    }
}

/// The compile-time build identity embedded in the running binary. Populated by
/// `clean-cli`'s `build.rs` (git SHA + build timestamp); `None` fields mean the
/// binary was built without a git-aware build (fail-loud rather than silent).
#[derive(Debug, Clone, Serialize)]
pub struct BuildIdentity {
    /// Full git SHA the binary was built from, or `None` if unknown at build.
    pub git_sha: Option<String>,
    /// Unix build timestamp (seconds), or `None` if unknown.
    pub build_unix: Option<u64>,
}

impl BuildIdentity {
    /// Build an identity from raw compile-time strings, normalizing the sentinel
    /// values `""` / `"unknown"` / `"0"` to `None`.
    #[must_use]
    pub fn new(git_sha: Option<String>, build_unix: Option<u64>) -> Self {
        let git_sha = git_sha.filter(|s| !s.is_empty() && s != "unknown");
        let build_unix = build_unix.filter(|&t| t != 0);
        BuildIdentity {
            git_sha,
            build_unix,
        }
    }

    /// An identity with nothing known — the fallback when the build did not
    /// embed git metadata (e.g. a source tarball with no `.git`).
    #[must_use]
    pub fn unknown() -> Self {
        BuildIdentity {
            git_sha: None,
            build_unix: None,
        }
    }

    /// The 7-char short SHA, if a SHA is known.
    #[must_use]
    pub fn short_sha(&self) -> Option<String> {
        self.git_sha.as_ref().map(|s| {
            let n = s.len().min(7);
            s[..n].to_string()
        })
    }
}

/// Whether the doctor escalates advisory `WARN`s to hard `FAIL`s.
///
/// A handful of checks (binary staleness, `/tmp` durability, disk headroom) are
/// advisory by default — a human running the preflight interactively can weigh
/// them. For an **unattended / CI** preflight a warning must still block, so
/// [`Strictness::Strict`] promotes exactly those advisory `WARN`s to `FAIL`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Strictness {
    /// Default: advisory checks `WARN` but do not fail the gate.
    #[default]
    Advisory,
    /// Unattended/CI: the advisory `WARN`s in [`STRICT_ESCALATED_CHECKS`] become
    /// `FAIL`.
    Strict,
}

/// The advisory check ids whose `WARN` is promoted to `FAIL` under
/// [`Strictness::Strict`]. Hard checks (verify-busy, corpus/index, snapshot
/// layout, dead script refs) already `FAIL` on their own and are unaffected.
pub(crate) const STRICT_ESCALATED_CHECKS: &[&str] =
    &["binary-identity", "durability", "disk-headroom", "afp-skew"];

/// Promote an advisory `WARN` to `FAIL` when `--strict` is set and the check is
/// one of [`STRICT_ESCALATED_CHECKS`]. Pass-through otherwise (a `PASS` or a
/// hard `FAIL` is never touched, nor is an unlisted `WARN`).
fn apply_strictness(mut check: Check, strictness: Strictness) -> Check {
    if strictness == Strictness::Strict
        && check.status == Status::Warn
        && STRICT_ESCALATED_CHECKS.contains(&check.id)
    {
        check.status = Status::Fail;
        check
            .summary
            .push_str(" [escalated WARN->FAIL by --strict]");
    }
    check
}

/// Everything the doctor needs to know about the machine it is preflighting.
#[derive(Debug, Clone)]
pub struct DoctorConfig {
    /// Ops working directory (default `~/isabelle-work`). Scanned for dead
    /// script refs; also the default home of the verify lock and the disk
    /// volume whose headroom is reported.
    pub ops_dir: PathBuf,
    /// A corpus `.jsonl` whose `.idx` sidecar coherence should be checked.
    pub corpus: Option<PathBuf>,
    /// A replay snapshot whose env-layout fingerprint should be checked.
    pub snapshot: Option<PathBuf>,
    /// An AFP `thys` checkout whose ROOT files are scanned for distribution
    /// theory references (the `afp-skew` check runs only when this and
    /// [`Self::isabelle_src`] are both set).
    pub afp_thys: Option<PathBuf>,
    /// The installed Isabelle distribution `src` dir (e.g.
    /// `…/Isabelle2025-2.app/src`) the AFP references are resolved against.
    pub isabelle_src: Option<PathBuf>,
    /// Override for the verify lock path (default `<ops_dir>/.clean_verify.lock`).
    pub verify_lock: Option<PathBuf>,
    /// Warn when free space on the ops volume drops below this many GiB.
    pub disk_threshold_gib: u64,
    /// Whether advisory `WARN`s are promoted to `FAIL` (`--strict`).
    pub strictness: Strictness,
}

/// The full doctor run: every check plus rolled-up counts and an overall verdict.
#[derive(Debug, Clone, Serialize)]
pub struct DoctorReport {
    /// The per-check outcomes, in run order.
    pub checks: Vec<Check>,
    /// Number of `PASS` checks.
    pub pass: usize,
    /// Number of `WARN` checks.
    pub warn: usize,
    /// Number of `FAIL` checks.
    pub fail: usize,
    /// TRUE iff no check failed (warnings do not clear this to `false`).
    pub ok: bool,
}

impl DoctorReport {
    fn from_checks(checks: Vec<Check>) -> Self {
        let mut pass = 0;
        let mut warn = 0;
        let mut fail = 0;
        for c in &checks {
            match c.status {
                Status::Pass => pass += 1,
                Status::Warn => warn += 1,
                Status::Fail => fail += 1,
            }
        }
        DoctorReport {
            checks,
            pass,
            warn,
            fail,
            ok: fail == 0,
        }
    }
}

/// Run every applicable check and return the assembled report. Pure with
/// respect to its inputs except for reading the environment (git, `pgrep`,
/// `df`, the filesystem) — it never mutates anything.
#[must_use]
pub fn run_doctor(cfg: &DoctorConfig, build: &BuildIdentity) -> DoctorReport {
    let mut checks = vec![
        check_binary_identity(build),
        check_verify_busy(cfg),
        check_dead_script_refs(&cfg.ops_dir),
    ];
    if let Some(corpus) = &cfg.corpus {
        checks.push(check_corpus_index(corpus));
    }
    if let Some(snap) = &cfg.snapshot {
        checks.push(check_snapshot_layout(snap, build));
    }
    // AFP↔Isabelle version skew: runs only when the operator supplied an AFP
    // checkout and/or an Isabelle src dir to check against (a one-sided flag is a
    // loud WARN from inside the check itself, so it is added whenever either is set).
    if cfg.afp_thys.is_some() || cfg.isabelle_src.is_some() {
        checks.push(check_afp_skew(
            cfg.afp_thys.as_deref(),
            cfg.isabelle_src.as_deref(),
        ));
    }
    checks.push(check_durability(cfg));
    checks.push(check_disk_headroom(&cfg.ops_dir, cfg.disk_threshold_gib));
    let checks = checks
        .into_iter()
        .map(|c| apply_strictness(c, cfg.strictness))
        .collect();
    DoctorReport::from_checks(checks)
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Run `cmd args…` and return trimmed stdout on a clean exit, else `None`. Used
/// for the read-only `git` / `pgrep` / `df` probes; a missing tool degrades to
/// `None` rather than an error.
fn run_capture(cmd: &str, args: &[&str]) -> Option<String> {
    let out = Command::new(cmd).args(args).output().ok()?;
    if !out.status.success() {
        return None;
    }
    let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if s.is_empty() {
        None
    } else {
        Some(s)
    }
}

fn home_dir() -> Option<String> {
    std::env::var("HOME").ok().filter(|s| !s.is_empty())
}

/// The default ops directory (`$HOME/isabelle-work`, or `./isabelle-work` when
/// `$HOME` is unset).
#[must_use]
pub fn default_ops_dir() -> PathBuf {
    match home_dir() {
        Some(h) => PathBuf::from(h).join("isabelle-work"),
        None => PathBuf::from("isabelle-work"),
    }
}

/// Render a [`DoctorReport`] as the human-readable check-by-check report plus a
/// final summary line. The caller prints this and sets the exit code from
/// [`DoctorReport::ok`].
#[must_use]
pub fn render_human(report: &DoctorReport, cfg: &DoctorConfig, build: &BuildIdentity) -> String {
    use std::fmt::Write as _;
    let mut s = String::new();
    let _ = writeln!(s, "clean mathverse isabelle-doctor — ops preflight");
    let _ = writeln!(s, "  ops dir:   {}", cfg.ops_dir.display());
    let _ = writeln!(
        s,
        "  binary:    {}",
        build.short_sha().unwrap_or_else(|| "unknown".to_string())
    );
    if let Some(c) = &cfg.corpus {
        let _ = writeln!(s, "  corpus:    {}", c.display());
    }
    if let Some(sn) = &cfg.snapshot {
        let _ = writeln!(s, "  snapshot:  {}", sn.display());
    }
    if let Some(afp) = &cfg.afp_thys {
        let _ = writeln!(s, "  afp-thys:  {}", afp.display());
    }
    if let Some(isa) = &cfg.isabelle_src {
        let _ = writeln!(s, "  isa-src:   {}", isa.display());
    }
    if cfg.strictness == Strictness::Strict {
        let _ = writeln!(s, "  mode:      strict (advisory WARNs escalate to FAIL)");
    }
    let _ = writeln!(s);
    for c in &report.checks {
        let _ = writeln!(s, "[{}] {:<17} {}", c.status.label(), c.id, c.summary);
        for item in &c.items {
            let _ = writeln!(s, "        - {item}");
        }
    }
    let verdict = if report.fail > 0 { "FAIL" } else { "OK" };
    let _ = writeln!(s);
    let _ = write!(
        s,
        "summary: {} PASS, {} WARN, {} FAIL  =>  {verdict}",
        report.pass, report.warn, report.fail
    );
    s
}

#[cfg(test)]
#[path = "isabelle_doctor_tests.rs"]
mod tests;
