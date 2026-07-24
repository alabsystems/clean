// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The seven ops-preflight checks behind [`super::run_doctor`]. Each `check_*`
//! entry point returns a [`Check`]; the decision logic is factored into pure
//! `evaluate_*` / `classify_*` helpers so it is unit-testable without touching
//! the host's git repo, processes, or real snapshots (see
//! `isabelle_doctor_tests.rs`). Split out of `isabelle_doctor.rs` to keep each
//! file under the size cap.

use std::io::ErrorKind;
use std::path::{Path, PathBuf};
use std::sync::LazyLock;

use regex::Regex;

use super::super::isabelle_index;
use super::super::isabelle_pure_verify::snapshot::{self, SnapshotError, SnapshotHeaderInfo};
use super::{home_dir, run_capture, BuildIdentity, Check, DoctorConfig, Status};

/// Naive absolute-path token matcher: `/Users/…`, `$HOME/…`, `~/…` runs that
/// stop at shell/quoting delimiters. Compiled once (used across every scanned
/// script). See [`extract_path_tokens`].
static PATH_TOKEN_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r#"(?:/Users/|\$HOME/|~/)[^\s"'`;:|&<>(){}]+"#)
        .expect("path-token regex is a valid literal")
});

// ---------------------------------------------------------------------------
// Check 1: stale binary
// ---------------------------------------------------------------------------

pub(super) fn check_binary_identity(build: &BuildIdentity) -> Check {
    evaluate_binary_freshness(build, git_head_sha().as_deref(), git_newest_crates_ct())
}

/// Pure freshness verdict: the embedded build identity vs. the repo HEAD SHA and
/// the newest `crates/` commit time. Factored out so it is directly testable
/// without a git repo.
pub(super) fn evaluate_binary_freshness(
    build: &BuildIdentity,
    head_sha: Option<&str>,
    newest_crates_ct: Option<u64>,
) -> Check {
    let id = "binary-identity";
    let Some(sha) = build.git_sha.as_deref() else {
        return Check::new(
            id,
            Status::Warn,
            "binary has NO embedded build identity — cannot verify it is current; \
             rebuild with a git-aware build before a grand run",
        );
    };
    let short = build.short_sha().unwrap_or_default();
    let built_at = build
        .build_unix
        .map(|t| format!(", built {t} (unix)"))
        .unwrap_or_default();

    let mut status = Status::Pass;
    let mut items: Vec<String> = Vec::new();
    let summary = match head_sha {
        Some(head) if head == sha => format!("binary @ {short}{built_at} matches repo HEAD"),
        Some(head) => {
            status = Status::Warn;
            let head_short = &head[..head.len().min(7)];
            items.push(format!("embedded: {sha}"));
            items.push(format!("repo HEAD: {head}"));
            format!(
                "binary @ {short}{built_at} does NOT match repo HEAD {head_short} — \
                 REBUILD before a grand run"
            )
        }
        None => {
            items.push(format!("embedded: {sha}"));
            format!("binary @ {short}{built_at}; repo HEAD unavailable (not a git checkout)")
        }
    };
    // Time-based staleness: a binary older than the newest crates/ commit is
    // suspect even if the SHA happens to match (uncommitted rebuild races).
    if let (Some(built), Some(newest)) = (build.build_unix, newest_crates_ct) {
        if built < newest {
            status = status.worst(Status::Warn);
            items.push(format!(
                "binary built {built} predates newest crates/ commit {newest} \
                 (~{}h older) — likely stale",
                (newest - built) / 3600
            ));
        }
    }
    Check::new(id, status, summary).with_items(items)
}

fn git_head_sha() -> Option<String> {
    run_capture("git", &["rev-parse", "HEAD"])
}

fn git_newest_crates_ct() -> Option<u64> {
    run_capture("git", &["log", "-1", "--format=%ct", "--", "crates"])
        .and_then(|s| s.parse::<u64>().ok())
}

// ---------------------------------------------------------------------------
// Check 2: concurrent verify
// ---------------------------------------------------------------------------

/// The observable state of the verify flock.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LockState {
    /// No lock file on disk — the flock infra has not landed (degrade softly).
    Absent,
    /// Lock file present and acquirable — nobody holds it.
    Free,
    /// Lock file present and held by another process — a verify is in progress.
    Held,
    /// Lock file present but could not be probed (permissions, unusual FS).
    Unknown,
}

pub(super) fn check_verify_busy(cfg: &DoctorConfig) -> Check {
    let lock_path = cfg
        .verify_lock
        .clone()
        .unwrap_or_else(|| cfg.ops_dir.join(".clean_verify.lock"));
    let state = probe_verify_lock(&lock_path);
    let procs = scan_verify_processes();
    let holder = read_lock_holder(&lock_path);
    // A bounded SIDE-VERIFY LEASE may be running alongside the primary; report its
    // holder metadata too so the operator sees the full concurrency picture.
    let side_path = super::super::isabelle_pure_verify::verify_lock::side_lock_path_for(&lock_path);
    let side_holder = read_live_side_holder(&side_path);
    evaluate_verify_busy(
        &lock_path,
        state,
        &procs,
        holder.as_ref(),
        side_holder.as_ref(),
    )
}

/// The holder metadata recorded in a verify lockfile by
/// `VerifyLock::acquire` (`pid=… started=… label=…`). Every field is optional so
/// an empty or legacy lockfile (written before this record existed) degrades to
/// "unknown" instead of failing the probe.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct LockHolder {
    /// The holder process id, if the record carried a parseable `pid=`.
    pub(super) pid: Option<u32>,
    /// The Unix start time (seconds), if the record carried a parseable `started=`.
    pub(super) started_unix: Option<u64>,
    /// The human label (e.g. `release grand`), if a non-empty `label=` was present.
    pub(super) label: Option<String>,
}

impl LockHolder {
    /// TRUE when nothing identifiable was parsed — a legacy or empty lockfile.
    pub(super) fn is_blank(&self) -> bool {
        self.pid.is_none() && self.started_unix.is_none() && self.label.is_none()
    }

    /// Human phrase for the verify-busy report, e.g.
    /// `held by PID 12345 since 1700000000 (release grand)`. Missing parts are
    /// omitted so a partial (legacy) record still renders sensibly.
    pub(super) fn describe(&self) -> String {
        let mut s = match self.pid {
            Some(pid) => format!("held by PID {pid}"),
            None => "held by an unknown process".to_string(),
        };
        if let Some(started) = self.started_unix {
            s.push_str(&format!(" since {started} (unix)"));
        }
        if let Some(label) = &self.label {
            s.push_str(&format!(" ({label})"));
        }
        s
    }
}

/// Read + parse the verify lockfile's holder record; `None` when the file is
/// absent/unreadable or carries no identifiable holder (legacy/empty).
fn read_lock_holder(path: &Path) -> Option<LockHolder> {
    let content = std::fs::read_to_string(path).ok()?;
    let holder = parse_lock_holder(&content);
    (!holder.is_blank()).then_some(holder)
}

/// Read + parse the SIDE-verify lease sentinel's holder, keeping it ONLY when it
/// names a LIVE process. A dead-holder sentinel is a stale leftover (a crashed side
/// job), not a running side verify, so it is suppressed from the report. `None`
/// when the sentinel is absent, blank/legacy, or stale.
fn read_live_side_holder(path: &Path) -> Option<LockHolder> {
    let content = std::fs::read_to_string(path).ok()?;
    let holder = parse_lock_holder(&content);
    if holder.is_blank() {
        return None;
    }
    if let Some(pid) = holder.pid {
        if !super::super::isabelle_pure_verify::verify_lock::holder_pid_alive(pid) {
            return None;
        }
    }
    Some(holder)
}

/// Parse a `pid=<n> started=<n> label=<text>` lockfile record. `label=` captures
/// the remainder of the line (so the label may contain spaces); the scalar keys
/// are read from the prefix. Pure and unit-tested; unparseable fields become
/// `None` rather than an error.
pub(super) fn parse_lock_holder(content: &str) -> LockHolder {
    let line = content.lines().find(|l| !l.trim().is_empty()).unwrap_or("");
    let (prefix, label) = match line.find("label=") {
        Some(i) => (
            &line[..i],
            Some(line[i + "label=".len()..].trim().to_string()),
        ),
        None => (line, None),
    };
    let mut holder = LockHolder {
        label: label.filter(|s| !s.is_empty()),
        ..LockHolder::default()
    };
    for tok in prefix.split_whitespace() {
        if let Some(v) = tok.strip_prefix("pid=") {
            holder.pid = v.parse().ok();
        } else if let Some(v) = tok.strip_prefix("started=") {
            holder.started_unix = v.parse().ok();
        }
    }
    holder
}

/// Non-destructively probe the flock at `path`: existence, then a non-blocking
/// exclusive acquire (immediately released). Never takes a hard dependency on
/// the lock's producer — a missing file is [`LockState::Absent`], not an error.
pub(super) fn probe_verify_lock(path: &Path) -> LockState {
    if !path.exists() {
        return LockState::Absent;
    }
    let Ok(file) = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(path)
    else {
        return LockState::Unknown;
    };
    let mut lock = fd_lock::RwLock::new(file);
    // Bind the guard-bearing `Result` to a local and release it (`drop`) before
    // `lock` falls out of scope, so the borrow of `lock` never outlives it.
    let attempt = lock.try_write();
    let state = match &attempt {
        Ok(_guard) => LockState::Free,
        Err(e) if e.kind() == ErrorKind::WouldBlock => LockState::Held,
        Err(_) => LockState::Unknown,
    };
    drop(attempt);
    state
}

/// The verify/import command lines currently running (best-effort via `pgrep`).
fn scan_verify_processes() -> Vec<String> {
    const PATTERNS: &[&str] = &[
        "isabelle_scale_run",
        "isabelle-import",
        "isabelle_pure_verify",
        "verify-kernel",
    ];
    let me = std::process::id();
    let mut hits: Vec<String> = Vec::new();
    for pat in PATTERNS {
        if let Some(out) = run_capture("pgrep", &["-fl", pat]) {
            collect_pgrep_hits(&out, me, &mut hits);
        }
    }
    hits
}

/// Parse `pgrep -fl` output into one entry per process, appending non-self,
/// deduplicated, length-capped entries into `hits`. A command whose arguments
/// contain literal newlines (e.g. an inline monitoring `eval` script) spans
/// several physical lines; those continuation lines are coalesced back onto the
/// preceding PID-led entry so one process counts once. Pure and unit-tested.
pub(super) fn collect_pgrep_hits(output: &str, me: u32, hits: &mut Vec<String>) {
    let mut entries: Vec<String> = Vec::new();
    for line in output.lines() {
        if line_starts_with_pid(line) {
            entries.push(line.trim().to_string());
        } else if let Some(last) = entries.last_mut() {
            let cont = line.trim();
            if !cont.is_empty() {
                last.push(' ');
                last.push_str(cont);
            }
        }
    }
    for entry in entries {
        let pid = entry
            .split_whitespace()
            .next()
            .and_then(|p| p.parse::<u32>().ok());
        if pid == Some(me) {
            continue;
        }
        let capped = truncate_str(&entry, 180);
        if !hits.iter().any(|h| h == &capped) {
            hits.push(capped);
        }
    }
}

/// TRUE when `line`'s first whitespace-delimited token is all ASCII digits — the
/// shape of a `pgrep -fl` entry's leading PID (vs. an embedded-newline
/// continuation line).
fn line_starts_with_pid(line: &str) -> bool {
    match line.split_whitespace().next() {
        Some(tok) => !tok.is_empty() && tok.bytes().all(|b| b.is_ascii_digit()),
        None => false,
    }
}

/// Truncate `s` to at most `max` characters (char-boundary safe), appending an
/// ellipsis when clipped.
pub(super) fn truncate_str(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        return s.to_string();
    }
    let mut out: String = s.chars().take(max).collect();
    out.push('…');
    out
}

pub(super) fn evaluate_verify_busy(
    lock_path: &Path,
    state: LockState,
    procs: &[String],
    holder: Option<&LockHolder>,
    side_holder: Option<&LockHolder>,
) -> Check {
    let id = "verify-busy";
    let mut check = if !procs.is_empty() {
        let mut check = Check::new(
            id,
            Status::Fail,
            format!(
                "VERIFY BUSY: {} verify/import process(es) running — an UNGUARDED concurrent \
                 verify silently corrupts KV numbers; wait for it or stop it before importing",
                procs.len()
            ),
        )
        .with_items(procs.to_vec());
        if let Some(h) = holder.filter(|h| !h.is_blank()) {
            check.items.push(format!("lock {}", h.describe()));
        }
        check
    } else {
        match state {
            LockState::Held => {
                let who = holder
                    .filter(|h| !h.is_blank())
                    .map(|h| h.describe())
                    .unwrap_or_else(|| "held by another process".to_string());
                Check::new(
                    id,
                    Status::Fail,
                    format!(
                        "VERIFY BUSY: lock {} is HELD ({who}) — a verify is in progress",
                        lock_path.display()
                    ),
                )
            }
            LockState::Free => Check::new(
                id,
                Status::Pass,
                "no verify running (lock free, no verify processes)",
            ),
            LockState::Absent => Check::new(
                id,
                Status::Pass,
                "no verify running (no lock file present, no verify processes)",
            ),
            LockState::Unknown => Check::new(
                id,
                Status::Warn,
                format!(
                    "could not probe verify lock {} — proceed only if you are certain no \
                     verify is running",
                    lock_path.display()
                ),
            ),
        }
    };
    // A bounded SIDE-VERIFY LEASE running alongside the primary is the SANCTIONED
    // concurrent mode (RAM-gated, verdict-safe), not the unguarded collapse the hard
    // FAIL exists for. Report its holder metadata; if nothing else flagged the
    // check, surface it as a WARN so a pre-grand operator knows a bounded verify is
    // live (it competes for RAM), without escalating an existing FAIL/WARN.
    if let Some(sh) = side_holder.filter(|h| !h.is_blank()) {
        check
            .items
            .push(format!("side-verify lease {}", sh.describe()));
        if check.status == Status::Pass {
            check.status = Status::Warn;
            check.summary = format!(
                "a bounded SIDE-VERIFY LEASE is active ({}) — sanctioned + RAM-gated, but it \
                 competes for RAM; no primary verify group is running",
                sh.describe()
            );
        }
    }
    check
}

// ---------------------------------------------------------------------------
// Check 3: dead script references
// ---------------------------------------------------------------------------

pub(super) fn check_dead_script_refs(ops_dir: &Path) -> Check {
    let id = "dead-script-refs";
    if !ops_dir.exists() {
        return Check::new(
            id,
            Status::Warn,
            format!(
                "ops dir {} does not exist — nothing to scan (create it or pass --ops-dir)",
                ops_dir.display()
            ),
        );
    }
    let mut scripts: Vec<PathBuf> = Vec::new();
    collect_shell_scripts(ops_dir, 0, &mut scripts);

    let home = home_dir();
    let mut broken: Vec<String> = Vec::new();
    let mut hard = false;
    for script in &scripts {
        let Ok(text) = std::fs::read_to_string(script) else {
            continue;
        };
        for token in extract_referenced_tokens(&text) {
            let Some(resolved) = resolve_token(&token, home.as_deref()) else {
                continue;
            };
            if resolved.exists() {
                continue;
            }
            let worktree = token.contains(".claude/worktrees");
            let launcher = token.ends_with(".sh");
            if worktree || launcher {
                hard = true;
            }
            broken.push(format!(
                "{} -> {} (MISSING{})",
                script.display(),
                token,
                if worktree { ", .claude/worktrees" } else { "" }
            ));
        }
    }

    if broken.is_empty() {
        return Check::new(
            id,
            Status::Pass,
            format!(
                "{} script(s) scanned — every referenced absolute path exists",
                scripts.len()
            ),
        );
    }
    let status = if hard { Status::Fail } else { Status::Warn };
    Check::new(
        id,
        status,
        format!(
            "{} broken path reference(s) across {} script(s) — a dead launcher fails at \
             fire time",
            broken.len(),
            scripts.len()
        ),
    )
    .with_items(broken)
}

/// Depth-bounded recursive collection of `*.sh` files (skips hidden dirs and
/// caps the tree so an accidental huge `--ops-dir` cannot stall the doctor).
/// `*.app` bundle trees are skipped: they are vendored third-party content
/// (e.g. an embedded `Isabelle2025-2.app/contrib/…`), not ops automation, and
/// their scripts' path references are irrelevant to this preflight.
fn collect_shell_scripts(dir: &Path, depth: usize, out: &mut Vec<PathBuf>) {
    const MAX_DEPTH: usize = 6;
    const MAX_FILES: usize = 2000;
    if depth > MAX_DEPTH || out.len() >= MAX_FILES {
        return;
    }
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name.starts_with('.') {
            continue; // skip .git, .claude, dotfiles
        }
        if path.is_dir() {
            if name.ends_with(".app") {
                continue; // vendored *.app bundle tree — not ops automation
            }
            collect_shell_scripts(&path, depth + 1, out);
        } else if path.extension().is_some_and(|e| e == "sh") {
            out.push(path);
        }
        if out.len() >= MAX_FILES {
            return;
        }
    }
}

/// Naive path-token extraction: `/Users/…`, `$HOME/…`, and `~/…` runs that look
/// like file references (a `.`-bearing final component). Stops at shell/quoting
/// delimiters. Deliberately conservative to keep false positives low.
pub(super) fn extract_path_tokens(text: &str) -> Vec<String> {
    let mut tokens: Vec<String> = Vec::new();
    for cap in PATH_TOKEN_RE.find_iter(text) {
        if let Some(tok) = normalize_path_token(cap.as_str()) {
            if !tokens.contains(&tok) {
                tokens.push(tok);
            }
        }
    }
    tokens
}

/// The path tokens a script DEPENDS ON: [`extract_path_tokens`] minus the paths
/// the script itself CREATES (redirection targets and `mkdir -p` arguments).
/// Those are outputs, not dependencies, so flagging them as "missing" is a false
/// positive — the live run flagged `release_grand.sh`'s own `> main_v3_release.snap`.
pub(super) fn extract_referenced_tokens(text: &str) -> Vec<String> {
    let mut tokens: Vec<String> = Vec::new();
    for m in PATH_TOKEN_RE.find_iter(text) {
        let Some(tok) = normalize_path_token(m.as_str()) else {
            continue;
        };
        if is_created_path(text, m.start()) {
            continue; // an output the script writes, not a dependency
        }
        if !tokens.contains(&tok) {
            tokens.push(tok);
        }
    }
    tokens
}

/// Normalize one raw regex match into a file-like path token, or `None` when it
/// is too short or has no extension on its final component (a directory, not a
/// file reference). Shared by [`extract_path_tokens`] and
/// [`extract_referenced_tokens`].
fn normalize_path_token(raw: &str) -> Option<String> {
    let tok = raw.trim_end_matches(['/', '.', ',']).to_string();
    if tok.len() < 4 {
        return None;
    }
    // Require a file-like final component (has an extension), so pure output
    // directories are not mistaken for missing files.
    let last = tok.rsplit('/').next().unwrap_or("");
    if !last.contains('.') {
        return None;
    }
    Some(tok)
}

/// Heuristic: is the path token starting at byte offset `start` an OUTPUT the
/// script writes, rather than a dependency it reads? TRUE when the nearest
/// non-space character before it is a `>` (any redirection — `>`, `>>`, `2>`,
/// `&>`, optionally with a quoted target), or when it is the argument of a
/// `mkdir` in the same command segment.
fn is_created_path(text: &str, start: usize) -> bool {
    let before = &text[..start];
    // Redirection target: the token may be quoted (`> "$HOME/x"`), so strip a
    // trailing quote before checking for the operator.
    let prefix = before.trim_end().trim_end_matches(['"', '\'']);
    if prefix.trim_end().ends_with('>') {
        return true;
    }
    // `mkdir -p <dir>`: only within the token's own command segment, so a later
    // dependency after `;`/`&&`/`|` on a mkdir line is NOT suppressed.
    let seg_start = before
        .rfind(['\n', ';', '&', '|', '('])
        .map_or(0, |i| i + 1);
    before[seg_start..].contains("mkdir")
}

/// Resolve a `$HOME`/`~`-prefixed or absolute token to a concrete path, or
/// `None` when it still contains an unresolved `$VAR` (cannot be checked).
pub(super) fn resolve_token(token: &str, home: Option<&str>) -> Option<PathBuf> {
    let expanded = if let Some(rest) = token.strip_prefix("$HOME/") {
        format!("{}/{rest}", home?)
    } else if let Some(rest) = token.strip_prefix("~/") {
        format!("{}/{rest}", home?)
    } else {
        token.to_string()
    };
    if expanded.contains('$') {
        return None; // unresolved variable — do not guess
    }
    Some(PathBuf::from(expanded))
}
