// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **AFP ↔ Isabelle version-skew** ops-preflight check. Split from
//! `isabelle_doctor_checks.rs` / `isabelle_doctor_artifacts.rs` (the process and
//! storage checks) to keep each file under the size cap; it is a `mod` child of
//! [`super`].
//!
//! # The burned lesson
//!
//! An AFP `master` checkout referenced distribution theories that had been
//! renamed or removed in the installed release (`HOL-Library.Code_Target_Bit_Shifts`
//! was renamed; `HOL-Data_Structures.Define_Time_Function` was absent) — the
//! breakage only surfaced deep in a multi-hour build plan. This check catches
//! that class of skew **up front**: it scans every AFP entry's `ROOT` for
//! qualified references into a distribution session (`HOL-Library.X`,
//! `HOL-Data_Structures.X`, …), maps each to the theory file the installed
//! Isabelle distribution should carry, and reports every reference with no
//! backing file.
//!
//! It is a `WARN` by default (advisory — an operator can weigh a handful of
//! renamed theories) and escalates to `FAIL` under `--strict` (unattended/CI),
//! via [`super::STRICT_ESCALATED_CHECKS`].

use std::path::{Path, PathBuf};
use std::sync::LazyLock;

use regex::Regex;

use super::{Check, Status};

/// Matches a session-qualified distribution theory token `HOL-<Session>.<Theory>`
/// (e.g. `HOL-Library.Multiset`), the only shape a cross-session theory reference
/// takes in a ROOT. A bare `sessions` entry (`HOL-Library`, no dot) never matches,
/// so scanning the whole ROOT effectively scans its `theories` blocks. Compiled
/// once. See [`extract_qualified_hol_theories`].
static QUALIFIED_HOL_THEORY_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"HOL-[A-Za-z0-9_']+\.[A-Za-z0-9_']+")
        .expect("qualified-HOL-theory regex is a valid literal")
});

/// Depth bound for the recursive theory-file search under a session subdir
/// (distribution theories are usually flat, occasionally one level deep).
const THEORY_SEARCH_MAX_DEPTH: usize = 4;

/// Cap on how many missing-reference detail lines the check renders (the scan is
/// ~945 entries; a broken-master checkout can produce hundreds of hits).
const MAX_REPORTED_FINDINGS: usize = 20;

/// One AFP → distribution reference that resolves to no theory file under the
/// installed Isabelle — the atomic unit of a version-skew report.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct AfpSkewFinding {
    /// The AFP entry (the `thys/<Entry>` directory whose ROOT referenced it).
    pub(super) entry: String,
    /// The distribution session qualifier (`HOL-Library`, `HOL-Data_Structures`, …).
    pub(super) qualifier: String,
    /// The referenced theory's base name (`Code_Target_Bit_Shifts`, …).
    pub(super) theory: String,
    /// The primary distribution path that was expected to hold it.
    pub(super) expected: PathBuf,
}

impl AfpSkewFinding {
    /// One human report line: `<entry>: HOL-Library.X -> <path> (MISSING)`.
    fn render(&self) -> String {
        format!(
            "{}: {}.{} -> {} (MISSING)",
            self.entry,
            self.qualifier,
            self.theory,
            self.expected.display()
        )
    }
}

/// The `afp-skew` check entry point (I/O). Both inputs are optional flags; the
/// check only runs when BOTH are supplied. Every failure mode degrades to a
/// `WARN` (never a crash): a missing/one-sided input, a missing directory, or a
/// version-skew hit. Under `--strict` the `WARN` is escalated to `FAIL` by
/// [`super::apply_strictness`] (afp-skew is in [`super::STRICT_ESCALATED_CHECKS`]).
pub(super) fn check_afp_skew(afp_thys: Option<&Path>, isabelle_src: Option<&Path>) -> Check {
    let id = "afp-skew";
    let (afp, src) = match (afp_thys, isabelle_src) {
        (Some(a), Some(s)) => (a, s),
        _ => {
            return Check::new(
                id,
                Status::Warn,
                "afp-skew needs BOTH --afp-thys and --isabelle-src — skipping the AFP↔Isabelle \
                 version-skew check",
            );
        }
    };
    if !afp.is_dir() {
        return Check::new(
            id,
            Status::Warn,
            format!(
                "AFP thys dir {} does not exist / is not a directory — nothing to scan (pass a \
                 real --afp-thys)",
                afp.display()
            ),
        );
    }
    if !src.is_dir() {
        return Check::new(
            id,
            Status::Warn,
            format!(
                "Isabelle src dir {} does not exist / is not a directory — cannot resolve \
                 distribution theories (pass a real --isabelle-src, e.g. \
                 /path/to/Isabelle.app/src)",
                src.display()
            ),
        );
    }
    let (findings, entries_scanned) = scan_afp_skew(afp, src);
    evaluate_afp_skew(&findings, entries_scanned)
}

/// Scan every AFP entry (`<afp_thys>/<Entry>/ROOT`) for qualified distribution
/// theory references that have no backing file under `isabelle_src`. Returns the
/// (deduplicated, sorted) findings and the number of entries with a ROOT scanned.
fn scan_afp_skew(afp_thys: &Path, isabelle_src: &Path) -> (Vec<AfpSkewFinding>, usize) {
    let Ok(entries) = std::fs::read_dir(afp_thys) else {
        return (Vec::new(), 0);
    };
    let mut findings: Vec<AfpSkewFinding> = Vec::new();
    let mut scanned = 0usize;
    for dir in entries.flatten() {
        let entry_path = dir.path();
        if !entry_path.is_dir() {
            continue;
        }
        let root = entry_path.join("ROOT");
        let Ok(text) = std::fs::read_to_string(&root) else {
            continue; // no ROOT (or unreadable) — not an entry we can check
        };
        scanned += 1;
        let entry_name = dir.file_name().to_string_lossy().into_owned();
        for (qualifier, theory) in extract_qualified_hol_theories(&text) {
            let Some(subdir) = session_subdir(&qualifier) else {
                continue; // not a `HOL-<Session>` qualifier we can map
            };
            let base = isabelle_src.join("HOL").join(&subdir);
            if theory_file_present(&base, &theory) {
                continue;
            }
            findings.push(AfpSkewFinding {
                entry: entry_name.clone(),
                qualifier,
                theory: theory.clone(),
                expected: base.join(format!("{theory}.thy")),
            });
        }
    }
    findings.sort();
    findings.dedup();
    (findings, scanned)
}

/// The distinct (qualifier, theory) pairs referenced qualified under a `HOL-*`
/// distribution session in `root_text`, in first-seen order. Deduplicated: a ROOT
/// that lists the same theory twice yields one pair.
pub(super) fn extract_qualified_hol_theories(root_text: &str) -> Vec<(String, String)> {
    let mut pairs: Vec<(String, String)> = Vec::new();
    for m in QUALIFIED_HOL_THEORY_RE.find_iter(root_text) {
        let tok = m.as_str();
        let Some((qualifier, theory)) = tok.split_once('.') else {
            continue;
        };
        let pair = (qualifier.to_string(), theory.to_string());
        if !pairs.contains(&pair) {
            pairs.push(pair);
        }
    }
    pairs
}

/// Map a distribution session qualifier to its subdirectory under
/// `<isabelle_src>/HOL/`: the suffix after `HOL-` (`HOL-Library` → `Library`,
/// `HOL-Data_Structures` → `Data_Structures`). Returns `None` for a qualifier
/// that is not a `HOL-<Session>` distribution session (e.g. bare `HOL`, or an AFP
/// session name), which this check does not map.
pub(super) fn session_subdir(qualifier: &str) -> Option<String> {
    let sub = qualifier.strip_prefix("HOL-")?;
    if sub.is_empty() {
        return None;
    }
    Some(sub.to_string())
}

/// Whether a theory `<theory>.thy` exists under the session `base` dir — the
/// direct `base/<theory>.thy` first, then a depth-bounded recursive search (a few
/// distribution theories live one subdirectory deep), so a theory that merely
/// nested is never falsely reported missing. A `base` that does not exist yields
/// `false` (the whole session subdir is gone → the theory is genuinely absent).
fn theory_file_present(base: &Path, theory: &str) -> bool {
    let direct = base.join(format!("{theory}.thy"));
    if direct.is_file() {
        return true;
    }
    find_theory_file(base, theory, 0)
}

/// Depth-bounded recursive search for a file named `<theory>.thy` anywhere under
/// `dir`. Skips hidden directories; capped at [`THEORY_SEARCH_MAX_DEPTH`].
fn find_theory_file(dir: &Path, theory: &str, depth: usize) -> bool {
    if depth > THEORY_SEARCH_MAX_DEPTH {
        return false;
    }
    let target = format!("{theory}.thy");
    let Ok(entries) = std::fs::read_dir(dir) else {
        return false;
    };
    let mut subdirs: Vec<PathBuf> = Vec::new();
    for entry in entries.flatten() {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name.starts_with('.') {
            continue;
        }
        let path = entry.path();
        if path.is_dir() {
            subdirs.push(path);
        } else if *name == *target {
            return true;
        }
    }
    subdirs
        .iter()
        .any(|sub| find_theory_file(sub, theory, depth + 1))
}

/// Pure verdict over the scan result — factored out so it is testable with
/// synthetic findings, no filesystem needed. `PASS` when nothing is missing;
/// `WARN` (skew) otherwise, with the top [`MAX_REPORTED_FINDINGS`] detail lines.
pub(super) fn evaluate_afp_skew(findings: &[AfpSkewFinding], entries_scanned: usize) -> Check {
    let id = "afp-skew";
    if findings.is_empty() {
        return Check::new(
            id,
            Status::Pass,
            format!(
                "{} AFP {} scanned — every referenced distribution theory resolves under the \
                 installed Isabelle",
                entries_scanned,
                plural(entries_scanned, "entry", "entries")
            ),
        );
    }
    let distinct_theories = distinct_missing_theories(findings);
    let distinct_entries = distinct_entries(findings);
    let summary = format!(
        "{} missing distribution {} referenced by {} AFP {} (version skew) — the AFP checkout \
         expects theories the installed Isabelle does not carry (renamed/removed); align the AFP \
         revision to the Isabelle release before building",
        distinct_theories,
        plural(distinct_theories, "theory", "theories"),
        distinct_entries,
        plural(distinct_entries, "entry", "entries"),
    );
    let mut items: Vec<String> = findings
        .iter()
        .take(MAX_REPORTED_FINDINGS)
        .map(AfpSkewFinding::render)
        .collect();
    if findings.len() > MAX_REPORTED_FINDINGS {
        items.push(format!(
            "… and {} more (capped at {MAX_REPORTED_FINDINGS})",
            findings.len() - MAX_REPORTED_FINDINGS
        ));
    }
    Check::new(id, Status::Warn, summary).with_items(items)
}

/// The number of distinct `(qualifier, theory)` references among `findings`.
fn distinct_missing_theories(findings: &[AfpSkewFinding]) -> usize {
    let mut seen: Vec<(&str, &str)> = findings
        .iter()
        .map(|f| (f.qualifier.as_str(), f.theory.as_str()))
        .collect();
    seen.sort_unstable();
    seen.dedup();
    seen.len()
}

/// The number of distinct AFP entries among `findings`.
fn distinct_entries(findings: &[AfpSkewFinding]) -> usize {
    let mut seen: Vec<&str> = findings.iter().map(|f| f.entry.as_str()).collect();
    seen.sort_unstable();
    seen.dedup();
    seen.len()
}

/// `singular` when `n == 1`, else `plural`.
fn plural(n: usize, singular: &'static str, plural: &'static str) -> &'static str {
    if n == 1 {
        singular
    } else {
        plural
    }
}
