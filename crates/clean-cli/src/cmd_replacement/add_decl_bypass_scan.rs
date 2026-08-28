// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `add_decl_structural` / `add_decl_unchecked` bypass, MEASURED FROM THE
//! SOURCE TREE, for the Rust half of the DENY_SORRY ratchet lane.
//!
//! **G7 (2026-08-27) — what this closes.** The lane
//! `unchecked_decl_ratchet_accounted` is written into
//! `reports/deny-sorry-launch-evidence.json` by TWO producers, and until this
//! module only ONE of them performed the measurement its name claims:
//!
//! * `scripts/deny_sorry_gate.sh` calls `scripts/check_add_decl_ratchet.py` —
//!   its `--selftest` arms, then a full re-derivation of every production call
//!   site from `crates/**/*.rs` — and prints `PASS (source-measured; …)`.
//! * `clean replacement trust-core-evidence --deny-sorry`
//!   ([`generate_deny_sorry_launch_evidence_with`]) ran
//!   [`validate_unchecked_decl_ratchet`] and
//!   [`validate_unchecked_decl_ratchet_closed`], both of which take
//!   `&UncheckedDeclRatchetArtifact` and NOTHING ELSE. By their signatures they
//!   cannot see a planted bypass. The lane was nevertheless minted
//!   `status: "passed", matched_expected_count: true`, and that Rust command —
//!   not the shell gate — is the evidence command cited by the **Green**
//!   `fallback-denial` scorecard row.
//!
//! So the green path was the one that did not measure. This module is the
//! measurement, run in-process by the Rust producer, so the two producers of
//! one lane id now answer the same question.
//!
//! **Scope, mirrored deliberately from the Python scanner** so the two cannot
//! disagree about the same tree: dot-call form only
//! (`<recv>.add_decl_{unchecked,structural}(`), over `crates/**/*.rs`, with test
//! FILES excluded by path and inline `#[cfg(test)]` items excluded by the token
//! lexer. Method definitions (`fn add_decl_*`), `Environment::add_decl_*(…)`
//! associated-call delegations, doc comments and string literals are all out of
//! scope — the lexer never emits them as the `.`/ident/`(` triple this matches,
//! which is the R9 property: a `// SOUNDNESS:` comment naming the call it
//! promises not to make must count ZERO, or the gate moves the wrong way on a
//! genuine fix.
//!
//! One known and deliberate difference from the Python scanner, in the safe
//! direction: it matches `\.add_decl_\w+\s*\(` within a single LINE, so a call
//! whose `(` sits on the next line is invisible to it. Tokens have no lines, so
//! this scan sees that shape. The two agree exactly on today's tree (both
//! measure `structural=0, unchecked=1`), and the arm
//! `real_tree_measures_exactly_the_one_sanctioned_add_decl_bypass` is what
//! keeps that a measurement rather than an assumption.
//!
//! The allowlist is [`SANCTIONED_ADD_DECL_BYPASS_SITES`] — the one that already
//! lives in code and is pinned against the Python scanner's `SANCTIONED_SITES`
//! by `sanctioned_add_decl_sites_match_the_source_scanner`. There is no second
//! allowlist here.

use super::sorry_bypass_syntax::{cfg_test_item_ranges, lex_rust_tokens};
use super::*;

/// A `// SOUNDNESS:` comment must sit within this many lines above the call.
/// Same window as `SOUNDNESS_WINDOW` in `scripts/check_add_decl_ratchet.py`.
pub(crate) const ADD_DECL_SOUNDNESS_WINDOW: usize = 40;

const ADD_DECL_BYPASS_METHODS: [&str; 2] = ["add_decl_unchecked", "add_decl_structural"];

/// One production `add_decl_*` bypass call site, as measured from the tree.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct MeasuredAddDeclBypass {
    pub(crate) file: String,
    pub(crate) line: usize,
    pub(crate) method: String,
}

/// True for test FILES. Mirrors `is_test_path` in
/// `scripts/check_add_decl_ratchet.py` exactly — including its final
/// `"test" in name` clause, which subsumes the regex before it. Mirroring
/// rather than tightening is deliberate: a Rust scan that classified MORE files
/// as production than the Python one would go red on a tree the registered
/// gate calls clean, and the first fix anyone reached for would be to switch
/// one of them off.
fn is_add_decl_test_path(relative_path: &str) -> bool {
    let mut components = relative_path.split('/');
    let name = relative_path.rsplit('/').next().unwrap_or(relative_path);
    components.any(|part| part == "tests" || part == "tests2") || name.contains("test")
}

/// Production `add_decl_*` dot-call sites in one file's source.
///
/// Returns one-based line numbers alongside the method name. Errors are fail
/// closed: an unlexable file is never silently treated as clean.
pub(crate) fn add_decl_bypass_lines_in_production(
    source: &str,
) -> Result<Vec<(usize, String)>, String> {
    let tokens = lex_rust_tokens(source)?;
    let test_ranges = cfg_test_item_ranges(&tokens);
    let production: Vec<_> = tokens
        .into_iter()
        .filter(|token| {
            !test_ranges
                .iter()
                .any(|(start, end)| token.start >= *start && token.start < *end)
        })
        .collect();

    let mut hits = Vec::new();
    for index in 0..production.len() {
        if !production[index].is_punct(b'.') {
            continue;
        }
        let Some(method) = ADD_DECL_BYPASS_METHODS.iter().find(|method| {
            production
                .get(index + 1)
                .is_some_and(|token| token.is_ident(method))
        }) else {
            continue;
        };
        if !production
            .get(index + 2)
            .is_some_and(|token| token.is_punct(b'('))
        {
            continue;
        }
        let offset = production[index].start;
        let line = 1 + source.as_bytes()[..offset]
            .iter()
            .filter(|byte| **byte == b'\n')
            .count();
        hits.push((line, (*method).to_string()));
    }
    hits.sort_unstable();
    hits.dedup();
    Ok(hits)
}

/// Re-derive every production `add_decl_*` bypass call site under
/// `<repo_root>/crates`.
pub(crate) fn measure_add_decl_bypass_sites(
    repo_root: &Path,
) -> Result<Vec<MeasuredAddDeclBypass>, String> {
    let crates_root = repo_root.join("crates");
    let mut measured = Vec::new();
    for entry in WalkDir::new(&crates_root)
        .into_iter()
        .filter_map(Result::ok)
    {
        if !entry.file_type().is_file()
            || entry.path().extension().and_then(|ext| ext.to_str()) != Some("rs")
        {
            continue;
        }
        let relative_path = entry
            .path()
            .strip_prefix(repo_root)
            .unwrap_or(entry.path())
            .to_string_lossy()
            .replace('\\', "/");
        if is_add_decl_test_path(&relative_path) {
            continue;
        }
        let source = fs::read_to_string(entry.path()).map_err(|error| {
            format!("failed to read {relative_path} for the add_decl bypass scan: {error}")
        })?;
        for (line, method) in add_decl_bypass_lines_in_production(&source).map_err(|message| {
            format!("failed to lex {relative_path} for the add_decl bypass scan: {message}")
        })? {
            measured.push(MeasuredAddDeclBypass {
                file: relative_path.clone(),
                line,
                method,
            });
        }
    }
    measured.sort();
    Ok(measured)
}

/// True when a `// SOUNDNESS:`-style line comment sits within
/// [`ADD_DECL_SOUNDNESS_WINDOW`] lines above the call (the call's own line
/// counts). Reads the RAW lines on purpose: the thing being looked for IS a
/// comment. Nothing about the verdict on a *call* is decided here.
fn has_soundness_comment(source: &str, line: usize) -> bool {
    let lines: Vec<&str> = source.lines().collect();
    let end = line.min(lines.len());
    let start = end.saturating_sub(ADD_DECL_SOUNDNESS_WINDOW + 1);
    lines[start..end].iter().any(|text| {
        text.split_once("//")
            .is_some_and(|(_, comment)| mentions_soundness(comment))
    })
}

fn mentions_soundness(comment: &str) -> bool {
    let bytes = comment.as_bytes();
    let mut from = 0usize;
    while let Some(found) = comment[from..].find("SOUNDNESS") {
        let at = from + found;
        let before_ok = at == 0 || !is_word_byte(bytes[at - 1]);
        let after = at + "SOUNDNESS".len();
        let after_ok = after >= bytes.len() || !is_word_byte(bytes[after]);
        if before_ok && after_ok {
            return true;
        }
        from = at + 1;
    }
    false
}

fn is_word_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// THE MEASUREMENT the `unchecked_decl_ratchet_accounted` lane names.
///
/// Fails closed unless the SOURCE TREE agrees with
/// `data/unchecked_decl_ratchet.json`: every production bypass is accounted for
/// by a `*_production_sites` row, carries its `// SOUNDNESS:` comment, is at or
/// under its [`SANCTIONED_ADD_DECL_BYPASS_SITES`] cap, and every accounted row
/// still names a live call site.
///
/// Call this *after* [`validate_unchecked_decl_ratchet_closed`], which owns the
/// artifact-side half (rows sanctioned, counts accounted). This is the half no
/// Rust gate performed.
pub(crate) fn validate_add_decl_bypass_sites_measured(
    repo_root: &Path,
    ratchet: &UncheckedDeclRatchetArtifact,
) -> Result<Vec<MeasuredAddDeclBypass>, String> {
    let measured = measure_add_decl_bypass_sites(repo_root)?;

    let accounted: BTreeSet<(String, String)> = ratchet
        .add_decl_structural_production_sites
        .iter()
        .chain(ratchet.add_decl_unchecked_production_sites.iter())
        .map(|site| (site.file.clone(), site.method.clone()))
        .collect();

    let unaccounted: Vec<String> = measured
        .iter()
        .filter(|site| !accounted.contains(&(site.file.clone(), site.method.clone())))
        .map(|site| format!("{}:{} {}", site.file, site.line, site.method))
        .collect();
    if !unaccounted.is_empty() {
        return Err(format!(
            "the source tree carries unaccounted add_decl_* bypass call site(s): {}. \
             A declaration registered without type checking needs a // SOUNDNESS: comment \
             at the call AND a {UNCHECKED_DECL_RATCHET_PATH} \
             *_production_sites row; an artifact row alone cannot legalise it.",
            unaccounted.join(", ")
        ));
    }

    for site in &measured {
        let source = fs::read_to_string(repo_root.join(&site.file))
            .map_err(|error| format!("failed to re-read {} : {error}", site.file))?;
        if !has_soundness_comment(&source, site.line) {
            return Err(format!(
                "{}:{} {} is accounted for in {UNCHECKED_DECL_RATCHET_PATH} but carries no \
                 // SOUNDNESS: comment within {ADD_DECL_SOUNDNESS_WINDOW} lines above the call",
                site.file, site.line, site.method
            ));
        }
    }

    let mut per_site: BTreeMap<(String, String), u32> = BTreeMap::new();
    for site in &measured {
        *per_site
            .entry((site.file.clone(), site.method.clone()))
            .or_insert(0) += 1;
    }
    for ((file, method), seen) in &per_site {
        let cap = SANCTIONED_ADD_DECL_BYPASS_SITES
            .iter()
            .find(|(f, m, _)| f == file && m == method)
            .map(|(_, _, cap)| *cap);
        match cap {
            None => {
                return Err(format!(
                    "the source tree carries {seen} production `{method}` call site(s) in \
                     `{file}`, which is NOT in SANCTIONED_ADD_DECL_BYPASS_SITES. Sanction it in \
                     code, with its argument, or remove the bypass."
                ));
            }
            Some(cap) if *seen > cap => {
                return Err(format!(
                    "`{file}` / `{method}` has {seen} production call site(s) in the source tree \
                     but the sanctioned cap is {cap}. A sanctioned bypass does not license \
                     further copies of itself."
                ));
            }
            Some(_) => {}
        }
    }

    let live: BTreeSet<(String, String)> = per_site.keys().cloned().collect();
    let stale: Vec<String> = accounted
        .difference(&live)
        .map(|(file, method)| format!("{file} / {method}"))
        .collect();
    if !stale.is_empty() {
        return Err(format!(
            "{UNCHECKED_DECL_RATCHET_PATH} records production site row(s) with no live call site \
             in the source tree: {}. If the bypass was removed, remove the row — the ratchet only \
             goes down.",
            stale.join(", ")
        ));
    }

    let mut measured_counts: BTreeMap<&str, u32> = BTreeMap::new();
    for site in &measured {
        *measured_counts.entry(site.method.as_str()).or_insert(0) += 1;
    }
    for (method, declared) in [
        ("add_decl_structural", ratchet.add_decl_structural_count),
        ("add_decl_unchecked", ratchet.add_decl_unchecked_count),
    ] {
        let seen = measured_counts.get(method).copied().unwrap_or(0);
        if seen > declared {
            return Err(format!(
                "the source tree has {seen} production `{method}` call site(s) but \
                 {UNCHECKED_DECL_RATCHET_PATH} declares {declared}. A new bypass must be \
                 justified and ratcheted, never absorbed."
            ));
        }
    }

    Ok(measured)
}
