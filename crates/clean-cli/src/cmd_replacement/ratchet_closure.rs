// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What it means for `data/unchecked_decl_ratchet.json` to be CLOSED.
//!
//! **G6 (2026-08-23) — this used to mean "both counts are the literal 0", and
//! that test could only ever pass while the artifact lied.** The tree has always
//! had exactly one production `add_decl_unchecked` call site — the
//! `mm_axiom_only` proof-drop arm of `Environment::add_decl`, the Metamath
//! two-pass PASS-1 — and no gate in the repo read a line of Rust to notice
//! (`scripts/check_add_decl_ratchet.py`, the source scanner, landed 2026-08-22
//! and measured it on its first run). The count was corrected 0 → 1, which is a
//! correction and not a ratchet regression: no bypass was added.
//!
//! So "closed" now asks the question the zero was standing in for. Every counted
//! bypass occurrence must be a **sanctioned** site — named in
//! [`SANCTIONED_ADD_DECL_BYPASS_SITES`], which lives in code — at or under its
//! pinned cap, with the declared counts accounting for exactly those
//! occurrences and nothing else. A row written into the artifact can no longer
//! legalise a bypass, and a sanctioned bypass cannot quietly gain a second call
//! site.
//!
//! The allowlist is mirrored in `scripts/check_add_decl_ratchet.py`
//! (`SANCTIONED_SITES`), which is the half that re-derives the sites from
//! `crates/**/*.rs`; `sanctioned_add_decl_sites_match_the_source_scanner` in the
//! test module fails closed if the two ever drift.

use super::*;

/// A ratchet row is honoured only for a `(file, method, max occurrences)` named
/// here. Mirrored by `SANCTIONED_SITES` in `scripts/check_add_decl_ratchet.py`.
///
/// The single entry is the Metamath two-pass PASS-1 proof-drop. It is sound
/// because three independent in-tree mechanisms stand between it and any
/// exported verdict: it fails closed outside the `MmAxiomOnlyGuard` sentinel,
/// PASS-2 re-adds every in-range theorem through the CHECKED `add_decl`, and
/// `mm_gate` drops any verified theorem whose transitive `$p` closure is not
/// itself verified. The full argument is the `trust` prose on the site's row in
/// `data/unchecked_decl_ratchet.json`.
pub(crate) const SANCTIONED_ADD_DECL_BYPASS_SITES: &[(&str, &str, u32)] = &[(
    "crates/clean-kernel/src/env/decl_add.rs",
    "add_decl_unchecked",
    1,
)];

fn sanctioned_cap(file: &str, method: &str) -> Option<u32> {
    SANCTIONED_ADD_DECL_BYPASS_SITES
        .iter()
        .find(|(f, m, _)| *f == file && *m == method)
        .map(|(_, _, cap)| *cap)
}

/// Fail closed unless every counted `add_decl_*` bypass is sanctioned, capped
/// and fully accounted by the declared counts.
///
/// Call this *after* [`validate_unchecked_decl_ratchet`], which owns the
/// artifact's internal shape (methods, non-empty trust prose, row/count sums).
pub(crate) fn validate_unchecked_decl_ratchet_closed(
    ratchet: &UncheckedDeclRatchetArtifact,
) -> Result<(), String> {
    // Legacy `files` rows are file-granularity totals with no site identity, so
    // they can never be matched against the allowlist. They must stay empty.
    if !ratchet.files.is_empty() {
        return Err(format!(
            "current ratchet is not closed: {} legacy `files` row(s) carry no site identity \
             and cannot be sanctioned",
            ratchet.files.len()
        ));
    }

    let mut structural_sanctioned: u32 = 0;
    let mut unchecked_sanctioned: u32 = 0;
    for (sites, method) in [
        (
            &ratchet.add_decl_structural_production_sites,
            "add_decl_structural",
        ),
        (
            &ratchet.add_decl_unchecked_production_sites,
            "add_decl_unchecked",
        ),
    ] {
        for site in sites {
            let occurrences = site.occurrences.unwrap_or(1);
            let Some(cap) = sanctioned_cap(&site.file, &site.method) else {
                return Err(format!(
                    "current ratchet is not closed: `{}` / `{}` is counted but is not in \
                     SANCTIONED_ADD_DECL_BYPASS_SITES. A bypass cannot be legalised by an \
                     artifact row; sanction it in code, with its argument, or remove it.",
                    site.file, site.method
                ));
            };
            if occurrences > cap {
                return Err(format!(
                    "current ratchet is not closed: `{}` / `{}` counts {occurrences} \
                     occurrences, sanctioned cap is {cap}",
                    site.file, site.method
                ));
            }
            if method == "add_decl_structural" {
                structural_sanctioned = structural_sanctioned.saturating_add(occurrences);
            } else {
                unchecked_sanctioned = unchecked_sanctioned.saturating_add(occurrences);
            }
        }
    }

    if ratchet.add_decl_structural_count != structural_sanctioned
        || ratchet.add_decl_unchecked_count != unchecked_sanctioned
    {
        return Err(format!(
            "current ratchet is not closed: declared counts {}/{} but sanctioned production \
             sites account for {structural_sanctioned}/{unchecked_sanctioned}",
            ratchet.add_decl_structural_count, ratchet.add_decl_unchecked_count
        ));
    }

    Ok(())
}
