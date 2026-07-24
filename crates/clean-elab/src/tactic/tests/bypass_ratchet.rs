// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bypass ratchet tests for close_goal and metas.assign (#2202, #2187).
//!
//! These tests scan tactic source files and count bypass sites — places where
//! proof terms are assigned to goal metavariables without type-checking.
//!
//! Two bypass pathways exist:
//! 1. `metas.assign(` — Direct metavariable assignment, completely bypassing
//!    both `close_goal_unchecked` and `close_goal`.
//! 2. `.close_goal_unchecked(` — The unchecked method that assigns without
//!    type-checking the proof term.
//!
//! The ratchet prevents new bypass sites from being added. When existing sites
//! are migrated to `close_goal` (the checked version), tighten the ratchet values downward.

use std::path::{Path, PathBuf};

use crate::tactic::core::{
    CLOSE_GOAL_UNCHECKED_RATCHET, ELAB_SORRY_SOURCE_SITE_RATCHET,
    LOCAL_DECL_REWRITE_SOURCE_SITE_RATCHET, METAS_ASSIGN_BYPASS_RATCHET,
    TRUSTED_ARITH_SOURCE_SITE_RATCHET, TRUSTED_AY_CALL_SITE_RATCHET,
};
use crate::test_support::source_scan::{
    cfg_test_mod_line_ranges, code_before_line_comment, collect_rust_source_files,
    line_is_inside_cfg_test_mod, DEFAULT_PRODUCTION_RULES,
};

/// Count occurrences of a pattern in source files, excluding files whose path
/// contains the given substring. Uses path containment to handle both single-file
/// and directory-module layouts — e.g., exclude `tactic/core/` matches both
/// the old `tactic/core.rs` and the split `tactic/core/mod.rs`, `tactic/core/goal_ops.rs`.
///
/// Skips lines inside `#[cfg(test)] mod` blocks — inline test modules are
/// not production code. Distinguishes test modules from conditional imports
/// (`#[cfg(test)] use ...`). (#2533 regression)
fn count_pattern_in_files(files: &[PathBuf], pattern: &str, exclude_path_part: &str) -> usize {
    let mut total = 0;
    for file in files {
        let path_str = file.to_str().unwrap();
        if path_str.contains(exclude_path_part) {
            continue;
        }
        let content = std::fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("failed to read {}: {}", file.display(), e));
        let test_mod_ranges = cfg_test_mod_line_ranges(&content);
        for (idx, line) in content.lines().enumerate() {
            if line_is_inside_cfg_test_mod(&test_mod_ranges, idx) {
                continue;
            }
            total += line.matches(pattern).count();
        }
    }
    total
}

/// Count occurrences of a pattern while excluding helper paths, imports, and
/// line comments that would otherwise self-count the ratchet.
///
/// Skips lines inside `#[cfg(test)] mod` blocks — inline test modules are
/// not production code. Distinguishes test modules from conditional imports
/// (`#[cfg(test)] use ...`). (#2533 regression)
fn count_pattern_in_files_excluding_imports(
    files: &[PathBuf],
    pattern: &str,
    excluded_path_parts: &[&str],
) -> usize {
    let mut total = 0;
    for file in files {
        let path_str = file.to_str().unwrap();
        if excluded_path_parts
            .iter()
            .any(|part| path_str.contains(part))
        {
            continue;
        }
        let content = std::fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("failed to read {}: {}", file.display(), e));
        let test_mod_ranges = cfg_test_mod_line_ranges(&content);
        for (idx, line) in content.lines().enumerate() {
            if line_is_inside_cfg_test_mod(&test_mod_ranges, idx) {
                continue;
            }
            let code = code_before_line_comment(line);
            let trimmed = code.trim_start();
            if trimmed.is_empty() {
                continue;
            }
            if trimmed.starts_with("use ")
                || trimmed.starts_with("pub use ")
                || trimmed.starts_with("pub(crate) use ")
                || trimmed.starts_with("pub(super) use ")
                || trimmed.starts_with("pub(self) use ")
                || trimmed.starts_with("pub(in ")
            {
                continue;
            }
            total += code.matches(pattern).count();
        }
    }
    total
}

fn trusted_arith_source_site_counts(files: &[PathBuf]) -> (usize, usize, usize, usize) {
    let close_sites = count_pattern_in_files_excluding_imports(
        files,
        "close_with_trusted_arith(",
        &["arith_linarith/trusted_arith.rs"],
    );
    let direct_sites = count_pattern_in_files_excluding_imports(
        files,
        "create_trusted_arith_term(",
        &["arith_linarith/trusted_arith.rs"],
    );
    let raw_sites = count_pattern_in_files_excluding_imports(
        files,
        "make_trusted_arith_term_untracked(",
        &["arith_linarith/trusted_arith.rs"],
    );
    let rewrite_sites = count_pattern_in_files_excluding_imports(
        files,
        "replace_target_with_trusted_fallback(",
        &["tactic/core/"],
    );
    (close_sites, direct_sites, raw_sites, rewrite_sites)
}

/// Files that perform `.ty = ` or `.value = ` on a *cloned* local context (not
/// the active goal), which is architecturally equivalent to `local_ops.rs` and
/// should not count as a bypass.
const CLONED_CONTEXT_EXCLUDES: &[&str] = &[
    // simp/mod.rs: builds `new_ctx = goal.local_ctx.clone()` then mutates the
    // clone, creates a new goal meta, and closes the old goal with a proof term.
    "simp/mod.rs",
    // finite_cases.rs: writes `decl.value = Some(inhabitant)` on a copied
    // branch-local context, not the inherited goal. Each branch is backed by
    // `build_fin_cases_proof()`. Design doc #2554 explicit carve-out.
    "finite_cases.rs",
];

fn collect_local_decl_rewrite_sites(
    root: &Path,
    files: &[PathBuf],
) -> Vec<(String, usize, String)> {
    let mut sites = Vec::new();
    for file in files {
        let path_str = file.to_str().unwrap();
        // Exclude `local_ops.rs` — the legitimate boundary implementation.
        if path_str.contains("core/local_ops.rs") {
            continue;
        }
        // Exclude files that only operate on cloned contexts.
        if CLONED_CONTEXT_EXCLUDES
            .iter()
            .any(|excl| path_str.contains(excl))
        {
            continue;
        }
        let content = std::fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("failed to read {}: {}", file.display(), e));
        let rel_path = file
            .strip_prefix(root)
            .unwrap_or(file)
            .display()
            .to_string();
        for (line_num, line) in content.lines().enumerate() {
            let code = line.split("//").next().unwrap_or("").trim();
            if code.is_empty() {
                continue;
            }
            // Pattern 1: indexed access — `goal.local_ctx[N].ty = ...`
            let is_indexed_bypass = code.contains("goal.local_ctx[")
                && (code.contains("].ty =")
                    || code.contains("].value =")
                    || code.contains("] = LocalDecl"));
            // Pattern 2: iterator-based — `.ty = ` or `.value = ` field assignment
            // on a variable obtained from `goal.local_ctx.iter_mut()` or
            // `&mut goal.local_ctx`. Detected by `.ty = ` not followed by `=`
            // (i.e., assignment not comparison), excluding `.name = ` (cosmetic).
            let is_iterator_bypass = !is_indexed_bypass
                && (code.contains(".ty = ") || code.contains(".value = "))
                && !code.contains(".ty ==")
                && !code.contains(".value ==")
                // Exclude struct initialization (field: value)
                && !code.contains("ty: ")
                && !code.contains("value: ");
            if is_indexed_bypass || is_iterator_bypass {
                sites.push((rel_path.clone(), line_num + 1, code.to_string()));
            }
        }
    }
    sites
}

#[test]
fn count_pattern_in_files_excluding_imports_ignores_line_comments() {
    let temp = tempfile::tempdir().expect("create temp dir");
    let file = temp.path().join("sample.rs");
    std::fs::write(
        &file,
        r#"// create_trusted_ay_term(comment_only)
let production = create_trusted_ay_term(env, target);
let comment_only = target; // create_trusted_ay_term(inline_comment)
"#,
    )
    .expect("write sample.rs");

    let count = count_pattern_in_files_excluding_imports(&[file], "create_trusted_ay_term(", &[]);

    assert_eq!(
        count, 1,
        "line comments and inline comment suffixes must not count as production call sites"
    );
}

#[test]
fn count_pattern_in_files_skips_inline_test_modules_but_keeps_production_afterward() {
    let temp = tempfile::tempdir().expect("create temp dir");
    let file = temp.path().join("sample.rs");
    std::fs::write(
        &file,
        r#"fn before(state: &mut ProofState, goal: MetaId, proof: Expr) {
    state.metas.assign(goal, proof);
}

#[cfg(test)]
mod tests {
    fn helper(state: &mut ProofState, goal: MetaId, proof: Expr) {
        state.metas.assign(goal, proof);
    }
}

fn after(state: &mut ProofState, goal: MetaId, proof: Expr) {
    state.metas.assign(goal, proof);
}
"#,
    )
    .expect("write sample.rs");

    let count = count_pattern_in_files(&[file], "metas.assign(", "never/matches");

    assert_eq!(
        count, 2,
        "inline #[cfg(test)] modules should be skipped without dropping later production matches"
    );
}

/// Ratchet: `metas.assign(` bypass sites must not exceed baseline.
///
/// Counts direct `metas.assign(` calls in tactic source files, excluding:
/// - `core.rs` (contains the `close_goal` implementation which legitimately calls it)
/// - `tests/` directory (test code is not a soundness pathway)
///
/// When bypass sites are migrated to `close_goal` or `close_goal_checked`,
/// tighten `METAS_ASSIGN_BYPASS_RATCHET` downward.
///
/// Part of #2202, #2187.
#[test]
fn metas_assign_bypass_ratchet() {
    let tactic_dir = format!("{}/src/tactic", env!("CARGO_MANIFEST_DIR"));
    let files = collect_rust_source_files(Path::new(&tactic_dir), &DEFAULT_PRODUCTION_RULES);

    let count = count_pattern_in_files(&files, "metas.assign(", "tactic/core/");

    match METAS_ASSIGN_BYPASS_RATCHET {
        0 => assert_eq!(
            count, 0,
            "metas.assign bypass ratchet FAILED: found {} sites, ratchet allows 0.\n\
             New metas.assign bypass site detected — use close_goal or close_goal_checked instead.\n\
             Sites must stay at zero once the ratchet floor reaches 0.",
            count,
        ),
        ratchet => {
            assert!(
                count <= ratchet,
                "metas.assign bypass ratchet FAILED: found {} sites, ratchet allows {}.\n\
                 New metas.assign bypass site detected — use close_goal or close_goal_checked instead.\n\
                 If this is intentional, update METAS_ASSIGN_BYPASS_RATCHET in core.rs.",
                count,
                ratchet,
            );

            if count < ratchet {
                eprintln!(
                    "INFO: metas.assign bypass count ({}) is below ratchet ({}). \
                     Tighten METAS_ASSIGN_BYPASS_RATCHET in core.rs.",
                    count, ratchet,
                );
            }
        }
    }
}

/// Ratchet: `.close_goal_unchecked(` sites must not exceed baseline.
///
/// Counts `.close_goal_unchecked(` calls in tactic source files, excluding:
/// - `core.rs` (contains the definition and the delegation from `close_goal`)
/// - `tests/` directory
///
/// When sites are migrated to checked `close_goal`, tighten
/// `CLOSE_GOAL_UNCHECKED_RATCHET` downward in core.rs.
///
/// Part of #2202, #2154, #2230.
#[test]
fn close_goal_unchecked_site_ratchet() {
    let tactic_dir = format!("{}/src/tactic", env!("CARGO_MANIFEST_DIR"));
    let files = collect_rust_source_files(Path::new(&tactic_dir), &DEFAULT_PRODUCTION_RULES);

    let count = count_pattern_in_files(&files, ".close_goal_unchecked(", "tactic/core/");

    assert!(
        count == CLOSE_GOAL_UNCHECKED_RATCHET,
        "close_goal_unchecked ratchet FAILED: found {} sites, ratchet allows {}.\n\
         New close_goal_unchecked site detected — use close_goal (checked) instead.\n\
         If this is intentional, update CLOSE_GOAL_UNCHECKED_RATCHET in core.rs.",
        count,
        CLOSE_GOAL_UNCHECKED_RATCHET,
    );
}

/// Ratchet: `create_trusted_ay_term(` call sites must not exceed baseline.
///
/// Counts trustedAy invocations in tactic source files, excluding:
/// - `tactic/core/` (contains the ratchet constant definition)
/// - `smt/mod.rs` (contains the re-export, not a call site)
/// - `tests/` directory (test code is not a soundness pathway)
/// - `use` statements (imports, not invocations)
///
/// When call sites are replaced by kernel-checkable proof reconstruction,
/// tighten `TRUSTED_AY_CALL_SITE_RATCHET` downward in core/mod.rs.
///
/// Part of #2442 Phase 3, #2231.
#[test]
fn trusted_ay_call_site_ratchet() {
    let tactic_dir = format!("{}/src/tactic", env!("CARGO_MANIFEST_DIR"));
    let files = collect_rust_source_files(Path::new(&tactic_dir), &DEFAULT_PRODUCTION_RULES);

    let count = count_pattern_in_files_excluding_imports(
        &files,
        "create_trusted_ay_term(",
        &["tactic/core/", "smt/mod.rs"],
    );
    let remaining = TRUSTED_AY_CALL_SITE_RATCHET.checked_sub(count);

    assert!(
        remaining.is_some(),
        "trustedAy call-site ratchet FAILED: found {} sites, ratchet allows {}.\n\
         New create_trusted_ay_term call detected — replace with kernel-checkable \
         proof reconstruction instead.\n\
         If this is intentional, update TRUSTED_AY_CALL_SITE_RATCHET in core/mod.rs.",
        count,
        TRUSTED_AY_CALL_SITE_RATCHET,
    );

    if let Some(remaining) = remaining {
        if remaining > 0 {
            eprintln!(
                "INFO: trustedAy call-site count ({}) is below ratchet ({}). \
                 Tighten TRUSTED_AY_CALL_SITE_RATCHET in core/mod.rs.",
                count, TRUSTED_AY_CALL_SITE_RATCHET,
            );
        }
    }
}

/// Ratchet: trustedArith production source sites must not exceed baseline.
///
/// Counts trustedArith-producing production sites in tactic source files,
/// excluding:
/// - `arith_linarith/trusted_arith.rs` (helper definitions and internal calls)
/// - `tests/` directory
/// - import/use statements
///
/// Counted production categories:
/// - `close_with_trusted_arith(` goal-closing fallbacks
/// - `create_trusted_arith_term(` tracked constructor callers
/// - `make_trusted_arith_term_untracked(` raw constructor callers
/// - `replace_target_with_trusted_fallback(` callers outside `tactic/core/`
///
/// When proof-carry work removes a site, tighten
/// `TRUSTED_ARITH_SOURCE_SITE_RATCHET` downward in core/ratchet.rs.
#[test]
#[allow(clippy::absurd_extreme_comparisons)] // ratchet may be 0 (usize floor)
fn trusted_arith_source_site_ratchet() {
    let tactic_dir = format!("{}/src/tactic", env!("CARGO_MANIFEST_DIR"));
    let files = collect_rust_source_files(Path::new(&tactic_dir), &DEFAULT_PRODUCTION_RULES);
    let (close_sites, direct_sites, raw_sites, rewrite_sites) =
        trusted_arith_source_site_counts(&files);
    let count = close_sites + direct_sites + raw_sites + rewrite_sites;

    assert!(
        count <= TRUSTED_ARITH_SOURCE_SITE_RATCHET,
        "trustedArith source-site ratchet FAILED: found {} sites \
         (close={}, direct={}, raw={}, rewrite={}), ratchet allows {}.\n\
         New trustedArith production site detected — replace it with \
         kernel-checkable proof reconstruction instead.\n\
         If this is intentional, update TRUSTED_ARITH_SOURCE_SITE_RATCHET \
         in core/ratchet.rs.",
        count,
        close_sites,
        direct_sites,
        raw_sites,
        rewrite_sites,
        TRUSTED_ARITH_SOURCE_SITE_RATCHET,
    );

    if count < TRUSTED_ARITH_SOURCE_SITE_RATCHET {
        eprintln!(
            "INFO: trustedArith source-site count ({}) is below ratchet ({}) \
             [close={}, direct={}, raw={}, rewrite={}]. Tighten \
             TRUSTED_ARITH_SOURCE_SITE_RATCHET in core/ratchet.rs.",
            count,
            TRUSTED_ARITH_SOURCE_SITE_RATCHET,
            close_sites,
            direct_sites,
            raw_sites,
            rewrite_sites,
        );
    }
}

/// Ratchet: inherited-goal local declaration rewrites must stay on the shared
/// `local_ops.rs` boundary.
///
/// Detects two bypass patterns:
/// 1. Indexed: `goal.local_ctx[N].ty = ...` / `.value = ...` / `= LocalDecl`
/// 2. Iterator-based: `.ty = ...` / `.value = ...` field assignment obtained
///    via `current_goal_mut()` + `local_ctx.iter_mut()` or `&mut goal.local_ctx`
///
/// Excludes `core/local_ops.rs` (the boundary) and files that only operate on
/// cloned contexts (e.g., `simp/mod.rs`).
///
/// All known local-declaration rewrite bypass sites have been migrated to the
/// checked `local_ops.rs` boundary.
#[test]
fn local_decl_rewrite_source_site_ratchet() {
    let tactic_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("tactic");
    let files = collect_rust_source_files(&tactic_dir, &DEFAULT_PRODUCTION_RULES);
    let sites = collect_local_decl_rewrite_sites(&tactic_dir, &files);

    assert_eq!(
        sites.len(),
        LOCAL_DECL_REWRITE_SOURCE_SITE_RATCHET,
        "local-declaration rewrite ratchet FAILED: found {} sites, ratchet allows {}.\n\
         All local declaration rewrites must go through tactic/core/local_ops.rs.\n\
         Sites:\n{}",
        sites.len(),
        LOCAL_DECL_REWRITE_SOURCE_SITE_RATCHET,
        sites
            .iter()
            .map(|(path, line, snippet)| format!("  {path}:{line}: {snippet}"))
            .collect::<Vec<_>>()
            .join("\n"),
    );
}

/// Count elaborator sorry-producing source sites in a set of `infer/` files.
///
/// Counts four kinds of source site:
/// 1. `elab_sorry_with_kind(` call sites (the two entrypoints)
/// 2. Direct `create_sorry_term_with_kind_at_level(` lines also containing `SorryKind::`
/// 3. Direct `create_sorry_term_with_kind(` lines also containing `SorryKind::`
/// 4. Direct `create_sorry_term(` lines
///
/// Strips line comments and skips `use`/`pub use` lines to avoid self-counting.
/// Each qualifying line counts once regardless of how many patterns it matches.
fn count_elab_sorry_source_sites(files: &[PathBuf]) -> usize {
    let mut total = 0;
    for file in files {
        let content = std::fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("failed to read {}: {}", file.display(), e));
        let test_mod_ranges = cfg_test_mod_line_ranges(&content);
        for (idx, line) in content.lines().enumerate() {
            if line_is_inside_cfg_test_mod(&test_mod_ranges, idx) {
                continue;
            }
            let code = code_before_line_comment(line);
            let trimmed = code.trim_start();
            if trimmed.is_empty() {
                continue;
            }
            if trimmed.starts_with("use ")
                || trimmed.starts_with("pub use ")
                || trimmed.starts_with("pub(crate) use ")
                || trimmed.starts_with("pub(super) use ")
            {
                continue;
            }
            // Skip function definitions — we want call sites, not signatures.
            if trimmed.starts_with("fn ")
                || trimmed.starts_with("pub fn ")
                || trimmed.starts_with("pub(super) fn ")
                || trimmed.starts_with("pub(crate) fn ")
            {
                continue;
            }
            let is_site = trimmed.contains("elab_sorry_with_kind(")
                || (trimmed.contains("create_sorry_term_with_kind_at_level(")
                    && trimmed.contains("SorryKind::"))
                || (trimmed.contains("create_sorry_term_with_kind(")
                    && trimmed.contains("SorryKind::"))
                || trimmed.contains("create_sorry_term(");
            if is_site {
                total += 1;
            }
        }
    }
    total
}

/// Ratchet: elaborator sorry-producing source sites must not change without review.
///
/// Scans production `infer/` files for sorry-creating call sites. The count
/// must exactly match `ELAB_SORRY_SOURCE_SITE_RATCHET` — both increases
/// (new sorry paths) and decreases (removed paths without tightening the
/// constant) are flagged.
///
/// Part of #2613, #2154.
#[test]
fn elab_sorry_source_site_ratchet() {
    let infer_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("infer");
    let files = collect_rust_source_files(&infer_dir, &DEFAULT_PRODUCTION_RULES);

    let count = count_elab_sorry_source_sites(&files);

    assert_eq!(
        count, ELAB_SORRY_SOURCE_SITE_RATCHET,
        "elaborator sorry source-site ratchet FAILED: found {} sites, ratchet expects {}.\n\
         If you added a new sorry-producing path, update ELAB_SORRY_SOURCE_SITE_RATCHET \
         in core/ratchet.rs.\n\
         If you removed a sorry-producing path, tighten the ratchet constant in the same change.",
        count, ELAB_SORRY_SOURCE_SITE_RATCHET,
    );
}

/// Combined report: total unchecked proof assignment pathways.
///
/// This is informational — the individual ratchets above are the enforcement
/// mechanism. This test just provides visibility into total bypass count.
#[test]
fn total_bypass_pathway_report() {
    let tactic_dir = format!("{}/src/tactic", env!("CARGO_MANIFEST_DIR"));
    let files = collect_rust_source_files(Path::new(&tactic_dir), &DEFAULT_PRODUCTION_RULES);

    let metas_assign = count_pattern_in_files(&files, "metas.assign(", "tactic/core/");
    let close_goal = count_pattern_in_files(&files, ".close_goal_unchecked(", "tactic/core/");
    let total = metas_assign + close_goal;

    eprintln!("=== Bypass pathway report ===");
    eprintln!(
        "  metas.assign direct:  {} (ratchet: {})",
        metas_assign, METAS_ASSIGN_BYPASS_RATCHET
    );
    eprintln!(
        "  close_goal unchecked: {} (ratchet: {})",
        close_goal, CLOSE_GOAL_UNCHECKED_RATCHET
    );
    eprintln!("  Total unchecked:      {}", total);
    eprintln!("=============================");
}
