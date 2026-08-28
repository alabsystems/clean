// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 19) for the SOURCE half of the `unchecked_decl_ratchet_accounted`
//! DENY_SORRY lane — the half the Rust producer of that lane did not perform
//! until G7 (2026-08-27).
//!
//! Every arm here is two-way by construction: the real tree must MEASURE (not
//! assert) to exactly the one sanctioned bypass, and each refusal arm is paired
//! with the shape that must stay green, so the battery cannot pass by refusing
//! everything.

use crate::cmd_replacement::*;

const SANCTIONED_FILE: &str = "crates/clean-kernel/src/env/decl_add.rs";

fn sanctioned_ratchet() -> UncheckedDeclRatchetArtifact {
    UncheckedDeclRatchetArtifact {
        add_decl_structural_count: 0,
        add_decl_unchecked_count: 1,
        add_decl_structural_production_sites: vec![],
        add_decl_unchecked_production_sites: vec![UncheckedDeclProductionSite {
            file: SANCTIONED_FILE.to_string(),
            method: "add_decl_unchecked".to_string(),
            trust: "SANCTIONED IMPORT-LANE PROOF-DROP (fixture copy of the real row)".to_string(),
            occurrences: Some(1),
        }],
        files: vec![],
        last_updated: "2026-08-27".to_string(),
    }
}

/// A synthetic repo root carrying the sanctioned call site, plus whatever else
/// the arm plants. `extra` is `(relative path, source)`.
fn synthetic_root(sanctioned_body: &str, extra: &[(&str, &str)]) -> (tempfile::TempDir, PathBuf) {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path().to_path_buf();
    for (relative, source) in std::iter::once(&(SANCTIONED_FILE, sanctioned_body)).chain(extra) {
        let path = root.join(relative);
        fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
        fs::write(&path, source).expect("write");
    }
    (dir, root)
}

const SANCTIONED_BODY: &str = "\
pub fn add_decl(env: &mut Environment, decl: Declaration) {
    // SOUNDNESS: the Metamath two-pass PASS-1 proof-drop; fixture copy.
    env.add_decl_unchecked(decl);
}
";

// ── the real tree ────────────────────────────────────────────────────────────

/// MEASURED, not asserted: the whole `crates/` tree contains exactly one
/// production `add_decl_*` bypass, and it is the sanctioned one. This is the
/// arm that keeps the Rust scan and `scripts/check_add_decl_ratchet.py`
/// (`structural=0/0, unchecked=1/1`) from drifting apart about the same tree.
#[test]
fn real_tree_measures_exactly_the_one_sanctioned_add_decl_bypass() {
    let measured = measure_add_decl_bypass_sites(&repo_root())
        .expect("the real tree must be scannable; an unlexable file fails closed");
    let sites: Vec<(String, String)> = measured
        .iter()
        .map(|site| (site.file.clone(), site.method.clone()))
        .collect();
    assert_eq!(
        sites,
        vec![(
            SANCTIONED_FILE.to_string(),
            "add_decl_unchecked".to_string()
        )],
        "measured production add_decl_* bypasses moved: {measured:?}"
    );
}

#[test]
fn the_real_tree_and_the_real_ratchet_agree() {
    let ratchet = load_unchecked_decl_ratchet().expect("the committed ratchet must parse");
    validate_add_decl_bypass_sites_measured(&repo_root(), &ratchet)
        .expect("HEAD must be source-measured clean");
}

// ── R9: a mention is not a call ──────────────────────────────────────────────

/// The anti-correlation arm. CLAUDE.md *requires* a `// SOUNDNESS:` comment at
/// every bypass, so a scanner that matched raw text would go red on the fix and
/// green on its absence. All four spellings here must count ZERO.
#[test]
fn comments_and_string_literals_naming_the_call_are_not_calls() {
    let source = r####"
// SOUNDNESS: this lane must never reach env.add_decl_unchecked(decl).
/// Doc: prefer `add_decl` over .add_decl_structural( — see the ratchet.
/* block: env.add_decl_unchecked(decl); */
pub fn describe() -> &'static str {
    "env.add_decl_unchecked(decl)"
}
pub fn describe_raw() -> &'static str {
    r#"chain.add_decl_structural(decl)"#
}
"####;
    assert!(
        add_decl_bypass_lines_in_production(source)
            .expect("lexable")
            .is_empty(),
        "a mention of the call is not the call"
    );
}

/// …and the other direction, so the arm above cannot pass by refusing
/// everything: a REAL call carrying a trailing comment still counts.
#[test]
fn a_real_call_with_a_trailing_comment_still_counts() {
    let source = "pub fn f(env: &mut E, d: D) { env.add_decl_unchecked(d); // SOUNDNESS: no\n}\n";
    assert_eq!(
        add_decl_bypass_lines_in_production(source).expect("lexable"),
        vec![(1, "add_decl_unchecked".to_string())]
    );
}

/// Definitions and `Environment::`-qualified delegations are infrastructure,
/// not usage — the same exclusion the Python scanner documents.
#[test]
fn definitions_and_associated_call_delegations_are_out_of_scope() {
    let source = "\
pub fn add_decl_unchecked(&mut self, d: Declaration) {}
pub fn delegate(env: &mut Environment, d: Declaration) {
    Environment::add_decl_unchecked(env, d);
}
";
    assert!(add_decl_bypass_lines_in_production(source)
        .expect("lexable")
        .is_empty());
}

#[test]
fn inline_cfg_test_mod_calls_are_not_production() {
    let source = "\
pub fn production(env: &mut E, d: D) {
    env.add_decl(d);
}

#[cfg(test)]
mod tests {
    #[test]
    fn plant(env: &mut E, d: D) {
        env.add_decl_unchecked(d);
    }
}
";
    assert!(add_decl_bypass_lines_in_production(source)
        .expect("lexable")
        .is_empty());

    // Two-way: the same call one line OUTSIDE the block is production.
    let production = source.replace("#[cfg(test)]\n", "");
    assert_eq!(
        add_decl_bypass_lines_in_production(&production)
            .expect("lexable")
            .len(),
        1
    );
}

// ── the reproduction ─────────────────────────────────────────────────────────

/// THE DEFECT, and the fix, in one arm.
///
/// A production file registers a declaration through `add_decl_unchecked` with
/// no ratchet row and no sanction. The two validators the Rust DENY_SORRY
/// producer used to run take `&UncheckedDeclRatchetArtifact` and nothing else,
/// so they return Ok on the identical tree and the lane was minted `passed`.
/// The measured validator refuses it and names the file.
#[test]
fn the_json_only_checks_cannot_see_a_planted_bypass_that_the_measured_lane_refuses() {
    let ratchet = sanctioned_ratchet();
    let (_dir, root) = synthetic_root(
        SANCTIONED_BODY,
        &[(
            "crates/clean-elab/src/planted_bypass.rs",
            "pub fn smuggle(env: &mut E, d: D) {\n    env.add_decl_unchecked(d);\n}\n",
        )],
    );

    // The pre-G7 lane, verbatim, on the planted tree.
    validate_unchecked_decl_ratchet(&ratchet)
        .expect("the JSON-only shape check cannot see the plant");
    validate_unchecked_decl_ratchet_closed(&ratchet)
        .expect("the JSON-only closure check cannot see the plant either");

    // The measurement.
    let err = validate_add_decl_bypass_sites_measured(&root, &ratchet)
        .expect_err("a planted unaccounted bypass must fail the lane closed");
    assert!(
        err.contains("crates/clean-elab/src/planted_bypass.rs") && err.contains("unaccounted"),
        "the refusal must name the file it refused: {err}"
    );

    // Two-way: remove the plant and the same tree is accepted.
    fs::remove_file(root.join("crates/clean-elab/src/planted_bypass.rs")).expect("unplant");
    validate_add_decl_bypass_sites_measured(&root, &ratchet)
        .expect("the sanctioned tree alone must pass");
}

#[test]
fn an_accounted_site_without_its_soundness_comment_is_refused() {
    let ratchet = sanctioned_ratchet();
    let stripped = SANCTIONED_BODY
        .lines()
        .filter(|line| !line.contains("SOUNDNESS"))
        .collect::<Vec<_>>()
        .join("\n");
    let (_dir, root) = synthetic_root(&stripped, &[]);
    let err = validate_add_decl_bypass_sites_measured(&root, &ratchet)
        .expect_err("an accounted bypass with no // SOUNDNESS: comment must fail closed");
    assert!(
        err.contains("carries no") && err.contains("SOUNDNESS"),
        "unexpected refusal: {err}"
    );

    // Two-way: restore the comment and the identical call is accepted.
    let (_dir, root) = synthetic_root(SANCTIONED_BODY, &[]);
    validate_add_decl_bypass_sites_measured(&root, &ratchet)
        .expect("the same call WITH its // SOUNDNESS: comment must pass");
}

#[test]
fn a_sanctioned_site_may_not_grow_a_second_call_site() {
    let ratchet = sanctioned_ratchet();
    let doubled = format!("{SANCTIONED_BODY}\n{SANCTIONED_BODY}");
    let (_dir, root) = synthetic_root(&doubled, &[]);
    let err = validate_add_decl_bypass_sites_measured(&root, &ratchet)
        .expect_err("a sanctioned bypass does not license a second copy of itself");
    assert!(
        err.contains("sanctioned cap is 1"),
        "unexpected refusal: {err}"
    );
}

#[test]
fn a_ratchet_row_whose_call_site_vanished_is_refused() {
    let ratchet = sanctioned_ratchet();
    let (_dir, root) = synthetic_root(
        "pub fn add_decl(env: &mut E, d: D) { env.add_decl(d); }\n",
        &[],
    );
    let err = validate_add_decl_bypass_sites_measured(&root, &ratchet)
        .expect_err("a row with no live call site is stale and must fail closed");
    assert!(
        err.contains("no live call site"),
        "unexpected refusal: {err}"
    );
}
