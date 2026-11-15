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

/// MEASURED, not asserted: the whole `crates/` tree contains exactly THREE
/// production `add_decl_*` bypasses and every one is sanctioned — the import-lane
/// proof-drop plus the two `TrustedEnvExt` delegations.
///
/// AUDIT r11 M11-6: the count moved 1 -> 3 because COVERAGE moved, not because
/// bypasses were added. The two delegations have been there unchanged
/// throughout; they were hidden first by a leading-dot call-shape requirement
/// and then by audit r10's whole-FILE exclusion of `env/trusted_ext.rs`. A file
/// skip is a suppression — measured, one extra `self.add_decl_unchecked(..)`
/// planted inside an existing delegation body was invisible to every scanner
/// under that blanket, while the pre-r10 scanner caught it.
///
/// This is also the arm that keeps the Rust scan and
/// `scripts/check_add_decl_ratchet.py` (`structural=1/1, unchecked=2/2`) from
/// drifting apart about the same tree.
#[test]
fn real_tree_measures_exactly_the_sanctioned_add_decl_bypasses() {
    let measured = measure_add_decl_bypass_sites(&repo_root())
        .expect("the real tree must be scannable; an unlexable file fails closed");
    let sites: Vec<(String, String)> = measured
        .iter()
        .map(|site| (site.file.clone(), site.method.clone()))
        .collect();
    assert_eq!(
        sites,
        vec![
            (
                SANCTIONED_FILE.to_string(),
                "add_decl_unchecked".to_string()
            ),
            (
                "crates/clean-kernel/src/env/trusted_ext.rs".to_string(),
                "add_decl_unchecked".to_string()
            ),
            (
                "crates/clean-kernel/src/env/trusted_ext.rs".to_string(),
                "add_decl_structural".to_string()
            ),
        ],
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

/// A DEFINITION is not a use; a `Environment::`-qualified CALL is.
///
/// AUDIT r10 M10-5 flipped this test. It used to assert that a UFCS call was
/// out of scope — pinning an exclusion by call SHAPE, which held in every file
/// and made `Environment::add_decl_unchecked(env, d)` invisible everywhere
/// (measured: a plant in `env/snapshot.rs` with no `// SOUNDNESS:` comment
/// passed both scanners byte-identically). The two genuine delegations are
/// excluded by FILE now, so this test asserts the honest split: the definition
/// is not a call site, and the UFCS call IS one.
#[test]
fn a_definition_is_not_a_call_but_a_ufcs_call_is() {
    let definition_only = "\
pub fn add_decl_unchecked(&mut self, d: Declaration) {}
";
    assert!(add_decl_bypass_lines_in_production(definition_only)
        .expect("lexable")
        .is_empty());

    let ufcs_call = "\
pub fn delegate(env: &mut Environment, d: Declaration) {
    Environment::add_decl_unchecked(env, d);
}
";
    assert_eq!(
        add_decl_bypass_lines_in_production(ufcs_call).expect("lexable"),
        vec![(2, "add_decl_unchecked".to_string())],
        "a UFCS call through the watched door must be counted; excluding it by \
         shape is what let a production bypass hide in every file"
    );

    // AUDIT r11: and every OTHER spelling of the same call, because a list of
    // accepted shapes is always one spelling short -- these three were still
    // invisible immediately after the r10 fix.
    for (label, src) in [
        ("fully qualified",
         "pub fn f(e: &mut Environment, d: Declaration) {\n    <Environment as TrustedEnvExt>::add_decl_unchecked(e, d);\n}\n"),
        ("import alias",
         "pub fn f(e: &mut E, d: Declaration) {\n    E::add_decl_unchecked(e, d);\n}\n"),
        ("generic parameter",
         "pub fn f<T: TrustedEnvExt>(e: &mut T, d: Declaration) {\n    T::add_decl_unchecked(e, d);\n}\n"),
    ] {
        assert_eq!(
            add_decl_bypass_lines_in_production(src).expect("lexable"),
            vec![(2, "add_decl_unchecked".to_string())],
            "{label} call through the watched door must be counted"
        );
    }
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

/// AUDIT r14 M14-11: the two producers of `unchecked_decl_ratchet_accounted`
/// agree on the SET OF FILES EACH READS, not merely on the sites both happen to
/// find in today's tree. Two scanners blind in the same place pass the latter
/// perfectly, and measured, these two were not even blind in the same place:
/// `crates/clean-elab/tests/soundness_gate/{common,baseline}.rs` — 675 lines
/// compiled into a production `[[bin]]` that `scripts/kernel_soundness_gate.sh`
/// RUNS to mint launch evidence — were production to the Python producer and
/// test code to this one, while a plant in either was invisible here.
///
/// This arm fails closed: no python3, no comparison, no pass.
#[test]
fn add_decl_scan_scope_matches_the_python_producer() {
    let root = repo_root();
    let out = Command::new("python3")
        .arg(root.join("scripts/check_add_decl_ratchet.py"))
        .arg("--dump-scope")
        .current_dir(&root)
        .output()
        .expect("python3 must be available; the Python producer IS a gate leg");
    assert!(
        out.status.success(),
        "--dump-scope failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let python: BTreeSet<String> = String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::to_string)
        .filter(|l| !l.is_empty())
        .collect();
    let rust = add_decl_scan_scope(&root);
    assert!(
        python.len() > 3_000,
        "the Python dump collapsed to {} files; a vacuous comparison is not agreement",
        python.len()
    );
    let only_python: Vec<&String> = python.difference(&rust).collect();
    let only_rust: Vec<&String> = rust.difference(&python).collect();
    assert!(
        only_python.is_empty() && only_rust.is_empty(),
        "the two producers of one lane id read different files.\n  python-only ({}): {:?}\n  rust-only ({}): {:?}",
        only_python.len(),
        &only_python[..only_python.len().min(12)],
        only_rust.len(),
        &only_rust[..only_rust.len().min(12)]
    );
}

/// AUDIT r15 M15-1: the cfg LATTICE itself, table-driven, on both producers.
///
/// The r14 rule dispatched on the outermost connective and token-searched the
/// unparsed argument text, so `all(not(test))` -- compiled in every non-test
/// build -- read TEST-ONLY, and `all(unix, feature = "test-utils")` read
/// TEST-ONLY off a string literal. Neither was visible to
/// `add_decl_scan_scope_matches_the_python_producer`, because that arm asserts
/// the two producers agree and they were blind in the SAME place. A parity test
/// structurally cannot catch a shared blindness; only a table of known answers
/// can, which is why this exists beside it rather than instead of it.
#[test]
fn the_cfg_lattice_answers_every_spelling_correctly() {
    use crate::cmd_replacement::rust_source_scope::cfg_body_is_test_only as t;
    let cases: &[(&str, bool)] = &[
        ("test", true),
        ("all(test, feature = \"x\")", true),
        ("any(test, feature = \"x\")", false),
        // the inversions r14 shipped
        ("all(not(test))", false),
        ("all(unix, not(test))", false),
        ("all(not(test), feature = \"math-overlays\")", false),
        ("not(test)", false),
        // negation of a NON-test atom must stay production
        ("not(unix)", false),
        // a token search reads inside this string literal; a parse does not
        ("all(unix, feature = \"test-utils\")", false),
        ("all(any(test, feature = \"x\"))", false),
        // genuinely unsatisfiable without `test`
        ("any(all(test, unix), all(test, windows))", true),
        ("any(test, all(test, unix))", true),
        ("all(unix)", false),
        ("any(test)", true),
        ("all(test)", true),
        ("feature = \"x\"", false),
    ];
    let wrong: Vec<&str> = cases
        .iter()
        .filter(|(body, want)| t(body) != *want)
        .map(|(body, _)| *body)
        .collect();
    assert!(
        wrong.is_empty(),
        "cfg spellings classified backwards: {wrong:?}"
    );
}
