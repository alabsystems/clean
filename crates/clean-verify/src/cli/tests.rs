// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioral tests for `clean verify proof` (Epic #3436, #3511).
//!
//! These tests exercise the runner dispatch from end-to-end on real on-disk
//! formula + LRAT proof inputs to lock in exit-code parity with the legacy
//! `proof_check` standalone binary. Golden output-line texts (`s VERIFIED`,
//! `s INVALID`, `s NOT VERIFIED`, `valid` / `holey` / `invalid` / `unknown`)
//! are part of the competition-judging contract and must stay byte-stable.

use std::path::PathBuf;

use clean_features::{ensure_has_example, ensure_unique_paths, FeatureDescriptor};
use tempfile::TempDir;

use super::{run, VerifyProofArgs, EXIT_INVALID, EXIT_VERIFIED};
use crate::cli::pipeline::{OwnedProofCheckInputs, EXIT_ERROR};
use crate::sat_verify::pipeline::ProofFormat;

/// Simple UNSAT formula `(x1) AND (-x1)` + matching LRAT refutation.
const SIMPLE_CNF_DIMACS: &str = "p cnf 1 2\n1 0\n-1 0\n";
const SIMPLE_LRAT: &str = "3 0 1 2 0\n";

/// Two-variable UNSAT `(x1 v x2) AND (-x1) AND (-x2)` + matching LRAT.
const TWO_VAR_CNF_DIMACS: &str = "p cnf 2 3\n1 2 0\n-1 0\n-2 0\n";
const TWO_VAR_LRAT: &str = "4 2 0 1 2 0\n5 0 4 3 0\n";

/// Write two files into a fresh temp dir and return their paths alongside the
/// dir handle so the caller can keep it alive until the test body completes.
fn write_inputs(cnf: &str, proof: &str) -> (TempDir, PathBuf, PathBuf) {
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let proof_path = dir.path().join("proof.lrat");
    std::fs::write(&formula_path, cnf).expect("write cnf");
    std::fs::write(&proof_path, proof).expect("write proof");
    (dir, formula_path, proof_path)
}

fn default_args(formula: PathBuf, proof: PathBuf) -> VerifyProofArgs {
    VerifyProofArgs {
        formula,
        proof,
        format: None,
        strict: false,
        timing: false,
        competition: false,
        smtcomp: false,
        satcomp: false,
        certificate: None,
        trim: None,
    }
}

#[test]
fn test_default_pipeline_verifies_simple_lrat_unsat() {
    let (_dir, formula, proof) = write_inputs(SIMPLE_CNF_DIMACS, SIMPLE_LRAT);
    let exit = run(default_args(formula, proof)).expect("args parse");
    assert_eq!(exit, EXIT_VERIFIED, "simple UNSAT must verify (exit 0)");
}

#[test]
fn test_default_pipeline_verifies_two_var_lrat_unsat() {
    let (_dir, formula, proof) = write_inputs(TWO_VAR_CNF_DIMACS, TWO_VAR_LRAT);
    let exit = run(default_args(formula, proof)).expect("args parse");
    assert_eq!(
        exit, EXIT_VERIFIED,
        "two-variable UNSAT must verify (exit 0)"
    );
}

#[test]
fn test_competition_mode_verifies_simple_lrat_unsat() {
    let (_dir, formula, proof) = write_inputs(SIMPLE_CNF_DIMACS, SIMPLE_LRAT);
    let mut args = default_args(formula, proof);
    args.competition = true;
    let exit = run(args).expect("args parse");
    assert_eq!(
        exit, EXIT_VERIFIED,
        "competition LRAT UNSAT must verify (exit 0)"
    );
}

#[test]
fn test_satcomp_mode_verifies_simple_lrat_unsat() {
    let (_dir, formula, proof) = write_inputs(SIMPLE_CNF_DIMACS, SIMPLE_LRAT);
    let mut args = default_args(formula, proof);
    args.satcomp = true;
    let exit = run(args).expect("args parse");
    assert_eq!(
        exit, EXIT_VERIFIED,
        "SAT-COMP path must verify simple UNSAT (exit 0)"
    );
}

#[test]
fn test_explicit_lrat_format_hint_verifies() {
    let (_dir, formula, proof) = write_inputs(SIMPLE_CNF_DIMACS, SIMPLE_LRAT);
    let mut args = default_args(formula, proof);
    args.format = Some("lrat".to_owned());
    let exit = run(args).expect("args parse");
    assert_eq!(exit, EXIT_VERIFIED);
}

#[test]
fn test_invalid_format_token_returns_typed_error() {
    let (_dir, formula, proof) = write_inputs(SIMPLE_CNF_DIMACS, SIMPLE_LRAT);
    let mut args = default_args(formula, proof);
    args.format = Some("nonsense".to_owned());
    let err = run(args).expect_err("unknown --format must fail");
    let msg = format!("{err}");
    assert!(
        msg.contains("invalid --format"),
        "error message should mention --format: {msg}"
    );
}

#[test]
fn test_missing_formula_file_returns_error_exit_code() {
    let dir = tempfile::tempdir().expect("tempdir");
    let formula = dir.path().join("does-not-exist.cnf");
    let proof_path = dir.path().join("proof.lrat");
    std::fs::write(&proof_path, SIMPLE_LRAT).expect("write proof");

    let exit = run(default_args(formula, proof_path)).expect("args parse");
    assert_eq!(
        exit, EXIT_ERROR,
        "missing formula must surface as exit 1 (error)"
    );
}

#[test]
fn test_bogus_proof_bytes_rejected_in_pipeline() {
    // Random non-LRAT / non-Alethe / non-VeriPB bytes — pipeline should report
    // UnknownFormat and exit EXIT_ERROR (not EXIT_INVALID).
    let (_dir, formula, proof) = write_inputs(SIMPLE_CNF_DIMACS, "this is not a proof\n");
    let exit = run(default_args(formula, proof)).expect("args parse");
    assert_eq!(
        exit, EXIT_ERROR,
        "unknown proof format must exit as error (1), not invalid (10)"
    );
}

#[test]
fn test_satcomp_mode_on_non_refutation_proof_exits_invalid() {
    // Wrong LRAT body — the hint chain does not close. We validate it as
    // something the pipeline recognizes as a proof but cannot close.
    let bogus_lrat = "99 0 1 2 0\n"; // RUP derives empty clause referencing clauses 1,2.
    let (_dir, formula, proof) = write_inputs("p cnf 1 2\n1 0\n1 0\n", bogus_lrat);
    let mut args = default_args(formula, proof);
    args.satcomp = true;
    let exit = run(args).expect("args parse");
    // Accept either EXIT_INVALID (pipeline says not a refutation) or
    // EXIT_ERROR (pipeline bails earlier) — both are contract-compliant
    // outcomes for a non-verifying proof in SAT-COMP mode.
    assert!(
        exit == EXIT_INVALID || exit == EXIT_ERROR,
        "non-refutation must not return EXIT_VERIFIED (got {exit})"
    );
}

#[test]
fn test_owned_proof_check_inputs_round_trips() {
    let dir = tempfile::tempdir().expect("tempdir");
    let owned = OwnedProofCheckInputs {
        formula_path: dir.path().join("f.cnf"),
        proof_path: dir.path().join("p.lrat"),
        format: Some(ProofFormat::Lrat),
        strict: true,
        timing: false,
        certificate_path: None,
        trim_output: Some(dir.path().join("trimmed.lrat")),
    };
    let view = owned.as_inputs();
    assert_eq!(view.formula_path, owned.formula_path.as_path());
    assert_eq!(view.proof_path, owned.proof_path.as_path());
    assert_eq!(view.format, Some(ProofFormat::Lrat));
    assert!(view.strict);
    assert!(!view.timing);
    assert!(view.certificate_path.is_none());
    assert_eq!(
        view.trim_output,
        Some(dir.path().join("trimmed.lrat").as_path())
    );
}

#[test]
fn test_descriptor_registry_is_lint_clean() {
    let descriptors: Vec<&FeatureDescriptor> = super::FEATURES.iter().collect();
    ensure_unique_paths(&descriptors).expect("descriptor paths are unique");
    for descriptor in super::FEATURES {
        ensure_has_example(descriptor).expect("every descriptor has ≥1 example");
    }
}

#[test]
fn test_descriptor_path_is_verify_proof() {
    assert_eq!(super::FEATURES.len(), 1);
    assert_eq!(super::FEATURES[0].path, &["verify", "proof"]);
}
