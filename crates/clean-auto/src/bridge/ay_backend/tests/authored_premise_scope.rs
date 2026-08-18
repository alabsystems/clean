// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The premise set `AyProofBackend` hands the Alethe exporter must be ay's
//! AUTHORED problem scope, never the live post-preprocessing assertion stack.
//!
//! `context().assertions` is rewritten in place by preprocessing: when an
//! authored assertion folds to `false`, that slot no longer holds the authored
//! term under any spelling. Handing that stack to the exporter made it refuse
//! every proof anchored on such a premise — through the INFALLIBLE wrapper,
//! which prints `ay-proof: UNVERIFIABLE PROOF ...` to stderr and returns an
//! `(error ...)` s-expression that the backend then reported as a proof.
//!
//! Both states are exercised here on ONE artifact, so the only variable is the
//! premise set:
//!
//! * ADMITTED — through the production `check_sat()` path, an authored premise
//!   exports as a real document naming the assertion the problem text wrote.
//! * PLANTED — the SAME proof and the SAME terms, handed the premise set that
//!   does NOT contain that assume, are still REFUSED. The gate was not widened;
//!   only the choice of which set is authoritative changed.

use super::*;
use ay_proof::{
    try_export_alethe_with_problem_scope_and_overrides, validate_reachable_assumes_in_problem_scope,
};

/// The tRust e9 postcondition shape: a `u64` range block plus `x < x`.
/// Preprocessing folds `(< x x)` to `false` and overwrites its slot.
fn fold_to_false_backend() -> AyProofBackend {
    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
    backend.add_raw_declaration("(declare-fun x () Int)");
    backend.assert_formula("(>= x 0)");
    backend.assert_formula("(<= x 18446744073709551615)");
    backend.assert_formula("(< x x)");
    backend
}

#[test]
fn a_fold_to_false_authored_premise_exports_through_the_backend() {
    let mut backend = fold_to_false_backend();
    let AyProofResult::Unsat { proof, .. } = backend.check_sat().expect("solve") else {
        panic!("expected UNSAT");
    };

    let proof = proof.expect(
        "ADMITTED: an authored premise that preprocessing folded to `false` is still a \
         problem-scope assertion, so the exporter must render it",
    );
    assert!(
        proof.contains("(assume t0 (< x x))"),
        "ADMITTED: the certificate must name the assertion the problem text wrote, got:\n{proof}"
    );
    assert!(
        !proof.contains("(error ") && !proof.contains("UNVERIFIABLE"),
        "a refusal must be reported as ABSENCE, never as an `(error ...)` document \
         masquerading as a proof, got:\n{proof}"
    );
}

/// No shape may hand back a refusal dressed as a proof. This is the property
/// the loud infallible wrapper broke; it holds for every backend result.
#[test]
fn no_backend_result_reports_a_refusal_as_a_proof_document() {
    let shapes: &[(&str, &[&str], &[&str])] = &[
        (
            "e9-postcondition",
            &["(declare-fun x () Int)"],
            &["(>= x 0)", "(<= x 18446744073709551615)", "(< x x)"],
        ),
        ("closed-shift", &[], &["(or (< 2 0) (>= 2 32))"]),
        (
            "nested-fold-false",
            &["(declare-fun w () Int)"],
            &["(>= w 0)", "(and (< 1 0) (>= w 0))"],
        ),
        (
            "ite-derived",
            &["(declare-fun c () Bool)", "(declare-fun z () Int)"],
            &["(= z (ite c 1 2))", "(> z 5)"],
        ),
    ];
    for (name, decls, asserts) in shapes {
        let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
        for decl in *decls {
            backend.add_raw_declaration(decl);
        }
        for assertion in *asserts {
            backend.assert_formula(assertion);
        }
        let AyProofResult::Unsat { proof, .. } = backend.check_sat().expect("solve") else {
            panic!("{name}: expected UNSAT");
        };
        let proof = proof.unwrap_or_else(|| panic!("{name}: expected a certificate"));
        assert!(
            !proof.contains("(error ") && !proof.contains("UNVERIFIABLE"),
            "{name}: a refusal must be reported as ABSENCE, got:\n{proof}"
        );
    }
}

#[test]
fn a_premise_set_without_the_assume_still_refuses_the_same_proof() {
    let mut backend = fold_to_false_backend();
    let AyProofResult::Unsat { .. } = backend.check_sat().expect("solve") else {
        panic!("expected UNSAT");
    };

    let proof = backend
        .executor
        .last_proof()
        .expect("anti-vacuity: the backend published a proof");
    let terms = backend.executor.terms();

    // PLANTED: the live post-preprocessing stack — the set the backend used to
    // hand over. The authored `(< x x)` slot was overwritten with `false`, so
    // this set does not contain the proof's reachable assume.
    let post_preprocessing = backend.executor.context().assertions.clone();
    let error = validate_reachable_assumes_in_problem_scope(proof, &post_preprocessing).expect_err(
        "PLANTED: an assume the given premise set does not contain must be REFUSED; \
             if this passes, the exporter's authority gate has been widened",
    );
    assert!(
        format!("{error}").contains("non-problem term"),
        "PLANTED: expected a non-problem-assume refusal, got: {error}"
    );
    assert!(
        try_export_alethe_with_problem_scope_and_overrides(proof, terms, &post_preprocessing, None)
            .is_err(),
        "PLANTED: the exporter itself must refuse, not just the standalone validator"
    );

    // And the degenerate set, so the refusal is not an artifact of one stack.
    assert!(
        validate_reachable_assumes_in_problem_scope(proof, &[]).is_err(),
        "PLANTED: an empty premise set authorises nothing"
    );
}
