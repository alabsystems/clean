// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Differential conformance test infrastructure for Alethe SMT proof checker.

use crate::smt_verify::dag::SmtTheory;
use crate::smt_verify::trust::StepTrustLevel;
use crate::smt_verify::{
    verify_alethe_proof, verify_alethe_proof_with_mode, AletheVerifyError, VerifyMode,
};

fn expect_valid_fully_verified(proof_text: &str) -> crate::smt_verify::trust::SmtVerifyResult {
    let result = verify_alethe_proof(proof_text)
        .unwrap_or_else(|err| panic!("proof should verify successfully: {err:?}\n{proof_text}"));
    assert!(result.valid, "proof should be valid");
    assert!(
        result.stats.is_fully_verified(),
        "proof should have no trusted steps: {:?}",
        result.stats
    );
    result
}

fn expect_holey_acceptance(proof_text: &str) -> crate::smt_verify::trust::SmtVerifyResult {
    let result = verify_alethe_proof(proof_text).unwrap_or_else(|err| {
        panic!("holey proof should be accepted in permissive mode: {err:?}\n{proof_text}")
    });
    assert!(
        result.valid,
        "holey proof should still derive the empty clause"
    );
    assert!(
        !result.stats.is_fully_verified(),
        "holey proof should not be fully verified"
    );
    assert!(result.stats.trusted >= 1, "holey proof should record trust");
    assert!(
        result
            .verdicts
            .iter()
            .any(|verdict| verdict.trust_level == StepTrustLevel::Trusted),
        "holey proof should expose a trusted step"
    );
    result
}

// ============================================================================
// Valid LRA proofs
// ============================================================================

/// Accepts a simple real-arithmetic Farkas proof for `x > 0` and `x <= 0`.
#[test]
fn test_conformance_alethe_lra_simple_farkas_accepts() {
    let proof_text = r#"
        (declare-const x Real)
        (assume h1 (> x 0.0))
        (assume h2 (<= x 0.0))
        (step t1 (cl (not (> x 0.0)) (not (<= x 0.0)))
            :rule la_generic :args (1.0 1.0))
        (step t2 (cl (not (<= x 0.0)))
            :rule resolution :premises (h1 t1))
        (step t3 (cl)
            :rule resolution :premises (h2 t2))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Lra),
        Some(&1)
    );
}

/// Accepts a two-variable LRA Farkas proof for `x + y >= 1`, `x <= 0`, `y <= 0`.
#[test]
fn test_conformance_alethe_lra_two_variable_farkas_accepts() {
    let proof_text = r#"
        (declare-const x Real)
        (declare-const y Real)
        (assume h1 (>= (+ x y) 1.0))
        (assume h2 (<= x 0.0))
        (assume h3 (<= y 0.0))
        (step t1
            (cl (not (>= (+ x y) 1.0)) (not (<= x 0.0)) (not (<= y 0.0)))
            :rule la_generic :args (1.0 1.0 1.0))
        (step t2
            (cl (not (<= x 0.0)) (not (<= y 0.0)))
            :rule resolution :premises (h1 t1))
        (step t3
            (cl (not (<= y 0.0)))
            :rule resolution :premises (h2 t2))
        (step t4 (cl)
            :rule resolution :premises (h3 t3))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Lra),
        Some(&1)
    );
}

// ============================================================================
// Valid LIA proofs
// ============================================================================

/// Accepts a simple integer-arithmetic bound conflict proved with `lia_generic`.
#[test]
fn test_conformance_alethe_lia_simple_bounds_accepts() {
    let proof_text = r#"
        (declare-const x Int)
        (assume h1 (>= x 1))
        (assume h2 (<= x (- 1)))
        (step t1 (cl (not (>= x 1)) (not (<= x (- 1))))
            :rule lia_generic :args (1 1))
        (step t2 (cl (not (<= x (- 1))))
            :rule resolution :premises (h1 t1))
        (step t3 (cl)
            :rule resolution :premises (h2 t2))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Lia),
        Some(&1)
    );
}

/// Accepts a two-variable integer Farkas proof for `x + y >= 3`, `x <= 0`, `y <= 0`.
#[test]
fn test_conformance_alethe_lia_two_variable_bounds_accepts() {
    let proof_text = r#"
        (declare-const x Int)
        (declare-const y Int)
        (assume h1 (>= (+ x y) 3))
        (assume h2 (<= x 0))
        (assume h3 (<= y 0))
        (step t1
            (cl (not (>= (+ x y) 3)) (not (<= x 0)) (not (<= y 0)))
            :rule lia_generic :args (1 1 1))
        (step t2
            (cl (not (<= x 0)) (not (<= y 0)))
            :rule resolution :premises (h1 t1))
        (step t3
            (cl (not (<= y 0)))
            :rule resolution :premises (h2 t2))
        (step t4 (cl)
            :rule resolution :premises (h3 t3))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Lia),
        Some(&1)
    );
}

// ============================================================================
// Valid EUF proofs
// ============================================================================

/// Accepts an EUF transitivity proof for `a = b`, `b = c`, and `a != c`.
#[test]
fn test_conformance_alethe_euf_transitivity_accepts() {
    let proof_text = r#"
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assume h1 (= a b))
        (assume h2 (= b c))
        (assume h3 (not (= a c)))
        (step t1 (cl (not (= a b)) (not (= b c)) (= a c))
            :rule eq_transitive)
        (step t2 (cl (not (= b c)) (= a c))
            :rule resolution :premises (h1 t1))
        (step t3 (cl (= a c))
            :rule resolution :premises (h2 t2))
        (step t4 (cl)
            :rule resolution :premises (h3 t3))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Euf),
        Some(&1)
    );
}

/// Accepts an EUF congruence proof for `a = b` and `f(a) != f(b)`.
#[test]
fn test_conformance_alethe_euf_congruence_accepts() {
    let proof_text = r#"
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (assume h1 (= a b))
        (assume h2 (not (= (f a) (f b))))
        (step t1 (cl (not (= a b)) (= (f a) (f b)))
            :rule eq_congruent)
        (step t2 (cl (= (f a) (f b)))
            :rule resolution :premises (h1 t1))
        (step t3 (cl)
            :rule resolution :premises (h2 t2))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Euf),
        Some(&1)
    );
}

// ============================================================================
// Valid BV proofs
// ============================================================================

/// Accepts a BV contradiction from assigning an 8-bit variable two different values.
#[test]
fn test_conformance_alethe_bv_conflicting_assignments_accepts() {
    let proof_text = r#"
        (declare-const x (_ BitVec 8))
        (assume h1 (= x #b00000101))
        (assume h2 (= x #b00000011))
        (step t1 (cl (not (= x #b00000101)) (not (= x #b00000011)))
            :rule bv_bitblast)
        (step t2 (cl (not (= x #b00000011)))
            :rule resolution :premises (h1 t1))
        (step t3 (cl)
            :rule resolution :premises (h2 t2))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Bv),
        Some(&1)
    );
}

/// Accepts a BV extract lemma showing the low byte of `#x1234` is `#x34`.
#[test]
fn test_conformance_alethe_bv_extract_contradiction_accepts() {
    let proof_text = r#"
        (declare-const x (_ BitVec 16))
        (assume h1 (= x #x1234))
        (assume h2 (not (= ((_ extract 7 0) x) #x34)))
        (step t1 (cl (not (= x #x1234)) (= ((_ extract 7 0) x) #x34))
            :rule bv_bitblast)
        (step t2 (cl (= ((_ extract 7 0) x) #x34))
            :rule resolution :premises (h1 t1))
        (step t3 (cl)
            :rule resolution :premises (h2 t2))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Bv),
        Some(&1)
    );
}

// ============================================================================
// Valid Array proofs
// ============================================================================

/// Accepts a read-over-write proof for `select(store(a, 0, 5), 0) = 5`.
#[test]
fn test_conformance_alethe_arrays_read_over_write_accepts() {
    let proof_text = r#"
        (declare-const a (Array Int Int))
        (assume h1 (not (= (select (store a 0 5) 0) 5)))
        (step t1 (cl (= (select (store a 0 5) 0) 5))
            :rule read_over_write_pos)
        (step t2 (cl)
            :rule resolution :premises (h1 t1))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Arrays),
        Some(&1)
    );
}

/// Accepts an extensionality proof using a shared witness index `k`.
#[test]
fn test_conformance_alethe_arrays_extensionality_accepts() {
    let proof_text = r#"
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const k Int)
        (assume h1 (not (= a b)))
        (assume h2 (= (select a k) (select b k)))
        (step t1 (cl (= a b) (not (= (select a k) (select b k))))
            :rule extensionality)
        (step t2 (cl (not (= (select a k) (select b k))))
            :rule resolution :premises (h1 t1))
        (step t3 (cl)
            :rule resolution :premises (h2 t2))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Arrays),
        Some(&1)
    );
}

// ============================================================================
// Valid String proofs
// ============================================================================

/// Accepts a concrete string-length proof for `str.len("abc") = 3`.
#[test]
fn test_conformance_alethe_strings_length_accepts() {
    let proof_text = r#"
        (assume h1 (not (= (str.len "abc") 3)))
        (step t1 (cl (= (str.len "abc") 3))
            :rule string_length)
        (step t2 (cl)
            :rule resolution :premises (h1 t1))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Strings),
        Some(&1)
    );
}

/// Accepts a string normal-form proof for the empty-concatenation identity.
#[test]
fn test_conformance_alethe_strings_empty_concat_accepts() {
    let proof_text = r#"
        (declare-const s String)
        (assume h1 (not (= (str.++ "" s) s)))
        (step t1 (cl (= (str.++ "" s) s))
            :rule string_code_inj)
        (step t2 (cl)
            :rule resolution :premises (h1 t1))
    "#;

    let result = expect_valid_fully_verified(proof_text);
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Strings),
        Some(&1)
    );
}

// ============================================================================
// Invalid proofs
// ============================================================================

/// Rejects a proof that parses but never derives the empty clause.
#[test]
fn test_conformance_alethe_invalid_no_empty_clause_rejects() {
    let proof_text = r#"
        (declare-const p Bool)
        (assume h1 p)
    "#;

    let result = verify_alethe_proof(proof_text);
    assert!(matches!(
        result,
        Err(AletheVerifyError::Verify(_)) | Err(AletheVerifyError::InvalidProof { .. })
    ));
}

/// Rejects a proof containing a completely unknown Alethe rule.
#[test]
fn test_conformance_alethe_invalid_bogus_rule_rejects() {
    let proof_text = r#"
        (step t1 (cl) :rule completely_bogus_rule)
    "#;

    let result = verify_alethe_proof(proof_text);
    assert!(matches!(result, Err(AletheVerifyError::Parse(_))));
}

/// Rejects a proof with a `trust` step when verification runs in strict mode.
#[test]
fn test_conformance_alethe_invalid_strict_trust_step_rejects() {
    let proof_text = r#"
        (declare-const p Bool)
        (assume h1 p)
        (step t1 (cl (not p)) :rule trust)
        (step t2 (cl) :rule resolution :premises (h1 t1))
    "#;

    let permissive = verify_alethe_proof(proof_text).expect("permissive mode should accept");
    assert!(permissive.valid);
    assert_eq!(permissive.stats.trusted, 1);

    let strict = verify_alethe_proof_with_mode(proof_text, VerifyMode::Strict);
    assert!(matches!(strict, Err(AletheVerifyError::Verify(_))));
}

// ============================================================================
// Holey proof detection
// ============================================================================

/// Detects a permissively accepted proof that contains a `trust` hole.
#[test]
fn test_conformance_alethe_holey_trust_step_detects() {
    let proof_text = r#"
        (declare-const p Bool)
        (assume h1 p)
        (step t1 (cl (not p)) :rule trust)
        (step t2 (cl) :rule resolution :premises (h1 t1))
    "#;

    let result = expect_holey_acceptance(proof_text);
    assert_eq!(result.stats.trusted, 1);
}

/// Detects a permissively accepted proof that contains a `hole` step.
#[test]
fn test_conformance_alethe_holey_hole_step_detects() {
    let proof_text = r#"
        (declare-const p Bool)
        (assume h1 p)
        (step t1 (cl (not p)) :rule hole)
        (step t2 (cl) :rule resolution :premises (h1 t1))
    "#;

    let result = expect_holey_acceptance(proof_text);
    assert_eq!(result.stats.trusted, 1);
}
