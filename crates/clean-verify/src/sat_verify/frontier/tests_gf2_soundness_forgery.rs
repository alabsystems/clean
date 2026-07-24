// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioral regression tests for #3330: `pc_soundness_gf2` must re-verify
//! each proof step by rebuilding from `clauses + steps`, not trust the
//! pre-built `derived` field of a `PcProof`.
//!
//! These tests construct `PcProof` values by directly setting the public
//! `steps`, `derived`, and `max_degree` fields (bypassing `PcProof::build()`)
//! so the `derived` polynomials do not match what the rules would actually
//! produce. If `pc_soundness_gf2` trusted the pre-built `derived` field,
//! it would accept these forgeries and claim a satisfiable formula is UNSAT
//! (or accept an invalid proof of an unsatisfiable formula).
//!
//! Post-fix (commit d940904bd on main), `pc_soundness_gf2` rebuilds the
//! proof via `PcProof::build()` before running the encoding and verify
//! checks, so every step is re-executed from the steps + clause list.
//! The rebuild re-derives the same intermediate polynomials `PcProof::build`
//! would compute, so any forgery in the original `derived` field is ignored
//! and the rebuilt proof must stand or fall on its own.

use super::gf2_algebra::*;

/// Satisfiable formula with a forged `Add` step claiming the final
/// derived polynomial is 1.
///
/// Clauses: `{x1}, {-x2}`. This is satisfiable (e.g., x1=true, x2=false).
/// No valid PC proof can derive the constant 1.
///
/// Pre-fix behavior: `pc_soundness_gf2` reads `proof.derived.last()`,
/// sees `1`, and returns `Ok(())` -- incorrectly accepting a "proof"
/// that the formula is UNSAT. The `ClauseAxiom` encoding check in the
/// original function only validates that `ClauseAxiom` steps match the
/// expected clause polynomial; `Add`/`MulVar`/`MulPoly` steps are
/// trusted without re-verification.
///
/// Post-fix behavior: `PcProof::build` re-executes the `Add(0, 1)` step
/// and produces `(1 + x1) + x2 = 1 + x1 + x2`, which is not the constant
/// 1. `rebuilt.verify()` returns `Err(PcError::NotContradiction(3))`.
#[test]
fn test_pc_soundness_rejects_forged_add_on_sat_formula() {
    let clauses = vec![vec![1], vec![-2]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];

    // Honest clause-axiom derivations for the first two steps,
    // then a fabricated final polynomial equal to 1.
    let forged_derived = vec![
        Gf2Poly::from_clause(&clauses[0]),
        Gf2Poly::from_clause(&clauses[1]),
        Gf2Poly::one(), // FORGERY: true Add(0, 1) = 1 + x1 + x2
    ];

    let forged = PcProof {
        steps,
        derived: forged_derived,
        max_degree: 1,
    };

    let result = pc_soundness_gf2(&clauses, &forged);
    assert!(
        result.is_err(),
        "forged PcProof for satisfiable formula must be rejected, got: {result:?}"
    );
}

/// UNSAT formula with a forged `Add` step that skips a required input.
///
/// Clauses: `{x1}, {-x1}` (UNSAT). The valid proof has 3 steps:
/// ClauseAxiom(0) -> 1+x1, ClauseAxiom(1) -> x1, Add(0, 1) -> 1.
///
/// The forgery skips `ClauseAxiom(1)` and uses `Add(0, 0)`. In GF(2),
/// `p + p = 0` for any polynomial `p`, so the actual `Add(0, 0)` derives
/// the zero polynomial, not 1.
///
/// Pre-fix behavior: the encoding check only looks at `ClauseAxiom` steps.
/// `Add(0, 0)` is not a `ClauseAxiom`, so the encoding check passes.
/// The final polynomial in `proof.derived` is the forged 1, so the
/// `verify()` call succeeds. `pc_soundness_gf2` returns `Ok(())`.
///
/// Post-fix behavior: `PcProof::build` computes `Add(0, 0)` as `zero()`.
/// `rebuilt.verify()` rejects with `PcError::NotContradiction(0)`.
#[test]
fn test_pc_soundness_rejects_forged_self_add_on_unsat_formula() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::Add(0, 0), // self-add: always 0 in GF(2)
    ];

    let forged_derived = vec![
        Gf2Poly::from_clause(&clauses[0]),
        Gf2Poly::one(), // FORGERY: actual Add(0, 0) = 0
    ];

    let forged = PcProof {
        steps,
        derived: forged_derived,
        max_degree: 1,
    };

    let result = pc_soundness_gf2(&clauses, &forged);
    assert!(
        result.is_err(),
        "forged PcProof with fake self-add must be rejected, got: {result:?}"
    );
}

/// Forgery at a `ClauseAxiom` step: claim the clause polynomial is 1
/// even though the encoded clause is a degree-2 polynomial.
///
/// Clauses: `{x1, x2}` (satisfiable). The encoded polynomial is
/// `(1 + x1)(1 + x2) = 1 + x1 + x2 + x1*x2`, not the constant 1.
///
/// Pre-fix behavior: the explicit `ClauseAxiom` encoding check at the
/// top of `pc_soundness_gf2` catches this particular forgery because
/// it re-computes `from_clause(clauses[idx])` and compares to the
/// (forged) `proof.derived[step_idx]`. Returns `EncodingMismatch`.
/// So pre-fix, this specific shape was already detected.
///
/// Post-fix behavior: the rebuild produces the correct clause polynomial
/// (ignoring the forged `derived` field entirely). The subsequent
/// encoding check trivially passes (rebuilt == expected), and the
/// final-polynomial check fails because `1 + x1 + x2 + x1*x2` is not 1.
/// Returns `NotContradiction`. Either way, the forgery is rejected,
/// and the test documents that both the old and new code paths reject
/// this specific attack shape.
#[test]
fn test_pc_soundness_rejects_forged_clause_axiom_derivation() {
    let clauses = vec![vec![1, 2]];
    let steps = vec![PcStepTracked::ClauseAxiom(0)];

    let forged_derived = vec![Gf2Poly::one()]; // FORGERY

    let forged = PcProof {
        steps,
        derived: forged_derived,
        max_degree: 0,
    };

    let result = pc_soundness_gf2(&clauses, &forged);
    assert!(
        result.is_err(),
        "forged ClauseAxiom derivation must be rejected, got: {result:?}"
    );
}

/// Forgery with a fake `MulVar` step that claims multiplication by a
/// variable collapses a polynomial to 1.
///
/// Clauses: `{x1, x2}` (satisfiable). Actual clause polynomial:
/// `(1+x1)(1+x2) = 1 + x1 + x2 + x1*x2`.
///
/// Forgery claims `MulVar(0, 0)` (multiply clause poly by x1) produces
/// the constant 1. The true value is
/// `(1 + x1 + x2 + x1*x2) * x1 = x1 + x1^2 + x1*x2 + x1^2*x2`
/// `= x1 + x1 + x1*x2 + x1*x2 = 0` (in multilinear GF(2)).
///
/// Post-fix behavior: the rebuild re-executes `MulVar(0, 0)` and
/// produces 0. `rebuilt.verify()` rejects with `NotContradiction`.
#[test]
fn test_pc_soundness_rejects_forged_mul_var_step() {
    let clauses = vec![vec![1, 2]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::MulVar(0, 0), // multiply by x1
    ];

    let honest_clause_poly = Gf2Poly::from_clause(&clauses[0]);
    let forged_derived = vec![
        honest_clause_poly,
        Gf2Poly::one(), // FORGERY: true MulVar(0, 0) = 0
    ];

    let forged = PcProof {
        steps,
        derived: forged_derived,
        max_degree: 2,
    };

    let result = pc_soundness_gf2(&clauses, &forged);
    assert!(
        result.is_err(),
        "forged MulVar step must be rejected, got: {result:?}"
    );
}

/// Sanity check: a correct proof constructed via `PcProof::build` still
/// passes `pc_soundness_gf2` after the fix. This ensures the rebuild did
/// not break the happy path.
#[test]
fn test_pc_soundness_accepts_honest_build_proof() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];
    let proof = PcProof::build(&clauses, steps).expect("honest proof builds");
    pc_soundness_gf2(&clauses, &proof).expect("honest proof passes soundness");
}
