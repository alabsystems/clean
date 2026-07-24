// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-checker soundness properties for DRAT, LRAT, Resolution,
//! Cutting Planes, FRAT, Extended Resolution, and GF(2) polynomial calculus.

use super::generators::{clause_strategy, cnf_strategy, drat_step_strategy};
use crate::sat_verify::cdcl::proof_logging::{verify_proof_log, verify_rup, ProofLog, ProofStep};
use crate::sat_verify::extended_resolution::ExtendedResolutionProof;
use crate::sat_verify::frat::{verify_frat, FratClauseId, FratStep};
use crate::sat_verify::frontier::extension_variable::ExtensionDef;
use crate::sat_verify::frontier::gf2_algebra::{cnf_to_gf2_system, verify_encoding_soundness};
use crate::sat_verify::lrat::{ClauseId, LratChecker};
use crate::sat_verify::proof_complexity::cutting_planes::{CpInequality, CuttingPlanesProof};
use crate::sat_verify::proof_complexity::resolution::ResolutionProof;
use crate::sat_verify::types::{Cnf, Lit, SatClause};

use proptest::collection::vec;
use proptest::prelude::*;

// ============================================================================
// DRAT soundness properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// Soundness: a random DRAT proof attempting to refute a trivially-SAT
    /// formula `{x1}` must NOT be accepted. The only satisfying assignment
    /// assigns x1=true, so empty clause is never RUP.
    #[test]
    fn prop_drat_cannot_refute_trivial_sat(
        steps in vec(drat_step_strategy(3, 3), 0..=8),
    ) {
        let formula = vec![vec![1]];
        let log = ProofLog {
            original_clauses: formula,
            steps,
        };
        let result = verify_proof_log(&log);
        // A trivially-SAT formula cannot have a valid refutation by a random
        // proof — empty clause cannot be derived from `{x1}` alone.
        if result.valid {
            prop_assert!(
                false,
                "SOUNDNESS VIOLATION: random DRAT proof accepted on SAT formula `{{x1}}`"
            );
        }
    }

    /// Determinism: verifying the same DRAT proof twice yields the same result.
    #[test]
    fn prop_drat_verify_deterministic(
        formula in cnf_strategy(4, 5, 3),
        steps in vec(drat_step_strategy(4, 3), 0..=5),
    ) {
        let log = ProofLog {
            original_clauses: formula,
            steps,
        };
        let r1 = verify_proof_log(&log);
        let r2 = verify_proof_log(&log);
        prop_assert_eq!(r1.valid, r2.valid);
    }

    /// `verify_rup` is deterministic and panic-free.
    #[test]
    fn prop_drat_verify_rup_deterministic(
        formula in cnf_strategy(4, 6, 3),
        claim in clause_strategy(4, 3),
    ) {
        let r1 = verify_rup(&formula, &claim);
        let r2 = verify_rup(&formula, &claim);
        prop_assert_eq!(r1, r2);
    }

    /// Valid DRAT: for every n in 1..=5, {x_i} AND {-x_i} for i=1..=n is UNSAT,
    /// and adding the empty clause via RUP must verify.
    #[test]
    fn prop_drat_complementary_units_always_verify(
        n in 1u32..=5,
    ) {
        let mut formula = Vec::new();
        for v in 1..=n as i32 {
            formula.push(vec![v]);
            formula.push(vec![-v]);
        }
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![ProofStep::Add(vec![])],
        };
        let result = verify_proof_log(&log);
        prop_assert!(result.valid, "n={n}: complementary units must yield UNSAT");
    }
}

// ============================================================================
// LRAT soundness properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// Soundness: random LRAT hints on a SAT formula must not derive the empty
    /// clause. The formula `{x1, x2}` is SAT (assign both true).
    #[test]
    fn prop_lrat_cannot_refute_sat_formula(
        hints in vec(1i64..=20, 0..=6),
    ) {
        let mut checker = LratChecker::new(2);
        checker
            .add_original(ClauseId(1), &[Lit(1), Lit(2)])
            .expect("add original");
        let result = checker.add_derived(ClauseId(2), &[], &hints);
        prop_assert!(
            result.is_err(),
            "SOUNDNESS VIOLATION: LRAT accepted empty clause from SAT formula"
        );
    }

    /// No panic: random LRAT operations on a random formula must not panic.
    #[test]
    fn prop_lrat_random_ops_no_panic(
        clauses in cnf_strategy(3, 4, 3),
        hints in vec(1i64..=10, 0..=5),
        target_clause in clause_strategy(3, 3),
    ) {
        let result = std::panic::catch_unwind(|| {
            let mut checker = LratChecker::new(3);
            for (i, c) in clauses.iter().enumerate() {
                let lits: Vec<Lit> = c.iter().map(|&l| Lit(l)).collect();
                let _ = checker.add_original(ClauseId(i as u64 + 1), &lits);
            }
            let target_lits: Vec<Lit> = target_clause.iter().map(|&l| Lit(l)).collect();
            let _ = checker.add_derived(
                ClauseId(clauses.len() as u64 + 1),
                &target_lits,
                &hints,
            );
        });
        prop_assert!(result.is_ok(), "LRAT panicked on random input");
    }

    /// Deleted clause must not be usable as a hint.
    #[test]
    fn prop_lrat_deleted_hint_rejected(
        var in 1i32..=5,
    ) {
        let mut checker = LratChecker::new(var as u32);
        checker.add_original(ClauseId(1), &[Lit(var)]).expect("add1");
        checker.add_original(ClauseId(2), &[Lit(-var)]).expect("add2");
        checker.delete(ClauseId(1)).expect("delete");
        let result = checker.add_derived(ClauseId(3), &[], &[1, 2]);
        prop_assert!(
            result.is_err(),
            "deleted clause usable as hint — soundness violated"
        );
    }
}

// ============================================================================
// Resolution soundness properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// Soundness: foreign clauses not in the formula must be rejected by
    /// `verify_against_formula`.
    #[test]
    fn prop_resolution_foreign_input_rejected(
        foreign_var in 5i32..=20,
    ) {
        let formula = vec![vec![1, 2]];
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![foreign_var]);
        proof.add_input(vec![-foreign_var]);
        let _ = proof.add_resolve(0, 1, foreign_var);
        prop_assert!(
            !proof.verify_against_formula(&formula),
            "foreign resolution inputs accepted — soundness violated"
        );
    }

    /// Invalid step indices must return an error, not panic.
    #[test]
    fn prop_resolution_invalid_indices_error(
        idx_l in 5usize..=100,
        idx_r in 5usize..=100,
        pivot in 1i32..=10,
    ) {
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]); // index 0
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            proof.add_resolve(idx_l, idx_r, pivot)
        }));
        let inner = result.expect("invalid resolution indices panicked");
        prop_assert!(inner.is_err(), "invalid indices accepted");
    }

    /// Valid refutations: for every variable v, {v} AND {-v} resolves to empty.
    #[test]
    fn prop_resolution_complementary_units_verify(
        v in 1i32..=100,
    ) {
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![v]);
        proof.add_input(vec![-v]);
        prop_assert!(proof.add_resolve(0, 1, v).is_ok());
        prop_assert!(proof.verify(), "complementary units must refute");
    }

    /// Non-refutations don't verify: if resolution ends with a non-empty clause,
    /// `verify()` must return false.
    #[test]
    fn prop_resolution_non_empty_final_not_verified(
        lit_a in 1i32..=5,
        lit_b in 6i32..=10,
    ) {
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![lit_a, lit_b]);
        proof.add_input(vec![-lit_a, lit_b]);
        prop_assert!(proof.add_resolve(0, 1, lit_a).is_ok());
        prop_assert!(!proof.verify(), "non-empty final clause verified");
    }
}

// ============================================================================
// Cutting planes soundness properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Soundness: non-positive multiplication scalars must be rejected.
    #[test]
    fn prop_cp_non_positive_scalar_rejected(
        scalar in -100i64..=0,
    ) {
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![1], 1));
        prop_assert!(
            proof.multiply(a, scalar).is_err(),
            "non-positive scalar {scalar} accepted — soundness violated"
        );
    }

    /// Soundness: non-positive divisors must be rejected.
    #[test]
    fn prop_cp_non_positive_divisor_rejected(
        divisor in -100i64..=0,
    ) {
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![1], 1));
        prop_assert!(
            proof.divide(a, divisor).is_err(),
            "non-positive divisor {divisor} accepted — soundness violated"
        );
    }

    /// Invalid indices for `CuttingPlanesProof::add` return an error, not panic.
    #[test]
    fn prop_cp_invalid_indices_error(
        l in 1usize..=100,
        r in 1usize..=100,
    ) {
        let mut proof = CuttingPlanesProof::new();
        let _ = proof.add_input(CpInequality::new(vec![1], 1));
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            proof.add(l, r)
        }));
        let inner = result.expect("CP.add panicked on invalid indices");
        prop_assert!(inner.is_err());
    }

    /// `CpInequality::evaluate` is consistent with the arithmetic definition.
    #[test]
    fn prop_cp_evaluate_matches_definition(
        coeffs in vec(-5i64..=5, 1..=5),
        rhs in -10i64..=10,
        assignment in vec(any::<bool>(), 1..=5),
    ) {
        let ineq = CpInequality::new(coeffs.clone(), rhs);
        let sum: i64 = coeffs
            .iter()
            .enumerate()
            .map(|(i, &c)| if *assignment.get(i).unwrap_or(&false) { c } else { 0 })
            .sum();
        let expected = sum >= rhs;
        prop_assert_eq!(ineq.evaluate(&assignment), expected);
    }

    /// Soundness: formula binding rejects proofs whose inputs are not in the
    /// provided formula.
    #[test]
    fn prop_cp_formula_binding_rejects_foreign(
        foreign_coeff in 10i64..=50,
    ) {
        let formula = vec![CpInequality::new(vec![1], 1)];
        let mut proof = CuttingPlanesProof::new();
        proof.add_input(CpInequality::new(vec![1], 1));
        proof.add_input(CpInequality::new(vec![foreign_coeff], 1)); // foreign
        let _ = proof.add(0, 1);
        prop_assert!(
            !proof.verify_against_formula(&formula),
            "foreign CP input accepted — soundness violated"
        );
    }
}

// ============================================================================
// FRAT soundness properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Empty FRAT proof is always rejected.
    #[test]
    fn prop_frat_empty_proof_rejected(
        formula in cnf_strategy(3, 3, 2),
    ) {
        let result = verify_frat(&formula, &[]);
        prop_assert!(
            result.is_err(),
            "empty FRAT proof accepted — soundness violated"
        );
    }

    /// Soundness: a FRAT lemma deriving the empty clause from a trivially-SAT
    /// formula `{x1, x2}` must fail.
    #[test]
    fn prop_frat_cannot_refute_sat_formula(
        lemma_id in 10u64..=1000,
    ) {
        let formula = vec![vec![1, 2]];
        let steps = vec![
            FratStep::Original {
                id: FratClauseId(1),
                clause: vec![1, 2],
            },
            FratStep::Lemma {
                id: FratClauseId(lemma_id),
                clause: vec![],
            },
        ];
        let result = verify_frat(&formula, &steps);
        let refuted = result.map(|r| r.valid).unwrap_or(false);
        prop_assert!(
            !refuted,
            "SOUNDNESS VIOLATION: FRAT empty-lemma accepted on SAT formula"
        );
    }

    /// Duplicate clause IDs rejected.
    #[test]
    fn prop_frat_duplicate_id_rejected(
        id in 1u64..=100,
    ) {
        let formula = vec![vec![1], vec![-1]];
        let steps = vec![
            FratStep::Original { id: FratClauseId(id), clause: vec![1] },
            FratStep::Original { id: FratClauseId(id), clause: vec![-1] },
        ];
        let result = verify_frat(&formula, &steps);
        prop_assert!(result.is_err(), "duplicate FRAT id accepted");
    }

    /// No panic on random FRAT steps.
    #[test]
    fn prop_frat_random_steps_no_panic(
        cnf in cnf_strategy(3, 4, 3),
        steps_raw in vec(
            (0u8..5, 1u64..=100, clause_strategy(3, 3)),
            0..=10,
        ),
    ) {
        let steps: Vec<FratStep> = steps_raw
            .into_iter()
            .map(|(kind, id, clause)| match kind {
                0 => FratStep::Original { id: FratClauseId(id), clause },
                1 => FratStep::Add { id: FratClauseId(id), clause },
                2 => FratStep::Lemma { id: FratClauseId(id), clause },
                3 => FratStep::Delete { id: FratClauseId(id), clause },
                _ => FratStep::Finalize { id: FratClauseId(id) },
            })
            .collect();
        let result = std::panic::catch_unwind(|| verify_frat(&cnf, &steps));
        prop_assert!(result.is_ok(), "FRAT panicked on random steps");
    }
}

// ============================================================================
// Extended resolution soundness properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Soundness: extension variables colliding with base variables rejected.
    #[test]
    fn prop_extres_variable_collision_rejected(
        base_vars in 2u32..=10,
        collision_var in 1u32..=10,
    ) {
        let collision_var = collision_var.min(base_vars);
        let cnf = Cnf {
            num_vars: base_vars,
            clauses: vec![SatClause(vec![Lit(1)])],
        };
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![ExtensionDef {
                var: collision_var,
                literal_a: 1,
                literal_b: -1,
            }],
            resolution_proof: ResolutionProof::new(),
        };
        prop_assert!(
            ext.verify_freshness().is_err(),
            "collision of extension var {collision_var} with base accepted"
        );
    }

    /// Duplicate extension variables rejected.
    #[test]
    fn prop_extres_duplicate_extension_rejected(
        ext_var in 10u32..=100,
    ) {
        let cnf = Cnf {
            num_vars: 3,
            clauses: vec![SatClause(vec![Lit(1)])],
        };
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![
                ExtensionDef { var: ext_var, literal_a: 1, literal_b: 2 },
                ExtensionDef { var: ext_var, literal_a: -1, literal_b: 2 },
            ],
            resolution_proof: ResolutionProof::new(),
        };
        prop_assert!(
            ext.verify_freshness().is_err(),
            "duplicate extension var {ext_var} accepted"
        );
    }
}

// ============================================================================
// GF(2) polynomial calculus properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Encoding soundness: for every small random formula, the GF(2) encoding
    /// is sound (proven over all assignments).
    #[test]
    fn prop_gf2_encoding_sound(
        clauses in cnf_strategy(3, 5, 3),
    ) {
        if clauses.is_empty() {
            return Ok(());
        }
        let polys = cnf_to_gf2_system(&clauses);
        prop_assert!(
            verify_encoding_soundness(&clauses, &polys, 3),
            "GF(2) encoding unsound for formula {clauses:?}"
        );
    }
}
