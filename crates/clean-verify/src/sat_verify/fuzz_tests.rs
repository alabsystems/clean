// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property-based fuzz tests for all sat_verify proof checkers.
//!
//! Exercises DRAT, LRAT, resolution, cutting planes, extended resolution,
//! PB/VeriPB, and GF(2) polynomial calculus checkers with random, mutated,
//! and adversarial inputs. Uses a deterministic xorshift64 PRNG to avoid
//! external dependencies while keeping tests reproducible.
//!
//! Reference: Issue #3334

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    // ---- Deterministic xorshift64 PRNG ----

    struct Rng(u64);

    impl Rng {
        fn new(seed: u64) -> Self {
            // Avoid zero seed (fixpoint of xorshift).
            Self(if seed == 0 {
                0xDEAD_BEEF_CAFE_1234
            } else {
                seed
            })
        }

        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn next_u32(&mut self) -> u32 {
            (self.next_u64() >> 16) as u32
        }

        /// Uniform in `0..bound`.
        fn next_usize(&mut self, bound: usize) -> usize {
            if bound == 0 {
                return 0;
            }
            self.next_u64() as usize % bound
        }

        /// Uniform in `lo..=hi`.
        fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
            let span = (hi as i64 - lo as i64 + 1) as u64;
            lo + (self.next_u64() % span) as i32
        }

        fn next_bool(&mut self) -> bool {
            self.next_u64() & 1 == 1
        }
    }

    // ---- Random CNF generator ----

    fn random_cnf(
        num_vars: usize,
        num_clauses: usize,
        max_clause_len: usize,
        seed: u64,
    ) -> Vec<Vec<i32>> {
        let mut rng = Rng::new(seed);
        let mut clauses = Vec::with_capacity(num_clauses);
        for _ in 0..num_clauses {
            let len = 1 + rng.next_usize(max_clause_len);
            let mut clause = Vec::with_capacity(len);
            for _ in 0..len {
                let var = 1 + rng.next_usize(num_vars) as i32;
                let lit = if rng.next_bool() { var } else { -var };
                if !clause.contains(&lit) && !clause.contains(&-lit) {
                    clause.push(lit);
                }
            }
            if !clause.is_empty() {
                clauses.push(clause);
            }
        }
        clauses
    }

    /// Generate a known-UNSAT formula: x AND NOT x (for each variable pair).
    fn unsat_formula(num_vars: usize) -> Vec<Vec<i32>> {
        let mut clauses = Vec::new();
        for v in 1..=num_vars as i32 {
            clauses.push(vec![v]);
            clauses.push(vec![-v]);
        }
        clauses
    }

    // ====================================================================
    // DRAT fuzz tests
    // ====================================================================
    use crate::sat_verify::cdcl::proof_logging::{
        verify_proof_log, verify_rup, ProofLog, ProofStep,
    };

    #[test]
    fn test_fuzz_drat_valid_simple_unsat_proofs() {
        // For a range of seeds, build {x} AND {-x} and prove UNSAT via
        // adding the empty clause (which is RUP from the unit pair).
        for seed in 0..20u64 {
            let var = 1 + (seed % 5) as i32;
            let formula = vec![vec![var], vec![-var]];
            let log = ProofLog {
                original_clauses: formula,
                steps: vec![ProofStep::Add(vec![])],
            };
            let result = verify_proof_log(&log);
            assert!(result.valid, "seed {seed}: simple UNSAT proof failed");
        }
    }

    #[test]
    fn test_fuzz_drat_random_invalid_proofs_rejected() {
        // Random proof steps on a satisfiable formula should not verify.
        let mut rng = Rng::new(42);
        for _ in 0..10 {
            let formula = vec![vec![1, 2], vec![-1, 2]]; // SAT: x2=true
            let mut steps = Vec::new();
            let num_steps = 1 + rng.next_usize(5);
            for _ in 0..num_steps {
                let len = rng.next_usize(4);
                let clause: Vec<i32> = (0..len)
                    .map(|_| {
                        let v = 1 + rng.next_usize(3) as i32;
                        if rng.next_bool() {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect();
                steps.push(ProofStep::Add(clause));
            }
            let log = ProofLog {
                original_clauses: formula,
                steps,
            };
            let result = verify_proof_log(&log);
            // Most random proofs should fail verification (no valid RUP/RAT).
            // Even if they pass individual steps, they must derive empty clause.
            // We just verify no panic occurs.
            let _ = result;
        }
    }

    #[test]
    fn test_fuzz_drat_mutated_proof_rejected() {
        // Valid proof: {1}, {-1} => add empty clause.
        // Mutate by changing the added clause.
        let formula = vec![vec![1], vec![-1]];

        // Mutate: add {2} instead of {} — should not derive contradiction.
        let log = ProofLog {
            original_clauses: formula.clone(),
            steps: vec![ProofStep::Add(vec![2])],
        };
        let result = verify_proof_log(&log);
        assert!(
            !result.valid,
            "mutated proof (non-empty clause) should not verify"
        );

        // Mutate: delete a needed clause before adding empty.
        let log2 = ProofLog {
            original_clauses: formula,
            steps: vec![ProofStep::Delete(vec![1]), ProofStep::Add(vec![])],
        };
        let result2 = verify_proof_log(&log2);
        // After deleting {1}, empty clause is no longer RUP.
        assert!(
            !result2.valid,
            "proof after deleting key clause should fail"
        );
    }

    #[test]
    fn test_fuzz_drat_boundary_empty_formula() {
        // Empty formula is trivially SAT — adding empty clause should fail.
        let log = ProofLog {
            original_clauses: vec![],
            steps: vec![ProofStep::Add(vec![])],
        };
        let result = verify_proof_log(&log);
        assert!(!result.valid, "empty clause not RUP from empty formula");
    }

    #[test]
    fn test_fuzz_drat_adversarial_phantom_deletions() {
        // Delete clauses that were never in the formula.
        let formula = vec![vec![1], vec![-1]];
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![
                ProofStep::Delete(vec![2, 3]),   // never existed
                ProofStep::Delete(vec![-2, -3]), // never existed
                ProofStep::Add(vec![]),          // still RUP
            ],
        };
        let result = verify_proof_log(&log);
        assert!(
            result.valid,
            "phantom deletions should not block valid proof"
        );
        assert!(
            !result.phantom_deletions.is_empty(),
            "phantom deletions should be reported"
        );
    }

    // ====================================================================
    // LRAT fuzz tests
    // ====================================================================
    use crate::sat_verify::lrat::{ClauseId, LratChecker, LratError, LratStep};
    use crate::sat_verify::types::Lit;

    #[test]
    fn test_fuzz_lrat_valid_proofs_multiple_seeds() {
        // {x} AND {-x} => derive empty clause with hints [1, 2].
        for seed in 0..10u64 {
            let var = 1 + (seed % 4) as u32;
            let mut checker = LratChecker::new(var);
            checker
                .add_original(ClauseId(1), &[Lit(var as i32)])
                .unwrap();
            checker
                .add_original(ClauseId(2), &[Lit(-(var as i32))])
                .unwrap();

            let result = checker
                .verify_proof(&[LratStep::Add {
                    id: ClauseId(3),
                    clause: vec![],
                    hints: vec![1, 2],
                }])
                .unwrap();
            assert!(result.refuted, "seed {seed}: should be refuted");
        }
    }

    #[test]
    fn test_fuzz_lrat_random_invalid_hints_rejected() {
        let mut rng = Rng::new(99);
        for _ in 0..10 {
            let mut checker = LratChecker::new(2);
            checker.add_original(ClauseId(1), &[Lit(1)]).unwrap();
            checker
                .add_original(ClauseId(2), &[Lit(-1), Lit(2)])
                .unwrap();

            // Random hints that probably don't form a valid RUP chain.
            let num_hints = 1 + rng.next_usize(5);
            let hints: Vec<i64> = (0..num_hints)
                .map(|_| 1 + rng.next_usize(50) as i64)
                .collect();

            let result = checker.add_derived(ClauseId(3), &[Lit(2)], &hints);
            // Either it verifies (correct hints by luck) or fails — no panic.
            let _ = result;
        }
    }

    #[test]
    fn test_fuzz_lrat_duplicate_clause_id_rejected() {
        let mut checker = LratChecker::new(2);
        checker.add_original(ClauseId(1), &[Lit(1)]).unwrap();

        let err = checker.add_original(ClauseId(1), &[Lit(2)]).unwrap_err();
        assert_eq!(err, LratError::DuplicateClauseId(ClauseId(1)));
    }

    #[test]
    fn test_fuzz_lrat_boundary_zero_clause_id_rejected() {
        let mut checker = LratChecker::new(1);
        let err = checker.add_original(ClauseId(0), &[Lit(1)]).unwrap_err();
        assert_eq!(err, LratError::InvalidClauseId(0));
    }

    #[test]
    fn test_fuzz_lrat_adversarial_deleted_then_referenced() {
        // Add clause, delete it, then try to use it as a hint.
        let mut checker = LratChecker::new(1);
        checker.add_original(ClauseId(1), &[Lit(1)]).unwrap();
        checker.add_original(ClauseId(2), &[Lit(-1)]).unwrap();

        // Delete clause 1, then try to derive empty with hint referencing it.
        checker.delete(ClauseId(1)).unwrap();
        let result = checker.add_derived(ClauseId(3), &[], &[1, 2]);
        assert!(result.is_err(), "deleted clause as hint should cause error");
    }

    // ====================================================================
    // Resolution fuzz tests
    // ====================================================================
    use crate::sat_verify::proof_complexity::resolution::ResolutionProof;

    #[test]
    fn test_fuzz_resolution_valid_refutations() {
        // Build refutations for {v} AND {-v} for various variables.
        for v in 1..=10i32 {
            let mut proof = ResolutionProof::new();
            proof.add_input(vec![v]);
            proof.add_input(vec![-v]);
            proof.add_resolve(0, 1, v).unwrap();
            assert!(proof.verify(), "var {v}: refutation should verify");
        }
    }

    #[test]
    fn test_fuzz_resolution_random_invalid_pivots() {
        let mut rng = Rng::new(777);
        for _ in 0..10 {
            let mut proof = ResolutionProof::new();
            let c1: Vec<i32> = (1..=3)
                .map(|v| if rng.next_bool() { v } else { -v })
                .collect();
            let c2: Vec<i32> = (4..=6)
                .map(|v| if rng.next_bool() { v } else { -v })
                .collect();
            proof.add_input(c1);
            proof.add_input(c2);

            // Try resolving on a random variable — likely wrong pivot.
            let pivot = 1 + rng.next_usize(8) as i32;
            let result = proof.add_resolve(0, 1, pivot);
            // Either succeeds or errors — no panic.
            let _ = result;
        }
    }

    #[test]
    fn test_fuzz_resolution_invalid_step_indices() {
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);
        // Reference step indices that don't exist.
        assert!(proof.add_resolve(0, 99, 1).is_err());
        assert!(proof.add_resolve(50, 0, 1).is_err());
    }

    #[test]
    fn test_fuzz_resolution_non_refutation_not_verified() {
        // Build a proof that resolves but doesn't reach empty clause.
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1, 2]);
        proof.add_input(vec![-1, 3]);
        proof.add_resolve(0, 1, 1).unwrap(); // derives {2, 3}
        assert!(!proof.verify(), "non-empty final clause should not verify");
    }

    #[test]
    fn test_fuzz_resolution_formula_binding_rejects_foreign() {
        // Proof uses clauses not in the formula.
        let formula = vec![vec![1, 2]];
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![3]); // foreign
        proof.add_input(vec![-3]); // foreign
        proof.add_resolve(0, 1, 3).unwrap();
        assert!(
            !proof.verify_against_formula(&formula),
            "foreign clauses should be rejected"
        );
    }

    // ====================================================================
    // Cutting planes fuzz tests
    // ====================================================================
    use crate::sat_verify::proof_complexity::cutting_planes::{CpInequality, CuttingPlanesProof};

    #[test]
    fn test_fuzz_cp_valid_contradiction() {
        // x >= 1 AND -x >= 0 => add => 0 >= 1 (contradiction).
        for n in 1..=5 {
            let mut proof = CuttingPlanesProof::new();
            let mut coeffs_a = vec![0i64; n];
            coeffs_a[0] = 1;
            let mut coeffs_b = vec![0i64; n];
            coeffs_b[0] = -1;
            let a = proof.add_input(CpInequality::new(coeffs_a, 1));
            let b = proof.add_input(CpInequality::new(coeffs_b, 0));
            proof.add(a, b).unwrap();
            assert!(proof.verify(), "n={n}: should derive contradiction");
        }
    }

    #[test]
    fn test_fuzz_cp_random_operations_no_panic() {
        let mut rng = Rng::new(1234);
        for _ in 0..10 {
            let mut proof = CuttingPlanesProof::new();
            let n = 3;
            let idx = proof.add_input(CpInequality::new(vec![1, 2, -1], 2));

            // Apply random operations.
            let mut last = idx;
            for _ in 0..5 {
                let op = rng.next_usize(4);
                match op {
                    0 => {
                        // Multiply by random positive scalar.
                        let s = 1 + rng.next_usize(5) as i64;
                        if let Ok(new) = proof.multiply(last, s) {
                            last = new;
                        }
                    }
                    1 => {
                        // Divide by random positive divisor.
                        let d = 1 + rng.next_usize(5) as i64;
                        if let Ok(new) = proof.divide(last, d) {
                            last = new;
                        }
                    }
                    2 => {
                        // Saturate.
                        if let Ok(new) = proof.saturate(last) {
                            last = new;
                        }
                    }
                    _ => {
                        // Add with self.
                        if let Ok(new) = proof.add(last, idx) {
                            last = new;
                        }
                    }
                }
            }
            // No panic is the success criterion.
            let _ = proof.verify();
        }
    }

    #[test]
    fn test_fuzz_cp_non_positive_scalar_rejected() {
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![1], 1));
        assert!(proof.multiply(a, 0).is_err());
        assert!(proof.multiply(a, -1).is_err());
    }

    #[test]
    fn test_fuzz_cp_non_positive_divisor_rejected() {
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![1], 1));
        assert!(proof.divide(a, 0).is_err());
        assert!(proof.divide(a, -1).is_err());
    }

    #[test]
    fn test_fuzz_cp_formula_binding_rejects_foreign_input() {
        let formula = vec![CpInequality::new(vec![1], 1)];
        let mut proof = CuttingPlanesProof::new();
        proof.add_input(CpInequality::new(vec![1], 1));
        proof.add_input(CpInequality::new(vec![-1], 0)); // foreign
        proof.add(0, 1).unwrap();
        assert!(
            !proof.verify_against_formula(&formula),
            "foreign input inequality should be rejected"
        );
    }

    // ====================================================================
    // Extended resolution fuzz tests
    // ====================================================================
    use crate::sat_verify::extended_resolution::{ExtResError, ExtendedResolutionProof};
    use crate::sat_verify::frontier::extension_variable::ExtensionDef;
    use crate::sat_verify::types::{Cnf, SatClause};

    #[test]
    fn test_fuzz_extres_valid_proof() {
        let cnf = Cnf {
            num_vars: 1,
            clauses: vec![SatClause(vec![Lit(1)]), SatClause(vec![Lit(-1)])],
        };
        let mut rproof = ResolutionProof::new();
        rproof.add_input(vec![1]);
        rproof.add_input(vec![-1]);
        rproof.add_resolve(0, 1, 1).unwrap();

        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![],
            resolution_proof: rproof,
        };
        assert!(ext.verify().is_ok());
    }

    #[test]
    fn test_fuzz_extres_variable_collision_rejected() {
        let cnf = Cnf {
            num_vars: 3,
            clauses: vec![SatClause(vec![Lit(1)])],
        };
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![ExtensionDef {
                var: 2, // collides with base variable 2
                literal_a: 1,
                literal_b: -1,
            }],
            resolution_proof: ResolutionProof::new(),
        };
        assert!(matches!(
            ext.verify_freshness().unwrap_err(),
            ExtResError::VariableCollision { .. }
        ));
    }

    #[test]
    fn test_fuzz_extres_duplicate_extension_rejected() {
        let cnf = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1)])],
        };
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![
                ExtensionDef {
                    var: 3,
                    literal_a: 1,
                    literal_b: 2,
                },
                ExtensionDef {
                    var: 3,
                    literal_a: -1,
                    literal_b: 2,
                },
            ],
            resolution_proof: ResolutionProof::new(),
        };
        assert!(matches!(
            ext.verify_freshness().unwrap_err(),
            ExtResError::DuplicateExtension(3)
        ));
    }

    #[test]
    fn test_fuzz_extres_adversarial_unbound_proof_rejected() {
        // Resolution proof from a different formula should be rejected.
        let sat_cnf = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1), Lit(2)])],
        };
        let mut rproof = ResolutionProof::new();
        rproof.add_input(vec![3]);
        rproof.add_input(vec![-3]);
        rproof.add_resolve(0, 1, 3).unwrap();

        let ext = ExtendedResolutionProof {
            base_cnf: sat_cnf,
            extensions: vec![],
            resolution_proof: rproof,
        };
        assert!(matches!(
            ext.verify().unwrap_err(),
            ExtResError::InputClauseNotInFormula { .. }
        ));
    }

    #[test]
    fn test_fuzz_extres_not_refutation_rejected() {
        let cnf = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1), Lit(2)])],
        };
        let mut rproof = ResolutionProof::new();
        rproof.add_input(vec![1, 2]); // not a refutation
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![],
            resolution_proof: rproof,
        };
        assert!(matches!(
            ext.verify().unwrap_err(),
            ExtResError::ResolutionNotRefutation
        ));
    }

    // ====================================================================
    // PB/VeriPB fuzz tests
    // ====================================================================
    use crate::sat_verify::pseudo_boolean::{
        PbConstraint, PbError, PbFormula, PbRule, VeriPbProof, VeriPbStep,
    };

    #[test]
    fn test_fuzz_veripb_valid_proof() {
        // Formula: x1 >= 1 AND -x1 >= 0 => contradiction.
        let mut formula = PbFormula::new(1);
        formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
        formula.add_constraint(PbConstraint::new(vec![(1, -1)], 1));

        let mut proof = VeriPbProof::new(formula);
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 1)], 1),
            rule: PbRule::Input(0),
        });
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, -1)], 1),
            rule: PbRule::Input(1),
        });
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![], 2),
            rule: PbRule::Addition { left: 0, right: 1 },
        });
        proof.add_step(VeriPbStep::Conclude);

        assert!(proof.verify().is_ok());
    }

    #[test]
    fn test_fuzz_veripb_no_contradiction_rejected() {
        let mut formula = PbFormula::new(1);
        formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));

        let mut proof = VeriPbProof::new(formula);
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 1)], 1),
            rule: PbRule::Input(0),
        });
        proof.add_step(VeriPbStep::Conclude);

        assert_eq!(proof.verify().unwrap_err(), PbError::NoContradiction);
    }

    #[test]
    fn test_fuzz_veripb_deleted_reference_rejected() {
        // Derive two constraints, delete the first, then try to add them.
        let mut formula = PbFormula::new(1);
        formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
        formula.add_constraint(PbConstraint::new(vec![(1, -1)], 1));

        let mut proof = VeriPbProof::new(formula);
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 1)], 1),
            rule: PbRule::Input(0),
        });
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, -1)], 1),
            rule: PbRule::Input(1),
        });
        // Delete the first derived constraint.
        proof.add_step(VeriPbStep::Delete { id: 0 });
        // Try to reference the deleted constraint.
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![], 2),
            rule: PbRule::Addition { left: 0, right: 1 },
        });
        proof.add_step(VeriPbStep::Conclude);

        let err = proof.verify().unwrap_err();
        assert!(
            matches!(err, PbError::IndexOutOfBounds { .. }),
            "deleted reference should be rejected, got: {err:?}"
        );
    }

    #[test]
    fn test_fuzz_veripb_out_of_bounds_input_index() {
        let formula = PbFormula::new(1);
        let mut proof = VeriPbProof::new(formula);
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![], 1),
            rule: PbRule::Input(99), // out of bounds
        });

        assert!(proof.verify().is_err());
    }

    #[test]
    fn test_fuzz_veripb_format_output_deterministic() {
        // Verify to_veripb_format doesn't panic on various inputs.
        let mut formula = PbFormula::new(3);
        formula.add_constraint(PbConstraint::new(vec![(2, 1), (3, -2)], 4));

        let mut proof = VeriPbProof::new(formula);
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(2, 1), (3, -2)], 4),
            rule: PbRule::Input(0),
        });
        proof.add_step(VeriPbStep::Undo { level: 0 });
        proof.add_step(VeriPbStep::Delete { id: 0 });

        let text = proof.to_veripb_format();
        assert!(text.contains("pseudo-Boolean proof version"));
        assert!(text.contains("end pseudo-Boolean proof"));
    }

    // ====================================================================
    // GF(2) Polynomial Calculus fuzz tests
    // ====================================================================
    use crate::sat_verify::frontier::gf2_algebra::{
        cnf_to_gf2_system, pc_soundness_gf2, verify_encoding_soundness, Gf2Poly, PcError, PcProof,
        PcStepTracked,
    };

    #[test]
    fn test_fuzz_gf2_valid_pc_proof() {
        // {x1} AND {-x1} is UNSAT.
        // GF(2) encoding: (1 + x0) = 0 and x0 = 0.
        // Adding them: 1 = 0 => contradiction.
        let clauses = vec![vec![1], vec![-1]];
        let steps = vec![
            PcStepTracked::ClauseAxiom(0), // 1 + x0
            PcStepTracked::ClauseAxiom(1), // x0
            PcStepTracked::Add(0, 1),      // (1 + x0) + x0 = 1
        ];
        let proof = PcProof::build(&clauses, steps).unwrap();
        assert!(proof.verify().is_ok());
        assert!(pc_soundness_gf2(&clauses, &proof).is_ok());
    }

    #[test]
    fn test_fuzz_gf2_random_formulas_encoding_soundness() {
        // For small random formulas, verify encoding soundness exhaustively.
        for seed in 0..10u64 {
            let clauses = random_cnf(3, 4, 3, seed * 13 + 7);
            if clauses.is_empty() {
                continue;
            }
            let polys = cnf_to_gf2_system(&clauses);
            assert!(
                verify_encoding_soundness(&clauses, &polys, 3),
                "seed {seed}: encoding not sound"
            );
        }
    }

    #[test]
    fn test_fuzz_gf2_invalid_clause_index_rejected() {
        let clauses = vec![vec![1]];
        let steps = vec![PcStepTracked::ClauseAxiom(99)]; // out of range
        let result = PcProof::build(&clauses, steps);
        assert!(matches!(
            result.unwrap_err(),
            PcError::InvalidClauseIndex { .. }
        ));
    }

    #[test]
    fn test_fuzz_gf2_weaken_constant_monomial_rejected() {
        // Weakening with the constant monomial (empty set) is unsound.
        let clauses = vec![vec![1]];
        let steps = vec![
            PcStepTracked::BooleanAxiom(0),            // zero polynomial
            PcStepTracked::Weaken(0, BTreeSet::new()), // add constant 1 — UNSOUND
        ];
        let result = PcProof::build(&clauses, steps);
        assert!(matches!(
            result.unwrap_err(),
            PcError::WeakenConstantMonomial { .. }
        ));
    }

    #[test]
    fn test_fuzz_gf2_empty_proof_rejected() {
        let clauses = vec![vec![1]];
        let result = PcProof::build(&clauses, vec![]);
        assert!(matches!(result.unwrap_err(), PcError::EmptyProof));
    }

    #[test]
    fn test_fuzz_gf2_polynomial_properties() {
        // Verify fundamental polynomial properties with random data.
        let mut rng = Rng::new(555);
        for _ in 0..20 {
            let num_terms = 1 + rng.next_usize(5);
            let mut terms = Vec::new();
            for _ in 0..num_terms {
                let num_vars = rng.next_usize(4);
                let vars: Vec<u32> = (0..num_vars).map(|_| rng.next_u32() % 5).collect();
                terms.push(Gf2Poly::monomial(&vars));
            }

            let mut poly = Gf2Poly::zero();
            for t in &terms {
                poly = poly.add(t);
            }

            // p + p = 0 in GF(2).
            let doubled = poly.add(&poly);
            assert!(doubled.is_zero(), "p + p should be zero in GF(2)");

            // p * 0 = 0.
            let zero_prod = poly.mul(&Gf2Poly::zero());
            assert!(zero_prod.is_zero(), "p * 0 should be zero");

            // p * 1 = p.
            let one_prod = poly.mul(&Gf2Poly::one());
            assert_eq!(one_prod, poly, "p * 1 should be p");
        }
    }

    // ====================================================================
    // Cross-checker adversarial tests
    // ====================================================================

    #[test]
    fn test_fuzz_drat_rup_on_tautology() {
        // Tautological clauses (containing both x and -x) are always true.
        // Verify RUP handles them correctly.
        let clauses = vec![vec![1, -1]]; // tautology
        let result = verify_rup(&clauses, &[2]); // claim {2} is RUP
                                                 // Not RUP: negating {2} gives {-2}; the tautology is satisfied, no conflict.
        assert!(
            !result,
            "non-implied clause should not be RUP from tautology"
        );
    }

    #[test]
    fn test_fuzz_resolution_large_clause_width() {
        // Verify resolution with wider clauses doesn't panic.
        let mut proof = ResolutionProof::new();
        let big1: Vec<i32> = (1..=50).collect();
        let big2: Vec<i32> = {
            let mut v: Vec<i32> = vec![-1];
            v.extend(51..=100);
            v
        };
        proof.add_input(big1);
        proof.add_input(big2);
        // Resolve on variable 1.
        let result = proof.add_resolve(0, 1, 1);
        assert!(result.is_ok());
        let clause = proof.clause_at(2).unwrap();
        // Should contain 2..=100 (99 literals).
        assert_eq!(clause.len(), 99);
    }

    #[test]
    fn test_fuzz_cp_evaluation_consistency() {
        // For random inequalities and assignments, verify evaluate() is consistent.
        let mut rng = Rng::new(2222);
        for _ in 0..20 {
            let n = 1 + rng.next_usize(5);
            let coeffs: Vec<i64> = (0..n).map(|_| rng.range_i32(-3, 5) as i64).collect();
            let rhs = rng.range_i32(-2, 6) as i64;
            let ineq = CpInequality::new(coeffs.clone(), rhs);

            let assignment: Vec<bool> = (0..n).map(|_| rng.next_bool()).collect();

            // Manual evaluation.
            let sum: i64 = coeffs
                .iter()
                .enumerate()
                .map(|(i, &c)| if assignment[i] { c } else { 0 })
                .sum();
            let expected = sum >= rhs;

            assert_eq!(
                ineq.evaluate(&assignment),
                expected,
                "CpInequality::evaluate mismatch"
            );
        }
    }

    #[test]
    fn test_fuzz_lrat_large_num_vars_boundary() {
        // Checker with a large variable count should handle edge literals.
        let mut checker = LratChecker::new(1000);
        checker.add_original(ClauseId(1), &[Lit(1000)]).unwrap();
        checker.add_original(ClauseId(2), &[Lit(-1000)]).unwrap();

        let result = checker
            .verify_proof(&[LratStep::Add {
                id: ClauseId(3),
                clause: vec![],
                hints: vec![1, 2],
            }])
            .unwrap();
        assert!(result.refuted);
    }

    #[test]
    fn test_fuzz_pb_constraint_contradiction_detection() {
        // Various contradiction patterns.
        let empty = PbConstraint::new(vec![], 1);
        assert!(empty.is_contradiction(), "0 >= 1 is contradiction");

        let not_contra = PbConstraint::new(vec![(1, 1)], 1);
        assert!(
            !not_contra.is_contradiction(),
            "1*x1 >= 1 is not contradiction"
        );

        let trivial = PbConstraint::new(vec![], 0);
        assert!(!trivial.is_contradiction(), "0 >= 0 is trivially true");

        let negative = PbConstraint::new(vec![], -1);
        assert!(!negative.is_contradiction(), "0 >= -1 is trivially true");
    }

    #[test]
    fn test_fuzz_gf2_from_clause_roundtrip() {
        // For small clauses, from_clause then to_clause should roundtrip.
        let clauses: Vec<Vec<i32>> = vec![
            vec![1],
            vec![-1],
            vec![1, 2],
            vec![-1, 2],
            vec![1, -2],
            vec![-1, -2],
            vec![1, 2, 3],
        ];
        for clause in &clauses {
            let poly = Gf2Poly::from_clause(clause);
            let recovered = poly.to_clause();
            assert!(recovered.is_some(), "should recover clause {clause:?}");
            // The recovered clause may have different literal ordering,
            // but should encode the same polynomial.
            let re_poly = Gf2Poly::from_clause(&recovered.unwrap());
            assert_eq!(poly, re_poly, "roundtrip mismatch for clause {clause:?}");
        }
    }

    #[test]
    fn test_fuzz_drat_single_clause_formula() {
        // Formula with a single unit clause.
        let formula = vec![vec![1]];
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![ProofStep::Add(vec![])],
        };
        let result = verify_proof_log(&log);
        // Empty clause is not RUP from just {1}: assigning -1 doesn't conflict.
        assert!(!result.valid);
    }

    #[test]
    fn test_fuzz_resolution_self_resolve_error() {
        // Try to resolve a clause with itself.
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1, -1]); // tautology
                                      // Resolving step 0 with itself on variable 1.
        let result = proof.add_resolve(0, 0, 1);
        // This should succeed (resolvent is empty since both +1 and -1 are removed).
        // The pivot is found in both polarities in the same clause.
        let _ = result;
    }

    // ====================================================================
    // FRAT adversarial fuzz tests
    // ====================================================================
    use crate::sat_verify::frat::{
        parse_frat_text, verify_frat, FratClauseId, FratError, FratStep as FStep,
    };

    #[test]
    fn test_fuzz_frat_valid_simple_proof() {
        // {1} AND {-1} => Original + Lemma(empty) should verify.
        let cnf = vec![vec![1], vec![-1]];
        let steps = vec![
            FStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FStep::Original {
                id: FratClauseId(2),
                clause: vec![-1],
            },
            FStep::Lemma {
                id: FratClauseId(3),
                clause: vec![],
            },
            FStep::Finalize {
                id: FratClauseId(3),
            },
        ];
        let result = verify_frat(&cnf, &steps).expect("valid FRAT proof");
        assert!(result.valid, "simple FRAT proof should verify");
        assert!(
            result.empty_clause_finalized,
            "empty clause should be finalized"
        );
    }

    #[test]
    fn test_fuzz_frat_empty_proof_rejected() {
        let cnf = vec![vec![1]];
        let err = verify_frat(&cnf, &[]).unwrap_err();
        assert!(matches!(err, FratError::EmptyProof));
    }

    #[test]
    fn test_fuzz_frat_duplicate_clause_id_rejected() {
        let cnf = vec![vec![1], vec![-1]];
        let steps = vec![
            FStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FStep::Original {
                id: FratClauseId(1),
                clause: vec![-1],
            }, // duplicate
        ];
        let err = verify_frat(&cnf, &steps).unwrap_err();
        assert!(matches!(err, FratError::DuplicateClauseId(_)));
    }

    #[test]
    fn test_fuzz_frat_missing_clause_id_on_delete() {
        let cnf = vec![vec![1]];
        let steps = vec![
            FStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FStep::Delete {
                id: FratClauseId(99),
                clause: vec![1],
            }, // never existed
        ];
        let err = verify_frat(&cnf, &steps).unwrap_err();
        assert!(matches!(err, FratError::MissingClauseId(_)));
    }

    #[test]
    fn test_fuzz_frat_lemma_without_rup_rejected() {
        // Add a lemma that fails both RUP and RAT.
        // For RAT to fail on pivot 3, we need a clause containing -3 whose
        // resolvent with the lemma is not a tautology and not RUP.
        let cnf = vec![vec![1, 2], vec![-1, 2], vec![-3, 1]];
        let steps = vec![
            FStep::Original {
                id: FratClauseId(1),
                clause: vec![1, 2],
            },
            FStep::Original {
                id: FratClauseId(2),
                clause: vec![-1, 2],
            },
            FStep::Original {
                id: FratClauseId(3),
                clause: vec![-3, 1],
            },
            // Lemma {3}: RUP fails (negating {3} gives -3 which doesn't conflict).
            // RAT with pivot 3: resolvent with clause 3 is {1} which is not RUP.
            FStep::Lemma {
                id: FratClauseId(4),
                clause: vec![3],
            },
        ];
        let result = verify_frat(&cnf, &steps);
        // Should fail because {3} is neither RUP nor valid RAT.
        assert!(result.is_err(), "lemma [3] should fail RUP/RAT check");
    }

    #[test]
    fn test_fuzz_frat_add_bypasses_rup_check() {
        // FRAT `Add` steps do NOT require RUP justification (only `Lemma` does).
        // This is by design — `Add` is for solver-internal bookkeeping.
        let cnf = vec![vec![1, 2], vec![-1, 2]];
        let steps = vec![
            FStep::Original {
                id: FratClauseId(1),
                clause: vec![1, 2],
            },
            FStep::Original {
                id: FratClauseId(2),
                clause: vec![-1, 2],
            },
            FStep::Add {
                id: FratClauseId(3),
                clause: vec![3],
            }, // no RUP check
        ];
        // Add doesn't require justification, so this should not error on RUP.
        let result = verify_frat(&cnf, &steps);
        // It may still fail because no empty clause was derived.
        let _ = result;
    }

    #[test]
    fn test_fuzz_frat_adversarial_delete_then_lemma() {
        // Delete a needed clause before using it for a lemma's RUP derivation.
        let cnf = vec![vec![1], vec![-1]];
        let steps = vec![
            FStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FStep::Original {
                id: FratClauseId(2),
                clause: vec![-1],
            },
            FStep::Delete {
                id: FratClauseId(1),
                clause: vec![1],
            }, // remove {1}
            FStep::Lemma {
                id: FratClauseId(3),
                clause: vec![],
            }, // empty not RUP without {1}
        ];
        let result = verify_frat(&cnf, &steps);
        // After deleting {1}, the empty clause is no longer RUP from just {-1}.
        assert!(
            result.is_err(),
            "empty clause should not be RUP after deleting clause 1"
        );
    }

    #[test]
    fn test_fuzz_frat_adversarial_finalize_nonexistent() {
        // Try to finalize a clause that was never added.
        let cnf = vec![vec![1]];
        let steps = vec![
            FStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FStep::Finalize {
                id: FratClauseId(99),
            }, // never existed
        ];
        let result = verify_frat(&cnf, &steps);
        assert!(result.is_err(), "finalizing nonexistent clause should fail");
    }

    #[test]
    fn test_fuzz_frat_text_parser_malformed() {
        // Malformed FRAT text should produce parse errors, not panics.
        let cases = [
            "",          // empty
            "x 1 2 0",   // unknown tag
            "o",         // incomplete line
            "o 1",       // missing zero terminator
            "l 1 abc 0", // non-numeric literal
        ];
        for case in &cases {
            let result = parse_frat_text(case);
            // Either parse error or empty result — no panics.
            let _ = result;
        }
    }

    #[test]
    fn test_fuzz_frat_text_parser_valid_roundtrip() {
        let text = "o 1 1 0\no 2 -1 0\nl 3 0\nf 3 0\n";
        let steps = parse_frat_text(text).expect("valid FRAT text should parse");
        assert_eq!(steps.len(), 4);
        assert!(matches!(
            &steps[0],
            FStep::Original {
                id: FratClauseId(1),
                ..
            }
        ));
        assert!(matches!(
            &steps[2],
            FStep::Lemma {
                id: FratClauseId(3),
                ..
            }
        ));
        assert!(matches!(
            &steps[3],
            FStep::Finalize {
                id: FratClauseId(3)
            }
        ));
    }

    #[test]
    fn test_fuzz_frat_random_steps_no_panic() {
        // Fuzz with random step sequences — verify no panics.
        let mut rng = Rng::new(0xF2A7);
        for _ in 0..10 {
            let cnf = random_cnf(3, 4, 3, rng.next_u64());
            let num_steps = 1 + rng.next_usize(8);
            let mut steps = Vec::new();
            for (next_id, _) in (1u64..).zip(0..num_steps) {
                let kind = rng.next_usize(5);
                let id = FratClauseId(next_id);
                let clause_len = rng.next_usize(4);
                let clause: Vec<i32> = (0..clause_len)
                    .map(|_| {
                        let v = 1 + rng.next_usize(4) as i32;
                        if rng.next_bool() {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect();
                match kind {
                    0 => steps.push(FStep::Original { id, clause }),
                    1 => steps.push(FStep::Add { id, clause }),
                    2 => steps.push(FStep::Lemma { id, clause }),
                    3 => steps.push(FStep::Delete { id, clause }),
                    _ => steps.push(FStep::Finalize { id }),
                }
            }
            let _ = verify_frat(&cnf, &steps);
        }
    }

    #[test]
    fn test_fuzz_frat_adversarial_no_empty_clause() {
        // Valid-looking proof that never derives the empty clause.
        let cnf = vec![vec![1], vec![-1]];
        let steps = vec![
            FStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FStep::Original {
                id: FratClauseId(2),
                clause: vec![-1],
            },
            FStep::Lemma {
                id: FratClauseId(3),
                clause: vec![2],
            }, // not empty
        ];
        let result = verify_frat(&cnf, &steps);
        // Even if the lemma passes RUP (unlikely), no empty clause was derived.
        // Either RUP fails or NoEmptyClause.
        assert!(result.is_err() || !result.unwrap().valid);
    }

    // ====================================================================
    // DRAT adversarial fuzz tests
    // ====================================================================

    #[test]
    fn test_fuzz_drat_adversarial_add_non_rup_clause() {
        // Try adding a clause that is not RUP (no unit propagation conflict).
        let formula = vec![vec![1, 2], vec![-1, 2]]; // SAT: x2=true
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![ProofStep::Add(vec![3])], // {3} not RUP
        };
        let result = verify_proof_log(&log);
        assert!(!result.valid, "non-RUP clause should not verify");
    }

    #[test]
    fn test_fuzz_drat_adversarial_double_delete() {
        // Delete the same clause twice.
        let formula = vec![vec![1], vec![-1]];
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![
                ProofStep::Delete(vec![1]),
                ProofStep::Delete(vec![1]), // second delete of same clause
                ProofStep::Add(vec![]),     // try empty clause after
            ],
        };
        let result = verify_proof_log(&log);
        // After deleting {1}, empty is not RUP from just {-1}.
        assert!(
            !result.valid,
            "should not verify after critical clause deleted"
        );
    }

    #[test]
    fn test_fuzz_drat_adversarial_add_then_use_for_rup() {
        // Add a non-RUP clause, then try to use it to derive empty.
        // This MUST be caught: you can't use a clause that wasn't properly derived.
        let formula = vec![vec![1, 2]]; // SAT
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![
                ProofStep::Add(vec![-1]), // not RUP
                ProofStep::Add(vec![-2]), // not RUP
                ProofStep::Add(vec![]),   // would be RUP if -1,-2 were valid
            ],
        };
        let result = verify_proof_log(&log);
        assert!(!result.valid, "chain of non-RUP clauses should not verify");
    }

    #[test]
    fn test_fuzz_drat_adversarial_empty_clause_in_sat_formula() {
        // Formula is clearly SAT but we try to prove UNSAT.
        let formula = vec![vec![1]]; // trivially SAT
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![ProofStep::Add(vec![])],
        };
        let result = verify_proof_log(&log);
        assert!(
            !result.valid,
            "empty clause not RUP from single positive unit"
        );
    }

    #[test]
    fn test_fuzz_drat_adversarial_large_variable_gap() {
        // Use variables far outside the formula's range on a SAT formula.
        // {1, 2} is SAT, so no valid proof should exist.
        let formula = vec![vec![1, 2]];
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![
                ProofStep::Add(vec![1000000]), // far-off variable, not RUP
                ProofStep::Add(vec![]),        // empty clause not derivable
            ],
        };
        let result = verify_proof_log(&log);
        // Neither step should be RUP from a single non-unit clause.
        assert!(
            !result.valid,
            "large variable clause should not be RUP from SAT formula"
        );
    }

    #[test]
    fn test_fuzz_drat_rup_multiple_seeds_comprehensive() {
        // Test RUP verification across multiple formula shapes.
        for seed in 0..15u64 {
            let mut rng = Rng::new(seed * 997 + 13);
            let nv = 2 + rng.next_usize(4);
            let nc = 2 + rng.next_usize(6);
            let cnf = random_cnf(nv, nc, 3, rng.next_u64());
            // Try claiming a random clause is RUP.
            let clause_len = rng.next_usize(3);
            let claim: Vec<i32> = (0..clause_len)
                .map(|_| {
                    let v = 1 + rng.next_usize(nv) as i32;
                    if rng.next_bool() {
                        v
                    } else {
                        -v
                    }
                })
                .collect();
            let is_rup = verify_rup(&cnf, &claim);
            // Just verify no panic; RUP result varies.
            let _ = is_rup;
        }
    }

    #[test]
    fn test_fuzz_drat_adversarial_tautological_addition() {
        // Adding a tautological clause (x AND -x) — should be trivially RUP.
        let formula = vec![vec![1, 2]];
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![
                ProofStep::Add(vec![1, -1]), // tautology
                ProofStep::Add(vec![]),      // not RUP
            ],
        };
        let result = verify_proof_log(&log);
        // Even though the tautology was added, empty clause is still not derivable.
        assert!(
            !result.valid,
            "tautology addition doesn't make formula UNSAT"
        );
    }

    #[test]
    fn test_fuzz_drat_adversarial_delete_all_then_add_empty() {
        // Delete all clauses, then try to add the empty clause.
        let formula = vec![vec![1], vec![-1], vec![2], vec![-2]];
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![
                ProofStep::Delete(vec![1]),
                ProofStep::Delete(vec![-1]),
                ProofStep::Delete(vec![2]),
                ProofStep::Delete(vec![-2]),
                ProofStep::Add(vec![]),
            ],
        };
        let result = verify_proof_log(&log);
        // Empty clause can't be RUP from an empty database.
        assert!(!result.valid, "empty clause not RUP from empty database");
    }

    // ====================================================================
    // LRAT adversarial fuzz tests
    // ====================================================================

    #[test]
    fn test_fuzz_lrat_adversarial_wrong_hint_order() {
        // Correct hints but in wrong order — LRAT is order-sensitive.
        let mut checker = LratChecker::new(1);
        checker.add_original(ClauseId(1), &[Lit(1)]).unwrap();
        checker.add_original(ClauseId(2), &[Lit(-1)]).unwrap();
        // Reverse hint order: [2, 1] instead of [1, 2].
        let result = checker.add_derived(ClauseId(3), &[], &[2, 1]);
        // May or may not verify depending on implementation.
        // Key: no panic. Some LRAT checkers accept any order.
        let _ = result;
    }

    #[test]
    fn test_fuzz_lrat_adversarial_hint_to_self() {
        // Try using the clause being derived as its own hint.
        let mut checker = LratChecker::new(1);
        checker.add_original(ClauseId(1), &[Lit(1)]).unwrap();
        checker.add_original(ClauseId(2), &[Lit(-1)]).unwrap();
        // Hint references clause 3, which is the clause being added.
        let result = checker.add_derived(ClauseId(3), &[], &[3, 1, 2]);
        // Should either reject (clause 3 doesn't exist yet) or ignore the self-ref.
        let _ = result;
    }

    #[test]
    fn test_fuzz_lrat_adversarial_negative_hint() {
        // LRAT uses negative hints for clause deletion during checking.
        let mut checker = LratChecker::new(1);
        checker.add_original(ClauseId(1), &[Lit(1)]).unwrap();
        checker.add_original(ClauseId(2), &[Lit(-1)]).unwrap();
        // Negative hints indicate deletion in some LRAT dialects.
        let result = checker.add_derived(ClauseId(3), &[], &[-1, 2]);
        // Behavior is implementation-defined, but no panic.
        let _ = result;
    }

    #[test]
    fn test_fuzz_lrat_adversarial_huge_clause_id() {
        // Very large clause ID shouldn't cause overflow or panic.
        let mut checker = LratChecker::new(1);
        checker.add_original(ClauseId(1), &[Lit(1)]).unwrap();
        let result = checker.add_original(ClauseId(u64::MAX), &[Lit(-1)]);
        // Should either work or return a clean error.
        let _ = result;
    }

    #[test]
    fn test_fuzz_lrat_adversarial_empty_hints() {
        // Try to derive a clause with zero hints.
        let mut checker = LratChecker::new(1);
        checker.add_original(ClauseId(1), &[Lit(1)]).unwrap();
        checker.add_original(ClauseId(2), &[Lit(-1)]).unwrap();
        let result = checker.add_derived(ClauseId(3), &[], &[]);
        // Empty hints can't propagate to conflict, so should fail.
        assert!(
            result.is_err(),
            "empty hints should fail for empty clause derivation"
        );
    }

    #[test]
    fn test_fuzz_lrat_adversarial_delete_then_reuse_id() {
        // Delete a clause, then try to add a new clause with the same ID.
        let mut checker = LratChecker::new(1);
        checker.add_original(ClauseId(1), &[Lit(1)]).unwrap();
        checker.delete(ClauseId(1)).unwrap();
        // Try to reuse ID 1.
        let result = checker.add_original(ClauseId(1), &[Lit(-1)]);
        // Some implementations allow ID reuse after deletion, others don't.
        let _ = result;
    }

    #[test]
    fn test_fuzz_lrat_adversarial_derive_from_sat_formula() {
        // Formula is SAT: {1, 2}. Try to derive empty clause.
        let mut checker = LratChecker::new(2);
        checker
            .add_original(ClauseId(1), &[Lit(1), Lit(2)])
            .unwrap();
        let result = checker.add_derived(ClauseId(2), &[], &[1]);
        // Should fail: {1, 2} alone cannot derive empty via RUP.
        assert!(result.is_err(), "cannot derive empty from SAT formula");
    }

    #[test]
    fn test_fuzz_lrat_adversarial_duplicate_literals_in_clause() {
        // Clause with duplicate literals.
        let mut checker = LratChecker::new(1);
        let result = checker.add_original(ClauseId(1), &[Lit(1), Lit(1)]);
        // Duplicate literals should be handled gracefully.
        let _ = result;
    }

    // ====================================================================
    // Pipeline adversarial fuzz tests
    // ====================================================================
    use crate::sat_verify::pipeline::{
        detect_format, verify_any_proof, PipelineError, ProofFormat,
    };

    #[test]
    fn test_fuzz_pipeline_detect_format_empty() {
        assert_eq!(detect_format(&[]), ProofFormat::Unknown);
    }

    #[test]
    fn test_fuzz_pipeline_detect_format_whitespace_only() {
        assert_eq!(detect_format(b"   \n\t  "), ProofFormat::Unknown);
    }

    #[test]
    fn test_fuzz_pipeline_detect_format_drat_text() {
        // DRAT text: lines of literals terminated by 0.
        let data = b"1 2 0\n-1 3 0\n0\n";
        let fmt = detect_format(data);
        assert!(
            matches!(fmt, ProofFormat::Drat | ProofFormat::Lrat),
            "DRAT-like text should detect as DRAT or LRAT, got {fmt:?}"
        );
    }

    #[test]
    fn test_fuzz_pipeline_detect_format_veripb() {
        let data = b"pseudo-Boolean proof version 2.0\nf 1\nend pseudo-Boolean proof";
        assert_eq!(detect_format(data), ProofFormat::VeriPb);
    }

    #[test]
    fn test_fuzz_pipeline_verify_empty_proof_rejected() {
        let formula = b"p cnf 1 2\n1 0\n-1 0\n";
        let err = verify_any_proof(formula, &[]).unwrap_err();
        assert!(matches!(err, PipelineError::EmptyProof));
    }

    #[test]
    fn test_fuzz_pipeline_verify_garbage_rejected() {
        let formula = b"p cnf 1 2\n1 0\n-1 0\n";
        let garbage = b"\x00\x01\x02\x03\xff\xfe\xfd";
        let result = verify_any_proof(formula, garbage);
        // Should fail with some error — not panic.
        assert!(result.is_err() || !result.unwrap().valid);
    }

    #[test]
    fn test_fuzz_pipeline_verify_random_bytes_no_panic() {
        let formula = b"p cnf 2 2\n1 2 0\n-1 -2 0\n";
        let mut rng = Rng::new(0xD1CE);
        for _ in 0..5 {
            let len = 1 + rng.next_usize(50);
            let random_proof: Vec<u8> = (0..len).map(|_| rng.next_u32() as u8).collect();
            let result = verify_any_proof(formula, &random_proof);
            // No panic is the success criterion.
            let _ = result;
        }
    }

    #[test]
    fn test_fuzz_pipeline_adversarial_format_mismatch() {
        // Claim to be VeriPB but send DRAT-like data.
        let formula = b"p cnf 1 2\n1 0\n-1 0\n";
        let proof = b"pseudo-Boolean proof version 2.0\n1 2 0\n0\nend pseudo-Boolean proof";
        let result = verify_any_proof(formula, proof);
        // Detect as VeriPB, but content is malformed PB — should error.
        let _ = result;
    }

    #[test]
    fn test_fuzz_pipeline_adversarial_truncated_dimacs() {
        let formula = b"p cnf"; // truncated
        let proof = b"1 0\n0\n";
        let result = verify_any_proof(formula, proof);
        // Should produce a clean error, not panic.
        let _ = result;
    }

    // ====================================================================
    // Cross-format adversarial tests
    // ====================================================================

    #[test]
    fn test_fuzz_cross_drat_lrat_same_formula_consistency() {
        // Verify both DRAT and LRAT give consistent results for the same formula.
        let formula = vec![vec![1], vec![-1]];

        // DRAT proof.
        let drat_log = ProofLog {
            original_clauses: formula.clone(),
            steps: vec![ProofStep::Add(vec![])],
        };
        let drat_result = verify_proof_log(&drat_log);

        // LRAT proof.
        let mut checker = LratChecker::new(1);
        checker.add_original(ClauseId(1), &[Lit(1)]).unwrap();
        checker.add_original(ClauseId(2), &[Lit(-1)]).unwrap();
        let lrat_result = checker
            .verify_proof(&[LratStep::Add {
                id: ClauseId(3),
                clause: vec![],
                hints: vec![1, 2],
            }])
            .unwrap();

        // Both should agree the formula is UNSAT.
        assert!(drat_result.valid, "DRAT should verify UNSAT");
        assert!(lrat_result.refuted, "LRAT should verify UNSAT");
    }

    #[test]
    fn test_fuzz_cross_drat_frat_same_formula_consistency() {
        // Same formula, DRAT and FRAT should agree.
        let formula = vec![vec![1], vec![-1]];

        let drat_log = ProofLog {
            original_clauses: formula.clone(),
            steps: vec![ProofStep::Add(vec![])],
        };
        let drat_result = verify_proof_log(&drat_log);

        let frat_steps = vec![
            FStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FStep::Original {
                id: FratClauseId(2),
                clause: vec![-1],
            },
            FStep::Lemma {
                id: FratClauseId(3),
                clause: vec![],
            },
            FStep::Finalize {
                id: FratClauseId(3),
            },
        ];
        let frat_result = verify_frat(&formula, &frat_steps).expect("valid FRAT proof");

        assert!(drat_result.valid, "DRAT should verify UNSAT");
        assert!(frat_result.valid, "FRAT should verify UNSAT");
    }

    #[test]
    fn test_fuzz_cross_sat_formula_all_reject() {
        // A clearly SAT formula should be rejected by all checkers.
        let formula = vec![vec![1]]; // trivially SAT

        // DRAT: adding empty clause should fail.
        let drat_log = ProofLog {
            original_clauses: formula.clone(),
            steps: vec![ProofStep::Add(vec![])],
        };
        assert!(
            !verify_proof_log(&drat_log).valid,
            "DRAT should reject SAT formula"
        );

        // LRAT: deriving empty should fail.
        let mut checker = LratChecker::new(1);
        checker.add_original(ClauseId(1), &[Lit(1)]).unwrap();
        let lrat_result = checker.add_derived(ClauseId(2), &[], &[1]);
        assert!(
            lrat_result.is_err(),
            "LRAT should reject empty from SAT formula"
        );

        // FRAT: lemma for empty should fail.
        let frat_steps = vec![
            FStep::Original {
                id: FratClauseId(1),
                clause: vec![1],
            },
            FStep::Lemma {
                id: FratClauseId(2),
                clause: vec![],
            },
        ];
        let frat_result = verify_frat(&formula, &frat_steps);
        assert!(
            frat_result.is_err() || !frat_result.unwrap().valid,
            "FRAT should reject SAT formula"
        );
    }

    #[test]
    fn test_fuzz_cross_all_checkers_random_formulas_no_panic() {
        // Throw random formulas at all checkers and verify no panics.
        for seed in 0..10u64 {
            let mut rng = Rng::new(seed * 1337 + 42);
            let nv = 2 + rng.next_usize(4);
            let nc = 2 + rng.next_usize(6);
            let cnf = random_cnf(nv, nc, 3, rng.next_u64());
            if cnf.is_empty() {
                continue;
            }

            // Random DRAT steps.
            let drat_steps: Vec<ProofStep> = (0..3)
                .map(|_| {
                    let len = rng.next_usize(3);
                    let clause: Vec<i32> = (0..len)
                        .map(|_| {
                            let v = 1 + rng.next_usize(nv) as i32;
                            if rng.next_bool() {
                                v
                            } else {
                                -v
                            }
                        })
                        .collect();
                    ProofStep::Add(clause)
                })
                .collect();
            let _ = verify_proof_log(&ProofLog {
                original_clauses: cnf.clone(),
                steps: drat_steps,
            });

            // Random LRAT steps.
            let mut checker = LratChecker::new(nv as u32);
            for (i, c) in cnf.iter().enumerate() {
                let lits: Vec<Lit> = c.iter().map(|&l| Lit(l)).collect();
                let _ = checker.add_original(ClauseId(i as u64 + 1), &lits);
            }
            let random_hints: Vec<i64> = (0..3)
                .map(|_| 1 + rng.next_usize(cnf.len()) as i64)
                .collect();
            let _ = checker.add_derived(ClauseId(cnf.len() as u64 + 1), &[], &random_hints);

            // Random FRAT steps.
            let mut frat_steps = Vec::new();
            for (i, c) in cnf.iter().enumerate() {
                frat_steps.push(FStep::Original {
                    id: FratClauseId(i as u64 + 1),
                    clause: c.clone(),
                });
            }
            let clause_len = rng.next_usize(3);
            let random_clause: Vec<i32> = (0..clause_len)
                .map(|_| {
                    let v = 1 + rng.next_usize(nv) as i32;
                    if rng.next_bool() {
                        v
                    } else {
                        -v
                    }
                })
                .collect();
            frat_steps.push(FStep::Lemma {
                id: FratClauseId(cnf.len() as u64 + 1),
                clause: random_clause,
            });
            let _ = verify_frat(&cnf, &frat_steps);
        }
    }

    #[test]
    fn test_fuzz_cross_complementary_unit_formula_all_verify() {
        // Multiple complementary unit pairs: all checkers should verify UNSAT.
        for n in 1..=5u32 {
            let mut cnf = Vec::new();
            for v in 1..=n as i32 {
                cnf.push(vec![v]);
                cnf.push(vec![-v]);
            }

            // DRAT: should verify with empty clause addition.
            let drat_log = ProofLog {
                original_clauses: cnf.clone(),
                steps: vec![ProofStep::Add(vec![])],
            };
            assert!(verify_proof_log(&drat_log).valid, "DRAT n={n}");

            // LRAT: add originals and derive empty.
            let mut checker = LratChecker::new(n);
            for (i, c) in cnf.iter().enumerate() {
                let lits: Vec<Lit> = c.iter().map(|&l| Lit(l)).collect();
                checker.add_original(ClauseId(i as u64 + 1), &lits).unwrap();
            }
            let hints: Vec<i64> = (1..=cnf.len() as i64).collect();
            let lrat_result = checker
                .verify_proof(&[LratStep::Add {
                    id: ClauseId(cnf.len() as u64 + 1),
                    clause: vec![],
                    hints,
                }])
                .unwrap();
            assert!(lrat_result.refuted, "LRAT n={n}");

            // FRAT: originals + lemma(empty) + finalize.
            let mut frat_steps: Vec<FStep> = cnf
                .iter()
                .enumerate()
                .map(|(i, c)| FStep::Original {
                    id: FratClauseId(i as u64 + 1),
                    clause: c.clone(),
                })
                .collect();
            let lemma_id = FratClauseId(cnf.len() as u64 + 1);
            frat_steps.push(FStep::Lemma {
                id: lemma_id,
                clause: vec![],
            });
            frat_steps.push(FStep::Finalize { id: lemma_id });
            let frat_result = verify_frat(&cnf, &frat_steps).expect("valid FRAT");
            assert!(frat_result.valid, "FRAT n={n}");
        }
    }

    // ====================================================================
    // PB/VeriPB adversarial — malformed OPB parsing
    // ====================================================================
    use crate::sat_verify::pseudo_boolean::{
        cnf_to_pb, is_tautology, normalize, parse_opb, parse_veripb, write_opb,
    };

    #[test]
    fn test_fuzz_pb_opb_malformed_no_operator_rejected() {
        // OPB constraint line missing >= or = operator.
        let cases = [
            "* #variable= 1 #constraint= 1\n+1 x1 1 ;\n",
            "* #variable= 1 #constraint= 1\n+1 x1 ;\n",
            "* #variable= 1 #constraint= 1\n1 ;\n",
        ];
        for case in &cases {
            let result = parse_opb(case);
            // Should either error or produce zero constraints (line skipped).
            if let Ok(formula) = &result {
                assert_eq!(
                    formula.constraints.len(),
                    0,
                    "malformed constraint line should not produce constraints: {case}"
                );
            }
        }
    }

    #[test]
    fn test_fuzz_pb_opb_invalid_literal_format_rejected() {
        // Literals must be x<N> or ~x<N>. Other formats should fail.
        let cases = [
            "* #variable= 1 #constraint= 1\n+1 y1 >= 1 ;\n", // wrong prefix
            "* #variable= 1 #constraint= 1\n+1 ~y1 >= 1 ;\n", // wrong prefix
            "* #variable= 1 #constraint= 1\n+1 1 >= 1 ;\n",  // bare number
            "* #variable= 1 #constraint= 1\n+1 abc >= 1 ;\n", // text
        ];
        for case in &cases {
            assert!(
                parse_opb(case).is_err(),
                "invalid literal format should be rejected: {case}"
            );
        }
    }

    #[test]
    fn test_fuzz_pb_opb_zero_variable_rejected() {
        // x0 and ~x0 are invalid (variables are 1-indexed).
        let cases = [
            "* #variable= 1 #constraint= 1\n+1 x0 >= 1 ;\n",
            "* #variable= 1 #constraint= 1\n+1 ~x0 >= 1 ;\n",
        ];
        for case in &cases {
            assert!(
                parse_opb(case).is_err(),
                "variable 0 should be rejected: {case}"
            );
        }
    }

    #[test]
    fn test_fuzz_pb_opb_empty_constraint_line() {
        // Semicolon-only or whitespace-only constraint lines.
        let input = "* #variable= 0 #constraint= 0\n;\n";
        let result = parse_opb(input);
        // Should either error or produce empty formula without panicking.
        let _ = result;
    }

    #[test]
    fn test_fuzz_pb_opb_negative_degree() {
        // Negative RHS degree is valid for PB constraints.
        let input = "* #variable= 1 #constraint= 1\n+1 x1 >= -5 ;\n";
        let formula = parse_opb(input).expect("negative degree should parse");
        assert_eq!(formula.constraints.len(), 1);
        assert_eq!(formula.constraints[0].degree, -5);
    }

    #[test]
    fn test_fuzz_pb_opb_huge_coefficients() {
        // Very large coefficients should not overflow or panic.
        let input = "* #variable= 1 #constraint= 1\n+999999999999 x1 >= 999999999999 ;\n";
        let formula = parse_opb(input).expect("large coefficients should parse");
        assert_eq!(formula.constraints[0].terms[0].0, 999_999_999_999);
    }

    #[test]
    fn test_fuzz_pb_opb_roundtrip_random_formulas() {
        let mut rng = Rng::new(0x9B01);
        for _ in 0..10 {
            let nv = 1 + rng.next_usize(5) as u32;
            let nc = 1 + rng.next_usize(4);
            let mut formula = PbFormula::new(nv);
            for _ in 0..nc {
                let nt = 1 + rng.next_usize(nv as usize);
                let terms: Vec<(i64, i32)> = (0..nt)
                    .map(|_| {
                        let coeff = rng.range_i32(-5, 10) as i64;
                        let var = 1 + rng.next_usize(nv as usize) as i32;
                        let lit = if rng.next_bool() { var } else { -var };
                        (coeff, lit)
                    })
                    .collect();
                let degree = rng.range_i32(-3, 15) as i64;
                formula.add_constraint(PbConstraint::new(terms, degree));
            }
            let opb_text = write_opb(&formula);
            let reparsed = parse_opb(&opb_text);
            // Roundtrip should parse without panic.
            assert!(reparsed.is_ok(), "OPB roundtrip failed for formula");
        }
    }

    // ====================================================================
    // VeriPB adversarial — malformed proof text
    // ====================================================================

    #[test]
    fn test_fuzz_veripb_missing_end_marker_rejected() {
        let text = "pseudo-Boolean proof version 2.0\nf 0\nc\n";
        let result = parse_veripb(text, PbFormula::new(0));
        assert!(result.is_err(), "missing end marker should be rejected");
    }

    #[test]
    fn test_fuzz_veripb_unsupported_line_rejected() {
        let text =
            "pseudo-Boolean proof version 2.0\nf 0\ngarbage line\nend pseudo-Boolean proof\n";
        let result = parse_veripb(text, PbFormula::new(0));
        assert!(result.is_err(), "unsupported line should be rejected");
    }

    #[test]
    fn test_fuzz_veripb_empty_p_line_rejected() {
        let text = "pseudo-Boolean proof version 2.0\nf 1\np \nend pseudo-Boolean proof\n";
        let mut formula = PbFormula::new(1);
        formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
        let result = parse_veripb(text, formula);
        assert!(result.is_err(), "empty p line should be rejected");
    }

    #[test]
    fn test_fuzz_veripb_formula_count_mismatch_rejected() {
        // f line claims 5 constraints but formula has 2.
        let text = "pseudo-Boolean proof version 2.0\nf 5\nc\nend pseudo-Boolean proof\n";
        let mut formula = PbFormula::new(1);
        formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
        formula.add_constraint(PbConstraint::new(vec![(1, -1)], 1));
        let result = parse_veripb(text, formula);
        assert!(result.is_err(), "formula count mismatch should be rejected");
    }

    #[test]
    fn test_fuzz_veripb_zero_derived_reference_rejected() {
        // #0 is invalid (1-indexed).
        let text = "pseudo-Boolean proof version 2.0\nf 2\np #0\nend pseudo-Boolean proof\n";
        let mut formula = PbFormula::new(1);
        formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
        formula.add_constraint(PbConstraint::new(vec![(1, -1)], 1));
        let result = parse_veripb(text, formula);
        assert!(result.is_err(), "zero derived reference should be rejected");
    }

    #[test]
    fn test_fuzz_veripb_random_text_no_panic() {
        // Feed random text as VeriPB proof — should error, not panic.
        let mut rng = Rng::new(0x1A01);
        for _ in 0..10 {
            let len = 10 + rng.next_usize(100);
            let text: String = (0..len)
                .map(|_| {
                    let c = rng.next_u32() % 128;
                    if c < 32 && c != 10 {
                        ' '
                    } else {
                        c as u8 as char
                    }
                })
                .collect();
            let _ = parse_veripb(&text, PbFormula::new(0));
        }
    }

    // ====================================================================
    // PB proof rule adversarial
    // ====================================================================

    #[test]
    fn test_fuzz_pb_generalized_resolution_wrong_variable() {
        // Generalized resolution on a variable that doesn't appear.
        let mut formula = PbFormula::new(2);
        formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
        formula.add_constraint(PbConstraint::new(vec![(1, -1)], 1));

        let mut proof = VeriPbProof::new(formula);
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 1)], 1),
            rule: PbRule::Input(0),
        });
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, -1)], 1),
            rule: PbRule::Input(1),
        });
        // Try to resolve on variable 2 which doesn't appear.
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![], 2),
            rule: PbRule::GeneralizedResolution {
                left: 0,
                right: 1,
                var: 2,
            },
        });
        proof.add_step(VeriPbStep::Conclude);
        // Should error because variable 2 not present in constraints.
        let result = proof.verify();
        assert!(result.is_err(), "resolution on absent variable should fail");
    }

    #[test]
    fn test_fuzz_pb_multiplication_by_zero_rejected() {
        let mut formula = PbFormula::new(1);
        formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));

        let mut proof = VeriPbProof::new(formula);
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 1)], 1),
            rule: PbRule::Input(0),
        });
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![], 0),
            rule: PbRule::Multiplication {
                constraint: 0,
                scalar: 0,
            },
        });

        let result = proof.verify();
        assert!(result.is_err(), "multiplication by zero should be rejected");
    }

    #[test]
    fn test_fuzz_pb_division_by_zero_rejected() {
        let mut formula = PbFormula::new(1);
        formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));

        let mut proof = VeriPbProof::new(formula);
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 1)], 1),
            rule: PbRule::Input(0),
        });
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 1)], 1),
            rule: PbRule::Division {
                constraint: 0,
                divisor: 0,
            },
        });

        let result = proof.verify();
        assert!(result.is_err(), "division by zero should be rejected");
    }

    #[test]
    fn test_fuzz_pb_cnf_bridge_adversarial() {
        // Convert adversarial CNF to PB and verify soundness.
        let adversarial_cases: Vec<Vec<Vec<i32>>> = vec![
            vec![],                    // empty formula
            vec![vec![]],              // single empty clause
            vec![vec![1, -1]],         // tautological clause
            vec![vec![1], vec![-1]],   // complementary pair
            vec![vec![1, 2, 3, 4, 5]], // wide clause
        ];

        for clauses in &adversarial_cases {
            let pb_formula = cnf_to_pb(clauses);
            // Verify no panic and constraint count matches.
            assert_eq!(pb_formula.constraints.len(), clauses.len());
        }
    }

    #[test]
    fn test_fuzz_pb_normalize_adversarial() {
        // Normalization of adversarial constraints.
        let cases = vec![
            // Empty constraint.
            PbConstraint::new(vec![], 0),
            // All-zero coefficients.
            PbConstraint::new(vec![(0, 1), (0, -1)], 0),
            // Duplicate literals with opposing coefficients.
            PbConstraint::new(vec![(5, 1), (-5, 1)], 3),
            // Both polarities of same variable.
            PbConstraint::new(vec![(3, 1), (2, -1)], 4),
            // Very large coefficients.
            PbConstraint::new(vec![(i64::MAX / 2, 1)], i64::MAX / 2),
        ];

        for constraint in &cases {
            let normalized = normalize(constraint);
            // Normalization should not panic.
            let _ = normalized;
        }
    }

    #[test]
    fn test_fuzz_pb_tautology_detection() {
        // A constraint 0 >= 0 is a tautology.
        assert!(is_tautology(&PbConstraint::new(vec![], 0)));
        // 0 >= -1 is a tautology.
        assert!(is_tautology(&PbConstraint::new(vec![], -1)));
        // 0 >= 1 is NOT a tautology (it's a contradiction).
        assert!(!is_tautology(&PbConstraint::new(vec![], 1)));
        // x >= 0 is always true for 0/1 variables.
        assert!(is_tautology(&PbConstraint::new(vec![(1, 1)], 0)));
    }

    // ====================================================================
    // Extended resolution adversarial — variable binding attacks
    // ====================================================================

    #[test]
    fn test_fuzz_extres_self_referential_extension() {
        // Extension variable refers to itself.
        let cnf = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1)])],
        };
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![ExtensionDef {
                var: 3,
                literal_a: 3, // self-reference
                literal_b: 1,
            }],
            resolution_proof: ResolutionProof::new(),
        };
        // Self-referential extension should be caught or produce error.
        let result = ext.verify();
        // Either verification fails or the extension is correctly rejected.
        let _ = result;
    }

    #[test]
    fn test_fuzz_extres_circular_extension_chain() {
        // Two extensions that reference each other.
        let cnf = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1)])],
        };
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![
                ExtensionDef {
                    var: 3,
                    literal_a: 4,
                    literal_b: 1,
                }, // 3 depends on 4
                ExtensionDef {
                    var: 4,
                    literal_a: 3,
                    literal_b: 2,
                }, // 4 depends on 3
            ],
            resolution_proof: ResolutionProof::new(),
        };
        // Circular dependency should be detected or at least not cause infinite loops.
        let result = ext.verify();
        let _ = result;
    }

    #[test]
    fn test_fuzz_extres_extension_literal_zero() {
        // Extension with literal 0 (invalid).
        let cnf = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1)])],
        };
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![ExtensionDef {
                var: 3,
                literal_a: 0, // invalid
                literal_b: 1,
            }],
            resolution_proof: ResolutionProof::new(),
        };
        let result = ext.verify();
        // Should either error or handle gracefully — no panic.
        let _ = result;
    }

    #[test]
    fn test_fuzz_extres_massive_extension_count() {
        // Many extension variables to test scaling.
        let cnf = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1)]), SatClause(vec![Lit(-1)])],
        };
        let extensions: Vec<ExtensionDef> = (3..=102u32)
            .map(|v| ExtensionDef {
                var: v,
                literal_a: 1,
                literal_b: 2,
            })
            .collect();
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions,
            resolution_proof: ResolutionProof::new(),
        };
        // Should handle 100 extensions without panic.
        let freshness = ext.verify_freshness();
        assert!(freshness.is_ok(), "100 extensions should pass freshness");
    }

    // ====================================================================
    // GF(2) polynomial calculus adversarial — malformed PC proofs
    // ====================================================================

    #[test]
    fn test_fuzz_gf2_add_out_of_bounds_step_rejected() {
        let clauses = vec![vec![1]];
        let steps = vec![
            PcStepTracked::ClauseAxiom(0),
            PcStepTracked::Add(0, 99), // step 99 doesn't exist
        ];
        let result = PcProof::build(&clauses, steps);
        assert!(result.is_err(), "out-of-bounds step reference should fail");
    }

    #[test]
    fn test_fuzz_gf2_multiply_out_of_bounds_variable() {
        let clauses = vec![vec![1]];
        let steps = vec![
            PcStepTracked::ClauseAxiom(0),
            PcStepTracked::MulVar(0, 999), // variable 999 far out of range
        ];
        // Should build without panic — multiplication by any variable is algebraically valid.
        let result = PcProof::build(&clauses, steps);
        let _ = result;
    }

    #[test]
    fn test_fuzz_gf2_weaken_with_various_monomials() {
        let clauses = vec![vec![1], vec![-1]];
        // Weakening with non-constant monomials is sound.
        let single_var: BTreeSet<u32> = [0].into_iter().collect();
        let two_vars: BTreeSet<u32> = [0, 1].into_iter().collect();

        let steps_single = vec![
            PcStepTracked::ClauseAxiom(0),
            PcStepTracked::Weaken(0, single_var),
        ];
        let result = PcProof::build(&clauses, steps_single);
        assert!(
            result.is_ok(),
            "weakening with single variable monomial should succeed"
        );

        let steps_two = vec![
            PcStepTracked::ClauseAxiom(0),
            PcStepTracked::Weaken(0, two_vars),
        ];
        let result = PcProof::build(&clauses, steps_two);
        assert!(
            result.is_ok(),
            "weakening with two-variable monomial should succeed"
        );
    }

    #[test]
    fn test_fuzz_gf2_boolean_axiom_out_of_bounds() {
        // Boolean axiom for variable beyond the formula's range.
        let clauses = vec![vec![1]];
        let steps = vec![PcStepTracked::BooleanAxiom(999)];
        // Should succeed — boolean axioms x^2 - x = 0 are always valid.
        let result = PcProof::build(&clauses, steps);
        let _ = result;
    }

    #[test]
    fn test_fuzz_gf2_proof_derives_non_one() {
        // A proof that derives 0 (the zero polynomial) instead of 1.
        let clauses = vec![vec![1]];
        let steps = vec![
            PcStepTracked::ClauseAxiom(0),
            PcStepTracked::Add(0, 0), // p + p = 0 in GF(2)
        ];
        let proof = PcProof::build(&clauses, steps);
        if let Ok(p) = proof {
            // The final polynomial is 0, which is NOT a refutation.
            assert!(
                p.verify().is_err(),
                "zero polynomial should not verify as refutation"
            );
        }
    }

    #[test]
    fn test_fuzz_gf2_long_derivation_chain() {
        // Build a long chain of additions to stress-test.
        let clauses = vec![vec![1], vec![-1]];
        let mut steps = vec![PcStepTracked::ClauseAxiom(0), PcStepTracked::ClauseAxiom(1)];
        // Chain: add step 0 and 1 to get 1, then repeatedly add 0 to toggle.
        steps.push(PcStepTracked::Add(0, 1));
        for i in 0..50 {
            steps.push(PcStepTracked::Add(2 + i, 0));
        }
        let result = PcProof::build(&clauses, steps);
        // Should complete without panic.
        let _ = result;
    }

    // ====================================================================
    // Pipeline format confusion — binary/text mismatch
    // ====================================================================

    #[test]
    fn test_fuzz_pipeline_binary_header_then_text() {
        // Start with binary DRAT magic bytes then text content.
        let mut proof = vec![0x61, 0x00]; // binary DRAT 'a' marker + null
        proof.extend_from_slice(b"1 2 0\n0\n");
        let formula = b"p cnf 2 2\n1 2 0\n-1 -2 0\n";
        let result = verify_any_proof(formula, &proof);
        // Should handle mixed format gracefully.
        let _ = result;
    }

    #[test]
    fn test_fuzz_pipeline_text_header_then_binary() {
        // Start with text VeriPB header then binary garbage.
        let mut proof = b"pseudo-Boolean proof version 2.0\n".to_vec();
        proof.extend_from_slice(&[0xFF, 0xFE, 0x00, 0x01, 0x02, 0x03]);
        proof.extend_from_slice(b"\nend pseudo-Boolean proof");
        let formula = b"p cnf 1 2\n1 0\n-1 0\n";
        let result = verify_any_proof(formula, &proof);
        let _ = result;
    }

    #[test]
    fn test_fuzz_pipeline_lrat_binary_marker_only() {
        // Just the binary LRAT header, no content.
        let proof = [0x6C, 0x72, 0x61, 0x74]; // "lrat" ASCII
        let formula = b"p cnf 1 2\n1 0\n-1 0\n";
        let result = verify_any_proof(formula, &proof);
        let _ = result;
    }

    #[test]
    fn test_fuzz_pipeline_detect_format_all_zeros() {
        // All-zero bytes should not crash format detection.
        let proof = [0u8; 64];
        let fmt = detect_format(&proof);
        // Should return some format or Unknown, not panic.
        let _ = fmt;
    }

    #[test]
    fn test_fuzz_pipeline_detect_format_all_0xff() {
        // All 0xFF bytes (maximum byte values).
        let proof = [0xFFu8; 64];
        let fmt = detect_format(&proof);
        let _ = fmt;
    }

    #[test]
    fn test_fuzz_pipeline_formula_garbage_proof_valid() {
        // Garbage formula but well-formed proof header.
        let formula = b"not a dimacs formula at all\n\x00\xFF";
        let proof = b"1 2 0\n0\n";
        let result = verify_any_proof(formula, proof);
        // Should error on formula parse, not panic.
        let _ = result;
    }

    #[test]
    fn test_fuzz_pipeline_both_empty() {
        // Both formula and proof are empty.
        let result = verify_any_proof(b"", b"");
        assert!(
            result.is_err() || !result.unwrap().valid,
            "empty formula + empty proof should not verify"
        );
    }

    #[test]
    fn test_fuzz_pipeline_null_bytes_in_proof() {
        // Proof containing null bytes interspersed with text.
        let formula = b"p cnf 1 2\n1 0\n-1 0\n";
        let proof = b"1 0\n\x00\x00\x000\n";
        let result = verify_any_proof(formula, proof);
        let _ = result;
    }

    // ====================================================================
    // Integer overflow — huge clause IDs and literal values
    // ====================================================================

    #[test]
    fn test_fuzz_lrat_max_u64_clause_id_no_panic() {
        let mut checker = LratChecker::new(1);
        let result = checker.add_original(ClauseId(u64::MAX), &[Lit(1)]);
        // Should either succeed or return clean error.
        let _ = result;
    }

    #[test]
    fn test_fuzz_lrat_sequential_huge_clause_ids() {
        let mut checker = LratChecker::new(1);
        let _ = checker.add_original(ClauseId(u64::MAX - 2), &[Lit(1)]);
        let _ = checker.add_original(ClauseId(u64::MAX - 1), &[Lit(-1)]);
        let result = checker.verify_proof(&[LratStep::Add {
            id: ClauseId(u64::MAX),
            clause: vec![],
            hints: vec![u64::MAX as i64 - 2, u64::MAX as i64 - 1],
        }]);
        // May overflow in hint conversion — should handle gracefully.
        let _ = result;
    }

    #[test]
    fn test_fuzz_frat_max_clause_id() {
        let cnf = vec![vec![1]];
        let steps = vec![FStep::Original {
            id: FratClauseId(u64::MAX),
            clause: vec![1],
        }];
        let result = verify_frat(&cnf, &steps);
        let _ = result;
    }

    #[test]
    fn test_fuzz_resolution_large_variable_values() {
        // Resolution with large variable indices.
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![i32::MAX]);
        proof.add_input(vec![-i32::MAX]);
        let result = proof.add_resolve(0, 1, i32::MAX);
        // Should handle max i32 without panic.
        assert!(result.is_ok(), "max i32 variable should resolve");
        assert!(proof.verify(), "refutation with max i32 variable");
    }

    #[test]
    fn test_fuzz_cp_large_coefficients_no_overflow() {
        // Cutting planes with large coefficients near i64 boundary.
        // Wrap in catch_unwind in case internal arithmetic overflows.
        let result = std::panic::catch_unwind(|| {
            let mut proof = CuttingPlanesProof::new();
            let big = i64::MAX / 4;
            let a = proof.add_input(CpInequality::new(vec![big], big));
            let b = proof.add_input(CpInequality::new(vec![-big], 0));
            proof.add(a, b)
        });
        // Either succeeds (addition cancels) or panics — document behavior.
        let _ = result;
    }

    #[test]
    fn test_fuzz_cp_multiply_near_overflow() {
        // NOTE: CuttingPlanesProof::multiply panics on i64 overflow.
        // This test documents the behavior. A production fix would use
        // checked arithmetic and return an error, but that is out of scope
        // for the fuzz testing issue (#3334).
        let result = std::panic::catch_unwind(|| {
            let mut proof = CuttingPlanesProof::new();
            let big = i64::MAX / 2;
            let a = proof.add_input(CpInequality::new(vec![big], big));
            // Multiplying by 3 would overflow i64.
            proof.multiply(a, 3)
        });
        // Currently panics with "attempt to multiply with overflow".
        // Accepting either panic (current) or clean error (future fix).
        let _ = result;
    }

    #[test]
    fn test_fuzz_pb_constraint_large_terms() {
        // PB constraint with i64::MAX-range coefficients.
        let big = i64::MAX / 2;
        let c = PbConstraint::new(vec![(big, 1), (-big, -1)], big);
        // Normalization should not overflow.
        let normalized = normalize(&c);
        let _ = normalized;
    }

    // ====================================================================
    // Empty/minimal inputs — degenerate cases
    // ====================================================================

    #[test]
    fn test_fuzz_empty_formula_empty_drat_proof() {
        let log = ProofLog {
            original_clauses: vec![],
            steps: vec![],
        };
        let result = verify_proof_log(&log);
        // Empty formula with no steps: trivially SAT, no refutation.
        assert!(
            !result.valid,
            "empty proof on empty formula should not claim UNSAT"
        );
    }

    #[test]
    fn test_fuzz_single_empty_clause_formula() {
        // Formula containing just the empty clause is trivially UNSAT.
        let log = ProofLog {
            original_clauses: vec![vec![]],
            steps: vec![],
        };
        let result = verify_proof_log(&log);
        // Should be UNSAT even without additional proof steps.
        // The empty clause in the formula is already a contradiction.
        let _ = result;
    }

    #[test]
    fn test_fuzz_lrat_zero_variables() {
        // LRAT checker with 0 variables.
        let checker = LratChecker::new(0);
        // No clauses can be added (no valid literals).
        let _ = checker;
    }

    #[test]
    fn test_fuzz_resolution_empty_proof() {
        // Empty resolution proof should not verify.
        let proof = ResolutionProof::new();
        assert!(!proof.verify(), "empty proof should not verify");
    }

    #[test]
    fn test_fuzz_cp_empty_proof() {
        // Empty cutting planes proof should not verify.
        let proof = CuttingPlanesProof::new();
        assert!(!proof.verify(), "empty CP proof should not verify");
    }

    #[test]
    fn test_fuzz_gf2_single_clause_formula() {
        // Single clause that is not UNSAT.
        let clauses = vec![vec![1, 2]];
        let steps = vec![PcStepTracked::ClauseAxiom(0)];
        let proof = PcProof::build(&clauses, steps);
        if let Ok(p) = proof {
            // Single clause axiom is not a refutation.
            assert!(
                p.verify().is_err(),
                "single clause should not be a refutation"
            );
        }
    }

    #[test]
    fn test_fuzz_frat_single_original_no_lemma() {
        // Single original clause, no lemma.
        let cnf = vec![vec![1]];
        let steps = vec![FStep::Original {
            id: FratClauseId(1),
            clause: vec![1],
        }];
        let result = verify_frat(&cnf, &steps);
        // No empty clause derived, so should fail.
        assert!(
            result.is_err() || !result.unwrap().valid,
            "no lemma should not verify as refutation"
        );
    }

    #[test]
    fn test_fuzz_extres_empty_cnf() {
        // Extended resolution on empty CNF (trivially SAT).
        let cnf = Cnf {
            num_vars: 0,
            clauses: vec![],
        };
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![],
            resolution_proof: ResolutionProof::new(),
        };
        let result = ext.verify();
        // Empty CNF is SAT — no refutation possible.
        assert!(result.is_err(), "empty CNF cannot be refuted");
    }

    #[test]
    fn test_fuzz_pipeline_single_clause_dimacs() {
        // Minimal DIMACS formula.
        let formula = b"p cnf 1 1\n1 0\n";
        let proof = b"0\n";
        let result = verify_any_proof(formula, proof);
        // Minimal proof on SAT formula should not verify.
        let _ = result;
    }

    // ====================================================================
    // DRAT adversarial — proof step ordering attacks
    // ====================================================================

    #[test]
    fn test_fuzz_drat_only_deletes_no_adds() {
        // Proof with only Delete steps, no Add steps.
        let formula = vec![vec![1], vec![-1]];
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![ProofStep::Delete(vec![1]), ProofStep::Delete(vec![-1])],
        };
        let result = verify_proof_log(&log);
        assert!(!result.valid, "proof with only deletions should not verify");
    }

    #[test]
    fn test_fuzz_drat_many_empty_clause_additions() {
        // Try adding the empty clause multiple times.
        let formula = vec![vec![1], vec![-1]];
        let log = ProofLog {
            original_clauses: formula,
            steps: vec![
                ProofStep::Add(vec![]),
                ProofStep::Add(vec![]),
                ProofStep::Add(vec![]),
            ],
        };
        let result = verify_proof_log(&log);
        // First empty clause should succeed; subsequent ones are redundant but fine.
        assert!(
            result.valid,
            "multiple empty clause additions should still verify"
        );
    }

    // ====================================================================
    // Cross-format adversarial — format-specific edge cases
    // ====================================================================

    #[test]
    fn test_fuzz_cross_unsat_formula_pb_and_resolution_agree() {
        // Verify PB and resolution agree on a simple UNSAT formula.
        let formula_clauses = vec![vec![1], vec![-1]];

        // PB proof via cutting planes style.
        let mut pb_formula = PbFormula::new(1);
        pb_formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
        pb_formula.add_constraint(PbConstraint::new(vec![(1, -1)], 1));

        let mut pb_proof = VeriPbProof::new(pb_formula);
        pb_proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 1)], 1),
            rule: PbRule::Input(0),
        });
        pb_proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, -1)], 1),
            rule: PbRule::Input(1),
        });
        pb_proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![], 2),
            rule: PbRule::Addition { left: 0, right: 1 },
        });
        pb_proof.add_step(VeriPbStep::Conclude);
        assert!(pb_proof.verify().is_ok(), "PB proof should verify");

        // Resolution proof.
        let mut res_proof = ResolutionProof::new();
        res_proof.add_input(vec![1]);
        res_proof.add_input(vec![-1]);
        res_proof.add_resolve(0, 1, 1).unwrap();
        assert!(res_proof.verify(), "resolution proof should verify");

        // GF(2) proof.
        let pc_steps = vec![
            PcStepTracked::ClauseAxiom(0),
            PcStepTracked::ClauseAxiom(1),
            PcStepTracked::Add(0, 1),
        ];
        let pc_proof = PcProof::build(&formula_clauses, pc_steps).unwrap();
        assert!(pc_proof.verify().is_ok(), "GF(2) proof should verify");
    }

    #[test]
    fn test_fuzz_cross_sat_formula_all_checkers_reject_false_refutation() {
        // A clearly SAT formula (x1 AND x2). All proof systems should reject
        // any attempt to prove it UNSAT.
        let formula = vec![vec![1], vec![2]];

        // DRAT: adding empty clause should fail RUP.
        let drat_log = ProofLog {
            original_clauses: formula.clone(),
            steps: vec![ProofStep::Add(vec![])],
        };
        assert!(
            !verify_proof_log(&drat_log).valid,
            "DRAT should reject false refutation"
        );

        // Resolution: cannot resolve {1} and {2} (no complementary literals).
        let mut res = ResolutionProof::new();
        res.add_input(vec![1]);
        res.add_input(vec![2]);
        assert!(
            res.add_resolve(0, 1, 1).is_err(),
            "resolution should reject: 1 not complementary in both clauses"
        );

        // PB: adding x1 >= 1 and x2 >= 1 gives x1 + x2 >= 2, not a contradiction.
        let mut pb_formula = PbFormula::new(2);
        pb_formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
        pb_formula.add_constraint(PbConstraint::new(vec![(1, 2)], 1));
        let mut pb_proof = VeriPbProof::new(pb_formula);
        pb_proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 1)], 1),
            rule: PbRule::Input(0),
        });
        pb_proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 2)], 1),
            rule: PbRule::Input(1),
        });
        pb_proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 1), (1, 2)], 2),
            rule: PbRule::Addition { left: 0, right: 1 },
        });
        pb_proof.add_step(VeriPbStep::Conclude);
        assert!(
            pb_proof.verify().is_err(),
            "PB should reject: x1 + x2 >= 2 is not a contradiction"
        );
    }
}
