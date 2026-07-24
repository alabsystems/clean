// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for interpolation sequence extraction (BMC).

#[cfg(test)]
mod tests {
    use crate::sat_verify::interpolation::mcmillan::{Partition, ResolutionDag};
    use crate::sat_verify::interpolation::sequence::{
        bmc_partitions, check_fixed_point, extract_interpolation_sequence,
        verify_sequence_properties, InterpolationError, InterpolationSequence,
        SequenceVerifyResult, I05_SEQUENCE_INTERPOLATION, I06_FIXED_POINT_DETECTION,
    };
    use crate::sat_verify::interpolation::PropFormula;
    use crate::spec::ProofStatus;
    use std::collections::HashSet;

    // ---- Helper builders ----

    fn var(v: u32) -> PropFormula {
        PropFormula::Var(v)
    }

    fn not(f: PropFormula) -> PropFormula {
        PropFormula::Not(Box::new(f))
    }

    fn and(l: PropFormula, r: PropFormula) -> PropFormula {
        PropFormula::AndType(Box::new(l), Box::new(r))
    }

    // ---- bmc_partitions tests ----

    #[test]
    fn test_bmc_partitions_single_transition() {
        let init = var(1);
        let transitions = vec![and(var(1), var(2))];
        let bad = var(3);

        let parts = bmc_partitions(&init, &transitions, &bad);
        assert_eq!(parts.len(), 1);

        // A_0 = Init, B_0 = T_0 AND NOT Bad
        let (a, b) = &parts[0];
        assert_eq!(*a, var(1));
        // B should contain T_0 and NOT Bad
        let b_vars = b.variables();
        assert!(b_vars.contains(&1));
        assert!(b_vars.contains(&2));
        assert!(b_vars.contains(&3));
    }

    #[test]
    fn test_bmc_partitions_two_transitions() {
        let init = var(1);
        let t0 = var(2);
        let t1 = var(3);
        let bad = var(4);

        let parts = bmc_partitions(&init, &[t0.clone(), t1.clone()], &bad);
        assert_eq!(parts.len(), 2);

        // Partition 0: A = Init, B = T_0 AND T_1 AND NOT Bad
        let a0_vars = parts[0].0.variables();
        assert!(a0_vars.contains(&1));
        assert!(!a0_vars.contains(&2));

        // Partition 1: A = Init AND T_0, B = T_1 AND NOT Bad
        let a1_vars = parts[1].0.variables();
        assert!(a1_vars.contains(&1));
        assert!(a1_vars.contains(&2));
    }

    #[test]
    fn test_bmc_partitions_three_transitions() {
        let init = var(1);
        let transitions = vec![var(2), var(3), var(4)];
        let bad = var(5);

        let parts = bmc_partitions(&init, &transitions, &bad);
        assert_eq!(parts.len(), 3);

        // Check that A grows and B shrinks with each partition
        for part in &parts {
            let a_vars = part.0.variables();
            let b_vars = part.1.variables();
            // A always contains init var
            assert!(a_vars.contains(&1));
            // B always contains bad var
            assert!(b_vars.contains(&5));
        }
    }

    #[test]
    fn test_bmc_partitions_empty_transitions() {
        let init = var(1);
        let bad = var(2);
        let parts = bmc_partitions(&init, &[], &bad);
        assert!(parts.is_empty());
    }

    // ---- extract_interpolation_sequence tests ----

    #[test]
    fn test_extract_sequence_empty_partitions() {
        let dag = ResolutionDag::new();
        let state_vars = HashSet::new();
        let result = extract_interpolation_sequence(&dag, &[], &state_vars);
        assert_eq!(result.unwrap_err(), InterpolationError::EmptyPartitions);
    }

    #[test]
    fn test_extract_sequence_empty_dag() {
        let dag = ResolutionDag::new();
        let state_vars = HashSet::new();
        let partitions = vec![(var(1), not(var(1)))];
        let result = extract_interpolation_sequence(&dag, &partitions, &state_vars);
        assert_eq!(result.unwrap_err(), InterpolationError::DagInconsistent);
    }

    #[test]
    fn test_extract_sequence_simple_two_step() {
        // Build a resolution DAG: A = {(1, 2)}, B = {(-1), (-2)}
        let mut dag = ResolutionDag::new();
        let n0 = dag.add_input(vec![1, 2], Partition::A);
        let n1 = dag.add_input(vec![-1], Partition::B);
        let n2 = dag.add_input(vec![-2], Partition::B);
        let n3 = dag.add_resolve(n0, n1, 1);
        dag.add_resolve(n3, n2, 2);

        let state_vars: HashSet<u32> = [1, 2].into_iter().collect();
        // Single partition: A has vars {1,2}, B has vars {1,2}
        let partitions = vec![(and(var(1), var(2)), and(not(var(1)), not(var(2))))];

        let seq = extract_interpolation_sequence(&dag, &partitions, &state_vars)
            .expect("extraction should succeed");
        assert_eq!(seq.depth, 1);
        assert_eq!(seq.interpolants.len(), 1);
    }

    #[test]
    fn test_extract_sequence_depth_matches_partitions() {
        let mut dag = ResolutionDag::new();
        let n0 = dag.add_input(vec![1], Partition::A);
        let n1 = dag.add_input(vec![-1], Partition::B);
        dag.add_resolve(n0, n1, 1);

        let state_vars: HashSet<u32> = [1].into_iter().collect();
        let partitions = vec![
            (var(1), not(var(1))),
            (var(1), not(var(1))),
            (var(1), not(var(1))),
        ];

        let seq = extract_interpolation_sequence(&dag, &partitions, &state_vars)
            .expect("extraction should succeed");
        assert_eq!(seq.depth, 3);
        assert_eq!(seq.interpolants.len(), 3);
    }

    // ---- verify_sequence_properties tests ----

    #[test]
    fn test_verify_valid_trivial_sequence() {
        // Trivial sequence: Init = True, T = True, Bad = False
        // I_0 = True (implied by Init=True)
        // I_0 AND True implies I_0 (trivially)
        // I_0 AND Bad = True AND False = False (unsat)
        let seq = InterpolationSequence {
            interpolants: vec![PropFormula::True],
            state_vars: HashSet::new(),
            depth: 1,
        };
        let result = verify_sequence_properties(
            &seq,
            &PropFormula::True,
            &[PropFormula::True],
            &PropFormula::False,
        );
        assert_eq!(result, SequenceVerifyResult::Valid);
    }

    #[test]
    fn test_verify_init_not_implied() {
        // Init = x1, I_0 = False. Init does not imply False.
        let seq = InterpolationSequence {
            interpolants: vec![PropFormula::False],
            state_vars: [1].into_iter().collect(),
            depth: 1,
        };
        let result =
            verify_sequence_properties(&seq, &var(1), &[PropFormula::True], &PropFormula::False);
        assert_eq!(result, SequenceVerifyResult::InitNotImplied);
    }

    #[test]
    fn test_verify_bad_not_excluded() {
        // I_k = True, Bad = True => I_k AND Bad is satisfiable
        let seq = InterpolationSequence {
            interpolants: vec![PropFormula::True],
            state_vars: HashSet::new(),
            depth: 1,
        };
        let result = verify_sequence_properties(
            &seq,
            &PropFormula::True,
            &[PropFormula::True],
            &PropFormula::True,
        );
        assert_eq!(result, SequenceVerifyResult::BadNotExcluded);
    }

    #[test]
    fn test_verify_non_state_variable() {
        // Interpolant uses var 5, which is not in state_vars {1,2}
        let seq = InterpolationSequence {
            interpolants: vec![var(5)],
            state_vars: [1, 2].into_iter().collect(),
            depth: 1,
        };
        let result = verify_sequence_properties(
            &seq,
            &PropFormula::True,
            &[PropFormula::True],
            &PropFormula::False,
        );
        match result {
            SequenceVerifyResult::NonStateVariable { var: v, step } => {
                assert_eq!(v, 5);
                assert_eq!(step, 0);
            }
            other => panic!("expected NonStateVariable, got {other:?}"),
        }
    }

    #[test]
    fn test_verify_transition_gap() {
        // I_0 = x1, T_0 = True, I_1 = False
        // x1 AND True does not imply False when x1 = true
        let seq = InterpolationSequence {
            interpolants: vec![var(1), PropFormula::False],
            state_vars: [1].into_iter().collect(),
            depth: 2,
        };
        let result = verify_sequence_properties(
            &seq,
            &var(1),
            &[PropFormula::True, PropFormula::True],
            &PropFormula::False,
        );
        assert_eq!(result, SequenceVerifyResult::TransitionGap { step: 0 });
    }

    #[test]
    fn test_verify_valid_two_step_sequence() {
        // Init = x1, T_0 = True, Bad = NOT x1
        // I_0 = x1 (implied by Init), I_1 = x1 (I_0 AND T implies I_1)
        // I_1 AND Bad = x1 AND NOT x1 = False (unsat)
        let seq = InterpolationSequence {
            interpolants: vec![var(1), var(1)],
            state_vars: [1].into_iter().collect(),
            depth: 2,
        };
        let result = verify_sequence_properties(
            &seq,
            &var(1),
            &[PropFormula::True, PropFormula::True],
            &not(var(1)),
        );
        assert_eq!(result, SequenceVerifyResult::Valid);
    }

    // ---- check_fixed_point tests ----

    #[test]
    fn test_fixed_point_identical_interpolants() {
        // I_0 = x1, I_1 = x1 => I_0 implies I_1 (they are equal)
        let seq = InterpolationSequence {
            interpolants: vec![var(1), var(1)],
            state_vars: [1].into_iter().collect(),
            depth: 2,
        };
        assert!(check_fixed_point(&seq, 0));
    }

    #[test]
    fn test_fixed_point_weakening() {
        // I_0 = x1 AND x2, I_1 = x1 => I_0 implies I_1 (stronger to weaker)
        let seq = InterpolationSequence {
            interpolants: vec![and(var(1), var(2)), var(1)],
            state_vars: [1, 2].into_iter().collect(),
            depth: 2,
        };
        assert!(check_fixed_point(&seq, 0));
    }

    #[test]
    fn test_no_fixed_point_strengthening() {
        // I_0 = x1, I_1 = x1 AND x2 => I_0 does NOT imply I_1
        let seq = InterpolationSequence {
            interpolants: vec![var(1), and(var(1), var(2))],
            state_vars: [1, 2].into_iter().collect(),
            depth: 2,
        };
        assert!(!check_fixed_point(&seq, 0));
    }

    #[test]
    fn test_fixed_point_out_of_bounds() {
        let seq = InterpolationSequence {
            interpolants: vec![var(1)],
            state_vars: [1].into_iter().collect(),
            depth: 1,
        };
        assert!(!check_fixed_point(&seq, 0)); // step+1 = 1 is out of bounds
        assert!(!check_fixed_point(&seq, 5)); // way out of bounds
    }

    #[test]
    fn test_fixed_point_true_implies_true() {
        let seq = InterpolationSequence {
            interpolants: vec![PropFormula::True, PropFormula::True],
            state_vars: HashSet::new(),
            depth: 2,
        };
        assert!(check_fixed_point(&seq, 0));
    }

    #[test]
    fn test_fixed_point_false_implies_anything() {
        let seq = InterpolationSequence {
            interpolants: vec![PropFormula::False, var(1)],
            state_vars: [1].into_iter().collect(),
            depth: 2,
        };
        // False implies anything, so this is a fixed point
        assert!(check_fixed_point(&seq, 0));
    }

    // ---- Proof constant tests ----

    #[test]
    fn test_sequence_proof_constants() {
        assert_eq!(I05_SEQUENCE_INTERPOLATION, ProofStatus::DerivedPending);
        assert_eq!(I06_FIXED_POINT_DETECTION, ProofStatus::DerivedPending);
    }

    // ---- State variable filtering ----

    #[test]
    fn test_state_vars_preserved_in_sequence() {
        let mut dag = ResolutionDag::new();
        let n0 = dag.add_input(vec![1, 2], Partition::A);
        let n1 = dag.add_input(vec![-2, 3], Partition::B);
        dag.add_resolve(n0, n1, 2);

        let state_vars: HashSet<u32> = [1, 2, 3].into_iter().collect();
        let partitions = vec![(and(var(1), var(2)), and(not(var(2)), var(3)))];

        let seq = extract_interpolation_sequence(&dag, &partitions, &state_vars)
            .expect("extraction should succeed");
        assert_eq!(seq.state_vars, state_vars);
    }

    // ---- Integration: partitions + extraction ----

    #[test]
    fn test_partitions_cover_all_transitions() {
        let init = var(1);
        let transitions = vec![var(2), var(3), var(4), var(5)];
        let bad = var(6);

        let parts = bmc_partitions(&init, &transitions, &bad);
        assert_eq!(parts.len(), 4);

        // Each transition variable appears in exactly one side
        for (i, (_a, b)) in parts.iter().enumerate() {
            let b_vars = b.variables();
            // Transition i should be in B (it is T_i ... T_{k-1})
            assert!(b_vars.contains(&(i as u32 + 2)), "T_{i} should be in B_{i}");
        }
    }

    #[test]
    fn test_empty_interpolant_sequence_verify_valid() {
        // Edge case: empty interpolants list with empty transitions
        let seq = InterpolationSequence {
            interpolants: vec![],
            state_vars: HashSet::new(),
            depth: 0,
        };
        let result = verify_sequence_properties(&seq, &PropFormula::True, &[], &PropFormula::False);
        assert_eq!(result, SequenceVerifyResult::Valid);
    }

    #[test]
    fn test_single_interpolant_init_and_safety() {
        // Depth-1: Init = x1, Bad = NOT x1, I_0 = x1
        // Init implies I_0 (both are x1)
        // I_0 AND Bad = x1 AND NOT x1 = unsat
        let seq = InterpolationSequence {
            interpolants: vec![var(1)],
            state_vars: [1].into_iter().collect(),
            depth: 1,
        };
        let result = verify_sequence_properties(&seq, &var(1), &[PropFormula::True], &not(var(1)));
        assert_eq!(result, SequenceVerifyResult::Valid);
    }
}
