// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for BCP (Boolean Constraint Propagation).

#[cfg(test)]
mod tests {
    use crate::sat_verify::cdcl::bcp::{
        bcp_loop, bcp_step, check_propagation_complete, BcpStepResult,
    };
    use crate::sat_verify::cdcl::CdclState;

    #[test]
    fn test_bcp_step_unit_clause() {
        let state = CdclState::new(2, vec![vec![1]]);
        match bcp_step(&state) {
            BcpStepResult::Propagated {
                literal,
                clause_idx,
            } => {
                assert_eq!(literal, 1);
                assert_eq!(clause_idx, 0);
            }
            other => panic!("expected Propagated, got {other:?}"),
        }
    }

    #[test]
    fn test_bcp_step_fixpoint_satisfied() {
        let mut state = CdclState::new(2, vec![vec![1, 2]]);
        state.assign(1, None).expect("assign");
        assert_eq!(bcp_step(&state), BcpStepResult::Fixpoint);
    }

    #[test]
    fn test_bcp_step_conflict() {
        let mut state = CdclState::new(2, vec![vec![1, 2]]);
        state.assign(-1, None).expect("a");
        state.assign(-2, None).expect("a");
        match bcp_step(&state) {
            BcpStepResult::Conflict { .. } => {}
            other => panic!("expected Conflict, got {other:?}"),
        }
    }

    #[test]
    fn test_bcp_step_becomes_unit() {
        let mut state = CdclState::new(2, vec![vec![1, 2]]);
        state.assign(-1, None).expect("a");
        match bcp_step(&state) {
            BcpStepResult::Propagated { literal, .. } => assert_eq!(literal, 2),
            other => panic!("expected Propagated(2), got {other:?}"),
        }
    }

    #[test]
    fn test_bcp_loop_chain() {
        // (1) AND (-1, 2) AND (-2, 3) should propagate 1 -> 2 -> 3
        let mut state = CdclState::new(3, vec![vec![1], vec![-1, 2], vec![-2, 3]]);
        let propagated = bcp_loop(&mut state).expect("bcp");
        assert_eq!(propagated, vec![1, 2, 3]);
    }

    #[test]
    fn test_bcp_loop_conflict() {
        // (1) AND (-1) is unsatisfiable
        let mut state = CdclState::new(1, vec![vec![1], vec![-1]]);
        assert!(bcp_loop(&mut state).is_err());
    }

    #[test]
    fn test_bcp_loop_no_propagation() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        let propagated = bcp_loop(&mut state).expect("bcp");
        assert!(propagated.is_empty());
    }

    #[test]
    fn test_bcp_propagation_complete_ok() {
        let mut state = CdclState::new(2, vec![vec![1], vec![-1, 2]]);
        bcp_loop(&mut state).expect("bcp");
        check_propagation_complete(&state).expect("complete");
    }

    #[test]
    fn test_bcp_propagation_incomplete() {
        let mut state = CdclState::new(2, vec![vec![1, 2]]);
        state.assign(-1, None).expect("a");
        // Now clause [1, 2] is unit (only 2 is unassigned) but 2 not propagated.
        assert!(check_propagation_complete(&state).is_err());
    }

    #[test]
    fn test_bcp_multiple_unit_clauses() {
        let mut state = CdclState::new(3, vec![vec![1], vec![2], vec![3]]);
        let propagated = bcp_loop(&mut state).expect("bcp");
        assert_eq!(propagated.len(), 3);
    }

    #[test]
    fn test_bcp_fixpoint_all_satisfied() {
        let mut state = CdclState::new(2, vec![vec![1, 2], vec![-1, 2]]);
        state.assign(2, None).expect("a");
        assert_eq!(bcp_step(&state), BcpStepResult::Fixpoint);
    }
}
