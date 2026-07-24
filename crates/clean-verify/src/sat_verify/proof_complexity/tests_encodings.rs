// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof complexity encodings: pigeonhole, Tseitin circuit
//! transformation, and cardinality constraints.

use super::encodings::*;

// ---------------------------------------------------------------------------
// Pigeonhole tests
// ---------------------------------------------------------------------------

#[test]
fn test_pigeonhole_cnf_2_1_clause_count() {
    // PHP(2,1): 2 pigeons, 1 hole.
    // Pigeon clauses: 2 (each pigeon must be in hole 1)
    // Hole clauses: C(2,2)*1 = 1 (no two pigeons in hole 1)
    // Total: 3
    let clauses = pigeonhole_cnf(2, 1);
    assert_eq!(clauses.len(), 3);
    assert_eq!(php_num_clauses(2, 1), 3);
}

#[test]
fn test_pigeonhole_cnf_2_1_structure() {
    // PHP(2,1): vars p_{1,1}=1, p_{2,1}=2
    let clauses = pigeonhole_cnf(2, 1);
    // Pigeon 1 in at least one hole: [1]
    assert_eq!(clauses[0], vec![1]);
    // Pigeon 2 in at least one hole: [2]
    assert_eq!(clauses[1], vec![2]);
    // No two pigeons in hole 1: [-1, -2]
    assert_eq!(clauses[2], vec![-1, -2]);
}

#[test]
fn test_pigeonhole_cnf_3_2_counts() {
    // PHP(3,2): 3 pigeons, 2 holes.
    // Variables: 3*2 = 6
    // Pigeon clauses: 3
    // Hole clauses: C(3,2)*2 = 3*2 = 6
    // Total: 9
    let clauses = pigeonhole_cnf(3, 2);
    assert_eq!(clauses.len(), 9);
    assert_eq!(php_num_vars(3, 2), 6);
    assert_eq!(php_num_clauses(3, 2), 9);
}

#[test]
fn test_pigeonhole_cnf_4_3_counts() {
    // PHP(4,3): 4 pigeons, 3 holes.
    // Variables: 4*3 = 12
    // Pigeon clauses: 4
    // Hole clauses: C(4,2)*3 = 6*3 = 18
    // Total: 22
    let clauses = pigeonhole_cnf(4, 3);
    assert_eq!(clauses.len(), 22);
    assert_eq!(php_num_vars(4, 3), 12);
    assert_eq!(php_num_clauses(4, 3), 22);
}

#[test]
fn test_pigeonhole_clause_formula() {
    // Verify the formula: pigeons + C(pigeons,2)*holes
    for pigeons in 1..=6 {
        for holes in 1..=5 {
            let clauses = pigeonhole_cnf(pigeons, holes);
            assert_eq!(
                clauses.len(),
                php_num_clauses(pigeons, holes),
                "mismatch for pigeons={pigeons}, holes={holes}"
            );
        }
    }
}

#[test]
fn test_pigeonhole_variable_numbering() {
    // PHP(3,2): p_{i,j} = (i-1)*2 + j
    // p_{1,1}=1, p_{1,2}=2, p_{2,1}=3, p_{2,2}=4, p_{3,1}=5, p_{3,2}=6
    let clauses = pigeonhole_cnf(3, 2);
    // Pigeon 1 clause: [1, 2]
    assert_eq!(clauses[0], vec![1, 2]);
    // Pigeon 2 clause: [3, 4]
    assert_eq!(clauses[1], vec![3, 4]);
    // Pigeon 3 clause: [5, 6]
    assert_eq!(clauses[2], vec![5, 6]);
}

#[test]
fn test_pigeonhole_num_vars() {
    assert_eq!(php_num_vars(2, 1), 2);
    assert_eq!(php_num_vars(3, 2), 6);
    assert_eq!(php_num_vars(4, 3), 12);
    assert_eq!(php_num_vars(5, 4), 20);
}

#[test]
fn test_pigeonhole_cnf_unsatisfiable_2_1() {
    // Brute-force check: PHP(2,1) has 2 vars, try all 4 assignments.
    let clauses = pigeonhole_cnf(2, 1);
    let num_vars = php_num_vars(2, 1) as usize;
    assert!(!has_satisfying_assignment(&clauses, num_vars));
}

#[test]
fn test_pigeonhole_cnf_unsatisfiable_3_2() {
    // PHP(3,2) has 6 vars, try all 64 assignments.
    let clauses = pigeonhole_cnf(3, 2);
    let num_vars = php_num_vars(3, 2) as usize;
    assert!(!has_satisfying_assignment(&clauses, num_vars));
}

#[test]
fn test_pigeonhole_cnf_satisfiable_2_2() {
    // PHP(2,2): 2 pigeons, 2 holes. Should be satisfiable.
    let clauses = pigeonhole_cnf(2, 2);
    let num_vars = php_num_vars(2, 2) as usize;
    assert!(has_satisfying_assignment(&clauses, num_vars));
}

#[test]
fn test_pigeonhole_zero_pigeons() {
    let clauses = pigeonhole_cnf(0, 3);
    assert!(clauses.is_empty());
    assert_eq!(php_num_clauses(0, 3), 0);
}

#[test]
fn test_pigeonhole_matches_encode_php() {
    // pigeonhole_cnf(n+1, n) should match encode_php(n) in clause count
    for n in 1..=5 {
        let (_, php_clauses) = encode_php(n);
        let gen_clauses = pigeonhole_cnf(n + 1, n);
        assert_eq!(
            php_clauses.len(),
            gen_clauses.len(),
            "clause count mismatch for n={n}"
        );
    }
}

// ---------------------------------------------------------------------------
// Tseitin circuit transformation tests
// ---------------------------------------------------------------------------

#[test]
fn test_tseitin_single_and_gate() {
    let circuit = Circuit {
        num_inputs: 2,
        gates: vec![Gate {
            gate_type: GateType::AndType,
            inputs: vec![1, 2],
            output: None,
        }],
    };
    let result = tseitin_transform(&circuit);
    // AND gate: 3 gate clauses + 1 output assertion = 4
    assert_eq!(result.clauses.len(), 4);
    assert_eq!(result.num_vars, 3); // 2 inputs + 1 gate
    assert_eq!(result.output_var, 3);
}

#[test]
fn test_tseitin_single_or_gate() {
    let circuit = Circuit {
        num_inputs: 2,
        gates: vec![Gate {
            gate_type: GateType::Or,
            inputs: vec![1, 2],
            output: None,
        }],
    };
    let result = tseitin_transform(&circuit);
    // OR gate: 3 gate clauses + 1 output assertion = 4
    assert_eq!(result.clauses.len(), 4);
    assert_eq!(result.num_vars, 3);
}

#[test]
fn test_tseitin_not_gate() {
    let circuit = Circuit {
        num_inputs: 1,
        gates: vec![Gate {
            gate_type: GateType::Not,
            inputs: vec![1],
            output: None,
        }],
    };
    let result = tseitin_transform(&circuit);
    // NOT gate: 2 gate clauses + 1 output assertion = 3
    assert_eq!(result.clauses.len(), 3);
    assert_eq!(result.num_vars, 2);
}

#[test]
fn test_tseitin_xor_gate() {
    let circuit = Circuit {
        num_inputs: 2,
        gates: vec![Gate {
            gate_type: GateType::Xor,
            inputs: vec![1, 2],
            output: None,
        }],
    };
    let result = tseitin_transform(&circuit);
    // XOR gate: 4 gate clauses + 1 output assertion = 5
    assert_eq!(result.clauses.len(), 5);
    assert_eq!(result.num_vars, 3);
}

#[test]
fn test_tseitin_implies_gate() {
    let circuit = Circuit {
        num_inputs: 2,
        gates: vec![Gate {
            gate_type: GateType::Implies,
            inputs: vec![1, 2],
            output: None,
        }],
    };
    let result = tseitin_transform(&circuit);
    // IMPLIES gate: 3 gate clauses + 1 output assertion = 4
    assert_eq!(result.clauses.len(), 4);
    assert_eq!(result.num_vars, 3);
}

#[test]
fn test_tseitin_chain_and_or() {
    // Circuit: (x1 AND x2) OR x3
    let circuit = Circuit {
        num_inputs: 3,
        gates: vec![
            Gate {
                gate_type: GateType::AndType,
                inputs: vec![1, 2],
                output: None,
            },
            Gate {
                gate_type: GateType::Or,
                inputs: vec![4, 3], // gate 0 output = var 4, input x3 = var 3
                output: None,
            },
        ],
    };
    let result = tseitin_transform(&circuit);
    // AND: 3 clauses, OR: 3 clauses, output assertion: 1 = 7
    assert_eq!(result.clauses.len(), 7);
    assert_eq!(result.num_vars, 5); // 3 inputs + 2 gate outputs
    assert_eq!(result.output_var, 5);
}

#[test]
fn test_tseitin_equisat_and_gate_true() {
    // AND(true, true) = true
    let circuit = Circuit {
        num_inputs: 2,
        gates: vec![Gate {
            gate_type: GateType::AndType,
            inputs: vec![1, 2],
            output: None,
        }],
    };
    let result = tseitin_transform(&circuit);
    assert!(verify_tseitin_equisat(&circuit, &result, &[true, true]));
}

#[test]
fn test_tseitin_equisat_and_gate_false() {
    // AND(true, false) = false, output asserted true => unsatisfied
    let circuit = Circuit {
        num_inputs: 2,
        gates: vec![Gate {
            gate_type: GateType::AndType,
            inputs: vec![1, 2],
            output: None,
        }],
    };
    let result = tseitin_transform(&circuit);
    assert!(!verify_tseitin_equisat(&circuit, &result, &[true, false]));
    assert!(!verify_tseitin_equisat(&circuit, &result, &[false, true]));
    assert!(!verify_tseitin_equisat(&circuit, &result, &[false, false]));
}

#[test]
fn test_tseitin_equisat_or_gate_exhaustive() {
    // OR gate: true when at least one input is true
    let circuit = Circuit {
        num_inputs: 2,
        gates: vec![Gate {
            gate_type: GateType::Or,
            inputs: vec![1, 2],
            output: None,
        }],
    };
    let result = tseitin_transform(&circuit);
    assert!(verify_tseitin_equisat(&circuit, &result, &[true, true]));
    assert!(verify_tseitin_equisat(&circuit, &result, &[true, false]));
    assert!(verify_tseitin_equisat(&circuit, &result, &[false, true]));
    assert!(!verify_tseitin_equisat(&circuit, &result, &[false, false]));
}

#[test]
fn test_tseitin_equisat_xor_gate_exhaustive() {
    // XOR gate: true when exactly one input is true
    let circuit = Circuit {
        num_inputs: 2,
        gates: vec![Gate {
            gate_type: GateType::Xor,
            inputs: vec![1, 2],
            output: None,
        }],
    };
    let result = tseitin_transform(&circuit);
    assert!(!verify_tseitin_equisat(&circuit, &result, &[true, true]));
    assert!(verify_tseitin_equisat(&circuit, &result, &[true, false]));
    assert!(verify_tseitin_equisat(&circuit, &result, &[false, true]));
    assert!(!verify_tseitin_equisat(&circuit, &result, &[false, false]));
}

#[test]
fn test_tseitin_equisat_not_gate_exhaustive() {
    let circuit = Circuit {
        num_inputs: 1,
        gates: vec![Gate {
            gate_type: GateType::Not,
            inputs: vec![1],
            output: None,
        }],
    };
    let result = tseitin_transform(&circuit);
    assert!(!verify_tseitin_equisat(&circuit, &result, &[true]));
    assert!(verify_tseitin_equisat(&circuit, &result, &[false]));
}

#[test]
fn test_tseitin_equisat_implies_exhaustive() {
    // x => y: false only when x=true, y=false
    let circuit = Circuit {
        num_inputs: 2,
        gates: vec![Gate {
            gate_type: GateType::Implies,
            inputs: vec![1, 2],
            output: None,
        }],
    };
    let result = tseitin_transform(&circuit);
    assert!(verify_tseitin_equisat(&circuit, &result, &[true, true]));
    assert!(!verify_tseitin_equisat(&circuit, &result, &[true, false]));
    assert!(verify_tseitin_equisat(&circuit, &result, &[false, true]));
    assert!(verify_tseitin_equisat(&circuit, &result, &[false, false]));
}

#[test]
fn test_tseitin_large_circuit_10_gates() {
    // Build a chain of 10 AND gates: ((x1 AND x2) AND x3) AND ... AND x11
    let mut gates = Vec::new();
    // First gate: AND(x1, x2) = gate_out_0 = var 12
    gates.push(Gate {
        gate_type: GateType::AndType,
        inputs: vec![1, 2],
        output: None,
    });
    // Subsequent gates: AND(prev_out, x_{i+2}) for i=1..9
    for i in 1..10 {
        let prev_out = (11 + i) as u32; // gate outputs start at var 12
        let next_input = (i + 2) as u32;
        gates.push(Gate {
            gate_type: GateType::AndType,
            inputs: vec![prev_out, next_input],
            output: None,
        });
    }

    let circuit = Circuit {
        num_inputs: 11,
        gates,
    };
    let result = tseitin_transform(&circuit);
    // 10 AND gates * 3 clauses each + 1 output assertion = 31
    assert_eq!(result.clauses.len(), 31);
    assert_eq!(result.num_vars, 21); // 11 inputs + 10 gate outputs
    assert_eq!(result.output_var, 21);

    // All-true should satisfy the AND chain
    let all_true = vec![true; 11];
    assert!(verify_tseitin_equisat(&circuit, &result, &all_true));

    // Any false input should make it unsatisfiable
    let mut one_false = vec![true; 11];
    one_false[5] = false;
    assert!(!verify_tseitin_equisat(&circuit, &result, &one_false));
}

#[test]
fn test_evaluate_circuit_and() {
    let circuit = Circuit {
        num_inputs: 2,
        gates: vec![Gate {
            gate_type: GateType::AndType,
            inputs: vec![1, 2],
            output: None,
        }],
    };
    assert_eq!(evaluate_circuit(&circuit, &[true, true]), Some(true));
    assert_eq!(evaluate_circuit(&circuit, &[true, false]), Some(false));
    assert_eq!(evaluate_circuit(&circuit, &[false, true]), Some(false));
    assert_eq!(evaluate_circuit(&circuit, &[false, false]), Some(false));
}

#[test]
fn test_evaluate_circuit_empty() {
    let circuit = Circuit {
        num_inputs: 2,
        gates: vec![],
    };
    assert_eq!(evaluate_circuit(&circuit, &[true, false]), None);
}

#[test]
fn test_evaluate_circuit_matches_equisat() {
    // For every gate type with 2 inputs, verify evaluate_circuit
    // matches verify_tseitin_equisat.
    for gate_type in [
        GateType::AndType,
        GateType::Or,
        GateType::Xor,
        GateType::Implies,
    ] {
        let circuit = Circuit {
            num_inputs: 2,
            gates: vec![Gate {
                gate_type,
                inputs: vec![1, 2],
                output: None,
            }],
        };
        let result = tseitin_transform(&circuit);

        for a in [false, true] {
            for b in [false, true] {
                let inputs = [a, b];
                let circuit_out = evaluate_circuit(&circuit, &inputs).unwrap();
                let cnf_sat = verify_tseitin_equisat(&circuit, &result, &inputs);
                assert_eq!(circuit_out, cnf_sat, "mismatch for {gate_type:?}({a}, {b})");
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Cardinality encoding tests
// ---------------------------------------------------------------------------

#[test]
fn test_amo_pairwise_3_vars() {
    // AMO(3 vars): C(3,2) = 3 clauses
    let clauses = amo_pairwise(&[1, 2, 3]);
    assert_eq!(clauses.len(), 3);
    assert_eq!(clauses[0], vec![-1, -2]);
    assert_eq!(clauses[1], vec![-1, -3]);
    assert_eq!(clauses[2], vec![-2, -3]);
}

#[test]
fn test_amo_pairwise_4_vars() {
    // AMO(4 vars): C(4,2) = 6 clauses
    let clauses = amo_pairwise(&[1, 2, 3, 4]);
    assert_eq!(clauses.len(), 6);
}

#[test]
fn test_amo_pairwise_1_var() {
    // AMO(1 var): 0 clauses (trivially satisfied)
    let clauses = amo_pairwise(&[1]);
    assert!(clauses.is_empty());
}

#[test]
fn test_amo_pairwise_empty() {
    let clauses = amo_pairwise(&[]);
    assert!(clauses.is_empty());
}

#[test]
fn test_alo_clause_3_vars() {
    let clause = alo_clause(&[1, 2, 3]);
    assert_eq!(clause, vec![1, 2, 3]);
}

#[test]
fn test_alo_clause_1_var() {
    let clause = alo_clause(&[5]);
    assert_eq!(clause, vec![5]);
}

#[test]
fn test_exactly_one_3_vars() {
    // EO(3 vars): 3 AMO clauses + 1 ALO clause = 4
    let clauses = exactly_one(&[1, 2, 3]);
    assert_eq!(clauses.len(), 4);
    // Last clause is the ALO clause
    assert_eq!(*clauses.last().unwrap(), vec![1, 2, 3]);
}

#[test]
fn test_exactly_one_4_vars() {
    // EO(4 vars): 6 AMO + 1 ALO = 7
    let clauses = exactly_one(&[1, 2, 3, 4]);
    assert_eq!(clauses.len(), 7);
}

#[test]
fn test_amo_satisfiability_all_false() {
    // All-false satisfies AMO
    let clauses = amo_pairwise(&[1, 2, 3]);
    assert!(check_cnf_satisfied(&clauses, &[false, false, false]));
}

#[test]
fn test_amo_satisfiability_exactly_one_true() {
    // Exactly one true satisfies AMO
    let clauses = amo_pairwise(&[1, 2, 3]);
    assert!(check_cnf_satisfied(&clauses, &[true, false, false]));
    assert!(check_cnf_satisfied(&clauses, &[false, true, false]));
    assert!(check_cnf_satisfied(&clauses, &[false, false, true]));
}

#[test]
fn test_amo_violation_two_true() {
    // Two true violates AMO
    let clauses = amo_pairwise(&[1, 2, 3]);
    assert!(!check_cnf_satisfied(&clauses, &[true, true, false]));
    assert!(!check_cnf_satisfied(&clauses, &[true, false, true]));
    assert!(!check_cnf_satisfied(&clauses, &[false, true, true]));
    assert!(!check_cnf_satisfied(&clauses, &[true, true, true]));
}

#[test]
fn test_eo_satisfiability() {
    // Exactly-one: only single-true assignments satisfy
    let clauses = exactly_one(&[1, 2, 3]);
    assert!(!check_cnf_satisfied(&clauses, &[false, false, false]));
    assert!(check_cnf_satisfied(&clauses, &[true, false, false]));
    assert!(check_cnf_satisfied(&clauses, &[false, true, false]));
    assert!(check_cnf_satisfied(&clauses, &[false, false, true]));
    assert!(!check_cnf_satisfied(&clauses, &[true, true, false]));
    assert!(!check_cnf_satisfied(&clauses, &[true, true, true]));
}

#[test]
fn test_pc05_pc06_status() {
    assert_eq!(
        PC05_TSEITIN_EQUISAT,
        crate::spec::ProofStatus::DerivedPending
    );
    assert_eq!(PC06_PHP_UNSAT, crate::spec::ProofStatus::DerivedPending);
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

/// Brute-force SAT check: try all 2^n assignments.
fn has_satisfying_assignment(clauses: &[Vec<i32>], num_vars: usize) -> bool {
    for assignment_bits in 0..(1u64 << num_vars) {
        let assignment: Vec<bool> = (0..num_vars)
            .map(|i| (assignment_bits >> i) & 1 == 1)
            .collect();
        if check_cnf_satisfied(clauses, &assignment) {
            return true;
        }
    }
    false
}

/// Check if a CNF formula is satisfied under a given assignment.
/// Variables are 1-indexed: variable i maps to assignment[i-1].
fn check_cnf_satisfied(clauses: &[Vec<i32>], assignment: &[bool]) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|&lit| {
            let var_idx = lit.unsigned_abs() as usize;
            if var_idx == 0 || var_idx > assignment.len() {
                return false;
            }
            let val = assignment[var_idx - 1];
            if lit > 0 {
                val
            } else {
                !val
            }
        })
    })
}
