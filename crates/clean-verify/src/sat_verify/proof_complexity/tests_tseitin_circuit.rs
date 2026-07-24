// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tseitin circuit-to-CNF transformation module.

use super::tseitin_circuit::*;

fn circuit_1gate(num_inputs: u32, gate_type: GateType, inputs: Vec<u32>) -> Circuit {
    Circuit {
        num_inputs,
        gates: vec![Gate {
            gate_type,
            inputs,
            output: None,
        }],
    }
}

fn and_circuit() -> Circuit {
    circuit_1gate(2, GateType::AndType, vec![1, 2])
}
fn or_circuit() -> Circuit {
    circuit_1gate(2, GateType::Or, vec![1, 2])
}
fn not_circuit() -> Circuit {
    circuit_1gate(1, GateType::Not, vec![1])
}
fn xor_circuit() -> Circuit {
    circuit_1gate(2, GateType::Xor, vec![1, 2])
}
fn implies_circuit() -> Circuit {
    circuit_1gate(2, GateType::Implies, vec![1, 2])
}

fn assert_equisat_2input(c: &Circuit) {
    let r = tseitin_transform(c);
    for a in &[
        &[false, false][..],
        &[false, true],
        &[true, false],
        &[true, true],
    ] {
        let out = evaluate_circuit(c, a) == Some(true);
        assert_eq!(
            out,
            verify_tseitin_equisat(c, &r, a),
            "equisat mismatch for {:?}",
            a
        );
    }
}

// GateType derive traits

#[test]
fn test_gate_type_debug() {
    assert_eq!(format!("{:?}", GateType::AndType), "AndType");
    assert_eq!(format!("{:?}", GateType::Xor), "Xor");
}

#[test]
fn test_gate_type_clone() {
    let g = GateType::Or;
    let g2 = g;
    assert_eq!(g, g2);
}

#[test]
fn test_gate_type_copy() {
    let g = GateType::Not;
    let g2 = g; // Copy semantics
    assert_eq!(g, g2);
}

#[test]
fn test_gate_type_partial_eq() {
    assert_eq!(GateType::AndType, GateType::AndType);
    assert_ne!(GateType::AndType, GateType::Or);
}

#[test]
fn test_gate_type_eq_all_variants_pairwise() {
    let variants = [
        GateType::AndType,
        GateType::Or,
        GateType::Not,
        GateType::Xor,
        GateType::Implies,
    ];
    for (i, a) in variants.iter().enumerate() {
        for (j, b) in variants.iter().enumerate() {
            assert_eq!(i == j, a == b, "{:?} vs {:?}", a, b);
        }
    }
}

// Gate / Circuit / TseitinResult construction and traits

#[test]
fn test_gate_construction() {
    let gate = Gate {
        gate_type: GateType::Xor,
        inputs: vec![1, 2],
        output: None,
    };
    assert_eq!(gate.gate_type, GateType::Xor);
    assert_eq!(gate.inputs, vec![1, 2]);
    assert!(gate.output.is_none());
}

#[test]
fn test_circuit_construction_empty() {
    let c = Circuit {
        num_inputs: 3,
        gates: vec![],
    };
    assert_eq!(c.num_inputs, 3);
    assert!(c.gates.is_empty());
}

#[test]
fn test_gate_debug_and_clone() {
    let gate = Gate {
        gate_type: GateType::AndType,
        inputs: vec![1, 2],
        output: Some(3),
    };
    assert!(format!("{:?}", gate).contains("AndType"));
    let cloned = gate.clone();
    assert_eq!(cloned.gate_type, GateType::AndType);
    assert_eq!(cloned.output, Some(3));
}

#[test]
fn test_circuit_debug_and_clone() {
    let c = and_circuit();
    assert!(format!("{:?}", c).contains("Circuit"));
    let cloned = c.clone();
    assert_eq!(cloned.num_inputs, 2);
    assert_eq!(cloned.gates.len(), 1);
}

#[test]
fn test_tseitin_result_debug_and_clone() {
    let r = tseitin_transform(&and_circuit());
    assert!(format!("{:?}", r).contains("TseitinResult"));
    let cloned = r.clone();
    assert_eq!(cloned.num_vars, r.num_vars);
    assert_eq!(cloned.output_var, r.output_var);
    assert_eq!(cloned.clauses.len(), r.clauses.len());
}

// evaluate_circuit

#[test]
fn test_gate_with_output_set() {
    let g = Gate {
        gate_type: GateType::Or,
        inputs: vec![1, 2],
        output: Some(5),
    };
    assert_eq!(g.output, Some(5));
}

#[test]
fn test_evaluate_empty_circuit_returns_none() {
    let c = Circuit {
        num_inputs: 2,
        gates: vec![],
    };
    assert_eq!(evaluate_circuit(&c, &[true, false]), None);
}

#[test]
fn test_evaluate_and_all_combos() {
    let c = and_circuit();
    assert_eq!(evaluate_circuit(&c, &[true, true]), Some(true));
    assert_eq!(evaluate_circuit(&c, &[true, false]), Some(false));
    assert_eq!(evaluate_circuit(&c, &[false, true]), Some(false));
    assert_eq!(evaluate_circuit(&c, &[false, false]), Some(false));
}

#[test]
fn test_evaluate_or_all_combos() {
    let c = or_circuit();
    assert_eq!(evaluate_circuit(&c, &[false, false]), Some(false));
    assert_eq!(evaluate_circuit(&c, &[true, false]), Some(true));
    assert_eq!(evaluate_circuit(&c, &[false, true]), Some(true));
    assert_eq!(evaluate_circuit(&c, &[true, true]), Some(true));
}

#[test]
fn test_evaluate_not_both() {
    assert_eq!(evaluate_circuit(&not_circuit(), &[true]), Some(false));
    assert_eq!(evaluate_circuit(&not_circuit(), &[false]), Some(true));
}

#[test]
fn test_evaluate_xor_all_combos() {
    let c = xor_circuit();
    assert_eq!(evaluate_circuit(&c, &[false, false]), Some(false));
    assert_eq!(evaluate_circuit(&c, &[true, false]), Some(true));
    assert_eq!(evaluate_circuit(&c, &[false, true]), Some(true));
    assert_eq!(evaluate_circuit(&c, &[true, true]), Some(false));
}

#[test]
fn test_evaluate_implies_all_combos() {
    let c = implies_circuit();
    assert_eq!(evaluate_circuit(&c, &[false, false]), Some(true));
    assert_eq!(evaluate_circuit(&c, &[false, true]), Some(true));
    assert_eq!(evaluate_circuit(&c, &[true, false]), Some(false));
    assert_eq!(evaluate_circuit(&c, &[true, true]), Some(true));
}

#[test]
fn test_evaluate_multi_gate_and_then_or() {
    let c = Circuit {
        num_inputs: 2,
        gates: vec![
            Gate {
                gate_type: GateType::AndType,
                inputs: vec![1, 2],
                output: None,
            },
            Gate {
                gate_type: GateType::Or,
                inputs: vec![3, 1],
                output: None,
            },
        ],
    };
    assert_eq!(evaluate_circuit(&c, &[true, true]), Some(true));
    assert_eq!(evaluate_circuit(&c, &[true, false]), Some(true));
    assert_eq!(evaluate_circuit(&c, &[false, false]), Some(false));
}

#[test]
fn test_evaluate_multi_gate_not_then_and() {
    let c = Circuit {
        num_inputs: 1,
        gates: vec![
            Gate {
                gate_type: GateType::Not,
                inputs: vec![1],
                output: None,
            },
            Gate {
                gate_type: GateType::AndType,
                inputs: vec![2, 1],
                output: None,
            },
        ],
    };
    assert_eq!(evaluate_circuit(&c, &[true]), Some(false));
    assert_eq!(evaluate_circuit(&c, &[false]), Some(false));
}

#[test]
fn test_evaluate_three_gate_chain() {
    let c = Circuit {
        num_inputs: 2,
        gates: vec![
            Gate {
                gate_type: GateType::AndType,
                inputs: vec![1, 2],
                output: None,
            },
            Gate {
                gate_type: GateType::Not,
                inputs: vec![3],
                output: None,
            },
            Gate {
                gate_type: GateType::Or,
                inputs: vec![4, 2],
                output: None,
            },
        ],
    };
    assert_eq!(evaluate_circuit(&c, &[true, true]), Some(true));
    assert_eq!(evaluate_circuit(&c, &[false, false]), Some(true));
    assert_eq!(evaluate_circuit(&c, &[true, false]), Some(true));
}

#[test]
fn test_evaluate_short_assignment_defaults_false() {
    let c = circuit_1gate(3, GateType::AndType, vec![1, 2]);
    assert_eq!(evaluate_circuit(&c, &[true]), Some(false)); // input 2 defaults to false
}

#[test]
fn test_evaluate_extra_inputs_ignored() {
    let c = circuit_1gate(1, GateType::Not, vec![1]);
    assert_eq!(evaluate_circuit(&c, &[true, true, true]), Some(false));
}

// tseitin_transform structure

#[test]
fn test_tseitin_and_clause_count() {
    let r = tseitin_transform(&and_circuit());
    assert_eq!(r.clauses.len(), 4); // 3 gate + 1 unit
    assert_eq!(r.num_vars, 3);
    assert_eq!(r.output_var, 3);
}

#[test]
fn test_tseitin_or_clause_count() {
    let r = tseitin_transform(&or_circuit());
    assert_eq!(r.clauses.len(), 4);
    assert_eq!(r.num_vars, 3);
}

#[test]
fn test_tseitin_not_clause_count() {
    let r = tseitin_transform(&not_circuit());
    assert_eq!(r.clauses.len(), 3); // 2 gate + 1 unit
    assert_eq!(r.num_vars, 2);
    assert_eq!(r.output_var, 2);
}

#[test]
fn test_tseitin_xor_clause_count() {
    let r = tseitin_transform(&xor_circuit());
    assert_eq!(r.clauses.len(), 5); // 4 gate + 1 unit
    assert_eq!(r.num_vars, 3);
}

#[test]
fn test_tseitin_implies_clause_count() {
    let r = tseitin_transform(&implies_circuit());
    assert_eq!(r.clauses.len(), 4);
    assert_eq!(r.num_vars, 3);
}

#[test]
fn test_tseitin_two_gates_clause_and_var_count() {
    let c = Circuit {
        num_inputs: 2,
        gates: vec![
            Gate {
                gate_type: GateType::AndType,
                inputs: vec![1, 2],
                output: None,
            },
            Gate {
                gate_type: GateType::Or,
                inputs: vec![3, 2],
                output: None,
            },
        ],
    };
    let r = tseitin_transform(&c);
    assert_eq!(r.clauses.len(), 7); // 3 + 3 + 1
    assert_eq!(r.num_vars, 4);
    assert_eq!(r.output_var, 4);
}

#[test]
fn test_tseitin_output_var_is_last_gate() {
    let c = Circuit {
        num_inputs: 3,
        gates: vec![
            Gate {
                gate_type: GateType::Xor,
                inputs: vec![1, 2],
                output: None,
            },
            Gate {
                gate_type: GateType::Not,
                inputs: vec![3],
                output: None,
            },
            Gate {
                gate_type: GateType::AndType,
                inputs: vec![4, 5],
                output: None,
            },
        ],
    };
    let r = tseitin_transform(&c);
    assert_eq!(r.output_var, 6);
    assert_eq!(r.num_vars, 6);
}

#[test]
fn test_tseitin_unit_clause_for_output() {
    let r = tseitin_transform(&and_circuit());
    let last = r.clauses.last().unwrap();
    assert_eq!(last, &vec![r.output_var as i32]);
}

#[test]
fn test_tseitin_and_gate_encoding_detail() {
    let r = tseitin_transform(&and_circuit());
    // z=3, x=1, y=2: [-z,x], [-z,y], [-x,-y,z], [z]
    assert_eq!(r.clauses[0], vec![-3, 1]);
    assert_eq!(r.clauses[1], vec![-3, 2]);
    assert_eq!(r.clauses[2], vec![-1, -2, 3]);
    assert_eq!(r.clauses[3], vec![3]);
}

#[test]
fn test_tseitin_not_gate_encoding_detail() {
    let r = tseitin_transform(&not_circuit());
    // z=2, x=1: [-x,-z], [x,z], [z]
    assert_eq!(r.clauses[0], vec![-1, -2]);
    assert_eq!(r.clauses[1], vec![1, 2]);
    assert_eq!(r.clauses[2], vec![2]);
}

// verify_tseitin_equisat

#[test]
fn test_verify_and_all_combos() {
    let c = and_circuit();
    let r = tseitin_transform(&c);
    assert!(verify_tseitin_equisat(&c, &r, &[true, true]));
    assert!(!verify_tseitin_equisat(&c, &r, &[true, false]));
    assert!(!verify_tseitin_equisat(&c, &r, &[false, true]));
    assert!(!verify_tseitin_equisat(&c, &r, &[false, false]));
}

#[test]
fn test_verify_or_all_combos() {
    let c = or_circuit();
    let r = tseitin_transform(&c);
    assert!(verify_tseitin_equisat(&c, &r, &[true, true]));
    assert!(verify_tseitin_equisat(&c, &r, &[true, false]));
    assert!(verify_tseitin_equisat(&c, &r, &[false, true]));
    assert!(!verify_tseitin_equisat(&c, &r, &[false, false]));
}

#[test]
fn test_verify_not_all_combos() {
    let c = not_circuit();
    let r = tseitin_transform(&c);
    assert!(verify_tseitin_equisat(&c, &r, &[false]));
    assert!(!verify_tseitin_equisat(&c, &r, &[true]));
}

#[test]
fn test_verify_xor_all_combos() {
    let c = xor_circuit();
    let r = tseitin_transform(&c);
    assert!(!verify_tseitin_equisat(&c, &r, &[false, false]));
    assert!(verify_tseitin_equisat(&c, &r, &[true, false]));
    assert!(verify_tseitin_equisat(&c, &r, &[false, true]));
    assert!(!verify_tseitin_equisat(&c, &r, &[true, true]));
}

#[test]
fn test_verify_implies_all_combos() {
    let c = implies_circuit();
    let r = tseitin_transform(&c);
    assert!(verify_tseitin_equisat(&c, &r, &[false, false]));
    assert!(verify_tseitin_equisat(&c, &r, &[false, true]));
    assert!(!verify_tseitin_equisat(&c, &r, &[true, false]));
    assert!(verify_tseitin_equisat(&c, &r, &[true, true]));
}

#[test]
fn test_verify_multi_gate_and_then_or() {
    let c = Circuit {
        num_inputs: 2,
        gates: vec![
            Gate {
                gate_type: GateType::AndType,
                inputs: vec![1, 2],
                output: None,
            },
            Gate {
                gate_type: GateType::Or,
                inputs: vec![3, 1],
                output: None,
            },
        ],
    };
    let r = tseitin_transform(&c);
    assert!(verify_tseitin_equisat(&c, &r, &[true, true]));
    assert!(verify_tseitin_equisat(&c, &r, &[true, false]));
    assert!(!verify_tseitin_equisat(&c, &r, &[false, true]));
    assert!(!verify_tseitin_equisat(&c, &r, &[false, false]));
}

#[test]
fn test_verify_three_gate_chain() {
    let c = Circuit {
        num_inputs: 2,
        gates: vec![
            Gate {
                gate_type: GateType::Xor,
                inputs: vec![1, 2],
                output: None,
            },
            Gate {
                gate_type: GateType::Not,
                inputs: vec![3],
                output: None,
            },
            Gate {
                gate_type: GateType::AndType,
                inputs: vec![4, 1],
                output: None,
            },
        ],
    };
    let r = tseitin_transform(&c);
    assert!(verify_tseitin_equisat(&c, &r, &[true, true]));
    assert!(!verify_tseitin_equisat(&c, &r, &[true, false]));
    assert!(!verify_tseitin_equisat(&c, &r, &[false, true]));
    assert!(!verify_tseitin_equisat(&c, &r, &[false, false]));
}

// Equisatisfiability property tests

#[test]
fn test_equisat_and_satisfying_count() {
    let c = and_circuit();
    let r = tseitin_transform(&c);
    let combos: &[&[bool]] = &[
        &[false, false],
        &[false, true],
        &[true, false],
        &[true, true],
    ];
    let sat_count = combos
        .iter()
        .filter(|a| evaluate_circuit(&c, a) == Some(true) && verify_tseitin_equisat(&c, &r, a))
        .count();
    assert_eq!(sat_count, 1);
}

#[test]
fn test_equisat_or_satisfying_count() {
    let c = or_circuit();
    let r = tseitin_transform(&c);
    let combos: &[&[bool]] = &[
        &[false, false],
        &[false, true],
        &[true, false],
        &[true, true],
    ];
    let sat_count = combos
        .iter()
        .filter(|a| evaluate_circuit(&c, a) == Some(true) && verify_tseitin_equisat(&c, &r, a))
        .count();
    assert_eq!(sat_count, 3);
}

#[test]
fn test_equisat_not_satisfying_count() {
    let c = not_circuit();
    let r = tseitin_transform(&c);
    let combos: &[&[bool]] = &[&[false], &[true]];
    let sat_count = combos
        .iter()
        .filter(|a| evaluate_circuit(&c, a) == Some(true) && verify_tseitin_equisat(&c, &r, a))
        .count();
    assert_eq!(sat_count, 1);
}

#[test]
fn test_equisat_xor_exhaustive() {
    assert_equisat_2input(&xor_circuit());
}

#[test]
fn test_equisat_implies_exhaustive() {
    assert_equisat_2input(&implies_circuit());
}

#[test]
fn test_equisat_and_exhaustive() {
    assert_equisat_2input(&and_circuit());
}

#[test]
fn test_equisat_or_exhaustive() {
    assert_equisat_2input(&or_circuit());
}

#[test]
fn test_equisat_chained_gates_exhaustive() {
    let c = Circuit {
        num_inputs: 2,
        gates: vec![
            Gate {
                gate_type: GateType::AndType,
                inputs: vec![1, 2],
                output: None,
            },
            Gate {
                gate_type: GateType::Or,
                inputs: vec![3, 2],
                output: None,
            },
        ],
    };
    assert_equisat_2input(&c);
}

#[test]
fn test_equisat_three_input_circuit_exhaustive() {
    let c = Circuit {
        num_inputs: 3,
        gates: vec![
            Gate {
                gate_type: GateType::Or,
                inputs: vec![1, 2],
                output: None,
            },
            Gate {
                gate_type: GateType::AndType,
                inputs: vec![4, 3],
                output: None,
            },
        ],
    };
    let r = tseitin_transform(&c);
    for b0 in [false, true] {
        for b1 in [false, true] {
            for b2 in [false, true] {
                let a = &[b0, b1, b2];
                let circuit_out = evaluate_circuit(&c, a) == Some(true);
                let tseitin_sat = verify_tseitin_equisat(&c, &r, a);
                assert_eq!(circuit_out, tseitin_sat, "3-input mismatch for {:?}", a);
            }
        }
    }
}

#[test]
fn test_equisat_all_gate_types_chained() {
    let c = Circuit {
        num_inputs: 1,
        gates: vec![
            Gate {
                gate_type: GateType::Not,
                inputs: vec![1],
                output: None,
            },
            Gate {
                gate_type: GateType::AndType,
                inputs: vec![2, 1],
                output: None,
            },
            Gate {
                gate_type: GateType::Or,
                inputs: vec![3, 1],
                output: None,
            },
            Gate {
                gate_type: GateType::Xor,
                inputs: vec![4, 1],
                output: None,
            },
            Gate {
                gate_type: GateType::Implies,
                inputs: vec![5, 1],
                output: None,
            },
        ],
    };
    let r = tseitin_transform(&c);
    for &b in &[false, true] {
        let circuit_out = evaluate_circuit(&c, &[b]) == Some(true);
        let tseitin_sat = verify_tseitin_equisat(&c, &r, &[b]);
        assert_eq!(
            circuit_out, tseitin_sat,
            "all-gate chain mismatch for input={}",
            b
        );
    }
}
