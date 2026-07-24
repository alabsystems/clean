// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::decide;
use super::*;
use serial_test::serial;

#[test]
#[serial]
fn test_validate_proof_term_type_mismatch_returns_error() {
    // Verify that validate_proof_term returns an error for a mistyped proof.
    // This is the code path that #2186 fixes: previously the error was silently
    // swallowed; now it's logged and counted.
    let env = Environment::new();
    let goal_ty = Expr::prop();
    let state = ProofState::new(env, goal_ty.clone());
    let goal = state.current_goal().expect("should have a goal").clone();

    // Construct a proof term with the wrong type (Type 0 instead of Prop)
    let bad_proof = Expr::type_();

    let result = decide::validate_proof_term(&state, &goal, &bad_proof, &goal_ty);
    assert!(
        result.is_err(),
        "validate_proof_term should reject a mistyped proof"
    );
}

#[test]
#[serial]
fn test_validate_proof_term_accepts_nat_le_proof_for_tc_target() {
    let mut env = Environment::new();
    env.init_nat().expect("Nat should initialize");
    env.init_le().expect("LE should initialize");

    let goal_ty = nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(0));
    let state = ProofState::new(env, goal_ty.clone());
    let goal = state.current_goal().expect("should have a goal").clone();

    let proof = Expr::app(
        Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
        Expr::nat_lit(0),
    );

    let result = decide::validate_proof_term(&state, &goal, &proof, &goal_ty);
    assert!(
        result.is_ok(),
        "Nat.le proof should validate against an equivalent LE.le target"
    );
}

#[test]
fn test_smt_sort_to_lean_type_int_maps_to_int() {
    // Regression test: SmtSort::Int must map to Lean "Int", not "Nat".
    // SMT-LIB Int includes negative numbers; Lean Nat does not.
    // Bug: ay_types.rs mapped SmtSort::Int → Name::from_string("Nat"). See #302.
    let lean_ty = ay_types::smt_sort_to_lean_type(SmtSort::Int);
    let actual = match lean_ty.kind() {
        clean_kernel::expr::ExprKind::Const(name, _) => name.to_string(),
        other => format!("{other:?}"),
    };
    assert_eq!(actual, "Int", "SmtSort::Int must map to Lean Int, not Nat");
}

#[test]
fn test_smt_sort_to_lean_type_bool_maps_to_prop() {
    let lean_ty = ay_types::smt_sort_to_lean_type(SmtSort::Bool);
    assert_eq!(lean_ty, Expr::prop(), "SmtSort::Bool must map to Lean Prop");
}

#[test]
fn test_smt_sort_to_lean_type_real_maps_to_real() {
    let lean_ty = ay_types::smt_sort_to_lean_type(SmtSort::Real);
    let actual = match lean_ty.kind() {
        clean_kernel::expr::ExprKind::Const(name, _) => name.to_string(),
        other => format!("{other:?}"),
    };
    assert_eq!(actual, "Real", "SmtSort::Real must map to Lean Real");
}

// Accepted-candidate finalization tests live in reconstruction_gate_tests.rs.
// Raw acceptance semantics now live on the clean-auto side of the #302 boundary.
