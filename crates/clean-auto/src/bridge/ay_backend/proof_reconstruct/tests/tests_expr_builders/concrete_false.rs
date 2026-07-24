// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// --- lt_irrefl cycle-closing tests (Phase D: trustedArith elimination) ---

#[test]
fn test_mk_lt_irrefl_false_int_produces_irrefl_application() {
    let a = Expr::fvar(FVarId::new(1));
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_lt_irrefl_false(&Sort::Int, &a, &chain_proof);
    assert!(result.is_some(), "Int lt_irrefl should succeed");
    let expr = result.unwrap();
    assert!(
        expr_contains_const(&expr, "Int.lt_irrefl"),
        "cycle closing must use Int.lt_irrefl, not trustedArith"
    );
    assert!(
        !expr_contains_const(&expr, "trustedArith"),
        "cycle closing must NOT contain trustedArith"
    );
}

#[test]
fn test_mk_lt_irrefl_false_real_produces_irrefl_application() {
    let a = Expr::fvar(FVarId::new(1));
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_lt_irrefl_false(&Sort::Real, &a, &chain_proof);
    assert!(result.is_some(), "Real lt_irrefl should succeed");
    let expr = result.unwrap();
    assert!(
        expr_contains_const(&expr, "Real.lt_irrefl"),
        "cycle closing must use Real.lt_irrefl"
    );
    assert!(
        !expr_contains_const(&expr, "trustedArith"),
        "cycle closing must NOT contain trustedArith"
    );
}

#[test]
fn test_mk_lt_irrefl_false_bool_returns_none() {
    let a = Expr::fvar(FVarId::new(1));
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_lt_irrefl_false(&Sort::Bool, &a, &chain_proof);
    assert!(result.is_none(), "Bool lt_irrefl should return None");
}

#[test]
fn test_mk_lt_irrefl_false_uninterpreted_returns_none() {
    let a = Expr::fvar(FVarId::new(1));
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_lt_irrefl_false(&Sort::Uninterpreted("Foo".to_string()), &a, &chain_proof);
    assert!(
        result.is_none(),
        "Uninterpreted lt_irrefl should return None"
    );
}

// --- mk_int_concrete_false tests (Phase D.3: NonNeg.casesOn elimination) ---

#[test]
fn test_mk_int_concrete_false_le_uses_nonneg_caseson() {
    // Simulate chain proof for 5 ≤ 3 (violated Le bound)
    let start = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(5),
    );
    let end_ = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(3),
    );
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_int_concrete_false(CmpOp::Le, &start, &end_, &chain_proof);

    assert!(
        expr_contains_const(&result, "Int.NonNeg.casesOn"),
        "concrete Le closing must use Int.NonNeg.casesOn"
    );
    assert!(
        expr_contains_const(&result, "Int.casesOn"),
        "discriminating motive must use Int.casesOn"
    );
    assert!(
        expr_contains_const(&result, "True.intro"),
        "mk branch must provide True.intro"
    );
    assert!(
        !expr_contains_const(&result, "trustedArith"),
        "concrete Le closing must NOT contain trustedArith"
    );
}

#[test]
fn test_mk_int_concrete_false_lt_uses_nonneg_caseson() {
    // Simulate chain proof for 5 < 3 (violated Lt bound)
    let start = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(5),
    );
    let end_ = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(3),
    );
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_int_concrete_false(CmpOp::Lt, &start, &end_, &chain_proof);

    assert!(
        expr_contains_const(&result, "Int.NonNeg.casesOn"),
        "concrete Lt closing must use Int.NonNeg.casesOn"
    );
    assert!(
        expr_contains_const(&result, "Int.add"),
        "Lt case must include Int.add (for start + 1)"
    );
    assert!(
        expr_contains_const(&result, "Int.sub"),
        "must include Int.sub for NonNeg index"
    );
    assert!(
        !expr_contains_const(&result, "trustedArith"),
        "concrete Lt closing must NOT contain trustedArith"
    );
}

#[test]
fn test_mk_int_concrete_false_le_contains_int_sub() {
    // Verify the NonNeg index uses Int.sub end start (matching Int.le definition)
    let start = Expr::fvar(FVarId::new(1));
    let end_ = Expr::fvar(FVarId::new(2));
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_int_concrete_false(CmpOp::Le, &start, &end_, &chain_proof);

    assert!(
        expr_contains_const(&result, "Int.sub"),
        "NonNeg index must use Int.sub"
    );
    assert!(
        expr_contains_const(&result, "True"),
        "motive must include True (for ofNat branch)"
    );
    assert!(
        expr_contains_const(&result, "False"),
        "motive must include False (for negSucc branch)"
    );
}

// --- mk_real_concrete_false tests (Phase D.5: Real bridge axiom closing) ---

#[test]
fn test_mk_real_concrete_false_le_uses_bridge_axiom() {
    // Simulate: chain proves Real.ofNat 5 ≤ Real.ofNat 3 (violated)
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_real_concrete_false(CmpOp::Le, 5, 3, &chain_proof);

    assert!(
        expr_contains_const(&result, "Real.not_ofNat_le_of_ble_false"),
        "Real Le closing must use bridge axiom Real.not_ofNat_le_of_ble_false"
    );
    assert!(
        expr_contains_const(&result, "Nat.ble"),
        "Real Le closing must contain Nat.ble (for kernel evaluation)"
    );
    assert!(
        expr_contains_const(&result, "Eq.refl"),
        "Real Le closing must use Eq.refl for ble proof"
    );
    assert!(
        !expr_contains_const(&result, "trustedArith"),
        "Real concrete Le closing must NOT contain trustedArith"
    );
}

#[test]
fn test_mk_real_concrete_false_lt_uses_bridge_axiom() {
    // Simulate: chain proves Real.ofNat 5 < Real.ofNat 3 (violated)
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_real_concrete_false(CmpOp::Lt, 5, 3, &chain_proof);

    assert!(
        expr_contains_const(&result, "Real.not_ofNat_lt_of_ble_true"),
        "Real Lt closing must use bridge axiom Real.not_ofNat_lt_of_ble_true"
    );
    assert!(
        expr_contains_const(&result, "Nat.ble"),
        "Real Lt closing must contain Nat.ble"
    );
    assert!(
        !expr_contains_const(&result, "trustedArith"),
        "Real concrete Lt closing must NOT contain trustedArith"
    );
}

#[test]
fn test_mk_real_concrete_false_le_equal_still_uses_bridge() {
    // Lt with equal endpoints: 5 < 5 (violated, 5 >= 5)
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_real_concrete_false(CmpOp::Lt, 5, 5, &chain_proof);

    assert!(
        expr_contains_const(&result, "Real.not_ofNat_lt_of_ble_true"),
        "Real Lt=equal closing must use bridge axiom"
    );
    assert!(
        !expr_contains_const(&result, "trustedArith"),
        "Real Lt=equal closing must NOT use trustedArith"
    );
}

// --- mk_real_ofint_concrete_false tests (Phase D.6: Real.ofInt bridge axioms) ---

#[test]
fn test_mk_real_ofint_concrete_false_le_uses_bridge_axiom() {
    // Simulate: chain proves Real.ofInt 3 ≤ Real.ofInt (-2) (violated: 3 > -2)
    // a_int = Int.ofNat 3, b_int = Int.negSucc 1 (represents -2)
    let a_int = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(3),
    );
    let b_int = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(1),
    );
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_real_ofint_concrete_false(CmpOp::Le, &a_int, &b_int, &chain_proof);

    assert!(
        expr_contains_const(&result, "Real.not_ofInt_le"),
        "Real.ofInt Le closing must use Real.not_ofInt_le bridge axiom"
    );
    assert!(
        expr_contains_const(&result, "Int.NonNeg.casesOn"),
        "Real.ofInt Le closing must delegate to Int proof via NonNeg.casesOn"
    );
    assert!(
        !expr_contains_const(&result, "trustedArith"),
        "Real.ofInt Le closing must NOT use trustedArith"
    );
}

#[test]
fn test_mk_real_ofint_concrete_false_lt_uses_bridge_axiom() {
    // Simulate: chain proves Real.ofInt 5 < Real.ofInt 5 (violated: 5 >= 5)
    let a_int = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(5),
    );
    let b_int = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(5),
    );
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_real_ofint_concrete_false(CmpOp::Lt, &a_int, &b_int, &chain_proof);

    assert!(
        expr_contains_const(&result, "Real.not_ofInt_lt"),
        "Real.ofInt Lt closing must use Real.not_ofInt_lt bridge axiom"
    );
    assert!(
        expr_contains_const(&result, "Int.NonNeg.casesOn"),
        "Real.ofInt Lt closing must delegate to Int NonNeg.casesOn"
    );
    assert!(
        expr_contains_const(&result, "Int.add"),
        "Real.ofInt Lt closing must contain Int.add (for start + 1 in Lt)"
    );
    assert!(
        !expr_contains_const(&result, "trustedArith"),
        "Real.ofInt Lt closing must NOT use trustedArith"
    );
}

#[test]
fn test_mk_real_ofint_concrete_false_negative_endpoints() {
    // Both endpoints negative: Real.ofInt (-1) ≤ Real.ofInt (-5)
    // a_int = Int.negSucc 0 (represents -1), b_int = Int.negSucc 4 (represents -5)
    let a_int = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(0),
    );
    let b_int = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(4),
    );
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_real_ofint_concrete_false(CmpOp::Le, &a_int, &b_int, &chain_proof);

    assert!(
        expr_contains_const(&result, "Real.not_ofInt_le"),
        "negative-negative Le must use Real.not_ofInt_le"
    );
    assert!(
        expr_contains_const(&result, "Int.sub"),
        "NonNeg index must include Int.sub"
    );
    assert!(
        !expr_contains_const(&result, "trustedArith"),
        "negative-negative Le must NOT use trustedArith"
    );
}

#[test]
fn test_mk_real_ofint_concrete_false_lambda_structure() {
    // Verify that the proof term has the expected lambda structure:
    // Real.not_ofInt_le a b (λ h : Int.le a b => <false_body>) chain_proof
    let a_int = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(7),
    );
    let b_int = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(2),
    );
    let chain_proof = Expr::fvar(FVarId::new(10));
    let result = mk_real_ofint_concrete_false(CmpOp::Le, &a_int, &b_int, &chain_proof);

    // The result should be an application of the bridge axiom.
    // Walk the Expr to verify it contains a lambda (the int_not_proof argument).
    assert!(
        expr_contains_lambda(&result),
        "Real.ofInt proof must contain a lambda binding the Int-level hypothesis"
    );
}

/// Walk an Expr tree checking if it contains any lambda.
fn expr_contains_lambda(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Lam(_, _, _) => true,
        ExprKind::App(f, a) => expr_contains_lambda(f) || expr_contains_lambda(a),
        ExprKind::Pi(_, ty, body) => expr_contains_lambda(ty) || expr_contains_lambda(body),
        _ => false,
    }
}
