// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int-sort arithmetic proof reconstruction tests for proof coverage (#302).
//!
//! All existing bridge-level arith reconstruction tests use Nat exclusively.
//! These tests exercise the Int sort paths in `arith_chain.rs` and
//! `arith_reconstruction.rs`, covering: detect_sort(Int), mk_chain_step(Int),
//! mk_le_refl(Int), mk_le_of_lt(Int), mk_lt_irrefl_false(Int),
//! mk_le_antisymm(Int), and the Real mk_le_of_lt rejection path.

use super::super::*;
use super::test_helpers::setup_env;
use clean_kernel::name::Name;

fn make_int_le(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.le"), vec![]), lhs),
        rhs,
    )
}

fn make_int_lt(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.lt"), vec![]), lhs),
        rhs,
    )
}

fn make_int_ge(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.ge"), vec![]), lhs),
        rhs,
    )
}

fn make_int_gt(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.gt"), vec![]), lhs),
        rhs,
    )
}

fn make_eq_int(lhs: Expr, rhs: Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    super::test_helpers::make_eq(int_ty, lhs, rhs)
}

fn assert_head_const_name(expr: &Expr, expected: &str) {
    let head = expr.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if name.to_string() == expected),
        "expected proof term head {expected}, got {head:?}"
    );
}

// ========================================================================
// Int Le reflexivity
// ========================================================================

#[test]
fn test_prove_int_le_reflexivity_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    let result = bridge
        .prove(&make_int_le(a.clone(), a.clone()))
        .expect("reflexive Int <= goal should solve")
        .verified()
        .expect("reflexive Int <= goal should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.le_refl"));
    assert_head_const_name(result.proof_term(), "Int.le_refl");
}

// ========================================================================
// Int Le transitivity chain
// ========================================================================

#[test]
fn test_prove_int_le_transitivity_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_int_le(a.clone(), b.clone()), Some(FVarId::new(1030)))
        .expect("first Int <= edge should assert");
    bridge
        .add_hypothesis_with_fvar(&make_int_le(b.clone(), c.clone()), Some(FVarId::new(1031)))
        .expect("second Int <= edge should assert");

    let result = bridge
        .prove(&make_int_le(a, c))
        .expect("Int transitivity goal should solve")
        .verified()
        .expect("Int transitivity goal should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Trans(_, _)));
    assert_head_const_name(result.proof_term(), "Int.le_trans");
}

// ========================================================================
// Int mixed Lt/Le transitivity
// ========================================================================

#[test]
fn test_prove_int_lt_le_transitivity_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_int_lt(a.clone(), b.clone()), Some(FVarId::new(1032)))
        .expect("Int < edge should assert");
    bridge
        .add_hypothesis_with_fvar(&make_int_le(b.clone(), c.clone()), Some(FVarId::new(1033)))
        .expect("Int <= edge should assert");

    let result = bridge
        .prove(&make_int_lt(a, c))
        .expect("Int mixed Lt/Le goal should solve")
        .verified()
        .expect("Int mixed Lt/Le goal should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Trans(_, _)));
    assert_head_const_name(result.proof_term(), "Int.lt_of_lt_of_le");
}

#[test]
fn test_prove_int_le_lt_transitivity_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_int_le(a.clone(), b.clone()), Some(FVarId::new(1034)))
        .expect("Int <= edge should assert");
    bridge
        .add_hypothesis_with_fvar(&make_int_lt(b.clone(), c.clone()), Some(FVarId::new(1035)))
        .expect("Int < edge should assert");

    let result = bridge
        .prove(&make_int_lt(a, c))
        .expect("Int Le/Lt chain should solve")
        .verified()
        .expect("Int Le/Lt chain should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Trans(_, _)));
    assert_head_const_name(result.proof_term(), "Int.lt_of_le_of_lt");
}

#[test]
fn test_prove_int_lt_lt_transitivity_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_int_lt(a.clone(), b.clone()), Some(FVarId::new(1036)))
        .expect("first Int < edge should assert");
    bridge
        .add_hypothesis_with_fvar(&make_int_lt(b.clone(), c.clone()), Some(FVarId::new(1037)))
        .expect("second Int < edge should assert");

    let result = bridge
        .prove(&make_int_lt(a, c))
        .expect("Int Lt/Lt chain should solve")
        .verified()
        .expect("Int Lt/Lt chain should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Trans(_, _)));
    assert_head_const_name(result.proof_term(), "Int.lt_trans");
}

// ========================================================================
// Int Lt-implies-Le weakening (exercises mk_le_of_lt for Int)
// ========================================================================

#[test]
fn test_prove_int_lt_implies_int_le_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_int_lt(a.clone(), b.clone()), Some(FVarId::new(1038)))
        .expect("Int < hypothesis should assert");

    let result = bridge
        .prove(&make_int_le(a, b))
        .expect("Int Lt-implies-Le should solve")
        .verified()
        .expect("Int Lt-implies-Le should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.le_of_lt"));
    assert_head_const_name(result.proof_term(), "Int.le_of_lt");
}

// ========================================================================
// Int Le antisymmetry (exercises mk_le_antisymm for Int)
// ========================================================================

#[test]
fn test_prove_int_le_antisymmetry_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_int_le(a.clone(), b.clone()), Some(FVarId::new(1039)))
        .expect("forward Int <= hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&make_int_le(b.clone(), a.clone()), Some(FVarId::new(1040)))
        .expect("backward Int <= hypothesis should assert");

    let result = bridge
        .prove(&make_eq_int(a, b))
        .expect("Int antisymmetry equality goal should solve")
        .verified()
        .expect("Int antisymmetry equality goal should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.le_antisymm"));
    assert_head_const_name(result.proof_term(), "Int.le_antisymm");
}

// ========================================================================
// Int False from strict cycle (exercises mk_lt_irrefl_false for Int)
// ========================================================================

#[test]
fn test_prove_false_from_int_strict_cycle_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_int_lt(a.clone(), b.clone()), Some(FVarId::new(1041)))
        .expect("first Int < hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&make_int_le(b.clone(), a.clone()), Some(FVarId::new(1042)))
        .expect("Int <= hypothesis closing cycle should assert");

    let result = bridge
        .prove(&Expr::const_(Name::from_string("False"), vec![]))
        .expect("Int strict cycle should solve");
    let verified = match result {
        SmtVerificationResult::Verified(v) => v,
        other => panic!("Int strict cycle should be verified, got {other:?}"),
    };

    assert!(
        matches!(verified.proof_step(), ProofStep::Propositional(s) if s == "arith.lt_irrefl_false")
    );
    assert_head_const_name(verified.proof_term(), "Int.lt_irrefl");
}

// ========================================================================
// Int Ge/Gt flipping (definitional abbreviations)
// ========================================================================

#[test]
fn test_prove_int_ge_reflexivity_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Int.ge a a = Int.le a a (definitional)
    let result = bridge
        .prove(&make_int_ge(a.clone(), a.clone()))
        .expect("reflexive Int >= goal should solve")
        .verified()
        .expect("reflexive Int >= goal should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.le_refl"));
    assert_head_const_name(result.proof_term(), "Int.le_refl");
}

#[test]
fn test_prove_int_gt_from_lt_hypothesis_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // hypothesis: a < b. Goal: b > a = b > a unfolds to a < b.
    bridge
        .add_hypothesis_with_fvar(&make_int_lt(a.clone(), b.clone()), Some(FVarId::new(1043)))
        .expect("Int < hypothesis should assert");

    let result = bridge
        .prove(&make_int_gt(b, a))
        .expect("Int Gt from Lt hypothesis should solve");
    let verified = match result {
        SmtVerificationResult::Verified(v) => v,
        other => panic!("Int Gt from Lt should be verified, got {other:?}"),
    };
    // Gt(b,a) unfolds to Lt(a,b), which is exactly the hypothesis
    assert!(matches!(verified.proof_step(), ProofStep::Hypothesis(_)));
}

// ========================================================================
// Real mk_le_of_lt rejection: Real sort returns None for Lt-implies-Le
// ========================================================================

#[test]
fn test_real_lt_does_not_weaken_to_le() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Make a Real.lt hypothesis
    let real_lt = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Real.lt"), vec![]),
            a.clone(),
        ),
        b.clone(),
    );
    bridge
        .add_hypothesis_with_fvar(&real_lt, Some(FVarId::new(1050)))
        .expect("Real < hypothesis should assert");

    // Try to prove Real.le a b — should NOT be verified because
    // mk_le_of_lt returns None for Real sort
    let real_le = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Real.le"), vec![]),
            a.clone(),
        ),
        b.clone(),
    );
    let result = bridge
        .prove(&real_le)
        .expect("Real proof attempt should not error");
    // Should not produce a Verified result through the le_of_lt path
    match &result {
        SmtVerificationResult::Verified(v) => {
            // If it is verified, it must NOT be through le_of_lt (which returns None for Real)
            assert!(
                !matches!(v.proof_step(), ProofStep::Propositional(s) if s == "arith.le_of_lt"),
                "Real sort must NOT produce arith.le_of_lt proofs"
            );
        }
        _ => {
            // Unverified or Unknown is the expected result for Real Lt -> Le
        }
    }
}

// ========================================================================
// Int multi-hop chain with Le weakening
// ========================================================================

#[test]
fn test_prove_int_lt_le_chain_implies_int_le_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_int_lt(a.clone(), b.clone()), Some(FVarId::new(1044)))
        .expect("Int < hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&make_int_le(b.clone(), c.clone()), Some(FVarId::new(1045)))
        .expect("Int <= hypothesis should assert");

    // Goal: a <= c. Chain gives a < c, weakened to a <= c via Int.le_of_lt
    let result = bridge
        .prove(&make_int_le(a, c))
        .expect("Int Lt/Le chain weakening should solve")
        .verified()
        .expect("Int Lt/Le chain weakening should be verified");

    assert_head_const_name(result.proof_term(), "Int.le_of_lt");
}
