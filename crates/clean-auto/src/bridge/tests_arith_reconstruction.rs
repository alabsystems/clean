// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused arithmetic proof reconstruction tests for #2442 Phase 2D.

use super::super::*;
use super::test_helpers::setup_env;
use clean_kernel::name::Name;

fn make_nat_le(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), lhs),
        rhs,
    )
}

fn make_nat_lt(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), lhs),
        rhs,
    )
}

fn make_nat_ge(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.ge"), vec![]), lhs),
        rhs,
    )
}

fn make_nat_gt(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.gt"), vec![]), lhs),
        rhs,
    )
}

fn make_eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    super::test_helpers::make_eq(nat_ty, lhs, rhs)
}

fn assert_head_const_name(expr: &Expr, expected: &str) {
    let head = expr.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if name.to_string() == expected),
        "expected proof term head {expected}, got {head:?}"
    );
}

#[test]
fn test_prove_nat_le_reflexivity_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    let result = bridge
        .prove(&make_nat_le(a.clone(), a.clone()))
        .expect("reflexive arithmetic goal should solve")
        .verified()
        .expect("reflexive arithmetic goal should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.le_refl"));
    assert_head_const_name(result.proof_term(), "Nat.le_refl");
}

#[test]
fn test_prove_ground_nat_le_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let result = bridge
        .prove(&make_nat_le(Expr::nat_lit(0), Expr::nat_lit(3)))
        .expect("ground Nat <= goal should solve")
        .verified()
        .expect("ground Nat <= goal should be verified");

    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.nat_ground_le")
    );
    assert_head_const_name(result.proof_term(), "Nat.le.step");
}

#[test]
fn test_prove_ground_nat_lt_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let result = bridge
        .prove(&make_nat_lt(Expr::nat_lit(2), Expr::nat_lit(5)))
        .expect("ground Nat < goal should solve")
        .verified()
        .expect("ground Nat < goal should be verified");

    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.nat_ground_lt")
    );
    assert_head_const_name(result.proof_term(), "Nat.le.step");
}

#[test]
fn test_prove_ground_nat_add_equality_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let lhs = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(3),
    );

    let result = bridge
        .prove(&make_eq_nat(lhs, Expr::nat_lit(5)))
        .expect("ground Nat addition equality should solve");
    let verified = match result {
        SmtVerificationResult::Verified(verified) => verified,
        other => panic!("ground Nat addition equality should be verified, got {other:?}"),
    };

    assert!(
        matches!(verified.proof_step(), ProofStep::Propositional(s) if s == "arith.le_antisymm")
    );
    assert_head_const_name(verified.proof_term(), "Nat.le_antisymm");
}

#[test]
fn test_prove_ground_nat_mul_equality_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    // 2 * 3 = 6: the arith lane folds `Nat.mul` on numerals and discharges the
    // equality via `Nat.le_antisymm` on the two ground `<=` sub-goals.
    let lhs = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(3),
    );

    let result = bridge
        .prove(&make_eq_nat(lhs, Expr::nat_lit(6)))
        .expect("ground Nat multiplication equality should solve");
    let verified = match result {
        SmtVerificationResult::Verified(verified) => verified,
        other => panic!("ground Nat multiplication equality should be verified, got {other:?}"),
    };

    assert!(
        matches!(verified.proof_step(), ProofStep::Propositional(s) if s == "arith.le_antisymm")
    );
    assert_head_const_name(verified.proof_term(), "Nat.le_antisymm");
}

#[test]
fn test_prove_ground_nested_add_mul_equality_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    // (2 + 3) * 2 = 10: nested `add`-under-`mul` must fold recursively.
    let inner_add = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(3),
    );
    let lhs = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            inner_add,
        ),
        Expr::nat_lit(2),
    );

    let result = bridge
        .prove(&make_eq_nat(lhs, Expr::nat_lit(10)))
        .expect("nested ground Nat add/mul equality should solve");
    let verified = match result {
        SmtVerificationResult::Verified(verified) => verified,
        other => panic!("nested ground add/mul equality should be verified, got {other:?}"),
    };

    assert!(
        matches!(verified.proof_step(), ProofStep::Propositional(s) if s == "arith.le_antisymm")
    );
    assert_head_const_name(verified.proof_term(), "Nat.le_antisymm");
}

#[test]
fn test_prove_nat_le_transitivity_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_nat_le(a.clone(), b.clone()), Some(FVarId::new(930)))
        .expect("first arithmetic edge should assert");
    bridge
        .add_hypothesis_with_fvar(&make_nat_le(b.clone(), c.clone()), Some(FVarId::new(931)))
        .expect("second arithmetic edge should assert");

    let result = bridge
        .prove(&make_nat_le(a, c))
        .expect("transitivity arithmetic goal should solve")
        .verified()
        .expect("transitivity arithmetic goal should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Trans(_, _)));
    assert_head_const_name(result.proof_term(), "Nat.le_trans");
}

#[test]
fn test_prove_nat_lt_le_transitivity_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_nat_lt(a.clone(), b.clone()), Some(FVarId::new(932)))
        .expect("strict arithmetic edge should assert");
    bridge
        .add_hypothesis_with_fvar(&make_nat_le(b.clone(), c.clone()), Some(FVarId::new(933)))
        .expect("weak arithmetic edge should assert");

    let result = bridge
        .prove(&make_nat_lt(a, c))
        .expect("mixed arithmetic goal should solve")
        .verified()
        .expect("mixed arithmetic goal should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Trans(_, _)));
    assert_head_const_name(result.proof_term(), "Nat.lt_of_lt_of_le");
}

#[test]
fn test_prove_nat_le_weakening_with_ground_tail_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    bridge
        .add_hypothesis_with_fvar(
            &make_nat_le(a.clone(), Expr::nat_lit(5)),
            Some(FVarId::new(960)),
        )
        .expect("weak arithmetic hypothesis should assert");

    let result = bridge
        .prove(&make_nat_le(a, Expr::nat_lit(10)))
        .expect("weakening goal should solve");
    let verified = match result {
        SmtVerificationResult::Verified(verified) => verified,
        other => panic!("weakening goal should be verified, got {other:?}"),
    };

    assert!(matches!(verified.proof_step(), ProofStep::Trans(_, _)));
}

#[test]
fn test_prove_nat_lt_implies_nat_le_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_nat_lt(a.clone(), b.clone()), Some(FVarId::new(941)))
        .expect("strict arithmetic hypothesis should assert");

    let result = bridge
        .prove(&make_nat_le(a, b))
        .expect("strict arithmetic hypothesis should discharge weak goal")
        .verified()
        .expect("strict arithmetic hypothesis should be kernel-verified");

    assert!(matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.le_of_lt"));
    assert_head_const_name(result.proof_term(), "Nat.le_of_lt");
}

#[test]
fn test_prove_nat_lt_le_chain_implies_nat_le_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_nat_lt(a.clone(), b.clone()), Some(FVarId::new(942)))
        .expect("strict arithmetic hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&make_nat_le(b.clone(), c.clone()), Some(FVarId::new(943)))
        .expect("first weak arithmetic hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&make_nat_le(c.clone(), d.clone()), Some(FVarId::new(944)))
        .expect("second weak arithmetic hypothesis should assert");

    let result = bridge
        .prove(&make_nat_le(a, d))
        .expect("mixed strict/weak arithmetic chain should discharge weak goal")
        .verified()
        .expect("mixed strict/weak arithmetic chain should be kernel-verified");

    assert_head_const_name(result.proof_term(), "Nat.le_of_lt");
}

#[test]
fn test_prove_nat_le_antisymmetry_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_nat_le(a.clone(), b.clone()), Some(FVarId::new(934)))
        .expect("forward <= hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&make_nat_le(b.clone(), a.clone()), Some(FVarId::new(935)))
        .expect("backward <= hypothesis should assert");

    let result = bridge
        .prove(&make_eq_nat(a, b))
        .expect("antisymmetry equality goal should solve")
        .verified()
        .expect("antisymmetry equality goal should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.le_antisymm"));
    assert_head_const_name(result.proof_term(), "Nat.le_antisymm");
}

#[test]
fn test_prove_false_from_nat_strict_cycle_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_nat_le(a.clone(), b.clone()), Some(FVarId::new(936)))
        .expect("first cycle edge should assert");
    bridge
        .add_hypothesis_with_fvar(&make_nat_lt(b.clone(), c.clone()), Some(FVarId::new(937)))
        .expect("strict cycle edge should assert");
    bridge
        .add_hypothesis_with_fvar(&make_nat_le(c.clone(), a.clone()), Some(FVarId::new(938)))
        .expect("closing cycle edge should assert");

    let result = bridge
        .prove(&Expr::const_(Name::from_string("False"), vec![]))
        .expect("strict arithmetic cycle should solve")
        .verified()
        .expect("strict arithmetic cycle should be verified");

    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.lt_irrefl_false")
    );
    assert_head_const_name(result.proof_term(), "Nat.lt_irrefl");
}

#[test]
fn test_prove_false_from_single_ground_nat_lt_contradiction_verified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    bridge
        .add_hypothesis_with_fvar(
            &make_nat_lt(Expr::nat_lit(5), Expr::nat_lit(3)),
            Some(FVarId::new(961)),
        )
        .expect("ground contradictory arithmetic hypothesis should assert");

    let result = bridge
        .prove(&Expr::const_(Name::from_string("False"), vec![]))
        .expect("ground contradictory arithmetic hypothesis should solve");
    let verified = match result {
        SmtVerificationResult::Verified(verified) => verified,
        other => {
            panic!("ground contradictory arithmetic hypothesis should be verified, got {other:?}")
        }
    };

    assert!(
        matches!(verified.proof_step(), ProofStep::Propositional(s) if s == "arith.lt_irrefl_false")
    );
    assert_head_const_name(verified.proof_term(), "Nat.lt_irrefl");
}

#[test]
fn test_prove_arithmetic_contradiction_without_supported_reconstruction_stays_unverified() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_nat_lt(a.clone(), b.clone()), Some(FVarId::new(939)))
        .expect("first contradictory arithmetic hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&make_nat_lt(b, a.clone()), Some(FVarId::new(940)))
        .expect("second contradictory arithmetic hypothesis should assert");

    let result = bridge
        .prove(&make_eq_nat(a, c))
        .expect("unsupported arithmetic contradiction goal should still solve");
    assert!(
        result.is_unverified(),
        "unsupported arithmetic contradiction should remain unverified, got {result:?}"
    );
}

/// Ge hypothesis is flipped to Le edge: h : a >= b should prove b <= a.
/// Exercises the Ge-to-Le flipping path in collect_arithmetic_hypothesis_edges.
#[test]
fn test_prove_nat_ge_flipped_to_le() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_nat_ge(a.clone(), b.clone()), Some(FVarId::new(950)))
        .expect("Ge hypothesis should assert");

    let result = bridge.prove(&make_nat_le(b, a));
    assert!(
        result.is_ok(),
        "Ge hypothesis should discharge the flipped Le goal"
    );
}

/// Gt hypothesis is flipped to Lt edge: h : a > b should prove b < a.
#[test]
fn test_prove_nat_gt_flipped_to_lt() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    bridge
        .add_hypothesis_with_fvar(&make_nat_gt(a.clone(), b.clone()), Some(FVarId::new(951)))
        .expect("Gt hypothesis should assert");

    let result = bridge.prove(&make_nat_lt(b, a));
    assert!(
        result.is_ok(),
        "Gt hypothesis should discharge the flipped Lt goal"
    );
}

/// Ge hypothesis in a transitive chain: h1 : b >= a (Le: a <= b), h2 : b <= c.
/// Goal: a <= c via transitivity after flipping Ge to Le.
#[test]
fn test_prove_ge_in_transitive_chain() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // h1 : b >= a → flipped to Le edge: a <= b
    bridge
        .add_hypothesis_with_fvar(&make_nat_ge(b.clone(), a.clone()), Some(FVarId::new(952)))
        .expect("Ge hypothesis should assert");
    // h2 : b <= c → Le edge: b <= c
    bridge
        .add_hypothesis_with_fvar(&make_nat_le(b, c.clone()), Some(FVarId::new(953)))
        .expect("Le hypothesis should assert");

    let result = bridge.prove(&make_nat_le(a, c));
    assert!(result.is_ok(), "Ge+Le transitive chain should solve a <= c");
}

// --- Nat.zero / Nat.succ literal shape coverage (Prover audit of W2 #2442 slice) ---
// eval_small_nat handles Nat.zero and Nat.succ forms (arith_chain.rs:52-66)
// but prior tests only exercised Expr::nat_lit() inputs. These tests verify
// the full prove() path with constructor-form Nat expressions.

fn mk_nat_zero() -> Expr {
    Expr::const_(Name::from_string("Nat.zero"), vec![])
}

fn mk_nat_succ(inner: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), inner)
}

#[test]
fn test_prove_ground_nat_le_nat_zero_form() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let result = bridge
        .prove(&make_nat_le(mk_nat_zero(), Expr::nat_lit(2)))
        .expect("Nat.zero <= 2 should solve")
        .verified()
        .expect("Nat.zero <= 2 should be verified");

    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.nat_ground_le")
    );
    assert_head_const_name(result.proof_term(), "Nat.le.step");
}

#[test]
fn test_prove_ground_nat_le_nat_succ_form() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let one = mk_nat_succ(mk_nat_zero());
    let result = bridge
        .prove(&make_nat_le(one, Expr::nat_lit(3)))
        .expect("Nat.succ(Nat.zero) <= 3 should solve")
        .verified()
        .expect("Nat.succ(Nat.zero) <= 3 should be verified");

    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.nat_ground_le")
    );
    assert_head_const_name(result.proof_term(), "Nat.le.step");
}

#[test]
fn test_prove_ground_nat_lt_nat_zero_succ() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let two_succ = mk_nat_succ(mk_nat_succ(mk_nat_zero()));
    let result = bridge
        .prove(&make_nat_lt(mk_nat_zero(), two_succ))
        .expect("Nat.zero < Nat.succ(Nat.succ(Nat.zero)) should solve")
        .verified()
        .expect("Nat.zero < Nat.succ(Nat.succ(Nat.zero)) should be verified");

    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.nat_ground_lt")
    );
    assert_head_const_name(result.proof_term(), "Nat.le.step");
}

#[test]
fn test_prove_ground_nat_le_mixed_lit_and_succ() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let succ_two = mk_nat_succ(mk_nat_succ(mk_nat_zero()));
    let result = bridge
        .prove(&make_nat_le(Expr::nat_lit(1), succ_two))
        .expect("nat_lit(1) <= Nat.succ(Nat.succ(Nat.zero)) should solve")
        .verified()
        .expect("nat_lit(1) <= Nat.succ(Nat.succ(Nat.zero)) should be verified");

    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.nat_ground_le")
    );
    assert_head_const_name(result.proof_term(), "Nat.le.step");
}

#[test]
fn test_prove_ground_nat_le_refl_nat_zero() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let zero = mk_nat_zero();
    let result = bridge
        .prove(&make_nat_le(zero.clone(), zero))
        .expect("Nat.zero <= Nat.zero should solve")
        .verified()
        .expect("Nat.zero <= Nat.zero should be verified");

    // Ground Nat.zero <= Nat.zero takes the nat_ground_le fast path
    // (build_direct_arithmetic_goal_proof) rather than the symbolic le_refl path,
    // producing Nat.le.refl via mk_nat_le_constructor_chain(0, 0).
    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.nat_ground_le")
    );
    assert_head_const_name(result.proof_term(), "Nat.le.refl");
}

#[test]
fn test_prove_ground_nat_ge_verified() {
    // Nat.ge a b = Nat.le b a (definitional). Proof of b <= a should
    // type-check against a >= b because GE.ge unfolds to LE.le with
    // swapped arguments.
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let result = bridge
        .prove(&make_nat_ge(Expr::nat_lit(3), Expr::nat_lit(0)))
        .expect("ground Nat >= goal should solve")
        .verified()
        .expect("ground Nat >= goal should be verified");

    // The Ge goal normalizes to Le with swapped args: 0 <= 3
    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.nat_ground_le")
    );
    assert_head_const_name(result.proof_term(), "Nat.le.step");
}

#[test]
fn test_prove_ground_nat_gt_verified() {
    // Nat.gt a b = Nat.lt b a (definitional). Proof of b < a should
    // type-check against a > b.
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let result = bridge
        .prove(&make_nat_gt(Expr::nat_lit(5), Expr::nat_lit(2)))
        .expect("ground Nat > goal should solve")
        .verified()
        .expect("ground Nat > goal should be verified");

    // The Gt goal normalizes to Lt with swapped args: 2 < 5
    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.nat_ground_lt")
    );
    assert_head_const_name(result.proof_term(), "Nat.le.step");
}

#[test]
fn test_prove_ground_nat_ge_reflexive() {
    // a >= a normalizes to a <= a, which should hit le_refl.
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    let result = bridge
        .prove(&make_nat_ge(a.clone(), a.clone()))
        .expect("reflexive Nat >= goal should solve")
        .verified()
        .expect("reflexive Nat >= goal should be verified");

    assert!(matches!(result.proof_step(), ProofStep::Propositional(s) if s == "arith.le_refl"));
    assert_head_const_name(result.proof_term(), "Nat.le_refl");
}
