// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Basic proof verification tests: reflexivity, symmetry, transitivity,
//! congruence, contradiction, and unprovability.
//!
//! Extracted from bridge/tests.rs as part of Phase A test migration (#307).

use super::super::*;
use super::test_helpers::{make_eq, setup_env};

#[test]
fn test_prove_reflexivity() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: a = a (reflexivity)
    let goal = make_eq(a_ty, a.clone(), a);

    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove a = a");
    // Proof step must be Refl
    let step = result.proof_step();
    assert!(
        matches!(step, ProofStep::Refl(_)),
        "Proof step for a = a should be Refl, got {step:?}"
    );
}

#[test]
fn test_prove_symmetry() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Hypothesis: a = b (with FVarId for proof reconstruction)
    let hyp = make_eq(a_ty.clone(), a.clone(), b.clone());
    bridge
        .add_hypothesis_with_fvar(&hyp, Some(FVarId::new(42)))
        .unwrap();

    // Goal: b = a
    let goal = make_eq(a_ty, b, a);

    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove b = a from a = b");
    // Proof step must be Symm wrapping the hypothesis
    let step = result.proof_step();
    assert!(
        matches!(step, ProofStep::Symm(_)),
        "Proof step for b = a from h: a = b should be Symm, got {step:?}"
    );
    // The inner step must reference hypothesis FVarId(42)
    let hyp_ids = super::collect_hypothesis_ids(step);
    assert!(
        hyp_ids.contains(&FVarId::new(42)),
        "Symmetry proof must reference hypothesis FVarId(42), found IDs: {hyp_ids:?}"
    );
}

#[test]
fn test_prove_from_false_hypothesis() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    // Hypothesis: False (ex falso quodlibet -- anything follows)
    let false_hyp = Expr::const_(Name::from_string("False"), vec![]);
    bridge.add_hypothesis(&false_hyp).unwrap();

    // Goal: arbitrary equality a = b with no other evidence
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let goal = make_eq(a_ty, a, b);

    // SMT returns UNSAT (False makes anything provable), but proof
    // reconstruction cannot build a kernel proof for a = b from False
    // alone -- the equality theory has no proof steps. This correctly
    // returns Unverified (#2393, #2387 TB2).
    let result = bridge.prove(&goal).unwrap();
    assert!(
        result.is_unverified(),
        "False hypothesis: SMT proves UNSAT but reconstruction cannot build proof, expected Unverified"
    );
}

#[test]
fn test_prove_from_tracked_false_hypothesis() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let false_hyp = Expr::const_(Name::from_string("False"), vec![]);
    bridge
        .add_hypothesis_with_fvar(&false_hyp, Some(FVarId::new(0)))
        .unwrap();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let goal = make_eq(a_ty, a, b);

    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("tracked False should prove any equality goal via ex-falso");

    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "False.elim"),
        "tracked False should use False.elim fallback, got {:?}",
        result.proof_step()
    );
}

#[test]
fn test_prove_transitivity() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Hypotheses: a = b, b = c (with FVarIds for proof reconstruction)
    let hyp1 = make_eq(a_ty.clone(), a.clone(), b.clone());
    let hyp2 = make_eq(a_ty.clone(), b, c.clone());
    bridge
        .add_hypothesis_with_fvar(&hyp1, Some(FVarId::new(10)))
        .unwrap();
    bridge
        .add_hypothesis_with_fvar(&hyp2, Some(FVarId::new(11)))
        .unwrap();

    // Goal: a = c
    let goal = make_eq(a_ty, a, c);

    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove a = c from a = b, b = c");
    // Proof step must be Trans composing both hypotheses
    let step = result.proof_step();
    assert!(
        matches!(step, ProofStep::Trans(_, _)),
        "Proof step for a = c from h1: a = b, h2: b = c should be Trans, got {step:?}"
    );
    // Both hypothesis FVarIds must appear in the proof tree
    let hyp_ids = super::collect_hypothesis_ids(step);
    assert!(
        hyp_ids.contains(&FVarId::new(10)),
        "Transitivity proof must reference h1 FVarId(10), found IDs: {hyp_ids:?}"
    );
    assert!(
        hyp_ids.contains(&FVarId::new(11)),
        "Transitivity proof must reference h2 FVarId(11), found IDs: {hyp_ids:?}"
    );
}

#[test]
fn test_prove_congruence() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let fa = Expr::app(f.clone(), a.clone());
    let fb = Expr::app(f, b.clone());

    // Hypothesis: a = b (with FVarId for proof reconstruction)
    let hyp = make_eq(a_ty.clone(), a, b);
    bridge
        .add_hypothesis_with_fvar(&hyp, Some(FVarId::new(20)))
        .unwrap();

    // Goal: f(a) = f(b)
    let goal = make_eq(a_ty, fa, fb);

    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove f(a) = f(b) from a = b");
    // Proof step must be Congr("f") with the hypothesis inside
    let step = result.proof_step();
    assert!(
        super::congr_func_name(step).as_deref() == Some("f"),
        "Proof step for f(a) = f(b) from h: a = b should be Congr(\"f\", ..), got {step:?}"
    );
    // The hypothesis FVarId must appear in the proof tree
    let hyp_ids = super::collect_hypothesis_ids(step);
    assert!(
        hyp_ids.contains(&FVarId::new(20)),
        "Congruence proof must reference hypothesis FVarId(20), found IDs: {hyp_ids:?}"
    );
}

#[test]
fn test_cannot_prove_false() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Goal: a = b (without any hypotheses)
    // This should NOT be provable
    let goal = make_eq(a_ty, a, b);

    let result = bridge.prove(&goal).unwrap();
    assert!(
        !result.is_verified(),
        "Should not prove a = b without hypotheses"
    );
}

#[test]
fn test_prove_with_contradiction() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Hypothesis h1: a = b (with FVarId for proof reconstruction)
    let hyp1 = make_eq(a_ty.clone(), a.clone(), b.clone());
    bridge
        .add_hypothesis_with_fvar(&hyp1, Some(FVarId::new(30)))
        .unwrap();

    // Add a != b (which is Not (Eq A a b))
    // Asserted directly through the SMT solver (no FVarId -- raw SMT assertion).
    // Proof reconstruction cannot track raw SMT assertions, so proof_step
    // verification is limited to the SmtUnsat method for this test.
    let t_a = bridge.translate_term(&a).unwrap();
    let t_b = bridge.translate_term(&b).unwrap();
    let _ = bridge.smt.assert_neq(t_a, t_b);

    // Now any goal should be provable (ex falso quodlibet)
    // The SMT solver should return UNSAT for any query
    let goal = make_eq(a_ty.clone(), a.clone(), c.clone());

    // Contradictory hypotheses (a=b AND a!=b) -> SMT returns UNSAT.
    // But proof reconstruction cannot build a kernel proof for a = c from
    // the contradiction (raw assert_neq bypasses proof tracking), so this
    // correctly returns Unverified (#2393, #2387 TB2).
    let result = bridge.prove(&goal).unwrap();
    assert!(
        result.is_unverified(),
        "contradiction: SMT proves UNSAT but reconstruction cannot build proof for a=c"
    );

    // Also verify the negative case: without contradiction, a=c should NOT be provable.
    // This ensures the test isn't trivially true because the solver always returns UNSAT.
    let mut bridge2 = SmtBridge::new(&env);
    bridge2
        .add_hypothesis_with_fvar(&hyp1, Some(FVarId::new(30)))
        .unwrap();
    // No assert_neq -- just h1: a = b, goal: a = c
    let goal2 = make_eq(a_ty, a, c);
    assert!(
        !bridge2.prove(&goal2).unwrap().is_verified(),
        "Without contradiction, a = c should NOT be provable from a = b alone"
    );
}

#[test]
fn test_prove_with_tracked_contradiction() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    let eq_ab = make_eq(a_ty.clone(), a.clone(), b.clone());
    let not_eq_ab = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_ab.clone(),
    );

    bridge
        .add_hypothesis_with_fvar(&eq_ab, Some(FVarId::new(0)))
        .unwrap();
    bridge
        .add_hypothesis_with_fvar(&not_eq_ab, Some(FVarId::new(1)))
        .unwrap();

    let goal = make_eq(a_ty, a, c);
    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("tracked contradiction should prove any equality goal via absurd");

    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "absurd"),
        "tracked contradiction should use absurd fallback, got {:?}",
        result.proof_step()
    );
}

// --- Propositional proof reconstruction tests (#2442 Phase 1) ---

#[test]
fn test_prove_true_goal() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    // Goal: True — should be trivially provable via True.intro
    let goal = Expr::const_(Name::from_string("True"), vec![]);

    let result = bridge.prove(&goal).unwrap();
    assert!(
        result.is_verified(),
        "True goal should produce Verified via propositional reconstruction"
    );
}

#[test]
fn test_prove_hypothesis_match() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    // Hypothesis: P (an opaque proposition), with FVarId for reconstruction
    let p = Expr::const_(Name::from_string("a"), vec![]);
    bridge
        .add_hypothesis_with_fvar(&p, Some(FVarId::new(100)))
        .unwrap();

    // Goal: P (same expression as hypothesis)
    let result = bridge.prove(&p).unwrap();
    assert!(
        result.is_verified(),
        "Goal matching a hypothesis should produce Verified via propositional reconstruction"
    );
}

/// Regression test for #2836: second prove() call must be rejected (clean-first case).
///
/// The bridge accumulates solver clauses, lossy atoms, and hypothesis state
/// that is not reset between calls. A second prove() would operate on
/// contaminated state, producing potentially unsound results.
#[test]
fn test_prove_reuse_rejected() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty, a.clone(), a);

    // First prove() should succeed
    let first = bridge.prove(&goal);
    assert!(first.is_ok(), "first prove() should succeed");

    // Second prove() must return BridgeReuse error
    let second = bridge.prove(&goal);
    assert!(
        matches!(second, Err(BridgeError::BridgeReuse)),
        "second prove() on same bridge must return BridgeReuse, got: {second:?}"
    );
}

/// Regression test for #2836: second prove() after a lossy first goal must be rejected.
///
/// Without the single-shot guard, the second prove() would inherit the first
/// goal's lossy_atoms and negated clauses, producing stale `Unknown` or
/// cross-goal contamination instead of a clean error.
#[test]
fn test_prove_reuse_rejected_after_lossy_first() {
    let env = Environment::new();
    let mut bridge = SmtBridge::new(&env);

    // Build a lossy goal: Eq Nat (let x : Nat := 0 in x) 0
    // Let-expressions produce lossy fallback atoms, causing Unknown.
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let let_expr = Expr::let_named(
        Name::anon(),
        nat_ty.clone(),
        Expr::nat_lit(0),
        Expr::bvar(0),
        false,
    );
    let lossy_goal = make_eq(nat_ty, let_expr, Expr::nat_lit(0));

    // First prove() returns Unknown due to lossy translation
    let first = bridge.prove(&lossy_goal);
    assert!(
        matches!(first, Ok(SmtVerificationResult::Unknown(_))),
        "first prove() with lossy goal should return Unknown, got: {first:?}"
    );

    // Second prove() must return BridgeReuse, not inherit stale lossy state
    let clean_goal = {
        let a_ty = Expr::const_(Name::from_string("A"), vec![]);
        let a = Expr::const_(Name::from_string("a"), vec![]);
        make_eq(a_ty, a.clone(), a)
    };
    let second = bridge.prove(&clean_goal);
    assert!(
        matches!(second, Err(BridgeError::BridgeReuse)),
        "second prove() after lossy first must return BridgeReuse, got: {second:?}"
    );
}
