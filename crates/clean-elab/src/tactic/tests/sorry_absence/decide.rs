// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
#[serial]
fn test_decide_sorry_count_on_reflexivity() {
    // Goal: a = a — decide proves via SMT with kernel-checkable proof reconstruction.
    //
    // PROOF QUALITY IMPROVEMENT (Part of #2047): SmtBridge proof reconstruction
    // now correctly threads the type argument through PropClass::Eq, so mk_eq_refl
    // receives the actual type α (not the wrong Type 0 fallback). The kernel can
    // verify @Eq.refl.{u} α a directly, eliminating the trustedAy dependency for
    // reflexivity goals.
    //
    // History: sorry → trustedAy (W1-1278, #1144) → kernel proof (#2047).
    reset_all_counters();
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    let goal = make_eq(a_ty, a.clone(), a);
    let mut state = ProofState::new(env, goal);

    let before = sorry_count();
    decide(&mut state).expect("decide should prove a = a");
    let after = sorry_count();
    let sorry_used = after - before;

    assert_eq!(
        sorry_used, 0,
        "REGRESSION: decide used {} sorry terms for a = a (expected 0)",
        sorry_used
    );

    // Proof reconstruction now produces kernel-checkable Eq.refl terms,
    // so trustedAy is no longer needed for reflexivity goals.
    let ay_used = ay_proof_count();
    let arith_used = arith_proof_count();
    assert_eq!(
        arith_used, 0,
        "UNEXPECTED: decide used {} trustedArith terms for a = a (decide should not use arith fallback)",
        arith_used
    );
    assert_eq!(
        ay_used, 0,
        "REGRESSION: decide used {} trustedAy terms for a = a \
         (expected 0 — proof reconstruction now produces kernel-checkable Eq.refl)",
        ay_used
    );
}

#[test]
#[serial]
fn test_decide_sorry_count_on_symmetry() {
    // Goal: b = a from h: a = b — decide proves via SMT, proof reconstruction
    // builds @Eq.symm.{u} α a b h with the correct universe derived from α.
    //
    // PROOF QUALITY (Part of #2047): mk_eq_symm now derives u from sort_level_of_type(α)
    // instead of hardcoding Level::succ(Level::zero()). The reconstructed proof term
    // has the correct structure, but validate_proof_term rejects it because the kernel
    // can't infer the implicit arguments (α, a, b) from the bare FVar proof term.
    // This causes a trustedAy fallback. Fixing this requires either:
    //   (a) Supplying explicit implicit args: @Eq.symm.{u} α a b h, or
    //   (b) Enhancing validate_proof_term to support implicit inference.
    //
    // History: sorry → trustedAy (W1-1278, #1144) — kernel proof blocked on validation.
    reset_all_counters();
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Hypothesis: h : a = b
    let hyp_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let local_decl = LocalDecl {
        fvar: FVarId::new(1),
        name: "h".to_string(),
        ty: hyp_ty,
        value: None,
    };

    // Goal: b = a (needs symmetry)
    let goal = make_eq(a_ty, b, a);
    let mut state = ProofState::with_context(env, goal, vec![local_decl]);

    let before = sorry_count();
    decide(&mut state).expect("decide should prove b = a from h : a = b");
    let sorry_used = sorry_count() - before;
    let ay_used = ay_proof_count();
    let arith_used = arith_proof_count();

    assert_eq!(
        sorry_used, 0,
        "REGRESSION: decide used {} sorry terms for symmetry goal (expected 0)",
        sorry_used
    );
    assert_eq!(
        arith_used, 0,
        "UNEXPECTED: decide used {} trustedArith for symmetry goal",
        arith_used
    );
    // mk_eq_symm now supplies explicit implicit args: @Eq.symm.{u} α a b h
    // The kernel type checker accepts the fully-explicit proof term.
    assert_eq!(
        ay_used, 0,
        "REGRESSION: decide used {} trustedAy for symmetry goal \
         (expected 0 — mk_eq_symm supplies explicit implicit args)",
        ay_used
    );
}

#[test]
#[serial]
fn test_decide_sorry_count_on_transitivity() {
    reset_all_counters();
    let env = setup_env_with_eq();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // h1 : a = b
    let h1_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let h1 = LocalDecl {
        fvar: FVarId::new(1),
        name: "h1".to_string(),
        ty: h1_ty,
        value: None,
    };
    // h2 : b = c
    let h2_ty = make_eq(a_ty.clone(), b, c.clone());
    let h2 = LocalDecl {
        fvar: FVarId::new(2),
        name: "h2".to_string(),
        ty: h2_ty,
        value: None,
    };

    // Goal: a = c (needs transitivity)
    let goal = make_eq(a_ty, a, c);
    let mut state = ProofState::with_context(env, goal, vec![h1, h2]);

    let before = sorry_count();
    decide(&mut state).expect("decide should prove a = c from h1 : a = b, h2 : b = c");
    let sorry_used = sorry_count() - before;
    let ay_used = ay_proof_count();

    assert_eq!(
        sorry_used, 0,
        "REGRESSION: decide used {} sorry terms for transitivity goal (expected 0)",
        sorry_used
    );
    // mk_eq_trans supplies explicit implicit args: @Eq.trans.{u} α a b c h₁ h₂
    assert_eq!(
        ay_used, 0,
        "REGRESSION: decide used {} trustedAy for transitivity goal \
         (expected 0 — mk_eq_trans supplies explicit implicit args)",
        ay_used
    );
}

#[test]
#[serial]
fn test_decide_sorry_count_on_congruence() {
    reset_all_counters();
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let fa = Expr::app(f.clone(), a.clone());
    let fb = Expr::app(f, b.clone());

    // Hypothesis: h : a = b
    let hyp = LocalDecl {
        fvar: FVarId::new(1),
        name: "h".to_string(),
        ty: make_eq(a_ty.clone(), a, b),
        value: None,
    };

    // Goal: f(a) = f(b) (needs congruence)
    let goal = make_eq(a_ty, fa, fb);
    let mut state = ProofState::with_context(env, goal, vec![hyp]);

    let before = sorry_count();
    decide(&mut state).expect("decide should prove f(a) = f(b) from h : a = b");
    let sorry_used = sorry_count() - before;
    let ay_used = ay_proof_count();
    let arith_used = arith_proof_count();

    assert_eq!(
        sorry_used, 0,
        "REGRESSION: decide used {} sorry terms for congruence goal (expected 0)",
        sorry_used
    );
    assert_eq!(
        arith_used, 0,
        "UNEXPECTED: decide used {} trustedArith for congruence goal",
        arith_used
    );
    assert_eq!(
        ay_used, 0,
        "REGRESSION: decide used {} trustedAy for congruence goal \
         (expected 0 — congrArg reconstruction now produces kernel-checkable proofs)",
        ay_used
    );
}

#[test]
#[serial]
fn test_decide_eq_no_sorry_on_inequality() {
    // Goal: Decidable (Eq Nat 5 6) — decide_eq verifies 5 ≠ 6 structurally,
    // then constructs isFalse with a noConfusion-based kernel proof.
    // Part of #302, #2154: eliminated trustedAy for Nat inequality proofs.
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap(); // Provides False for noConfusion proofs
    env.init_nat().unwrap(); // Provides Nat.noConfusion for kernel proofs
    env.init_decidable().unwrap(); // Provides Decidable.isFalse/isTrue for close_goal

    // Build Decidable (Eq Nat 5 6)
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let five = Expr::nat_lit(5);
    let six = Expr::nat_lit(6);
    let eq_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            five,
        ),
        six,
    );
    let decidable_goal = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        eq_expr,
    );
    let mut state = ProofState::new(env, decidable_goal);

    let result = decide_eq(&mut state);
    assert!(result.is_ok(), "decide_eq should solve Decidable (5 = 6)");

    // With init_true_false + init_nat + init_decidable + constructor-form
    // expansion, the noConfusion-based kernel proof succeeds via close_goal.
    // Uses per-state counter (immune to parallel test races on global counter).
    // Part of #302, #2154.
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "REGRESSION: decide_eq used {} trusted axioms (expected 0 — kernel proof should succeed)",
        state.trusted_axiom_count()
    );
}
