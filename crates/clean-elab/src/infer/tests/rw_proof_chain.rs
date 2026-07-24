// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end proof-chain regression tests for `rw` tactic through `elab_by_tactic`.
//!
//! Part of #2477: validates that standalone `rw` properly constructs `Eq.subst`
//! proof terms that maintain the proof chain through the elaboration pipeline.
//! Complements the simp/ring_nf/conv e2e tests in verification.rs.

use super::*;

/// Build env with x, y : Nat and target `(h : x = y) → Nat.add x 0 = Nat.add y 0`.
fn setup_rw_hypothesis_env() -> (Environment, Expr) {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    for name in ["x", "y"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }

    let eq_u1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

    // Eq Nat x y
    let eq_xy = Expr::app(
        Expr::app(Expr::app(eq_u1.clone(), nat.clone()), x.clone()),
        y.clone(),
    );

    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let add_x_zero = Expr::app(Expr::app(add.clone(), x), zero.clone());
    let add_y_zero = Expr::app(Expr::app(add, y), zero);

    // Eq Nat (Nat.add x 0) (Nat.add y 0)
    let eq_add = Expr::app(Expr::app(Expr::app(eq_u1, nat), add_x_zero), add_y_zero);

    // (h : x = y) → Nat.add x 0 = Nat.add y 0
    let target = Expr::arrow(eq_xy, eq_add);
    (env, target)
}

/// Regression test for #2477: standalone `rw` must preserve the proof chain
/// through `elab_by_tactic` when rewriting the goal with a local hypothesis.
///
/// `intro h` introduces `h : x = y` into the local context.
/// `rw [h]` rewrites x → y in the goal via `Eq.subst`, producing
/// `Nat.add y 0 = Nat.add y 0`, then auto-closes with `rfl`.
/// Exercises the `rewrite` function's `Eq.subst` proof construction
/// (equality/rewrite.rs) through the full elaboration pipeline.
#[test]
fn test_elab_by_tactic_rw_preserves_proof_chain() {
    let (env, target) = setup_rw_hypothesis_env();

    let surface = parse_expr("by intro h; rw [h]").expect("by-tactic expression should parse");
    let SurfaceExpr::ByTactic(_, tactics) = surface else {
        panic!("expected a ByTactic surface expression");
    };

    let mut ctx = ElabCtx::new(&env);
    ctx.current_expected_type = Some(target.clone());
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("rw with local hypothesis should elaborate successfully through elab_by_tactic");

    assert!(
        !proof.has_fvar_quick(),
        "rw proof should be closed (no residual FVars), got: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("elab_by_tactic output should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "rw proof type should match the original target after post-hoc verification"
    );
}

/// Regression test for #2529: `rw [h]` must work when `h` is a theorem
/// parameter (elaborator-scope local) rather than a tactic-introduced
/// hypothesis.
///
/// Before the bridge fix, `elab_by_tactic` did not propagate elab_locals
/// to the initial goal's `local_ctx`, so `rw` could not find `h` and
/// failed with `HypothesisNotFound`.
///
/// This test sets up `x, y : Nat` and `h : x = y` as elaborator locals
/// (simulating theorem parameters), with target `Nat.add x 0 = Nat.add y 0`.
/// `rw [h]` rewrites x → y and auto-closes with rfl.
#[test]
fn test_elab_by_tactic_rw_theorem_param_hypothesis() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let mut ctx = ElabCtx::new(&env);
    let x_fvar = ctx.push_local("x".to_string(), nat.clone());
    let y_fvar = ctx.push_local("y".to_string(), nat.clone());
    let x_expr = Expr::fvar(x_fvar);
    let y_expr = Expr::fvar(y_fvar);

    // h : Eq Nat x y
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let eq_xy = Expr::app(
        Expr::app(Expr::app(eq_const.clone(), nat.clone()), x_expr.clone()),
        y_expr.clone(),
    );
    ctx.push_local("h".to_string(), eq_xy);

    // Target: Eq Nat (Nat.add x 0) (Nat.add y 0)
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let add_x_zero = Expr::app(Expr::app(add.clone(), x_expr), zero.clone());
    let add_y_zero = Expr::app(Expr::app(add, y_expr), zero);
    let target = Expr::app(Expr::app(Expr::app(eq_const, nat), add_x_zero), add_y_zero);

    ctx.current_expected_type = Some(target.clone());

    let surface = parse_expr("by rw [h]").expect("by-tactic expression should parse");
    let SurfaceExpr::ByTactic(_, tactics) = surface else {
        panic!("expected a ByTactic surface expression");
    };

    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("rw [h] with theorem-parameter hypothesis should succeed (#2529)");

    // Proof contains elab_locals FVars (x, y, h) — closed by the enclosing
    // elaborator, not by ProofState.closed_proof. Verify type matches.
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("elab_by_tactic output should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "rw proof type should match the original target"
    );
}

// ===========================================================================
// `rw [<global lemma>] at <hyp>` — env-lemma resolution at a hypothesis (#2624)
// ===========================================================================
//
// Before this fix, the `rw [lemma] at h` path (`rewrite_at`) resolved the
// rewrite *rule* against the LOCAL CONTEXT only — `Nat.add_zero` was looked up
// as if it were a hypothesis name and failed with
// `HypothesisNotFound("Nat.add_zero")`. The at-GOAL path (`rewrite`) already
// fell back to the environment via `resolve_env_rewrite_equation`. These tests
// pin the env-lemma-at-hyp behavior to match the at-goal path and real Lean 4.

/// Build an env with `x : Nat` and a global lemma
/// `Nat.add_zero : ∀ (n : Nat), n + 0 = n` (registered as an axiom — the
/// kernel's `init_nat` does not ship the named simp lemmas), plus a target
/// `(h : Nat.add x 0 = x) → (x = x)`. The proof introduces `h`, rewrites it
/// with the GLOBAL lemma, then closes by `exact h`.
fn setup_env_add_zero_lemma() -> (Environment, Expr) {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    let eq_u1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);

    // Nat.add_zero : ∀ (n : Nat), Nat.add n Nat.zero = n
    // Body (under the binder, bvar #0): Eq Nat (Nat.add #0 Nat.zero) #0
    let bvar0 = Expr::bvar(0);
    let add_bvar_zero = Expr::app(Expr::app(add.clone(), bvar0.clone()), zero.clone());
    let body = Expr::app(
        Expr::app(Expr::app(eq_u1.clone(), nat.clone()), add_bvar_zero),
        bvar0,
    );
    let add_zero_ty = Expr::pi(BinderInfo::Default, nat.clone(), body);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.add_zero"),
        level_params: vec![],
        type_: add_zero_ty,
    })
    .unwrap();

    // h : Eq Nat (Nat.add x Nat.zero) x
    let add_x_zero = Expr::app(Expr::app(add, x.clone()), zero);
    let h_ty = Expr::app(
        Expr::app(Expr::app(eq_u1.clone(), nat.clone()), add_x_zero),
        x.clone(),
    );

    // Goal: Eq Nat x x   (after `rw [Nat.add_zero] at h`, h becomes `x = x`)
    let goal = Expr::app(Expr::app(Expr::app(eq_u1, nat), x.clone()), x);

    // Target: (h : Nat.add x 0 = x) → (x = x)
    let target = Expr::arrow(h_ty, goal);
    (env, target)
}

/// Regression for #2624: `rw [Nat.add_zero] at h` must resolve the GLOBAL
/// lemma `Nat.add_zero` (not look it up as a local hypothesis) and rewrite the
/// hypothesis `h : Nat.add x 0 = x` into `x = x`, then `exact h` closes the
/// `x = x` goal. Mirrors the at-goal env-lemma path.
#[test]
fn test_elab_by_tactic_rw_global_lemma_at_hyp() {
    let (env, target) = setup_env_add_zero_lemma();

    let surface = parse_expr("by intro h; rw [Nat.add_zero] at h; exact h")
        .expect("by-tactic expression should parse");
    let SurfaceExpr::ByTactic(_, tactics) = surface else {
        panic!("expected a ByTactic surface expression");
    };

    let mut ctx = ElabCtx::new(&env);
    ctx.current_expected_type = Some(target.clone());
    let proof = ctx.elab_by_tactic(&tactics).expect(
        "rw [Nat.add_zero] at h should resolve the GLOBAL lemma and rewrite the hypothesis",
    );

    assert!(
        !proof.has_fvar_quick(),
        "rw-at-hyp proof should be closed (no residual FVars), got: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("elab_by_tactic output should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "rw-at-hyp proof type should match the original target"
    );
}

/// Negative: `rw [Nat.add_zero] at h` where `h`'s type contains no `_ + 0`
/// occurrence must fail with `RewriteNoMatch` (never panic, never over-accept).
#[test]
fn test_elab_by_tactic_rw_global_lemma_at_hyp_no_match_errors() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    // Nat.add_zero : ∀ (n : Nat), Nat.add n Nat.zero = n
    let eq_u1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let bvar0 = Expr::bvar(0);
    let add_bvar_zero = Expr::app(Expr::app(add.clone(), bvar0.clone()), zero.clone());
    let body = Expr::app(
        Expr::app(Expr::app(eq_u1.clone(), nat.clone()), add_bvar_zero),
        bvar0,
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.add_zero"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat.clone(), body),
    })
    .unwrap();

    // h : Eq Nat x x  (no `_ + 0` subterm anywhere)
    let h_ty = Expr::app(
        Expr::app(Expr::app(eq_u1.clone(), nat.clone()), x.clone()),
        x.clone(),
    );
    // Goal: Eq Nat x x
    let goal = Expr::app(Expr::app(Expr::app(eq_u1, nat), x.clone()), x);
    let target = Expr::arrow(h_ty, goal);

    let surface = parse_expr("by intro h; rw [Nat.add_zero] at h; exact h")
        .expect("by-tactic expression should parse");
    let SurfaceExpr::ByTactic(_, tactics) = surface else {
        panic!("expected a ByTactic surface expression");
    };

    let mut ctx = ElabCtx::new(&env);
    ctx.current_expected_type = Some(target);
    let result = ctx.elab_by_tactic(&tactics);
    let err = result.expect_err("rw of a non-matching lemma at a hyp must error, not succeed");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("RewriteNoMatch"),
        "expected RewriteNoMatch, got: {msg}"
    );
}

/// Decisive multi-step: `rw [Nat.add_zero] at h2; rw [h] at h2` — a GLOBAL
/// lemma rewrite at a hyp followed by a LOCAL hypothesis rewrite at the same
/// hyp, then `exact h2`. Exercises both arms of the resolution fork in
/// `rewrite_at` in a single proof.
#[test]
fn test_elab_by_tactic_rw_lemma_then_hyp_at_hyp_chain() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let five = Expr::const_(Name::from_string("five"), vec![]);

    for name in ["a", "b", "five"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }

    let eq_u1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);

    // Nat.add_zero : ∀ (n : Nat), Nat.add n Nat.zero = n
    let bvar0 = Expr::bvar(0);
    let add_bvar_zero = Expr::app(Expr::app(add.clone(), bvar0.clone()), zero.clone());
    let body = Expr::app(
        Expr::app(Expr::app(eq_u1.clone(), nat.clone()), add_bvar_zero),
        bvar0,
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.add_zero"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat.clone(), body),
    })
    .unwrap();

    let mk_eq =
        |l: Expr, r: Expr| Expr::app(Expr::app(Expr::app(eq_u1.clone(), nat.clone()), l), r);

    // h  : a = b
    let h_ty = mk_eq(a.clone(), b.clone());
    // h2 : Nat.add a 0 = five
    let add_a_zero = Expr::app(Expr::app(add, a.clone()), zero);
    let h2_ty = mk_eq(add_a_zero, five.clone());
    // Goal: b = five
    let goal = mk_eq(b, five);

    // Target: (h : a = b) → (h2 : a + 0 = five) → (b = five)
    let target = Expr::arrow(h_ty, Expr::arrow(h2_ty, goal));

    let surface =
        parse_expr("by intro h; intro h2; rw [Nat.add_zero] at h2; rw [h] at h2; exact h2")
            .expect("by-tactic expression should parse");
    let SurfaceExpr::ByTactic(_, tactics) = surface else {
        panic!("expected a ByTactic surface expression");
    };

    let mut ctx = ElabCtx::new(&env);
    ctx.current_expected_type = Some(target.clone());
    let proof = ctx.elab_by_tactic(&tactics).expect(
        "lemma-at-hyp then hyp-at-hyp chain should elaborate (both resolution arms of rewrite_at)",
    );

    assert!(
        !proof.has_fvar_quick(),
        "chained rw-at-hyp proof should be closed, got: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("elab_by_tactic output should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "chained rw-at-hyp proof type should match the original target"
    );
}
