// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Regression test for #2477: `ring_nf` must preserve the proof chain through
/// `elab_by_tactic` instead of completing with no proof term produced.
///
/// This exercises `Nat.add Nat.zero Nat.zero = Nat.zero` which `ring_nf` now
/// closes directly via `Eq.refl` (def-eq base case in ring axiom prover, #2442).
#[test]
fn test_elab_by_tactic_ring_nf_preserves_proof_chain() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let lhs = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            zero.clone(),
        ),
        zero.clone(),
    );
    let target = eq_target(nat, lhs, zero.clone());

    assert_tactic_preserves_target(
        &env,
        target,
        "by ring_nf",
        "ring_nf should elaborate successfully through elab_by_tactic",
        "ring_nf proof should be closed",
        "ring_nf proof type should match the original target after post-hoc verification",
    );
}

/// Regression test for #2477: `dsimp` must preserve the proof chain through
/// `elab_by_tactic` when performing beta reduction on the goal target.
///
/// Target: `(fun x : Nat => x) Nat.zero = Nat.zero`
/// Tactic: `by dsimp; rfl`
/// dsimp beta-reduces the LHS to `Nat.zero`, then rfl closes.
/// Exercises the `replace_target_def_eq` path in the full elab pipeline.
#[test]
fn test_elab_by_tactic_dsimp_beta_preserves_proof_chain() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let id_app = Expr::app(
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
        zero.clone(),
    );
    let target = eq_target(nat, id_app, zero.clone());

    assert_tactic_preserves_target(
        &env,
        target,
        "by dsimp; rfl",
        "dsimp followed by rfl should elaborate successfully through elab_by_tactic",
        "dsimp proof should be closed",
        "dsimp proof type should match the original target after post-hoc verification",
    );
}

/// Regression test for #2477: `dsimp at *` must preserve the proof chain when
/// it beta-reduces both the goal target and hypothesis types in one call.
///
/// The theorem starts with:
/// - hypothesis: `(fun X : Prop => X) A`
/// - target: `(fun X : Prop => X) A`
///
/// `dsimp at *` reduces both to `A`, then `exact h` closes the goal. The final
/// theorem proof must still typecheck against the original unreduced theorem
/// type after `closed_proof()` abstracts the simplified local context.
#[test]
fn test_elab_by_tactic_dsimp_at_all_preserves_proof_chain() {
    let result = elab_decl(
        "theorem t (A : Prop) (h : (fun X : Prop => X) A) : (fun X : Prop => X) A := by \
         dsimp at *; exact h",
    )
    .expect("dsimp at * followed by exact h should elaborate successfully");

    let ElabResult::Theorem { ty, proof, .. } = result else {
        panic!("expected theorem elaboration result");
    };

    assert!(
        !proof.has_fvar_quick(),
        "dsimp at * proof should be closed, got: {proof:?}"
    );

    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let proof_ty = tc
        .infer_type(&proof)
        .expect("elaborated dsimp at * proof should have an inferable type");
    assert!(
        tc.is_def_eq(&proof_ty, &ty),
        "dsimp at * proof type should remain definitionally equal to the original theorem type"
    );
}
