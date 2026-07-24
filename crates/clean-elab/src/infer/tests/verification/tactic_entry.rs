// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Regression test for #2201: type mismatch between proof and target.
/// Mirrors verify_tactic_proof's type-mismatch branch (line 86-91).
#[test]
fn test_proof_type_mismatch_detected_by_elab_ctx() {
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .unwrap();

    let ctx = ElabCtx::new(&env);
    let proof = Expr::const_(Name::from_string("p"), vec![]);
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let proof_ty = ctx.infer_type(&proof).expect("p should be well-typed");

    assert!(
        !ctx.is_def_eq(&proof_ty, &target),
        "BUG: P should NOT be def-eq to Q — this is the condition that \
         triggers ProofTypeMismatch in verify_tactic_proof"
    );
}

/// Regression test for #2201: ill-typed proof (undefined constant).
/// Mirrors verify_tactic_proof's Err branch (line 95-101).
#[test]
fn test_ill_typed_proof_detected_by_elab_ctx() {
    let env = Environment::new();
    let ctx = ElabCtx::new(&env);
    let proof = Expr::const_(Name::from_string("nonexistent_const"), vec![]);

    let result = ctx.infer_type(&proof);
    assert!(
        result.is_err(),
        "infer_type should fail for undefined constant — this is the condition \
         that triggers ProofTypeMismatch ill-typed branch in verify_tactic_proof"
    );
}

/// Positive control: proof type matches target.
/// Confirms verify_tactic_proof's Ok path (line 93).
#[test]
fn test_correct_proof_accepted_by_elab_ctx() {
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .unwrap();

    let ctx = ElabCtx::new(&env);
    let proof = Expr::const_(Name::from_string("p"), vec![]);
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let proof_ty = ctx.infer_type(&proof).expect("p should be well-typed");

    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "proof type P should be def-eq to target P — verify_tactic_proof accepts this"
    );
}

/// Regression test for #2212: ProofState lacks elaborator-scope FVars.
///
/// `theorem t (A : Prop) (a : A) : A := by exact a` must elaborate
/// successfully. Before the fix, the ProofState TypeChecker didn't
/// know about parameter FVars (A, a), causing `exact a` to fail with
/// `UnknownFVar(FVarId(1))`.
#[test]
fn test_elab_by_tactic_with_param_fvars() {
    let result = elab_decl("theorem t (A : Prop) (a : A) : A := by exact a");
    assert!(
        result.is_ok(),
        "theorem with params and `by exact a` should succeed — \
         elab_by_tactic must inherit elaborator FVars (#2212), got: {:?}",
        result.err()
    );
}

/// Regression test for #2212: `intro` + `exact` with elaborator FVars.
///
/// Verifies that `close_fvars` correctly handles the offset when the
/// ProofState inherits elaborator locals: tactic-created FVars (from intro)
/// must be closed, while elaborator FVars are preserved.
///
/// With the ProofState → ElabCtx bridge (#2212), `exact h` now resolves
/// `h` to the tactic-introduced hypothesis FVar via ElabCtx name lookup.
#[test]
fn test_elab_by_tactic_intro_with_param_fvars() {
    let result = elab_decl("theorem t (A : Prop) : A → A := by intro h; exact h");
    assert!(
        result.is_ok(),
        "theorem with params and `by intro h; exact h` should succeed — \
         close_fvars_with_base must offset tactic FVars (#2212), got: {:?}",
        result.err()
    );
}

/// Regression test for #2212: nested binders with elab FVar application.
///
/// `theorem t (A B : Prop) (f : A → B) : A → B := by intro h; exact f h`
/// exercises the case where an elab FVar (f) is applied to a tactic FVar (h).
/// After the ProofState → ElabCtx bridge (#2212), `h` resolves to the
/// intro'd hypothesis FVar, so `f h` type-checks correctly.
#[test]
fn test_elab_by_tactic_nested_binder_with_multiple_elab_fvars() {
    let result = elab_decl("theorem t (A B : Prop) (f : A → B) : A → B := by intro h; exact f h");
    assert!(
        result.is_ok(),
        "exact f h should succeed now that tactic locals are visible to \
         the elaborator (#2212), got: {:?}",
        result.err()
    );
}

/// Regression test for #2212: multiple intro with elab FVars.
///
/// `theorem t (A B : Prop) : A → B → A := by intro h1; intro h2; exact h1`
/// exercises close_fvars_with_base with 2 elab FVars and 2 tactic FVars.
/// With the ProofState → ElabCtx bridge (#2212), h1 resolves to the
/// tactic-introduced hypothesis FVar.
#[test]
fn test_elab_by_tactic_multiple_intro_with_elab_fvars() {
    let result = elab_decl("theorem t (A B : Prop) : A → B → A := by intro h1; intro h2; exact h1");
    assert!(
        result.is_ok(),
        "theorem with 2 elab params and double intro should succeed — \
         close_fvars_with_base must correctly index multiple tactic FVars (#2212), \
         got: {:?}",
        result.err()
    );
}
