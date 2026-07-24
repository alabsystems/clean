// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for #2184 -- tactic proof term soundness.
//!
//! These tests verify that tactic proof terms are well-typed and pass
//! kernel type inference. Isolated from other tactic-family tests per #2947.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;

// =========================================================================
// Regression tests for #2184 — tactic proof term soundness
// =========================================================================

/// Regression test for #2184 F3: refine with placeholders must assign the
/// original goal's metavariable. Currently, `refine` pops the goal and creates
/// subgoals but never assigns the refined term to the original metavariable,
/// leaving it orphaned.
#[test]
fn test_refine_with_holes_assigns_original_meta() {
    let env = setup_env();
    // Goal: prove B
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, b);

    // Get the original goal's meta_id before refine
    let original_meta = state.current_goal().unwrap().meta_id;

    // Create a term with a placeholder: `f _` where f : A → B
    // This should create one subgoal for the placeholder
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let placeholder = Expr::const_(Name::from_string("_"), vec![]);
    let refined_term = Expr::app(f, placeholder);

    // refine should succeed
    refine(&mut state, refined_term).expect("refine with placeholder should succeed");

    // The original goal's metavariable must be assigned to the refined term
    // (with placeholders replaced by new metavariables)
    assert!(
        state.metas.is_assigned(original_meta),
        "BUG #2184 F3: refine does not assign the original goal's metavariable — \
         the proof term is orphaned and the original goal will never be resolved \
         even if all subgoals are closed"
    );
}

/// Regression test for #2184 F2: abs_cases constructs an ill-typed
/// Classical.em proof term using Expr::type_() as a placeholder.
/// The proof should be kernel-checkable.
///
/// Part of #2154: uses enriched env since abs_cases now uses checked close_goal.
#[test]
fn test_abs_cases_proof_term_is_well_typed() {
    let env = setup_env_with_int_ord();
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let ctx = vec![LocalDecl {
        fvar: FVarId::new(0),
        name: "x".to_string(),
        ty: Expr::const_(Name::from_string("Int"), vec![]),
        value: None,
    }];
    let mut state = ProofState::with_context(env, target, ctx);

    // Get original goal meta
    let original_meta = state.current_goal().unwrap().meta_id;

    // abs_cases should succeed on an Int variable
    if abs_cases(&mut state, "x").is_ok() {
        // If the original meta was assigned, check the proof term doesn't
        // contain Expr::type_() as a bare argument (that's the placeholder bug)
        if let Some(meta) = state.metas.get(original_meta) {
            if let Some(ref assignment) = meta.assignment {
                let has_type_placeholder = contains_type_placeholder(assignment);
                assert!(
                    !has_type_placeholder,
                    "BUG #2184 F2: abs_cases proof term contains Expr::type_() placeholder — \
                     this produces an ill-typed Classical.em application"
                );
            }
        }
    }
}

/// Verify that by_cases produces a proof term that passes kernel type inference.
///
/// Or.rec has 0 universe params (Prop-valued inductive with elim-only-at-zero).
/// The tactic must pass `vec![]` (0 args), not `vec![Level::zero()]` (1 arg).
/// Fixed in #2216.
#[test]
fn test_by_cases_proof_passes_type_inference() {
    let mut env = Environment::new();
    env.init_classical().unwrap();

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

    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let prop = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target.clone());

    let original_meta = state.current_goal().unwrap().meta_id;
    by_cases(&mut state, "h", prop).expect("by_cases should succeed");

    let meta = state.metas.get(original_meta).expect("meta should exist");
    let proof = meta.assignment.as_ref().expect("meta should be assigned");

    let goal = Goal {
        meta_id: original_meta,
        target,
        local_ctx: vec![],
        tag: None,
    };

    // After #2216 fix: Or.rec gets vec![] (0 universe args), matching its 0 params.
    let result = state.infer_type(&goal, proof);
    let inferred_ty = result.expect("by_cases proof should pass type inference after #2216 fix");

    // Verify the inferred type matches the goal target (Q : Prop).
    // Without this, a proof that type-checks but proves the wrong proposition
    // would pass the test. Part of P1-783 reflection finding.
    assert!(
        state.is_def_eq(&goal, &inferred_ty, &goal.target),
        "by_cases proof inferred type should be def-eq to goal target Q, got: {:?}",
        inferred_ty
    );
}

/// Regression test for #2184: abs_cases and wlog both reference `Or.elim` which is
/// NOT defined in the kernel environment. The inductive machinery generates `Or.rec`,
/// `Or.casesOn`, `Or.recOn` — but NOT `Or.elim`. The correct constant is `Or.rec`
/// (as used by `by_cases` in existential.rs).
///
/// This test confirms the bug: Or.elim is absent even after init_classical().
#[test]
fn test_or_elim_not_in_environment() {
    let mut env = Environment::new();
    env.init_classical().unwrap();

    // Or.rec IS generated by the inductive machinery
    assert!(
        env.get_const(&Name::from_string("Or.rec")).is_some(),
        "Or.rec should be generated by init_classical"
    );

    // Or.elim is NOT defined anywhere in clean
    assert!(
        env.get_const(&Name::from_string("Or.elim")).is_none(),
        "BUG: Or.elim should NOT exist — abs_cases and wlog reference a nonexistent constant. \
         The correct constant is Or.rec (see by_cases in existential.rs)"
    );

    // Also confirm the other generated constants exist
    env.get_const(&Name::from_string("Or"))
        .expect("Or should be declared in classical env");
    env.get_const(&Name::from_string("Or.inl"))
        .expect("Or.inl should be declared");
    env.get_const(&Name::from_string("Or.inr"))
        .expect("Or.inr should be declared");
    env.get_const(&Name::from_string("Classical.em"))
        .expect("Classical.em should be declared");
}

/// After #2154 Wave 7: abs_cases proof now passes type inference.
/// Previously regression test for #2184 (Or.elim UnknownConst).
///
/// Fixes applied: Or.elim → Or.rec (Wave 5-6), Not P → Pi(P, False) (Wave 7),
/// enriched env with init_int_ord + init_ge (Wave 7).
#[test]
fn test_abs_cases_proof_passes_type_inference() {
    let env = setup_env_with_int_ord();

    let target = Expr::const_(Name::from_string("B"), vec![]);
    let ctx = vec![LocalDecl {
        fvar: FVarId::new(100),
        name: "x".to_string(),
        ty: Expr::const_(Name::from_string("Int"), vec![]),
        value: None,
    }];
    let mut state = ProofState::with_context(env, target, ctx);

    let original_meta = state.current_goal().unwrap().meta_id;

    // abs_cases now uses checked close_goal (Or.rec proof + type-checking)
    abs_cases(&mut state, "x").expect("abs_cases should succeed with checked close_goal");

    // The original meta should be assigned with an Or.rec proof
    let meta = state.metas.get(original_meta).expect("meta should exist");
    let proof = meta.assignment.as_ref().expect("meta should be assigned");

    let goal = Goal {
        meta_id: original_meta,
        target: Expr::const_(Name::from_string("B"), vec![]),
        local_ctx: vec![LocalDecl {
            fvar: FVarId::new(100),
            name: "x".to_string(),
            ty: Expr::const_(Name::from_string("Int"), vec![]),
            value: None,
        }],
        tag: None,
    };

    // Type inference should PASS now with Or.rec + Pi(P, False) + enriched env
    let result = state.infer_type(&goal, proof);
    let _ = result.expect("abs_cases proof should pass type inference after #2154 Wave 7 fixes");
}

/// After Or.elim → Or.rec fix (#2154 Wave 5): wlog proof now passes type inference.
/// Previously regression test for #2184 (Or.elim UnknownConst).
#[test]
fn test_wlog_proof_passes_type_inference() {
    let mut env = Environment::new();
    env.init_classical().unwrap();

    // Add propositions
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

    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let assumption = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target.clone());

    let original_meta = state.current_goal().unwrap().meta_id;

    // wlog should succeed (now uses checked close_goal with Or.rec)
    wlog(&mut state, "h", assumption).expect("wlog should succeed");

    // The original meta should be assigned with an Or.rec proof
    let meta = state.metas.get(original_meta).expect("meta should exist");
    let proof = meta.assignment.as_ref().expect("meta should be assigned");

    let goal = Goal {
        meta_id: original_meta,
        target,
        local_ctx: vec![],
        tag: None,
    };

    // Type inference should PASS now that we use Or.rec (0 universe params, Prop-valued)
    let result = state.infer_type(&goal, proof);
    let _ = result.expect("wlog proof should pass type inference after Or.elim → Or.rec fix");
}

/// After #2154 Wave 7: abs_cases negation type now uses Pi(P, False) matching
/// Classical.em's structural output. Previously regression test for #2184.
#[test]
fn test_abs_cases_negation_type_is_pi() {
    let env = setup_env_with_int_ord();

    let target = Expr::const_(Name::from_string("B"), vec![]);
    let ctx = vec![LocalDecl {
        fvar: FVarId::new(100),
        name: "x".to_string(),
        ty: Expr::const_(Name::from_string("Int"), vec![]),
        value: None,
    }];
    let mut state = ProofState::with_context(env, target, ctx);
    abs_cases(&mut state, "x").expect("abs_cases should succeed");

    assert!(
        state.goals.len() >= 2,
        "abs_cases should produce at least 2 goals (nonneg and neg), got {}",
        state.goals.len()
    );

    // After fix: neg_hyp.ty is Pi(ge_zero, False) matching Classical.em's output
    let neg_goal = &state.goals[1];
    let neg_hyp = neg_goal
        .local_ctx
        .iter()
        .find(|d| d.name == "h_neg")
        .expect("negative case should have h_neg hypothesis");

    // Negation should now be Pi(ge_zero, False), not App(Not, ge_zero)
    let is_pi = matches!(neg_hyp.ty.kind(), ExprKind::Pi(..));
    assert!(
        is_pi,
        "abs_cases negation should use Pi(P, False) form after #2154 fix, got: {:?}",
        neg_hyp.ty
    );
}

/// Helper: recursively check if an expression contains a bare `Type` (Sort(Succ(Zero)))
/// used as an argument in an application — a sign of a placeholder bug.
fn contains_type_placeholder(e: &Expr) -> bool {
    use clean_kernel::level::Level;
    match e.kind() {
        ExprKind::App(f, arg) => {
            // Check if the argument is Type (Sort(Succ(Zero)))
            let arg_is_type = matches!(
                arg.kind(),
                ExprKind::Sort(Level::Succ(inner)) if matches!(&**inner, Level::Zero)
            );
            arg_is_type || contains_type_placeholder(f) || contains_type_placeholder(arg)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_type_placeholder(ty) || contains_type_placeholder(body)
        }
        ExprKind::Let(_, ty, val, body, ..) => {
            contains_type_placeholder(ty)
                || contains_type_placeholder(val)
                || contains_type_placeholder(body)
        }
        _ => false,
    }
}
