// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// ==========================================================================
// rewrite_at proof term validity (#1857)
// ==========================================================================
// These tests verify that rewrite_at constructs proper Eq.subst proof terms
// instead of silently modifying hypothesis types in-place.

/// Helper: set up state for rewrite_at proof-term tests.
/// Returns (state, initial_meta_id) with h_eq : x = y and h_target : target_ty.
fn setup_rewrite_at_state(target_ty: Expr) -> (ProofState, crate::unify::MetaId) {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let target = make_p(x.clone());
    let h_eq_ty = make_eq_n(x, y);
    let state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(0),
                name: clean_parser::SurfaceName::generated_path("h_eq"),
                ty: h_eq_ty,
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: clean_parser::SurfaceName::generated_path("h_target"),
                ty: target_ty,
                value: None,
            },
        ],
    );
    let meta_id = state.current_goal().unwrap().meta_id;
    (state, meta_id)
}

#[test]
fn test_rewrite_at_closes_goal_with_let_binding() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let (mut state, initial_meta_id) = setup_rewrite_at_state(make_p(x));

    let result = rewrite_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("h_eq"),
        &clean_parser::SurfaceName::generated_path("h_target"),
        false,
    );
    assert!(result.is_ok(), "rewrite_at should succeed: {result:?}");

    // The old goal meta should be assigned (closed with a proof term)
    assert!(
        state.metas().is_assigned(initial_meta_id),
        "rewrite_at must close the old goal with a proof term"
    );

    // The proof term should be a Let expression (not a raw metavariable)
    let proof = state.metas().get_assignment(initial_meta_id).unwrap();
    assert!(
        matches!(proof.kind(), ExprKind::Let(..)),
        "proof term should be a let-binding, got: {:?}",
        proof.kind()
    );
}

#[test]
fn test_rewrite_at_let_binding_uses_eq_subst() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let (mut state, initial_meta_id) = setup_rewrite_at_state(make_p(x));

    rewrite_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("h_eq"),
        &clean_parser::SurfaceName::generated_path("h_target"),
        false,
    )
    .unwrap();

    let proof = state.metas().get_assignment(initial_meta_id).unwrap();
    if let ExprKind::Let(_name, ty, val, _body, _) = proof.kind() {
        // Type should be P(y) (the rewritten hypothesis type)
        assert_eq!(ty.as_ref().clone(), make_p(y), "let type should be P(y)");
        // Value head should be Eq.subst
        let val_head = val.get_app_fn();
        match val_head.kind() {
            ExprKind::Const(name, _) => assert_eq!(
                name,
                &Name::from_string("Eq.subst"),
                "cast value should use Eq.subst"
            ),
            _ => panic!("cast head should be Eq.subst, got: {:?}", val_head.kind()),
        }
    } else {
        panic!("proof should be Let");
    }
}

#[test]
fn test_rewrite_at_fresh_fvar_and_new_goal() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let target = make_p(x.clone());
    let (mut state, _) = setup_rewrite_at_state(make_p(x));

    rewrite_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("h_eq"),
        &clean_parser::SurfaceName::generated_path("h_target"),
        false,
    )
    .unwrap();

    let new_goal = state.current_goal().unwrap();
    let h = new_goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h_target"))
        .unwrap();
    assert_ne!(h.fvar, FVarId::new(1), "must use fresh fvar");
    assert_eq!(h.ty, make_p(y), "hypothesis should be P(y)");
    assert_eq!(new_goal.target, target, "goal target unchanged");
    assert!(!state.is_complete(), "new goal still needs proving");
}

#[test]
fn test_rewrite_at_reverse_uses_eq_symm() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let (mut state, initial_meta_id) = setup_rewrite_at_state(make_p(y.clone()));

    rewrite_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("h_eq"),
        &clean_parser::SurfaceName::generated_path("h_target"),
        true,
    )
    .unwrap();

    let proof = state.metas().get_assignment(initial_meta_id).unwrap();
    assert!(
        matches!(proof.kind(), ExprKind::Let(..)),
        "should be let-binding"
    );

    if let ExprKind::Let(_, _ty, val, _, _) = proof.kind() {
        let val_args = val.get_app_args();
        // The second-to-last arg to Eq.subst is eq_proof, which should use Eq.symm
        if val_args.len() >= 2 {
            let eq_proof_arg = &val_args[val_args.len() - 2];
            let head = eq_proof_arg.get_app_fn();
            if let ExprKind::Const(name, _) = head.kind() {
                assert_eq!(name, &Name::from_string("Eq.symm"), "should use Eq.symm");
            }
        }
    }

    let h = state
        .current_goal()
        .unwrap()
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h_target"))
        .unwrap();
    assert_eq!(h.ty, make_p(x), "hypothesis should be P(x)");
}

#[test]
fn test_rewrite_at_old_fvar_not_in_new_context() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let old_fvar = FVarId::new(1);
    let (mut state, _) = setup_rewrite_at_state(make_p(x));

    rewrite_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("h_eq"),
        &clean_parser::SurfaceName::generated_path("h_target"),
        false,
    )
    .unwrap();

    let goal = state.current_goal().unwrap();
    let has_old = goal.local_ctx.iter().any(|d| {
        d.fvar == old_fvar && d.name == clean_parser::SurfaceName::generated_path("h_target")
    });
    assert!(!has_old, "old fvar must not appear in new context");
    let h = goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h_target"))
        .unwrap();
    assert_ne!(h.fvar, old_fvar, "must use fresh fvar");
    assert_eq!(h.ty, make_p(y), "should have rewritten type");
}

// ==========================================================================
// simp_at proof term validity (#1857 AC2)
// ==========================================================================
// Verifies that simp_at produces Eq.subst proof terms (not sorry) when a
// top-level simp lemma matches the hypothesis.

/// Build state with h : n+0 = n for simp_at tests (#1857 AC2).
fn setup_simp_at_nat_arith_state() -> (ProofState, crate::unify::MetaId) {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    env.init_nat_arith_lemmas().unwrap();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: nat_ty.clone(),
    })
    .unwrap();

    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let lhs = Expr::app(Expr::app(nat_add, n.clone()), nat_zero);
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty.clone(),
            ),
            lhs,
        ),
        n.clone(),
    );

    let target = Expr::const_(Name::from_string("A"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
    })
    .unwrap();

    let state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: eq_ty,
            value: None,
        }],
    );
    let meta_id = state.current_goal().unwrap().meta_id;
    (state, meta_id)
}

#[test]
fn test_simp_at_uses_eq_subst_for_top_level_lemma() {
    let (mut state, initial_meta_id) = setup_simp_at_nat_arith_state();

    let result = simp_at(&mut state, &clean_parser::SurfaceName::generated_path("h"));
    assert!(result.is_ok(), "simp_at should succeed: {result:?}");

    assert!(
        state.metas().is_assigned(initial_meta_id),
        "old goal must be closed"
    );
    let proof = state.metas().get_assignment(initial_meta_id).unwrap();
    assert!(
        matches!(proof.kind(), ExprKind::Let(..)),
        "proof should be a let-binding, got: {:?}",
        proof.kind()
    );

    if let ExprKind::Let(_name, _ty, val, _body, _) = proof.kind() {
        let val_head = val.get_app_fn();
        match val_head.kind() {
            ExprKind::Const(name, _) => {
                assert_eq!(
                    name,
                    &Name::from_string("Eq.subst"),
                    "simp_at cast should use Eq.subst, not sorry. Got: {name}"
                );
            }
            _ => panic!(
                "simp_at cast head should be Eq.subst, got: {:?}",
                val_head.kind()
            ),
        }
    } else {
        panic!("proof should be Let");
    }

    let goal = state.current_goal().unwrap();
    let h = goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h"))
        .unwrap();
    assert_ne!(h.fvar, FVarId::new(0), "must use fresh fvar");
}

#[test]
fn test_simp_at_definitional_uses_identity_cast() {
    // simp_at with beta reduction only (definitional) should use
    // Expr::fvar (identity cast, no sorry) because the types are
    // definitionally equal.
    let mut env = setup_env();
    env.init_eq().unwrap();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // h : (λ x : A => x) a = a  (beta-reducible to a = a)
    let identity = Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0));
    let lhs = Expr::app(identity, a.clone());
    let h_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty.clone(),
            ),
            lhs,
        ),
        a,
    );

    let target = a_ty;
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: h_ty,
            value: None,
        }],
    );
    let initial_meta_id = state.current_goal().unwrap().meta_id;

    let result = simp_at(&mut state, &clean_parser::SurfaceName::generated_path("h"));
    assert!(result.is_ok(), "simp_at should succeed: {result:?}");

    // Check that the proof uses identity cast (fvar, not sorry)
    let proof = state.metas().get_assignment(initial_meta_id).unwrap();
    if let ExprKind::Let(_name, _ty, val, _body, _) = proof.kind() {
        // For definitional equality, the cast should be Expr::fvar(old_hyp_fvar)
        assert!(
            matches!(val.kind(), ExprKind::FVar(_)),
            "definitional simp_at should use identity cast (fvar), not sorry. Got: {:?}",
            val.kind()
        );
    }
}

// =============================================================================
// simp_at congruence failure returns error, not sorry (#2185)
// =============================================================================

/// Regression test for #2185: simp_at must return an error when the congruence
/// builder fails — not silently insert sorry.
///
/// With beta=false, simp_expr preserves Let structure (no zeta-reduction).
/// The Let case always returns proof: None (no congruence lemma for
/// let-expressions). When a simp lemma rewrites inside the let-value, the
/// result is not definitionally equal to the original, triggering the error.
#[test]
fn test_simp_at_congruence_failure_returns_error() {
    use crate::tactic::simp::{simp_at_with_config, SimpConfig};
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env();
    env.init_eq().unwrap();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: a_ty.clone(),
    })
    .unwrap();

    // Simp lemma: a_eq_b : Eq A a b (rewrites a → b)
    let eq = |ty: Expr, l: Expr, r: Expr| {
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        Expr::app(Expr::app(Expr::app(eq_c, ty), l), r)
    };
    let b = Expr::const_(Name::from_string("b"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a_eq_b"),
        level_params: vec![],
        type_: eq(a_ty.clone(), a.clone(), b),
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("a_eq_b"), SimpPriority::Default);

    // h : let x : A = a in Eq A x x
    // With beta=false, the Let is preserved. simp rewrites let-value a → b,
    // producing (let x : A = b in Eq A x x). Let congruence builder returns
    // proof: None; types not def-eq → error.
    let h_ty = Expr::let_named(
        Name::anon(),
        a_ty.clone(),
        a,
        eq(a_ty.clone(), Expr::bvar(0), Expr::bvar(0)),
        false,
    );
    let mut state = ProofState::with_context(
        env,
        a_ty,
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: h_ty,
            value: None,
        }],
    );

    let config = SimpConfig {
        beta: false,
        eta: false,
        ..SimpConfig::new()
    };
    let result = simp_at_with_config(
        &mut state,
        &clean_parser::SurfaceName::generated_path("h"),
        config,
    );
    assert!(
        result.is_err(),
        "simp_at should error on congruence failure, not silently insert sorry"
    );
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("congruence proof construction failed"),
        "error should mention congruence failure, got: {err_msg}"
    );
}
