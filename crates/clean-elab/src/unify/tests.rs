// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::expr::{BinderInfo, ZFCSetExpr};
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Level, LocalContext};
use std::sync::Arc;

#[test]
fn test_meta_state_fresh() {
    let mut state = MetaState::new();
    let id1 = state.fresh(Expr::type_());
    let id2 = state.fresh(Expr::prop());
    assert_ne!(id1, id2);
}

#[test]
fn test_meta_assignment() {
    let mut state = MetaState::new();
    let id = state.fresh(Expr::type_());

    assert!(!state.is_assigned(id));
    assert!(state.assign(id, Expr::prop()));
    assert!(state.is_assigned(id));
    assert_eq!(state.get_assignment(id), Some(&Expr::prop()));
}

#[test]
fn test_unify_same() {
    let mut state = MetaState::new();
    let mut unifier = Unifier::new(&mut state);

    let result = unifier.unify(&Expr::type_(), &Expr::type_());
    assert!(matches!(result, UnifyResult::Success));
}

#[test]
fn test_unify_different() {
    let mut state = MetaState::new();
    let mut unifier = Unifier::new(&mut state);

    let result = unifier.unify(&Expr::type_(), &Expr::prop());
    assert!(matches!(result, UnifyResult::Failure(_)));
}

/// `Bool` and `Prop` are not kernel-defeq, but the unifier's lenient
/// fallback treats them as unifiable so that `decide`-style elaboration
/// sites don't fail before coercion. Pins the behavior added in
/// `unify_expr::is_bool_prop_pair`.
#[test]
fn test_unify_bool_prop_pair_lenient() {
    let bool_const = Expr::const_str("Bool");

    let mut state = MetaState::new();
    let mut unifier = Unifier::new(&mut state);
    let result = unifier.unify(&bool_const, &Expr::prop());
    assert!(matches!(result, UnifyResult::Success));

    let mut state = MetaState::new();
    let mut unifier = Unifier::new(&mut state);
    let result = unifier.unify(&Expr::prop(), &bool_const);
    assert!(matches!(result, UnifyResult::Success));
}

#[test]
fn test_unify_whnf_beta_reduction() {
    let env = Environment::new();
    let ctx = LocalContext::new();
    let mut state = MetaState::new();
    let mut unifier = Unifier::with_env(&mut state, &env, ctx);

    let lam = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let app = Expr::app(lam, Expr::prop());
    let result = unifier.unify(&app, &Expr::prop());
    assert!(matches!(result, UnifyResult::Success));
}

#[test]
fn test_unify_app() {
    let mut state = MetaState::new();
    let mut unifier = Unifier::new(&mut state);

    let app1 = Expr::app(
        Expr::from_kind(ExprKind::BVar(0)),
        Expr::from_kind(ExprKind::BVar(1)),
    );
    let app2 = Expr::app(
        Expr::from_kind(ExprKind::BVar(0)),
        Expr::from_kind(ExprKind::BVar(1)),
    );
    let result = unifier.unify(&app1, &app2);
    assert!(matches!(result, UnifyResult::Success));

    let app3 = Expr::app(
        Expr::from_kind(ExprKind::BVar(0)),
        Expr::from_kind(ExprKind::BVar(2)),
    );
    let result = unifier.unify(&app1, &app3);
    assert!(matches!(result, UnifyResult::Failure(_)));
}

#[test]
fn test_unify_assigns_meta() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(meta_id)));

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&meta_expr, &Expr::prop())
    };
    assert!(matches!(result, UnifyResult::Success));

    // Assignment should be stored and instantiation should replace the metavariable
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));
    assert_eq!(state.instantiate(&meta_expr), Expr::prop());
}

#[test]
fn test_unify_meta_constrains_concrete_type_level_for_fvar_assignment() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let mut state = MetaState::new();
    let alpha_level = Level::param(Name::from_string("u_0"));
    let alpha = ctx.push(
        Name::from_string("α"),
        Expr::sort(alpha_level.clone()),
        BinderInfo::Implicit,
    );
    let meta_id = state.fresh(Expr::type_());
    let meta_expr = meta_expr(meta_id);

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&meta_expr, &Expr::fvar(alpha))
    };
    assert!(
        matches!(result, UnifyResult::Success),
        "type metavariable assignment should succeed, got {result:?}"
    );
    assert_eq!(
        state.instantiate_level(&alpha_level),
        Level::succ(Level::zero()),
        "assigning a type metavariable expected at Type should constrain the local type level"
    );
    assert_eq!(
        state.get_assignment(meta_id),
        Some(&Expr::fvar(alpha)),
        "meta should still assign to the local fvar after constraining its level"
    );
}

#[test]
fn test_unify_meta_keeps_direct_sort_assignment_without_false_level_conflict() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::prop());
    let meta_expr = meta_expr(meta_id);

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&meta_expr, &Expr::sort(Level::zero()))
    };
    assert!(
        matches!(result, UnifyResult::Success),
        "direct sort assignment should stay accepted, got {result:?}"
    );
    assert_eq!(
        state.get_assignment(meta_id),
        Some(&Expr::sort(Level::zero())),
        "Prop-typed metavars should keep direct Sort assignments"
    );
}

#[test]
fn test_unify_meta_type_accepts_prop_fvar_by_cumulativity() {
    // Regression test for refine regression: `?α : Type` assigned `A : Prop`
    // must succeed by universe cumulativity (Sort(0) ≤ Sort(1)).
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let mut state = MetaState::new();
    let a_fvar = ctx.push(Name::from_string("A"), Expr::prop(), BinderInfo::Default);
    let meta_id = state.fresh(Expr::type_());
    let meta_expr = meta_expr(meta_id);

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&meta_expr, &Expr::fvar(a_fvar))
    };
    assert!(
        matches!(result, UnifyResult::Success),
        "?α : Type assigned A : Prop should succeed by cumulativity, got {result:?}"
    );
    assert_eq!(
        state.get_assignment(meta_id),
        Some(&Expr::fvar(a_fvar)),
        "meta should assign to the Prop-typed fvar"
    );
}

#[test]
fn test_unify_mdata_transparent_with_meta() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta = meta_expr(meta_id);
    let wrapped = Expr::mdata(vec![], meta.clone());

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&wrapped, &Expr::prop())
    };
    assert!(matches!(result, UnifyResult::Success));
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));
}

#[test]
fn test_unify_squash_with_meta() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta = meta_expr(meta_id);

    let left = Expr::from_kind(ExprKind::Squash(Arc::new(meta)));
    let right = Expr::from_kind(ExprKind::Squash(Arc::new(Expr::prop())));

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&left, &right)
    };
    assert!(matches!(result, UnifyResult::Success));
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));
}

#[test]
fn test_unify_cubical_path_with_meta() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta = meta_expr(meta_id);

    let left = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(meta),
        left: Arc::new(Expr::type_()),
        right: Arc::new(Expr::type_()),
    });
    let right = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(Expr::prop()),
        left: Arc::new(Expr::type_()),
        right: Arc::new(Expr::type_()),
    });

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&left, &right)
    };
    assert!(matches!(result, UnifyResult::Success));
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));
}

#[test]
fn test_unify_cubical_path_lam_with_meta() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta = meta_expr(meta_id);

    let left = Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(meta),
    });
    let right = Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(Expr::prop()),
    });

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&left, &right)
    };
    assert!(matches!(result, UnifyResult::Success));
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));
}

#[test]
fn test_unify_cubical_path_app_with_meta() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta = meta_expr(meta_id);

    let left = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(meta),
        arg: Arc::new(Expr::from_kind(ExprKind::CubicalI0)),
    });
    let right = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(Expr::prop()),
        arg: Arc::new(Expr::from_kind(ExprKind::CubicalI0)),
    });

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&left, &right)
    };
    assert!(matches!(result, UnifyResult::Success));
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));
}

#[test]
fn test_unify_cubical_hcomp_with_meta() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta = meta_expr(meta_id);

    let left = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(Expr::type_()),
        phi: Arc::new(Expr::type_()),
        u: Arc::new(meta),
        base: Arc::new(Expr::type_()),
    });
    let right = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(Expr::type_()),
        phi: Arc::new(Expr::type_()),
        u: Arc::new(Expr::prop()),
        base: Arc::new(Expr::type_()),
    });

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&left, &right)
    };
    assert!(matches!(result, UnifyResult::Success));
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));
}

#[test]
fn test_unify_cubical_transp_with_meta() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta = meta_expr(meta_id);

    let left = Expr::from_kind(ExprKind::CubicalTransp {
        ty: Arc::new(Expr::type_()),
        phi: Arc::new(meta),
        base: Arc::new(Expr::type_()),
    });
    let right = Expr::from_kind(ExprKind::CubicalTransp {
        ty: Arc::new(Expr::type_()),
        phi: Arc::new(Expr::prop()),
        base: Arc::new(Expr::type_()),
    });

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&left, &right)
    };
    assert!(matches!(result, UnifyResult::Success));
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));
}

#[test]
fn test_unify_zfc_set_singleton_with_meta() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta = meta_expr(meta_id);

    let left = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(Arc::new(meta))));
    let right = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(Arc::new(
        Expr::prop(),
    ))));

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&left, &right)
    };
    assert!(matches!(result, UnifyResult::Success));
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));
}

#[test]
fn test_unify_zfc_mem_with_meta() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta = meta_expr(meta_id);

    let left = Expr::from_kind(ExprKind::ZFCMem {
        element: Arc::new(meta),
        set: Arc::new(Expr::type_()),
    });
    let right = Expr::from_kind(ExprKind::ZFCMem {
        element: Arc::new(Expr::prop()),
        set: Arc::new(Expr::type_()),
    });

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&left, &right)
    };
    assert!(matches!(result, UnifyResult::Success));
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));
}

#[test]
fn test_unify_zfc_comprehension_with_meta() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta = meta_expr(meta_id);

    let left = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::type_()),
        pred: Arc::new(meta),
    });
    let right = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::type_()),
        pred: Arc::new(Expr::prop()),
    });

    let result = {
        let mut unifier = Unifier::new(&mut state);
        unifier.unify(&left, &right)
    };
    assert!(matches!(result, UnifyResult::Success));
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));
}

#[test]
fn test_unify_mode_leaf_variants() {
    let mut state = MetaState::new();
    let mut unifier = Unifier::new(&mut state);

    assert!(matches!(
        unifier.unify(
            &Expr::from_kind(ExprKind::SProp),
            &Expr::from_kind(ExprKind::SProp)
        ),
        UnifyResult::Success
    ));
    assert!(matches!(
        unifier.unify(
            &Expr::from_kind(ExprKind::CubicalInterval),
            &Expr::from_kind(ExprKind::CubicalInterval)
        ),
        UnifyResult::Success
    ));
    assert!(matches!(
        unifier.unify(
            &Expr::from_kind(ExprKind::CubicalI0),
            &Expr::from_kind(ExprKind::CubicalI0)
        ),
        UnifyResult::Success
    ));
    assert!(matches!(
        unifier.unify(
            &Expr::from_kind(ExprKind::CubicalI1),
            &Expr::from_kind(ExprKind::CubicalI1)
        ),
        UnifyResult::Success
    ));
}

#[test]
fn test_occurs_check_blocks_self_reference() {
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(meta_id)));

    // Try to unify ?m with (?m) applied to Prop, which should fail occurs check
    let mut unifier = Unifier::new(&mut state);
    let bad = Expr::app(meta_expr.clone(), Expr::prop());
    let result = unifier.unify(&meta_expr, &bad);
    assert!(matches!(result, UnifyResult::Failure(_)));
}

// =====================================================================
// Universe level union-find tests (#168)
// =====================================================================

#[test]
fn test_level_param_to_concrete() {
    // Test: u_0 = Zero => instantiate_level(u_0) = Zero
    let mut state = MetaState::new();
    let u0 = Level::param(Name::from_string("u_0"));

    state
        .add_level_constraint(Name::from_string("u_0"), Level::zero())
        .expect("u_0 := 0 should succeed");

    let result = state.instantiate_level(&u0);
    assert_eq!(result, Level::zero());
}

#[test]
fn test_level_param_to_param_to_concrete() {
    // Test: u_0 = u_1, u_1 = Zero => instantiate_level(u_0) = Zero
    // This is the key test for #168
    let mut state = MetaState::new();
    let u0 = Level::param(Name::from_string("u_0"));
    let u1 = Level::param(Name::from_string("u_1"));

    // First unify u_0 with u_1 (param to param)
    state
        .add_level_constraint(Name::from_string("u_0"), u1.clone())
        .expect("u_0 := u_1 should succeed");
    // Then unify u_1 with Zero (param to concrete)
    state
        .add_level_constraint(Name::from_string("u_1"), Level::zero())
        .expect("u_1 := 0 should succeed");

    // Both should now resolve to Zero
    assert_eq!(state.instantiate_level(&u0), Level::zero());
    assert_eq!(state.instantiate_level(&u1), Level::zero());
}

#[test]
fn test_level_param_to_param_same_canonical() {
    // Test: u_0 = u_1 (no concrete) => both resolve to same canonical param
    // This ensures kernel doesn't see u_0 vs u_1 mismatch
    let mut state = MetaState::new();
    let u0 = Level::param(Name::from_string("u_0"));
    let u1 = Level::param(Name::from_string("u_1"));

    state
        .add_level_constraint(Name::from_string("u_0"), u1.clone())
        .expect("u_0 := u_1 should succeed");

    let result_u0 = state.instantiate_level(&u0);
    let result_u1 = state.instantiate_level(&u1);

    // Both must be the SAME - this is the fix for #168
    assert_eq!(
        result_u0, result_u1,
        "u_0 and u_1 should resolve to same canonical param"
    );
}

#[test]
fn test_level_chain_resolution() {
    // Test: u_0 = u_1 = u_2 = Zero => all resolve to Zero
    let mut state = MetaState::new();
    let u0 = Level::param(Name::from_string("u_0"));
    let u1 = Level::param(Name::from_string("u_1"));
    let u2 = Level::param(Name::from_string("u_2"));

    state
        .add_level_constraint(Name::from_string("u_0"), u1.clone())
        .expect("u_0 := u_1 should succeed");
    state
        .add_level_constraint(Name::from_string("u_1"), u2.clone())
        .expect("u_1 := u_2 should succeed");
    state
        .add_level_constraint(Name::from_string("u_2"), Level::zero())
        .expect("u_2 := 0 should succeed");

    assert_eq!(state.instantiate_level(&u0), Level::zero());
    assert_eq!(state.instantiate_level(&u1), Level::zero());
    assert_eq!(state.instantiate_level(&u2), Level::zero());
}

#[test]
fn test_level_succ_with_param() {
    // Test: Succ(u_0), u_0 = Zero => Succ(Zero)
    let mut state = MetaState::new();
    let u0 = Level::param(Name::from_string("u_0"));
    let succ_u0 = Level::succ(u0);

    state
        .add_level_constraint(Name::from_string("u_0"), Level::zero())
        .expect("u_0 := 0 should succeed");

    let result = state.instantiate_level(&succ_u0);
    assert_eq!(result, Level::succ(Level::zero()));
}

#[test]
fn test_level_unify_resolves_to_concrete() {
    // Integration test: unify levels through Unifier, verify both resolve to same concrete
    let mut state = MetaState::new();
    let u0 = Level::param(Name::from_string("u_0"));
    let u1 = Level::param(Name::from_string("u_1"));

    {
        let mut unifier = Unifier::new(&mut state);
        // Unify u_0 = u_1
        let result = unifier.unify_levels(&u0, &u1);
        assert!(matches!(result, UnifyResult::Success));
        // Unify u_1 = Zero
        let result = unifier.unify_levels(&u1, &Level::zero());
        assert!(matches!(result, UnifyResult::Success));
    }

    // After unification, both should resolve to Zero
    assert_eq!(state.instantiate_level(&u0), Level::zero());
    assert_eq!(state.instantiate_level(&u1), Level::zero());
}

#[test]
fn test_level_union_conflicting_concretes_reports_failure() {
    let mut state = MetaState::new();
    let u0_name = Name::from_string("u_0");
    let u1_name = Name::from_string("u_1");
    let u0 = Level::param(u0_name.clone());
    let u1 = Level::param(u1_name.clone());

    state
        .add_level_constraint(u0_name, Level::zero())
        .expect("u_0 := 0 should succeed");
    state
        .add_level_constraint(u1_name, Level::succ(Level::zero()))
        .expect("u_1 := 1 should succeed");

    {
        let mut unifier = Unifier::new(&mut state);
        let result = unifier.unify_levels(&u0, &u1);
        assert!(
            matches!(&result, UnifyResult::Failure(msg) if msg.contains("universe level conflict")),
            "unifying concretely-incompatible levels should fail, got: {result:?}"
        );
    }

    // Failure must not silently overwrite either concrete assignment.
    assert_eq!(state.instantiate_level(&u0), Level::zero());
    assert_eq!(state.instantiate_level(&u1), Level::succ(Level::zero()));
}

#[test]
fn test_level_concrete_reassignment_conflict_is_rejected() {
    let mut state = MetaState::new();
    let u0_name = Name::from_string("u_0");
    let u0 = Level::param(u0_name.clone());

    state
        .add_level_constraint(u0_name.clone(), Level::zero())
        .expect("u_0 := 0 should succeed");

    let result = state.add_level_constraint(u0_name, Level::succ(Level::zero()));
    assert!(
        matches!(&result, Err(msg) if msg.contains("universe level conflict")),
        "conflicting reassignment should fail, got: {result:?}"
    );

    // Original assignment must remain in force.
    assert_eq!(state.instantiate_level(&u0), Level::zero());
}

#[test]
fn test_level_expr_const_unification() {
    // Test: Expr::Const with universe levels gets properly instantiated
    // Simulates: myFn.{u_0} and MyType.{u_1} where u_0 = u_1 = Zero
    let mut state = MetaState::new();
    let u0 = Level::param(Name::from_string("u_0"));
    let u1 = Level::param(Name::from_string("u_1"));

    // Simulate constraint: u_0 = u_1 = Zero
    state
        .add_level_constraint(Name::from_string("u_0"), u1.clone())
        .expect("u_0 := u_1 should succeed");
    state
        .add_level_constraint(Name::from_string("u_1"), Level::zero())
        .expect("u_1 := 0 should succeed");

    // Create expressions with these levels
    let const_fn = Expr::const_(Name::from_string("myFn"), vec![u0]);
    let const_ty = Expr::const_(Name::from_string("MyType"), vec![u1]);

    // Instantiate levels
    let const_fn_inst = state.instantiate_levels(&const_fn);
    let const_ty_inst = state.instantiate_levels(&const_ty);

    // Both should have Zero as their universe level
    if let ExprKind::Const(_, levels) = const_fn_inst.kind() {
        assert_eq!(levels[0], Level::zero(), "myFn should have level Zero");
    } else {
        panic!("Expected Const");
    }

    if let ExprKind::Const(_, levels) = const_ty_inst.kind() {
        assert_eq!(levels[0], Level::zero(), "MyType should have level Zero");
    } else {
        panic!("Expected Const");
    }
}

// =====================================================================
// Undo Trail Tests (#383)
// =====================================================================

#[test]
fn test_undo_trail_basic_meta_assign() {
    // Test: push_scope, assign meta, pop_scope => assignment is undone
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());

    // Without scope: assignment is permanent
    state.assign(meta_id, Expr::prop());
    assert!(state.is_assigned(meta_id));

    // Now with a fresh state
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());

    state.push_scope();
    assert!(!state.is_assigned(meta_id));
    state.assign(meta_id, Expr::prop());
    assert!(state.is_assigned(meta_id));

    // Pop should undo the assignment
    assert!(state.pop_scope());
    assert!(
        !state.is_assigned(meta_id),
        "Assignment should be undone after pop_scope"
    );
}

#[test]
fn test_undo_trail_meta_create() {
    // Test: push_scope, create meta, pop_scope => meta is removed
    let mut state = MetaState::new();

    state.push_scope();
    let meta_id = state.fresh(Expr::type_());
    let meta = state
        .get(meta_id)
        .expect("meta should exist after creation");
    assert_eq!(meta.ty, Expr::type_(), "meta should have Type type");

    // Pop should remove the metavariable
    assert!(state.pop_scope());
    assert!(
        state.get(meta_id).is_none(),
        "Metavariable should be removed after pop_scope"
    );
}

#[test]
fn test_undo_trail_level_constraint() {
    // Test: push_scope, add level constraint, pop_scope => constraint is undone
    let mut state = MetaState::new();
    let u0 = Level::param(Name::from_string("u_0"));

    state.push_scope();
    state
        .add_level_constraint(Name::from_string("u_0"), Level::zero())
        .expect("u_0 := 0 should succeed");
    assert_eq!(state.instantiate_level(&u0), Level::zero());

    // Pop should undo the constraint
    assert!(state.pop_scope());
    // The param should now just return itself (no constraint)
    assert_eq!(
        state.instantiate_level(&u0),
        u0,
        "Level constraint should be undone after pop_scope"
    );
}

#[test]
fn test_undo_trail_nested_scopes() {
    // Test: nested push_scope/pop_scope work correctly
    let mut state = MetaState::new();

    // Outer scope: create m1
    state.push_scope();
    let m1 = state.fresh(Expr::type_());
    assert_eq!(state.scope_depth(), 1);

    // Inner scope: create m2
    state.push_scope();
    let m2 = state.fresh(Expr::type_());
    assert_eq!(state.scope_depth(), 2);

    // Pop inner: m2 removed, m1 still exists
    assert!(state.pop_scope());
    assert_eq!(state.scope_depth(), 1);
    let m1_meta = state
        .get(m1)
        .expect("m1 should still exist after inner pop");
    assert_eq!(m1_meta.ty, Expr::type_(), "m1 should retain Type type");
    assert!(
        state.get(m2).is_none(),
        "m2 should be removed after inner pop"
    );

    // Pop outer: m1 also removed
    assert!(state.pop_scope());
    assert_eq!(state.scope_depth(), 0);
    assert!(
        state.get(m1).is_none(),
        "m1 should be removed after outer pop"
    );
}

#[test]
fn test_undo_trail_commit() {
    // Test: commit keeps changes from the scope
    let mut state = MetaState::new();

    state.push_scope();
    let meta_id = state.fresh(Expr::type_());
    state.assign(meta_id, Expr::prop());

    // Commit instead of pop - changes should be kept
    assert!(state.commit());
    let meta = state
        .get(meta_id)
        .expect("Metavariable should exist after commit");
    assert_eq!(
        meta.ty,
        Expr::type_(),
        "meta type should be preserved after commit"
    );
    assert!(
        state.is_assigned(meta_id),
        "Assignment should be kept after commit"
    );
}

#[test]
fn test_undo_trail_commit_then_pop_outer() {
    // Test: commit inner scope, then pop outer scope undoes everything
    let mut state = MetaState::new();

    // Outer scope
    state.push_scope();
    let m1 = state.fresh(Expr::type_());

    // Inner scope
    state.push_scope();
    let m2 = state.fresh(Expr::type_());
    state.assign(m2, Expr::prop());

    // Commit inner scope
    assert!(state.commit());
    let m1_meta = state.get(m1).expect("m1 should exist after commit");
    assert_eq!(m1_meta.ty, Expr::type_(), "m1 type should be preserved");
    let m2_meta = state.get(m2).expect("m2 should exist after commit");
    assert_eq!(m2_meta.ty, Expr::type_(), "m2 type should be preserved");
    assert!(state.is_assigned(m2));

    // Pop outer scope should undo everything
    assert!(state.pop_scope());
    assert!(
        state.get(m1).is_none(),
        "m1 should be removed after outer pop"
    );
    assert!(
        state.get(m2).is_none(),
        "m2 should be removed after outer pop (committed changes undone)"
    );
}

#[test]
fn test_undo_trail_no_scope_no_undo() {
    // Test: without push_scope, pop_scope returns false
    let mut state = MetaState::new();
    assert!(!state.pop_scope());
    assert!(!state.commit());
}

#[test]
fn test_undo_trail_level_union() {
    // Test: push_scope, unify levels, pop_scope => union is undone
    let mut state = MetaState::new();
    let u0 = Level::param(Name::from_string("u_0"));
    let u1 = Level::param(Name::from_string("u_1"));

    state.push_scope();
    // Unify u_0 = u_1
    state
        .add_level_constraint(Name::from_string("u_0"), u1.clone())
        .expect("u_0 := u_1 should succeed");
    // Both should resolve to the same canonical param
    assert_eq!(state.instantiate_level(&u0), state.instantiate_level(&u1));

    // Pop should undo the union
    assert!(state.pop_scope());
    // Now they should be different again
    assert_eq!(state.instantiate_level(&u0), u0);
    assert_eq!(state.instantiate_level(&u1), u1);
}

#[test]
fn test_undo_trail_speculative_unification() {
    // Integration test: speculative unification with backtracking
    // This simulates what tactics would do during proof search
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(meta_id)));

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);

    // Try first candidate: Nat
    state.push_scope();
    {
        let mut unifier = Unifier::new(&mut state);
        let result = unifier.unify(&meta_expr, &nat);
        assert!(matches!(result, UnifyResult::Success));
    }
    assert_eq!(state.get_assignment(meta_id), Some(&nat));

    // Oops, that didn't work for the proof - rollback
    state.pop_scope();
    assert!(
        !state.is_assigned(meta_id),
        "Assignment should be rolled back"
    );

    // Try second candidate: Bool
    state.push_scope();
    {
        let mut unifier = Unifier::new(&mut state);
        let result = unifier.unify(&meta_expr, &bool_ty);
        assert!(matches!(result, UnifyResult::Success));
    }
    assert_eq!(state.get_assignment(meta_id), Some(&bool_ty));

    // This worked - commit
    state.commit();
    assert_eq!(state.get_assignment(meta_id), Some(&bool_ty));
}

#[test]
fn test_undo_trail_has_scope() {
    let mut state = MetaState::new();
    assert!(!state.has_scope());

    state.push_scope();
    assert!(state.has_scope());

    state.pop_scope();
    assert!(!state.has_scope());
}

#[test]
fn test_undo_trail_create_and_assign_same_scope() {
    // Test: creating and assigning a meta in the same scope undoes both
    let mut state = MetaState::new();

    state.push_scope();

    // Create meta in scope
    let meta_id = state.fresh(Expr::type_());
    let meta = state
        .get(meta_id)
        .expect("meta should exist after creation in scope");
    assert_eq!(meta.ty, Expr::type_(), "meta should have Type type");

    // Assign meta in same scope
    state.assign(meta_id, Expr::prop());
    assert!(state.is_assigned(meta_id));
    assert_eq!(state.get_assignment(meta_id), Some(&Expr::prop()));

    // Pop should undo BOTH the creation and the assignment
    assert!(state.pop_scope());
    assert!(
        state.get(meta_id).is_none(),
        "Meta should be removed after pop (undo both create and assign)"
    );
}

#[test]
fn test_undo_trail_multiple_metas_in_scope() {
    // Test: multiple metas created in same scope are all removed on pop
    let mut state = MetaState::new();

    state.push_scope();
    let m1 = state.fresh(Expr::type_());
    let m2 = state.fresh(Expr::prop());
    let m3 = state.fresh(Expr::type_());

    // Assign some but not all
    state.assign(m1, Expr::prop());
    state.assign(m3, Expr::type_());

    let m1_meta = state.get(m1).expect("m1 should exist before pop");
    assert_eq!(m1_meta.ty, Expr::type_(), "m1 should have Type type");
    let m2_meta = state.get(m2).expect("m2 should exist before pop");
    assert_eq!(m2_meta.ty, Expr::prop(), "m2 should have Prop type");
    let m3_meta = state.get(m3).expect("m3 should exist before pop");
    assert_eq!(m3_meta.ty, Expr::type_(), "m3 should have Type type");
    assert!(state.is_assigned(m1));
    assert!(!state.is_assigned(m2));
    assert!(state.is_assigned(m3));

    // Pop should remove all three
    assert!(state.pop_scope());
    assert!(state.get(m1).is_none(), "m1 should be removed");
    assert!(state.get(m2).is_none(), "m2 should be removed");
    assert!(state.get(m3).is_none(), "m3 should be removed");
}

#[test]
fn test_undo_trail_memory_cleanup_on_commit() {
    // Test: when all scopes are committed, undo_trail is cleared (#730)
    // This prevents unbounded memory growth in long proof searches
    let mut state = MetaState::new();

    // Push scope and make some changes
    state.push_scope();
    let _ = state.fresh(Expr::type_());
    state
        .add_level_constraint(Name::from_string("u_0"), Level::zero())
        .expect("u_0 := 0 should succeed");

    // Verify trail has records
    assert!(
        !state.is_trail_empty(),
        "Trail should have records after changes"
    );

    // Commit the scope - trail should be cleared since no scopes remain
    assert!(state.commit());
    assert!(
        state.is_trail_empty(),
        "Trail should be cleared after all scopes committed (#730)"
    );
}

#[test]
fn test_undo_trail_memory_not_cleared_with_remaining_scopes() {
    // Test: when there are remaining scopes, trail is NOT cleared
    let mut state = MetaState::new();

    // Push outer scope
    state.push_scope();
    let _ = state.fresh(Expr::type_());

    // Push inner scope
    state.push_scope();
    let _ = state.fresh(Expr::prop());

    // Commit inner scope - trail should NOT be cleared (outer scope still exists)
    assert!(state.commit());
    assert!(
        !state.is_trail_empty(),
        "Trail should NOT be cleared when outer scope exists"
    );

    // Commit outer scope - now trail should be cleared
    assert!(state.commit());
    assert!(
        state.is_trail_empty(),
        "Trail should be cleared after all scopes committed"
    );
}

#[test]
fn test_undo_trail_memory_cleared_on_final_pop() {
    // Test: pop_scope also clears trail when it's the last scope
    let mut state = MetaState::new();

    state.push_scope();
    let _ = state.fresh(Expr::type_());

    // Pop removes the scope marker and replays undo records
    // After pop, trail is empty because records were consumed
    assert!(state.pop_scope());
    assert!(state.is_trail_empty(), "Trail should be empty after pop");
}

#[test]
fn test_undo_trail_level_chain_path_compression() {
    // Test: path compression side effects in level union-find are undone correctly
    // When resolving u0 -> u1 -> u2, path compression updates u0 to point directly to u2.
    // This test verifies that change is undone on pop_scope.
    let mut state = MetaState::new();
    let u0 = Level::param(Name::from_string("u_0"));
    let u1 = Level::param(Name::from_string("u_1"));
    let u2 = Level::param(Name::from_string("u_2"));

    state.push_scope();

    // Create chain: u0 -> u1 -> u2 -> Zero
    state
        .add_level_constraint(Name::from_string("u_0"), u1.clone())
        .expect("u_0 := u_1 should succeed");
    state
        .add_level_constraint(Name::from_string("u_1"), u2.clone())
        .expect("u_1 := u_2 should succeed");
    state
        .add_level_constraint(Name::from_string("u_2"), Level::zero())
        .expect("u_2 := 0 should succeed");

    // All should resolve to Zero (triggering path compression)
    assert_eq!(state.instantiate_level(&u0), Level::zero());
    assert_eq!(state.instantiate_level(&u1), Level::zero());
    assert_eq!(state.instantiate_level(&u2), Level::zero());

    // Pop should undo all constraints AND path compression
    assert!(state.pop_scope());

    // All params should resolve back to themselves
    assert_eq!(
        state.instantiate_level(&u0),
        u0,
        "u_0 should not be constrained after pop"
    );
    assert_eq!(
        state.instantiate_level(&u1),
        u1,
        "u_1 should not be constrained after pop"
    );
    assert_eq!(
        state.instantiate_level(&u2),
        u2,
        "u_2 should not be constrained after pop"
    );
}

#[test]
fn test_undo_trail_fresh_after_pop_reuses_id() {
    // Test: creating a meta in scope, popping, then creating another reuses the ID
    let mut state = MetaState::new();

    // Create meta before scope
    let m0 = state.fresh(Expr::type_());
    assert_eq!(m0, MetaId(0));

    // Create meta in scope
    state.push_scope();
    let m1_in_scope = state.fresh(Expr::prop());
    assert_eq!(m1_in_scope, MetaId(1));

    // Pop the scope - m1 should be removed and next_id decremented
    assert!(state.pop_scope());
    assert!(
        state.get(m1_in_scope).is_none(),
        "m1_in_scope should be removed after pop"
    );

    // New fresh should reuse ID 1
    let m1_after = state.fresh(Expr::type_());
    assert_eq!(m1_after, MetaId(1), "ID should be reused after scope pop");
    let meta = state.get(m1_after).expect("reused meta should exist");
    assert_eq!(meta.ty, Expr::type_(), "reused meta should have Type type");
}

#[test]
fn test_ensure_meta_sparse_id_rollback_restores_exact_cursor() {
    let mut state = MetaState::new();
    let stable = state.fresh(Expr::type_());
    let baseline_next_id = state.next_id;
    let sparse = MetaId(10_000);

    state.push_scope();
    state.ensure_meta(sparse, Expr::prop());
    assert!(state.get(sparse).is_some());
    assert_eq!(state.next_id, 10_001);
    assert_eq!(
        state.undo_trail_len_for_tests(),
        2,
        "ensure_meta should record one map insertion and one cursor change"
    );

    // Re-ensuring an existing meta is a complete no-op, including the trail.
    state.ensure_meta(sparse, Expr::type_());
    assert_eq!(state.undo_trail_len_for_tests(), 2);
    assert_eq!(
        state.get(sparse).expect("sparse meta must remain").ty,
        Expr::prop()
    );

    assert!(state.pop_scope());
    assert!(state.get(sparse).is_none());
    assert_eq!(state.next_id, baseline_next_id);
    assert!(state.get(stable).is_some());

    let next = state.fresh(Expr::prop());
    assert_eq!(next, MetaId(baseline_next_id));
}

/// Build a focused proof state that exercises every `merge_from` mutation:
/// assignment of an existing meta, insertion of a sparse meta, and insertion
/// into all three universe-level maps.
fn merge_undo_fixture(base: &MetaState, stable: MetaId, sparse: MetaId) -> MetaState {
    let mut focused = base.clone();
    assert!(focused.assign(stable, Expr::prop()));
    focused.ensure_meta(sparse, Expr::type_());
    assert!(focused.assign(sparse, Expr::prop()));

    let u0 = Name::from_string("merge_u0");
    let u1 = Name::from_string("merge_u1");
    focused
        .add_level_constraint(u0, Level::param(u1.clone()))
        .expect("fixture level union should succeed");
    focused
        .add_level_constraint(u1, Level::zero())
        .expect("fixture concrete level should succeed");
    focused
}

fn assert_merge_fixture_restored(
    state: &MetaState,
    stable: MetaId,
    sparse_ids: &[MetaId],
    baseline_next_id: u64,
) {
    assert!(!state.is_assigned(stable));
    for id in sparse_ids {
        assert!(state.get(*id).is_none(), "sparse meta {id:?} leaked");
    }
    assert_eq!(state.next_id, baseline_next_id);
    assert!(state.level_constraints.is_empty());
    assert!(state.level_parent.is_empty());
    assert!(state.level_concrete.is_empty());
}

#[test]
fn test_merge_from_owned_rollback_restores_every_mutation_exactly() {
    let mut state = MetaState::new();
    let stable = state.fresh(Expr::type_());
    let sparse = MetaId(10_000);
    let focused = merge_undo_fixture(&state, stable, sparse);
    let baseline_next_id = state.next_id;

    let scope = state.push_owned_scope();
    state.merge_from(&focused);
    assert!(state.is_assigned(stable));
    assert!(state.is_assigned(sparse));
    assert_eq!(state.next_id, 10_001);
    assert_eq!(state.level_constraints.len(), 2);
    assert_eq!(state.level_parent.len(), 1);
    assert_eq!(state.level_concrete.len(), 1);

    let trail_after_first_merge = state.undo_trail_len_for_tests();
    assert_eq!(
        trail_after_first_merge, 7,
        "merge should record exactly its two meta, cursor, and four level-map mutations"
    );
    state.merge_from(&focused);
    assert_eq!(
        state.undo_trail_len_for_tests(),
        trail_after_first_merge,
        "merging the same state twice must not add no-op undo records"
    );

    state
        .close_owned_scope(scope, true)
        .expect("owned rollback should close its exact marker");
    assert_eq!(state.scope_depth(), 0);
    assert!(state.is_trail_empty());
    assert_merge_fixture_restored(&state, stable, &[sparse], baseline_next_id);
}

#[test]
fn test_merge_from_owned_commit_persists_and_clears_trail() {
    let mut state = MetaState::new();
    let stable = state.fresh(Expr::type_());
    let sparse = MetaId(10_000);
    let focused = merge_undo_fixture(&state, stable, sparse);

    let scope = state.push_owned_scope();
    state.merge_from(&focused);
    state
        .close_owned_scope(scope, false)
        .expect("owned commit should close its exact marker");

    assert_eq!(state.scope_depth(), 0);
    assert!(state.is_trail_empty());
    assert!(state.is_assigned(stable));
    assert!(state.is_assigned(sparse));
    assert_eq!(state.next_id, 10_001);
    assert_eq!(state.level_constraints.len(), 2);
    assert_eq!(state.level_parent.len(), 1);
    assert_eq!(state.level_concrete.len(), 1);
    assert_eq!(state.fresh(Expr::type_()), MetaId(10_001));
}

#[test]
fn test_owned_commit_and_nested_commit_remain_undoable_by_outer_scope() {
    let mut state = MetaState::new();
    let stable = state.fresh(Expr::type_());
    let sparse = MetaId(10_000);
    let nested_sparse = MetaId(20_000);
    let focused = merge_undo_fixture(&state, stable, sparse);
    let baseline_next_id = state.next_id;

    state.push_scope();
    let owned = state.push_owned_scope();
    state.merge_from(&focused);
    state.push_scope();
    state.ensure_meta(nested_sparse, Expr::prop());
    assert!(state.commit(), "ordinary nested scope should commit");
    state
        .close_owned_scope(owned, false)
        .expect("owned scope should commit beneath the outer scope");

    assert_eq!(state.scope_depth(), 1);
    assert!(state.is_assigned(stable));
    assert!(state.get(sparse).is_some());
    assert!(state.get(nested_sparse).is_some());
    assert_eq!(state.next_id, 20_001);

    assert!(state.pop_scope());
    assert_merge_fixture_restored(&state, stable, &[sparse, nested_sparse], baseline_next_id);
}

#[test]
fn test_nested_owned_obstruction_rolls_back_both_scopes_exactly() {
    let mut state = MetaState::new();
    let stable = state.fresh(Expr::type_());
    let sparse = MetaId(10_000);
    let nested_sparse = MetaId(20_000);
    let focused = merge_undo_fixture(&state, stable, sparse);
    let baseline_next_id = state.next_id;

    let outer = state.push_owned_scope();
    state.merge_from(&focused);
    let inner = state.push_owned_scope();
    state.ensure_meta(nested_sparse, Expr::prop());

    assert_eq!(
        state.close_owned_scope(outer, false),
        Err(OwnedMetaScopeCloseError::Obstructed)
    );
    assert_eq!(state.scope_depth(), 0);
    assert!(state.is_trail_empty());
    assert_merge_fixture_restored(&state, stable, &[sparse, nested_sparse], baseline_next_id);
    assert_eq!(
        state.close_owned_scope(inner, true),
        Err(OwnedMetaScopeCloseError::Missing)
    );
}

// =====================================================================
// Expression kind coverage tests for instantiate/occurs (#1693)
// =====================================================================

/// Helper: create a metavar expression from a MetaId
fn meta_expr(id: MetaId) -> Expr {
    Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(id)))
}

/// Helper: did `id` get an intersection-rule assignment, i.e. a lambda chain
/// `λ … . (?h …)` whose innermost body applies a metavariable head?
///
/// The flex-flex intersection rule is the only path that assigns a lambda whose
/// body head is itself a (fresh) metavariable, so this distinguishes an
/// intersection solve from ordinary structural fallback assignments (which
/// assign bare metas or rigid terms).
fn assigned_via_fresh_meta_body(state: &MetaState, id: MetaId) -> bool {
    let Some(assigned) = state.get_assignment(id) else {
        return false;
    };
    // The intersection rule always wraps ≥1 lambda binder (the flex side has at
    // least one argument). A bare structural assignment like `?n := ?m x` has no
    // outer lambda, so we require the assignment to start with a Lam.
    if !assigned.is_lam() {
        return false;
    }
    let mut body = assigned;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = inner;
    }
    MetaState::from_fvar(match body.get_app_fn().kind() {
        ExprKind::FVar(fid) => *fid,
        _ => return false,
    })
    .is_some()
}

#[test]
fn test_instantiate_mdata() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    state.assign(m, Expr::prop());

    let wrapped = Expr::mdata(vec![], meta_expr(m));
    let result = state.instantiate(&wrapped);

    // After instantiation, the inner metavar should be replaced
    if let ExprKind::MData(_, inner) = result.kind() {
        assert_eq!(
            **inner,
            Expr::prop(),
            "metavar inside MData should be instantiated"
        );
    } else {
        panic!("Expected MData, got {:?}", result.kind());
    }
}

#[test]
fn test_instantiate_squash() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    state.assign(m, Expr::prop());

    let squash = Expr::from_kind(ExprKind::Squash(Arc::new(meta_expr(m))));
    let result = state.instantiate(&squash);

    if let ExprKind::Squash(inner) = result.kind() {
        assert_eq!(
            **inner,
            Expr::prop(),
            "metavar inside Squash should be instantiated"
        );
    } else {
        panic!("Expected Squash, got {:?}", result.kind());
    }
}

#[test]
fn test_instantiate_cubical_path() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    state.assign(m, Expr::prop());

    let path = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(meta_expr(m)),
        left: Arc::new(Expr::type_()),
        right: Arc::new(Expr::type_()),
    });
    let result = state.instantiate(&path);

    if let ExprKind::CubicalPath { ty, .. } = result.kind() {
        assert_eq!(
            **ty,
            Expr::prop(),
            "metavar in CubicalPath.ty should be instantiated"
        );
    } else {
        panic!("Expected CubicalPath, got {:?}", result.kind());
    }
}

#[test]
fn test_instantiate_cubical_hcomp() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    state.assign(m, Expr::prop());

    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(Expr::type_()),
        phi: Arc::new(Expr::type_()),
        u: Arc::new(meta_expr(m)),
        base: Arc::new(Expr::type_()),
    });
    let result = state.instantiate(&hcomp);

    if let ExprKind::CubicalHComp { u, .. } = result.kind() {
        assert_eq!(
            **u,
            Expr::prop(),
            "metavar in CubicalHComp.u should be instantiated"
        );
    } else {
        panic!("Expected CubicalHComp, got {:?}", result.kind());
    }
}

#[test]
fn test_instantiate_zfc_mem() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    state.assign(m, Expr::prop());

    let mem = Expr::from_kind(ExprKind::ZFCMem {
        element: Arc::new(meta_expr(m)),
        set: Arc::new(Expr::type_()),
    });
    let result = state.instantiate(&mem);

    if let ExprKind::ZFCMem { element, .. } = result.kind() {
        assert_eq!(
            **element,
            Expr::prop(),
            "metavar in ZFCMem.element should be instantiated"
        );
    } else {
        panic!("Expected ZFCMem, got {:?}", result.kind());
    }
}

#[test]
fn test_instantiate_zfc_set_singleton() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    state.assign(m, Expr::prop());

    let zfc = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(Arc::new(
        meta_expr(m),
    ))));
    let result = state.instantiate(&zfc);

    if let ExprKind::ZFCSet(ZFCSetExpr::Singleton(inner)) = result.kind() {
        assert_eq!(
            **inner,
            Expr::prop(),
            "metavar in ZFCSet::Singleton should be instantiated"
        );
    } else {
        panic!("Expected ZFCSet(Singleton), got {:?}", result.kind());
    }
}

#[test]
fn test_instantiate_zfc_comprehension() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    state.assign(m, Expr::prop());

    let comp = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::type_()),
        pred: Arc::new(meta_expr(m)),
    });
    let result = state.instantiate(&comp);

    if let ExprKind::ZFCComprehension { pred, .. } = result.kind() {
        assert_eq!(
            **pred,
            Expr::prop(),
            "metavar in ZFCComprehension.pred should be instantiated"
        );
    } else {
        panic!("Expected ZFCComprehension, got {:?}", result.kind());
    }
}

#[test]
fn test_occurs_in_mdata() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    let wrapped = Expr::mdata(vec![], meta_expr(m));

    assert!(
        state.occurs(m, &wrapped),
        "occurs should find metavar inside MData"
    );
}

#[test]
fn test_occurs_in_squash() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    let squash = Expr::from_kind(ExprKind::Squash(Arc::new(meta_expr(m))));

    assert!(
        state.occurs(m, &squash),
        "occurs should find metavar inside Squash"
    );
}

#[test]
fn test_occurs_in_cubical_path() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    let path = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(Expr::type_()),
        left: Arc::new(meta_expr(m)),
        right: Arc::new(Expr::type_()),
    });

    assert!(
        state.occurs(m, &path),
        "occurs should find metavar inside CubicalPath.left"
    );
}

#[test]
fn test_occurs_in_zfc_mem() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    let mem = Expr::from_kind(ExprKind::ZFCMem {
        element: Arc::new(Expr::type_()),
        set: Arc::new(meta_expr(m)),
    });

    assert!(
        state.occurs(m, &mem),
        "occurs should find metavar inside ZFCMem.set"
    );
}

#[test]
fn test_occurs_in_zfc_set_separation() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    let zfc = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
        set: Arc::new(Expr::type_()),
        pred: Arc::new(meta_expr(m)),
    }));

    assert!(
        state.occurs(m, &zfc),
        "occurs should find metavar inside ZFCSet::Separation.pred"
    );
}

#[test]
fn test_occurs_negative_leaf_nodes() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());

    // CubicalI0 is a leaf, should not contain metavars
    let i0 = Expr::from_kind(ExprKind::CubicalI0);
    assert!(
        !state.occurs(m, &i0),
        "occurs should return false for CubicalI0 leaf"
    );

    // Empty ZFCSet is a leaf
    let empty = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    assert!(
        !state.occurs(m, &empty),
        "occurs should return false for ZFCSet::Empty leaf"
    );
}

#[test]
fn test_occurs_check_blocks_self_reference_in_mdata() {
    // If ?m appears inside MData wrapping ?m, occurs check should catch it
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    let me = meta_expr(m);
    let wrapped = Expr::mdata(vec![], Expr::app(me.clone(), Expr::prop()));

    let mut unifier = Unifier::new(&mut state);
    let result = unifier.unify(&me, &wrapped);
    assert!(
        matches!(result, UnifyResult::Failure(_)),
        "occurs check should block self-reference through MData"
    );
}

#[test]
fn test_instantiate_cubical_path_lam() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    state.assign(m, Expr::prop());

    let plam = Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(meta_expr(m)),
    });
    let result = state.instantiate(&plam);

    if let ExprKind::CubicalPathLam { body } = result.kind() {
        assert_eq!(
            **body,
            Expr::prop(),
            "metavar in CubicalPathLam.body should be instantiated"
        );
    } else {
        panic!("Expected CubicalPathLam, got {:?}", result.kind());
    }
}

#[test]
fn test_instantiate_cubical_path_app() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    state.assign(m, Expr::prop());

    let papp = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(meta_expr(m)),
        arg: Arc::new(Expr::from_kind(ExprKind::CubicalI0)),
    });
    let result = state.instantiate(&papp);

    if let ExprKind::CubicalPathApp { path, .. } = result.kind() {
        assert_eq!(
            **path,
            Expr::prop(),
            "metavar in CubicalPathApp.path should be instantiated"
        );
    } else {
        panic!("Expected CubicalPathApp, got {:?}", result.kind());
    }
}

#[test]
fn test_instantiate_cubical_transp() {
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    state.assign(m, Expr::prop());

    let transp = Expr::from_kind(ExprKind::CubicalTransp {
        ty: Arc::new(Expr::type_()),
        phi: Arc::new(meta_expr(m)),
        base: Arc::new(Expr::type_()),
    });
    let result = state.instantiate(&transp);

    if let ExprKind::CubicalTransp { phi, .. } = result.kind() {
        assert_eq!(
            **phi,
            Expr::prop(),
            "metavar in CubicalTransp.phi should be instantiated"
        );
    } else {
        panic!("Expected CubicalTransp, got {:?}", result.kind());
    }
}

// =====================================================================
// MetaState::assign occurs check (#2199)
// =====================================================================

#[test]
fn test_assign_rejects_direct_circular_reference() {
    // Regression test for #2199: assign(?m, ?m) must return false
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    let me = meta_expr(m);

    let result = state.assign(m, me);
    assert!(!result, "assign(?m, ?m) must be rejected by occurs check");
    assert!(
        !state.is_assigned(m),
        "meta must remain unassigned after circular rejection"
    );
}

#[test]
fn test_assign_rejects_indirect_circular_reference() {
    // assign(?m, App(?m, Prop)) must return false — ?m appears in the value
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());
    let me = meta_expr(m);
    let bad = Expr::app(me, Expr::prop());

    let result = state.assign(m, bad);
    assert!(
        !result,
        "assign(?m, App(?m, Prop)) must be rejected by occurs check"
    );
    assert!(!state.is_assigned(m));
}

#[test]
fn test_assign_allows_non_circular_reference() {
    // assign(?m, Prop) must succeed — no circularity
    let mut state = MetaState::new();
    let m = state.fresh(Expr::type_());

    let result = state.assign(m, Expr::prop());
    assert!(result, "assign(?m, Prop) should succeed");
    assert!(state.is_assigned(m));
    assert_eq!(*state.get_assignment(m).unwrap(), Expr::prop());
}

#[test]
fn test_assign_rejects_transitive_circular_reference() {
    // assign(?m1, ?m2), then assign(?m2, App(?m1, Prop)) must fail
    // because after instantiation, ?m2's value becomes App(?m1, Prop)
    // and ?m1 is assigned to ?m2, so the chain is ?m1 -> ?m2 -> App(?m1, Prop)
    let mut state = MetaState::new();
    let m1 = state.fresh(Expr::type_());
    let m2 = state.fresh(Expr::type_());
    let m1_expr = meta_expr(m1);
    let m2_expr = meta_expr(m2);

    // First assignment: ?m1 := ?m2 (non-circular, fine)
    assert!(state.assign(m1, m2_expr));

    // Second assignment: ?m2 := App(?m1, Prop)
    // After instantiation of m1, this becomes App(?m2, Prop) which contains m2
    let bad = Expr::app(m1_expr, Expr::prop());
    let result = state.assign(m2, bad);
    assert!(
        !result,
        "transitive circular assignment must be rejected by occurs check"
    );
}

#[test]
fn test_infer_level_for_type_non_hardcoded_const() {
    // Regression test for #2782: infer_level_for_type should use environment
    // lookups, not hardcoded name lists. UInt32 was NOT in the old hardcoded
    // list, so this would have returned None before the fix.
    let mut env = Environment::new();
    // Declare UInt32 : Type 0 (= Sort(Succ(Zero))) as an axiom
    env.add_skolem_axiom(
        Name::from_string("UInt32"),
        Expr::sort(Level::succ(Level::zero())),
    );
    let ctx = LocalContext::new();
    let mut state = MetaState::new();
    let meta_id = state.fresh(Expr::type_());
    let meta_expr = meta_expr(meta_id);

    let uint32_const = Expr::const_(Name::from_string("UInt32"), vec![]);
    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&meta_expr, &uint32_const)
    };
    assert!(
        matches!(result, UnifyResult::Success),
        "assigning non-hardcoded type constant to type meta should succeed via env lookup, got {result:?}"
    );
    assert_eq!(
        state.get_assignment(meta_id),
        Some(&uint32_const),
        "meta should be assigned to UInt32 constant"
    );
}

#[test]
fn test_bare_meta_scope_check_rejects_out_of_scope_local() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let escaped = ctx.push(
        Name::from_string("escaped"),
        nat.clone(),
        BinderInfo::Default,
    );

    let mut state = MetaState::new();
    let meta = state.fresh_with_locals(nat, Vec::new());
    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&meta_expr(meta), &Expr::fvar(escaped))
    };

    assert!(
        matches!(result, UnifyResult::Failure(_)),
        "an out-of-scope local cannot solve a bare metavariable: {result:?}"
    );
    assert!(
        !state.is_assigned(meta),
        "the rejected local must not escape through a partial assignment"
    );
}

#[test]
fn test_bare_meta_scope_check_accepts_captured_local() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let captured = ctx.push(
        Name::from_string("captured"),
        nat.clone(),
        BinderInfo::Default,
    );

    let mut state = MetaState::new();
    let meta = state.fresh_with_locals(nat.clone(), vec![("captured".to_string(), captured, nat)]);
    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&meta_expr(meta), &Expr::fvar(captured))
    };

    assert!(matches!(result, UnifyResult::Success));
    assert_eq!(state.get_assignment(meta), Some(&Expr::fvar(captured)));
}

#[test]
fn test_pi_comparison_cannot_leak_temporary_binder_into_bare_meta() {
    let env = Environment::new();
    let ctx = LocalContext::new();
    let mut state = MetaState::new();
    let meta = state.fresh(Expr::type_());
    let left = Expr::pi(BinderInfo::Default, Expr::type_(), meta_expr(meta));
    let right = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::bvar(0));

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&left, &right)
    };

    assert!(
        !matches!(result, UnifyResult::Success),
        "a meta created outside the Pi cannot depend on its binder: {result:?}"
    );
    assert!(
        !state.is_assigned(meta),
        "the Pi comparison's temporary FVar must not escape"
    );
}

#[test]
fn test_pi_comparison_skips_historical_meta_local_id() {
    let env = Environment::new();
    let ctx = LocalContext::new();
    let mut state = MetaState::new();
    let historical = FVarId::new(0);
    let meta = state.fresh_with_locals(
        Expr::type_(),
        vec![("historical".to_string(), historical, Expr::type_())],
    );
    let left = Expr::pi(BinderInfo::Default, Expr::type_(), meta_expr(meta));
    let right = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::bvar(0));

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&left, &right)
    };

    assert!(
        !matches!(result, UnifyResult::Success),
        "a temporary binder must not alias a popped local captured by a meta: {result:?}"
    );
    assert!(
        !state.is_assigned(meta),
        "the aliased temporary binder must not escape through the historical scope"
    );
}

#[test]
fn test_delayed_nested_meta_is_contextually_lifted_through_its_type() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);
    let x_scope = vec![("x".to_string(), x, nat.clone())];

    let mut state = MetaState::new();
    // The nested value's type is itself an unsolved meta with the wider x
    // scope. Context restriction must lift that dependency before lifting n.
    let nested_ty = state.fresh_with_locals(Expr::type_(), x_scope.clone());
    let nested = state.fresh_with_locals(meta_expr(nested_ty), x_scope);
    let outer = state.fresh_with_locals(Expr::arrow(nat.clone(), nat.clone()), Vec::new());

    let lhs = Expr::app(meta_expr(outer), Expr::fvar(x));
    let first = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx.clone());
        unifier.unify(&lhs, &meta_expr(nested))
    };
    assert!(matches!(first, UnifyResult::Success), "{first:?}");

    // Solving the original nested meta after the outer lambda was built must
    // solve its restricted helper application, not reveal a free x under the
    // already-created lambda.
    let second = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&meta_expr(nested), &Expr::fvar(x))
    };
    assert!(matches!(second, UnifyResult::Success), "{second:?}");
    let outer_value = state.instantiate(
        state
            .get_assignment(outer)
            .expect("outer pattern meta must be solved"),
    );
    assert_eq!(
        outer_value.abstract_fvar(x),
        outer_value,
        "fully instantiated outer solution must not retain the local x"
    );
}

#[test]
fn test_contextual_lift_rolls_back_helpers_and_partial_assignments() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);
    let z = ctx.push(Name::from_string("z"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    let outer = state.fresh_with_locals(Expr::arrow(nat.clone(), nat.clone()), Vec::new());
    let good = state.fresh_with_locals(nat.clone(), vec![("x".to_string(), x, nat.clone())]);
    let bad = state.fresh_with_locals(nat, vec![("z".to_string(), z, Expr::const_str("Nat"))]);
    let before_count = state.iter().count();
    let before_depth = state.scope_depth();
    let rhs = Expr::apps(Expr::const_str("Pair"), [meta_expr(good), meta_expr(bad)]);
    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&Expr::app(meta_expr(outer), Expr::fvar(x)), &rhs)
    };

    assert!(!matches!(result, UnifyResult::Success), "{result:?}");
    assert!(!state.is_assigned(outer));
    assert!(!state.is_assigned(good));
    assert!(!state.is_assigned(bad));
    assert_eq!(
        state.iter().count(),
        before_count,
        "helper metas must roll back"
    );
    assert_eq!(
        state.scope_depth(),
        before_depth,
        "scope stack must balance"
    );
}

#[test]
fn test_fresh_is_explicit_empty_and_cannot_capture_later_ambient_local() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);
    let mut state = MetaState::new();
    let tracked_empty = state.fresh_with_locals(nat.clone(), Vec::new());
    let shorthand_empty = state.fresh(nat);

    let tracked_result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx.clone());
        unifier.unify(&meta_expr(tracked_empty), &Expr::fvar(x))
    };
    assert!(!matches!(tracked_result, UnifyResult::Success));
    assert!(!state.is_assigned(tracked_empty));

    let shorthand_result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&meta_expr(shorthand_empty), &Expr::fvar(x))
    };
    assert!(!matches!(shorthand_result, UnifyResult::Success));
    assert!(!state.is_assigned(shorthand_empty));
}

#[test]
fn test_bare_meta_meta_reverses_away_from_scope_widening() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);
    let mut state = MetaState::new();
    let outer = state.fresh_with_locals(nat.clone(), Vec::new());
    let inner = state.fresh_with_locals(nat, vec![("x".to_string(), x, Expr::const_str("Nat"))]);

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&meta_expr(outer), &meta_expr(inner))
    };
    assert!(matches!(result, UnifyResult::Success), "{result:?}");
    assert!(!state.is_assigned(outer));
    assert_eq!(state.get_assignment(inner), Some(&meta_expr(outer)));
}

// =====================================================================
// Miller-pattern higher-order unification
// =====================================================================

/// `?f x =?= Nat.succ x` is a Miller pattern (single distinct local arg).
/// It must solve `?f := λ x. Nat.succ x` (the `?f x := x + 1` archetype).
#[test]
fn test_miller_pattern_single_arg_solves_lambda() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    // `x : Nat` is a local that the metavariable may legitimately depend on.
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    // `?f : Nat → Nat`, created with `x` in its captured scope.
    let f_ty = Expr::arrow(nat.clone(), nat.clone());
    let f = state.fresh_with_locals(f_ty, vec![("x".to_string(), x, nat.clone())]);

    // LHS: `?f x`.  RHS: `Nat.succ x`.
    let lhs = Expr::app(meta_expr(f), Expr::fvar(x));
    let rhs = Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(x));

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs, &rhs)
    };
    assert!(
        matches!(result, UnifyResult::Success),
        "Miller pattern ?f x =?= Nat.succ x should solve, got {result:?}"
    );

    // Expected solution: `λ x. Nat.succ (BVar 0)` — the abstracted body.
    let assigned = state
        .get_assignment(f)
        .expect("?f should be assigned by the pattern rule")
        .clone();
    let ExprKind::Lam(_, _, body) = assigned.kind() else {
        panic!("expected ?f := λ _. _, got {:?}", assigned.kind());
    };
    let expected_body = Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0));
    assert_eq!(
        **body, expected_body,
        "?f should be λ x. Nat.succ x with x abstracted to BVar(0)"
    );

    // Instantiating `?f x` yields the redex `(λ x. Nat.succ x) x`; the unifier
    // assigns but does not beta-reduce. The redex beta-reduces to the RHS,
    // which is exactly what the kernel will check.
    assert!(
        matches!(state.instantiate(&lhs).kind(), ExprKind::App(f, _) if f.is_lam()),
        "instantiating ?f x should produce the beta-redex (λ x. _) x"
    );
}

/// `?g x y =?= ?g_body` with two distinct local args abstracts in the right
/// de Bruijn order: x at the outer binder (BVar 1), y at the inner (BVar 0).
#[test]
fn test_miller_pattern_two_args_abstraction_order() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);
    let y = ctx.push(Name::from_string("y"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    let g_ty = Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone()));
    let g = state.fresh_with_locals(
        g_ty,
        vec![
            ("x".to_string(), x, nat.clone()),
            ("y".to_string(), y, nat.clone()),
        ],
    );

    // LHS: `?g x y`.  RHS: `Foo y x` (note: y before x in the body).
    let lhs = Expr::apps(meta_expr(g), [Expr::fvar(x), Expr::fvar(y)]);
    let rhs = Expr::apps(Expr::const_str("Foo"), [Expr::fvar(y), Expr::fvar(x)]);

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs, &rhs)
    };
    assert!(
        matches!(result, UnifyResult::Success),
        "two-arg Miller pattern should solve, got {result:?}"
    );

    // Expected: `λ x. λ y. Foo (BVar 0) (BVar 1)` — y is innermost (BVar 0),
    // x is the outer binder (BVar 1).
    let assigned = state.get_assignment(g).expect("?g assigned").clone();
    let expected = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::apps(Expr::const_str("Foo"), [Expr::bvar(0), Expr::bvar(1)]),
        ),
    );
    assert_eq!(
        assigned, expected,
        "abstraction order: x↦BVar(1), y↦BVar(0)"
    );
}

/// A NON-pattern constraint with a repeated argument (`?f x x`) must NOT be
/// solved by the Miller rule (no unique solution). It defers to the structural
/// dispatch, which here finds no solution — so no wrong assignment is made.
#[test]
fn test_miller_non_pattern_repeated_arg_defers_no_assignment() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    let f = state.fresh_with_locals(
        Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
        vec![("x".to_string(), x, nat.clone())],
    );

    // `?f x x =?= x` — repeated arg ⇒ not a pattern (λx.λx.? could be either).
    let lhs = Expr::apps(meta_expr(f), [Expr::fvar(x), Expr::fvar(x)]);
    let rhs = Expr::fvar(x);

    let _result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs, &rhs)
    };
    assert!(
        !state.is_assigned(f),
        "repeated-argument non-pattern must not be solved by the Miller rule"
    );
}

/// A constraint whose RHS contains a free local NOT among the pattern args and
/// NOT in the metavariable's scope must defer (the local would escape). The RHS
/// here is a bare local, so the structural fallback cannot decompose it either:
/// the constraint is left entirely unsolved, with no Miller assignment.
#[test]
fn test_miller_scope_check_out_of_scope_local_defers() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);
    // `z` is in the ambient context but is NOT in ?f's captured scope and is
    // NOT a pattern argument.
    let z = ctx.push(Name::from_string("z"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    // ?f's scope only contains `x`, deliberately excluding `z`.
    let f = state.fresh_with_locals(
        Expr::arrow(nat.clone(), nat.clone()),
        vec![("x".to_string(), x, nat.clone())],
    );

    // `?f x =?= z`. `z` escapes ?f's scope ⇒ Miller defers; the RHS is a bare
    // local so nothing else can solve it either. No assignment.
    let lhs = Expr::app(meta_expr(f), Expr::fvar(x));
    let rhs = Expr::fvar(z);

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs, &rhs)
    };
    assert!(
        !matches!(result, UnifyResult::Success),
        "out-of-scope RHS must not unify, got {result:?}"
    );
    assert!(
        !state.is_assigned(f),
        "out-of-scope local in RHS must prevent a Miller-pattern assignment"
    );
}

/// A genuine pattern whose RHS is a bare local within the metavariable's scope
/// solves to the projection `λ x. z` (the body need not mention the argument).
#[test]
fn test_miller_pattern_in_scope_local_rhs_solves() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let z = ctx.push(Name::from_string("z"), nat.clone(), BinderInfo::Default);
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    // ?f's scope contains both z and x, so `z` in the body is legal.
    let f = state.fresh_with_locals(
        Expr::arrow(nat.clone(), nat.clone()),
        vec![
            ("z".to_string(), z, nat.clone()),
            ("x".to_string(), x, nat.clone()),
        ],
    );

    // `?f x =?= z` with z in scope ⇒ `?f := λ x. z` (constant function).
    let lhs = Expr::app(meta_expr(f), Expr::fvar(x));
    let rhs = Expr::fvar(z);

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs, &rhs)
    };
    assert!(
        matches!(result, UnifyResult::Success),
        "?f x =?= z with z in scope should solve, got {result:?}"
    );
    let assigned = state.get_assignment(f).expect("?f assigned").clone();
    let expected = Expr::lam(BinderInfo::Default, nat.clone(), Expr::fvar(z));
    assert_eq!(
        assigned, expected,
        "?f should be the constant function λ x. z (x abstracted, z preserved)"
    );
}

/// Occurs check: `?f x =?= Nat.succ (?f x)` must fail (the body mentions ?f).
/// No assignment is made.
#[test]
fn test_miller_occurs_check_prevents_self_reference() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    let f = state.fresh_with_locals(
        Expr::arrow(nat.clone(), nat.clone()),
        vec![("x".to_string(), x, nat.clone())],
    );

    // `?f x =?= Nat.succ (?f x)` — ?f occurs in the RHS.
    let f_x = Expr::app(meta_expr(f), Expr::fvar(x));
    let rhs = Expr::app(Expr::const_str("Nat.succ"), f_x.clone());

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&f_x, &rhs)
    };
    assert!(
        matches!(result, UnifyResult::Failure(_)),
        "occurs check should make ?f x =?= Nat.succ (?f x) fail, got {result:?}"
    );
    assert!(
        !state.is_assigned(f),
        "occurs-check failure must not leave a partial assignment"
    );
}

/// Pattern argument that is a metavariable (not a genuine local) is not a
/// pattern; the rule defers. Regression guard against treating meta args as
/// abstractable locals. The RHS is a bare local so the structural fallback also
/// cannot decompose it — isolating the Miller decision.
#[test]
fn test_miller_meta_argument_is_not_a_pattern() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let z = ctx.push(Name::from_string("z"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    let other = state.fresh(nat.clone()); // a metavariable used as an "argument"
    let f = state.fresh(Expr::arrow(nat.clone(), nat.clone()));

    // `?f ?other =?= z` — the argument is a metavar, not a local, so this is
    // not a Miller pattern; the bare-local RHS blocks the structural path too.
    let lhs = Expr::app(meta_expr(f), meta_expr(other));
    let rhs = Expr::fvar(z);

    let _result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs, &rhs)
    };
    assert!(
        !state.is_assigned(f),
        "a metavariable argument must not be treated as a pattern variable"
    );
}

/// Regression: ordinary (non-flex) application unification must still work
/// exactly as before — the Miller path returns `None` and the structural
/// dispatch handles it.
#[test]
fn test_miller_regression_rigid_app_still_unifies() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    // `?a` is a bare metavariable argument inside a rigid head `Nat.succ ?a`.
    let a = state.fresh_with_locals(nat.clone(), vec![("x".to_string(), x, nat.clone())]);

    // `Nat.succ ?a =?= Nat.succ x` should solve `?a := x` via the structural
    // App arm (rigid head, meta in argument position), unchanged by Miller.
    let lhs = Expr::app(Expr::const_str("Nat.succ"), meta_expr(a));
    let rhs = Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(x));

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs, &rhs)
    };
    assert!(
        matches!(result, UnifyResult::Success),
        "rigid application unification must still succeed, got {result:?}"
    );
    assert_eq!(
        state.get_assignment(a),
        Some(&Expr::fvar(x)),
        "?a should be assigned x by ordinary structural unification"
    );
}

/// Same-metavariable flex-flex `?f x =?= ?f y` decomposes argument-wise:
/// it reduces to `x =?= y`, which fails for distinct locals (no wrong
/// assignment, preserving prior congruence behavior).
#[test]
fn test_miller_same_meta_flex_flex_decomposes() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);
    let y = ctx.push(Name::from_string("y"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    let f = state.fresh_with_locals(
        Expr::arrow(nat.clone(), nat.clone()),
        vec![
            ("x".to_string(), x, nat.clone()),
            ("y".to_string(), y, nat.clone()),
        ],
    );

    // `?f x =?= ?f y`: same head, distinct args ⇒ decompose to `x =?= y`,
    // which fails. No assignment to ?f.
    let lhs = Expr::app(meta_expr(f), Expr::fvar(x));
    let rhs = Expr::app(meta_expr(f), Expr::fvar(y));

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs, &rhs)
    };
    assert!(
        matches!(result, UnifyResult::Failure(_)),
        "?f x =?= ?f y with distinct args should fail via arg decomposition, got {result:?}"
    );
    assert!(
        !state.is_assigned(f),
        "same-meta flex-flex decomposition must not assign ?f"
    );
}

// --- Flex-flex intersection rule -------------------------------------------

/// Distinct-head flex-flex where both sides are Miller patterns:
/// `?m x y =?= ?n y z`. The intersection rule invents a fresh `?h` over the
/// shared variable `{y}` and assigns `?m := λ x y. ?h y`, `?n := λ y z. ?h y`.
/// Both `?m x y` and `?n y z` then beta-reduce to `?h y`, so re-unifying the
/// instantiated sides succeeds (the kernel-level definitional equality holds).
#[test]
fn test_miller_flex_flex_intersection_distinct_patterns_solves() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);
    let y = ctx.push(Name::from_string("y"), nat.clone(), BinderInfo::Default);
    let z = ctx.push(Name::from_string("z"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    // ?m : Nat → Nat → Nat, scoped over {x, y}.
    let m = state.fresh_with_locals(
        Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
        vec![
            ("x".to_string(), x, nat.clone()),
            ("y".to_string(), y, nat.clone()),
        ],
    );
    // ?n : Nat → Nat → Nat, scoped over {y, z}.
    let n = state.fresh_with_locals(
        Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
        vec![
            ("y".to_string(), y, nat.clone()),
            ("z".to_string(), z, nat.clone()),
        ],
    );

    // `?m x y =?= ?n y z`: distinct heads, both patterns, common var = {y}.
    let lhs = Expr::apps(meta_expr(m), [Expr::fvar(x), Expr::fvar(y)]);
    let rhs = Expr::apps(meta_expr(n), [Expr::fvar(y), Expr::fvar(z)]);

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx.clone());
        unifier.unify(&lhs, &rhs)
    };
    assert!(
        matches!(result, UnifyResult::Success),
        "flex-flex intersection ?m x y =?= ?n y z should solve, got {result:?}"
    );

    // ?m := λ x y. ?h (BVar 0)  — y is the inner binder, so the common var y is
    // BVar(0) in the body.
    let m_assigned = state
        .get_assignment(m)
        .expect("?m should be assigned by the intersection rule")
        .clone();
    let ExprKind::Lam(_, _, m_body1) = m_assigned.kind() else {
        panic!("expected ?m := λ _. λ _. _, got {:?}", m_assigned.kind());
    };
    let ExprKind::Lam(_, _, m_body2) = m_body1.kind() else {
        panic!("expected ?m to have two binders, got {:?}", m_body1.kind());
    };
    // The fresh ?h is the only meta created after m and n.
    let h_fvar = match m_body2.get_app_fn().kind() {
        ExprKind::FVar(id) => *id,
        other => panic!("expected ?m body head to be ?h, got {other:?}"),
    };
    assert!(
        MetaState::from_fvar(h_fvar).is_some(),
        "?m body head must be a fresh metavariable ?h"
    );
    assert_eq!(
        **m_body2,
        Expr::app(Expr::fvar(h_fvar), Expr::bvar(0)),
        "?m := λ x y. ?h y with y abstracted to BVar(0)"
    );

    // ?n := λ y z. ?h (BVar 1)  — y is the OUTER binder here, so the common var
    // y is BVar(1) in the body. Same ?h head as ?m.
    let n_assigned = state.get_assignment(n).expect("?n assigned").clone();
    let ExprKind::Lam(_, _, n_body1) = n_assigned.kind() else {
        panic!("expected ?n := λ _. λ _. _, got {:?}", n_assigned.kind());
    };
    let ExprKind::Lam(_, _, n_body2) = n_body1.kind() else {
        panic!("expected ?n to have two binders, got {:?}", n_body1.kind());
    };
    assert_eq!(
        **n_body2,
        Expr::app(Expr::fvar(h_fvar), Expr::bvar(1)),
        "?n := λ y z. ?h y with y (outer binder) abstracted to BVar(1)"
    );

    // The solution is correct up to definitional equality: instantiating both
    // sides yields beta-redexes that reduce to the same `?h y`. Re-unifying the
    // instantiated sides (which WHNF-reduces) must succeed.
    let lhs_inst = state.instantiate(&lhs);
    let rhs_inst = state.instantiate(&rhs);
    let recheck = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs_inst, &rhs_inst)
    };
    assert!(
        matches!(recheck, UnifyResult::Success),
        "instantiated intersection solution must be definitionally equal, got {recheck:?}"
    );
}

/// A non-pattern flex-flex (distinct heads, one side has a repeated argument)
/// must NOT trigger the intersection rule: there is no unique most-general
/// solution. The intersection rule invents a fresh `?h` (and a result-type
/// metavariable) when it fires, so its *not* firing is witnessed precisely by
/// the absence of any newly-created metavariable. (The pre-existing structural
/// dispatch may still touch the bare flex heads — that is unrelated to the
/// intersection rule, which is what this test pins.)
#[test]
fn test_miller_flex_flex_intersection_non_pattern_defers() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);
    let y = ctx.push(Name::from_string("y"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    // ?m has a repeated argument (x x) ⇒ not a pattern.
    let m = state.fresh_with_locals(
        Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
        vec![("x".to_string(), x, nat.clone())],
    );
    let n = state.fresh_with_locals(
        Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
        vec![
            ("x".to_string(), x, nat.clone()),
            ("y".to_string(), y, nat.clone()),
        ],
    );
    let metas_before = state.iter().count();

    // `?m x x =?= ?n x y`: ?m's arg list repeats x ⇒ not a pattern, so the
    // intersection rule must not fire (no fresh ?h created).
    let lhs = Expr::apps(meta_expr(m), [Expr::fvar(x), Expr::fvar(x)]);
    let rhs = Expr::apps(meta_expr(n), [Expr::fvar(x), Expr::fvar(y)]);

    let _result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs, &rhs)
    };
    assert_eq!(
        state.iter().count(),
        metas_before,
        "non-pattern flex-flex must not fire the intersection rule (no fresh ?h)"
    );
    // ?m's non-pattern (repeated-arg) side may never be abstracted into an
    // intersection-shaped solution.
    assert!(
        !assigned_via_fresh_meta_body(&state, m),
        "?m must not receive an intersection-rule assignment"
    );
}

/// Same-head flex-flex still decomposes argument-wise even when the
/// intersection-rule code path is present: `?m x =?= ?m x` reduces to `x =?= x`
/// (success) with no lambda assignment to ?m.
#[test]
fn test_miller_flex_flex_intersection_same_head_still_decomposes() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    let m = state.fresh_with_locals(
        Expr::arrow(nat.clone(), nat.clone()),
        vec![("x".to_string(), x, nat.clone())],
    );

    // `?m x =?= ?m x`: same head, identical args ⇒ decompose to `x =?= x`,
    // which succeeds WITHOUT assigning ?m (congruence, not the intersection rule).
    let lhs = Expr::app(meta_expr(m), Expr::fvar(x));
    let rhs = Expr::app(meta_expr(m), Expr::fvar(x));

    let result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs, &rhs)
    };
    assert!(
        matches!(result, UnifyResult::Success),
        "?m x =?= ?m x should succeed via arg decomposition, got {result:?}"
    );
    assert!(
        !state.is_assigned(m),
        "same-head flex-flex must decompose, not assign ?m via the intersection rule"
    );
}

/// Occurs/scope edge: a non-pattern left side combined with a scope-blocked
/// right side must not fire the intersection rule. `?m x x =?= ?n z`, where
/// `?m`'s arguments repeat (not a pattern) and `?n`'s scope excludes `x`:
///
/// - the intersection rule cannot fire (`?m x x` is not a pattern), and
/// - the one-sided solve `?n := λ z. (?m x x)` is rejected by the scope check
///   (the free local `x` would escape `?n`'s scope).
///
/// So no fresh `?h` is ever created — exactly the conservative defer.
#[test]
fn test_miller_flex_flex_intersection_non_pattern_and_scope_blocked_defers() {
    let env = Environment::new();
    let mut ctx = LocalContext::new();
    let nat = Expr::const_str("Nat");
    let x = ctx.push(Name::from_string("x"), nat.clone(), BinderInfo::Default);
    let z = ctx.push(Name::from_string("z"), nat.clone(), BinderInfo::Default);

    let mut state = MetaState::new();
    // ?m's scope is {x}; it is applied to a repeated argument (x x).
    let m = state.fresh_with_locals(
        Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
        vec![("x".to_string(), x, nat.clone())],
    );
    // ?n's scope is only {z}; it deliberately does NOT contain x.
    let n = state.fresh_with_locals(
        Expr::arrow(nat.clone(), nat.clone()),
        vec![("z".to_string(), z, nat.clone())],
    );

    // `?m x x =?= ?n z`: left is non-pattern (repeated x); the only other
    // candidate, `?n := λ z. (?m x x)`, has free local x escaping ?n's scope.
    let lhs = Expr::apps(meta_expr(m), [Expr::fvar(x), Expr::fvar(x)]);
    let rhs = Expr::app(meta_expr(n), Expr::fvar(z));

    let metas_before = state.iter().count();
    let _result = {
        let mut unifier = Unifier::with_env(&mut state, &env, ctx);
        unifier.unify(&lhs, &rhs)
    };
    // The intersection rule cannot fire (left is non-pattern) and the one-sided
    // `?n := λ z. (?m x x)` is scope-blocked, so no fresh ?h is ever created.
    assert_eq!(
        state.iter().count(),
        metas_before,
        "non-pattern/scope-blocked flex-flex must not create a fresh ?h"
    );
    assert!(
        !assigned_via_fresh_meta_body(&state, m),
        "?m must not receive an intersection-rule assignment"
    );
    assert!(
        !assigned_via_fresh_meta_body(&state, n),
        "the scope check must block any λ-over-meta solve for ?n"
    );
}

// --- Max/IMax level-metavar unification (Miller-style slice) ---------------

/// `?v =?= max(u0, u1)`: the unassigned level metavar `?v` is assigned the
/// `Max` expression, and the resulting `Sort(max(u0, u1))` term kernel-checks.
#[test]
fn test_unify_levels_meta_assigned_to_max() {
    let mut state = MetaState::new();
    let v_name = Name::from_string("?v");
    let v = Level::param(v_name.clone());
    let u0 = Level::param(Name::from_string("u0"));
    let u1 = Level::param(Name::from_string("u1"));
    let max = Level::max(u0, u1);

    {
        let mut unifier = Unifier::new(&mut state);
        let result = unifier.unify_levels(&v, &max);
        assert!(
            matches!(result, UnifyResult::Success),
            "?v =?= max(u0, u1) should assign ?v, got {result:?}"
        );
    }

    // ?v now resolves to max(u0, u1).
    assert_eq!(
        state.instantiate_level(&v),
        max,
        "?v should resolve to max(u0, u1) after assignment"
    );

    // The instantiated term Sort(max(u0, u1)) kernel-checks: a Sort over a
    // well-formed (parametric) level is a valid type.
    let env = Environment::new();
    let tc = clean_kernel::TypeChecker::with_context(&env, LocalContext::new());
    let sort = Expr::sort(state.instantiate_level(&v));
    assert!(
        tc.infer_type(&sort).is_ok(),
        "Sort(max(u0, u1)) should kernel-type-check after the level assignment"
    );
}

/// Commutative case: `max(u0, u1) =?= ?v` assigns `?v` just like the
/// metavar-on-the-left orientation.
#[test]
fn test_unify_levels_max_assigned_to_meta_commutative() {
    let mut state = MetaState::new();
    let v_name = Name::from_string("?v");
    let v = Level::param(v_name);
    let u0 = Level::param(Name::from_string("u0"));
    let u1 = Level::param(Name::from_string("u1"));
    let max = Level::max(u0, u1);

    {
        let mut unifier = Unifier::new(&mut state);
        let result = unifier.unify_levels(&max, &v);
        assert!(
            matches!(result, UnifyResult::Success),
            "max(u0, u1) =?= ?v should assign ?v, got {result:?}"
        );
    }

    assert_eq!(
        state.instantiate_level(&v),
        max,
        "commutative orientation should assign ?v to max(u0, u1)"
    );
}

/// `?v =?= imax(u0, u1)`: IMax is handled the same way as Max.
#[test]
fn test_unify_levels_meta_assigned_to_imax() {
    let mut state = MetaState::new();
    let v_name = Name::from_string("?v");
    let v = Level::param(v_name);
    // Use distinct parametric children so imax does not reduce to a Max/0.
    let u0 = Level::param(Name::from_string("u0"));
    let u1 = Level::param(Name::from_string("u1"));
    // imax(u0, u1) with distinct parametric children does not reduce (u1 is
    // not statically nonzero), so the smart constructor yields a literal IMax.
    let imax = Level::imax(u0, u1);
    assert!(
        matches!(imax, Level::IMax(_, _)),
        "imax(u0, u1) over distinct params should stay an IMax, got {imax:?}"
    );

    {
        let mut unifier = Unifier::new(&mut state);
        let result = unifier.unify_levels(&v, &imax);
        assert!(
            matches!(result, UnifyResult::Success),
            "?v =?= imax(u0, u1) should assign ?v, got {result:?}"
        );
    }

    assert_eq!(
        state.instantiate_level(&v),
        imax,
        "?v should resolve to imax(u0, u1) after assignment"
    );
}

/// Occurs-check: `?v =?= max(?v, u0)` must NOT assign `?v` (the metavar occurs
/// in the expression) — it defers/fails instead.
#[test]
fn test_unify_levels_meta_occurs_in_max_defers() {
    let mut state = MetaState::new();
    let v_name = Name::from_string("?v");
    let v = Level::param(v_name.clone());
    let u0 = Level::param(Name::from_string("u0"));
    // max(?v, u0) with distinct params yields a literal Max containing ?v.
    let max_with_v = Level::max(v.clone(), u0);
    assert!(
        matches!(max_with_v, Level::Max(_, _)),
        "max(?v, u0) over distinct params should stay a Max, got {max_with_v:?}"
    );

    {
        let mut unifier = Unifier::new(&mut state);
        let result = unifier.unify_levels(&v, &max_with_v);
        assert!(
            matches!(result, UnifyResult::Failure(_)),
            "?v =?= max(?v, u0) must fail the level occurs-check, got {result:?}"
        );
    }

    // No assignment should have been recorded: ?v still resolves to itself.
    assert_eq!(
        state.instantiate_level(&v),
        v,
        "occurs-check failure must not assign ?v"
    );
    assert!(
        state.get_level_constraint(&v_name).is_none(),
        "occurs-check failure must not record a level constraint for ?v"
    );
}

/// `max =?= max` with NO metavar head still uses the conservative
/// normalize + is_def_eq path (unchanged behavior). `max(u0, u1)` and
/// `max(u1, u0)` are definitionally equal.
#[test]
fn test_unify_levels_max_vs_max_uses_def_eq_unchanged() {
    let mut state = MetaState::new();
    let u0 = Level::param(Name::from_string("u0"));
    let u1 = Level::param(Name::from_string("u1"));
    // Structurally distinct Max nodes (different argument order) that are
    // definitionally equal by commutativity after normalization.
    let max_ab = Level::max(u0.clone(), u1.clone());
    let max_ba = Level::max(u1, u0);
    assert_ne!(
        max_ab, max_ba,
        "the two Max nodes must be structurally distinct"
    );

    let mut unifier = Unifier::new(&mut state);
    let result = unifier.unify_levels(&max_ab, &max_ba);
    assert!(
        matches!(result, UnifyResult::Success),
        "max(u0, u1) =?= max(u1, u0) should hold by def_eq (commutativity), got {result:?}"
    );
}

/// Regression: ordinary Param/Succ level unification is unchanged. The
/// metavar-vs-Max arms must not perturb the existing param/concrete and
/// Succ/Succ paths.
#[test]
fn test_unify_levels_param_succ_paths_unchanged() {
    // Param =?= concrete: assigns.
    {
        let mut state = MetaState::new();
        let u0 = Level::param(Name::from_string("u_0"));
        let mut unifier = Unifier::new(&mut state);
        let result = unifier.unify_levels(&u0, &Level::succ(Level::zero()));
        assert!(matches!(result, UnifyResult::Success));
        drop(unifier);
        assert_eq!(state.instantiate_level(&u0), Level::succ(Level::zero()));
    }
    // Succ =?= Succ: unifies inner levels (param assigned to zero).
    {
        let mut state = MetaState::new();
        let u0 = Level::param(Name::from_string("u_0"));
        let lhs = Level::succ(u0.clone());
        let rhs = Level::succ(Level::zero());
        let mut unifier = Unifier::new(&mut state);
        let result = unifier.unify_levels(&lhs, &rhs);
        assert!(matches!(result, UnifyResult::Success));
        drop(unifier);
        assert_eq!(state.instantiate_level(&u0), Level::zero());
    }
    // Param =?= Param: unions (both resolve to the same representative).
    {
        let mut state = MetaState::new();
        let u0 = Level::param(Name::from_string("u_0"));
        let u1 = Level::param(Name::from_string("u_1"));
        let mut unifier = Unifier::new(&mut state);
        let result = unifier.unify_levels(&u0, &u1);
        assert!(matches!(result, UnifyResult::Success));
        drop(unifier);
        assert_eq!(state.instantiate_level(&u0), state.instantiate_level(&u1));
    }
}
