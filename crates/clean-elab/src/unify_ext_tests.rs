// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended unification (Miller patterns, postponed constraints, etc.)

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, Level};

use crate::unify::{MetaId, MetaState, UnifyResult};
use crate::unify_ext::{TraceKind, UnifyExt, UnifyExtConfig};

/// Helper: create a meta expression from a MetaId.
fn meta_expr(_state: &MetaState, id: MetaId) -> Expr {
    Expr::fvar(MetaState::to_fvar(id))
}

/// Helper: check if unification succeeded.
fn is_success(result: &UnifyResult) -> bool {
    matches!(result, UnifyResult::Success)
}

/// Helper: check if unification failed.
fn is_failure(result: &UnifyResult) -> bool {
    matches!(result, UnifyResult::Failure(_))
}

/// Helper: check if unification is stuck.
fn is_stuck(result: &UnifyResult) -> bool {
    matches!(result, UnifyResult::Stuck)
}

// ============================================================================
// Miller pattern unification
// ============================================================================

#[test]
fn test_miller_pattern_simple_bvar_arg() {
    // ?m (BVar 0) = Prop  =>  ?m := fun _ => Prop
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let lhs = Expr::app(meta_expr(&metas, m), Expr::bvar(0));
    let rhs = Expr::prop();

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(is_success(&result), "Miller pattern should succeed");
    assert!(metas.is_assigned(m), "meta should be assigned");
}

#[test]
fn test_miller_pattern_two_distinct_bvars() {
    // ?m (BVar 0) (BVar 1) = BVar 0  =>  ?m := fun x y => x
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let inner = Expr::app(meta_expr(&metas, m), Expr::bvar(0));
    let lhs = Expr::app(inner, Expr::bvar(1));
    let rhs = Expr::bvar(0);

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(
        is_success(&result),
        "Miller pattern with 2 args should succeed"
    );
    assert!(metas.is_assigned(m));
}

#[test]
fn test_miller_pattern_duplicate_bvars_not_pattern() {
    // ?m (BVar 0) (BVar 0) is NOT a Miller pattern (duplicate args)
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let m2 = metas.fresh(Expr::type_()); // rhs has a meta => should get stuck
    let inner = Expr::app(meta_expr(&metas, m), Expr::bvar(0));
    let lhs = Expr::app(inner, Expr::bvar(0));
    let rhs = meta_expr(&metas, m2);

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(
        is_stuck(&result),
        "Duplicate bvars with meta rhs should be stuck"
    );
}

#[test]
fn test_miller_pattern_non_bvar_args_fallthrough() {
    // ?m (Const "a") = Prop => not a Miller pattern, commits via a
    // constant imitation `?m := fun _ => Prop`. Closed in Wave 88.
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let lhs = Expr::app(meta_expr(&metas, m), Expr::const_str("a"));
    let rhs = Expr::prop();

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(
        is_success(&result),
        "non-bvar args with meta-free rhs should commit a constant \
         imitation, got {result:?}",
    );
    assert!(metas.is_assigned(m), "meta should be assigned");
}

#[test]
fn test_miller_pattern_non_bvar_args_meta_rhs_stays_stuck() {
    // ?m (Const "a") = ?n  =>  rhs has a meta, so the non-pattern
    // imitation MUST NOT fire (committing here could mask the real
    // higher-order constraint). The unifier must postpone and report
    // Stuck. Negative guard for the Wave-88 constant-imitation path.
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let n = metas.fresh(Expr::type_());
    let lhs = Expr::app(meta_expr(&metas, m), Expr::const_str("a"));
    let rhs = meta_expr(&metas, n);

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(
        is_stuck(&result),
        "non-bvar args with a meta rhs must remain Stuck (not commit \
         a spurious imitation), got {result:?}",
    );
    assert!(
        !metas.is_assigned(m),
        "meta ?m must remain unassigned when the imitation would be unsound",
    );
}

// ============================================================================
// Occurs check
// ============================================================================

#[test]
fn test_occurs_check_direct_cycle() {
    // ?m = ?m should succeed (identity)
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let lhs = meta_expr(&metas, m);
    let rhs = meta_expr(&metas, m);

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(is_success(&result), "Self-unification should succeed");
}

#[test]
fn test_occurs_check_nested_cycle() {
    // ?m = App(?m, Prop) should fail (occurs check)
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let lhs = meta_expr(&metas, m);
    let rhs = Expr::app(meta_expr(&metas, m), Expr::prop());

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(is_failure(&result), "Nested occurs check should fail");
}

#[test]
fn test_occurs_check_no_cycle() {
    // ?m = Prop should succeed
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let lhs = meta_expr(&metas, m);
    let rhs = Expr::prop();

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(is_success(&result), "No-cycle assignment should succeed");
    assert_eq!(metas.get_assignment(m).unwrap(), &Expr::prop());
}

// ============================================================================
// Definitional equality with unfolding
// ============================================================================

#[test]
fn test_def_eq_identical_exprs() {
    let mut metas = MetaState::new();
    let a = Expr::const_str("Nat");
    let b = Expr::const_str("Nat");

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&a, &b);
    assert!(is_success(&result));
}

#[test]
fn test_def_eq_different_consts() {
    let mut metas = MetaState::new();
    let a = Expr::const_str("Nat");
    let b = Expr::const_str("Bool");

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&a, &b);
    assert!(is_failure(&result));
}

#[test]
fn test_def_eq_sort_levels() {
    // Sort(Zero) vs Sort(Zero)
    let mut metas = MetaState::new();
    let a = Expr::sort(Level::zero());
    let b = Expr::sort(Level::zero());

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&a, &b);
    assert!(is_success(&result));
}

#[test]
fn test_def_eq_sort_level_mismatch() {
    // Sort(Zero) vs Sort(Succ(Zero))
    let mut metas = MetaState::new();
    let a = Expr::sort(Level::zero());
    let b = Expr::sort(Level::succ(Level::zero()));

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&a, &b);
    assert!(is_failure(&result));
}

// ============================================================================
// Universe level unification
// ============================================================================

#[test]
fn test_level_param_to_concrete() {
    let mut metas = MetaState::new();
    let u = Name::from_string("u_test");

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify_levels(&Level::param(u.clone()), &Level::zero());
    assert!(is_success(&result));
    let resolved = metas.instantiate_level(&Level::param(u));
    assert_eq!(resolved, Level::zero());
}

#[test]
fn test_level_param_to_param() {
    let mut metas = MetaState::new();
    let u1 = Name::from_string("u1");
    let u2 = Name::from_string("u2");

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify_levels(&Level::param(u1.clone()), &Level::param(u2.clone()));
    assert!(is_success(&result));
}

#[test]
fn test_level_succ_unification() {
    let mut metas = MetaState::new();
    let u = Name::from_string("u_succ");

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify_levels(
        &Level::succ(Level::param(u.clone())),
        &Level::succ(Level::zero()),
    );
    assert!(is_success(&result));
    let resolved = metas.instantiate_level(&Level::param(u));
    assert_eq!(resolved, Level::zero());
}

#[test]
fn test_level_concrete_mismatch() {
    let mut metas = MetaState::new();
    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify_levels(&Level::zero(), &Level::succ(Level::zero()));
    assert!(is_failure(&result));
}

#[test]
fn test_level_param_to_succ() {
    // u = Succ(Zero) should constrain u
    let mut metas = MetaState::new();
    let u = Name::from_string("u_ps");

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify_levels(&Level::param(u.clone()), &Level::succ(Level::zero()));
    assert!(is_success(&result));
}

// ============================================================================
// Postponed constraint processing
// ============================================================================

#[test]
fn test_postponed_resolved_by_later_assignment() {
    // ?m1 =?= ?m2, then assign ?m2 := Prop, process postponed => success
    let mut metas = MetaState::new();
    let m1 = metas.fresh(Expr::type_());
    let m2 = metas.fresh(Expr::type_());

    let lhs = meta_expr(&metas, m1);
    let rhs = meta_expr(&metas, m2);

    let mut ext = UnifyExt::with_defaults(&mut metas);
    // This will assign one to the other via structural unification
    let result = ext.unify(&lhs, &rhs);
    assert!(
        is_success(&result),
        "Two metas should assign one to the other"
    );
}

#[test]
fn test_postponed_queue_empty_initially() {
    let mut metas = MetaState::new();
    let ext = UnifyExt::with_defaults(&mut metas);
    assert_eq!(ext.postponed_count(), 0);
}

#[test]
fn test_postponed_process_empty_queue() {
    let mut metas = MetaState::new();
    let mut ext = UnifyExt::with_defaults(&mut metas);
    assert!(ext.process_postponed());
}

#[test]
fn test_postponed_constraint_stuck_then_resolved() {
    // Create a constraint that gets stuck, then solve it
    let mut metas = MetaState::new();
    let m1 = metas.fresh(Expr::type_());
    let m2 = metas.fresh(Expr::type_());

    // ?m1(BVar(0)) (BVar(0)) =?= ?m2 — duplicate bvar means non-pattern, stuck
    let inner = Expr::app(meta_expr(&metas, m1), Expr::bvar(0));
    let lhs = Expr::app(inner, Expr::bvar(0));
    let rhs = meta_expr(&metas, m2);

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(is_stuck(&result));
    assert!(
        ext.postponed_count() > 0,
        "Should have postponed constraints"
    );
}

// ============================================================================
// Constraint simplification
// ============================================================================

#[test]
fn test_simplify_already_equal() {
    let mut metas = MetaState::new();
    let a = Expr::const_str("X");
    let b = Expr::const_str("X");

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&a, &b);
    assert!(is_success(&result));
}

#[test]
fn test_simplify_through_meta_instantiation() {
    // ?m = Nat, then Nat = ?m => should succeed
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let nat = Expr::const_str("Nat");

    let me = meta_expr(&metas, m);
    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&me, &nat);
    assert!(is_success(&result));

    // Now unify Nat with ?m (which is now Nat)
    let result2 = ext.unify(&nat, &me);
    assert!(is_success(&result2));
}

// ============================================================================
// First-order approximation
// ============================================================================

#[test]
fn test_first_order_approx_matching_heads() {
    // ?m X = f X where f is known => ?m := f
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let f = Expr::const_str("f");
    let x = Expr::const_str("X");

    let lhs = Expr::app(meta_expr(&metas, m), x.clone());
    let rhs = Expr::app(f.clone(), x.clone());

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(is_success(&result), "First-order approx should match heads");
    assert!(metas.is_assigned(m));
}

#[test]
fn test_first_order_approx_arity_mismatch() {
    // ?m X Y = f X => different arity, should fail
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let f = Expr::const_str("f");
    let x = Expr::const_str("X");
    let y = Expr::const_str("Y");

    let inner = Expr::app(meta_expr(&metas, m), x.clone());
    let lhs = Expr::app(inner, y);
    let rhs = Expr::app(f, x);

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    // Falls through to structural which will fail
    assert!(is_failure(&result) || is_stuck(&result));
}

#[test]
fn test_first_order_disabled_in_config() {
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let f = Expr::const_str("f");
    let x = Expr::const_str("X");

    let lhs = Expr::app(meta_expr(&metas, m), x.clone());
    let rhs = Expr::app(f, x);

    let config = UnifyExtConfig {
        first_order_approx: false,
        ..UnifyExtConfig::default()
    };
    let mut ext = UnifyExt::new(&mut metas, config);
    let result = ext.unify(&lhs, &rhs);
    // Without first-order approx the structural unifier handles it
    // (meta on lhs head gets assigned via decompose)
    assert!(!is_stuck(&result));
}

// ============================================================================
// Trace generation
// ============================================================================

#[test]
fn test_trace_enabled_records_entries() {
    let mut metas = MetaState::new();
    let config = UnifyExtConfig {
        trace_enabled: true,
        ..UnifyExtConfig::default()
    };
    let a = Expr::const_str("A");
    let b = Expr::const_str("A");

    let mut ext = UnifyExt::new(&mut metas, config);
    let result = ext.unify(&a, &b);
    assert!(is_success(&result));
    assert!(!ext.trace().is_empty(), "Trace should have entries");
    assert_eq!(ext.trace()[0].kind, TraceKind::Attempt);
    assert_eq!(ext.trace()[1].kind, TraceKind::Success);
}

#[test]
fn test_trace_disabled_no_entries() {
    let mut metas = MetaState::new();
    let config = UnifyExtConfig {
        trace_enabled: false,
        ..UnifyExtConfig::default()
    };
    let a = Expr::const_str("A");
    let b = Expr::const_str("A");

    let mut ext = UnifyExt::new(&mut metas, config);
    let result = ext.unify(&a, &b);
    assert!(is_success(&result));
    assert!(
        ext.trace().is_empty(),
        "Trace should be empty when disabled"
    );
}

#[test]
fn test_trace_records_miller_assign() {
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let config = UnifyExtConfig {
        trace_enabled: true,
        ..UnifyExtConfig::default()
    };
    let lhs = Expr::app(meta_expr(&metas, m), Expr::bvar(0));
    let rhs = Expr::prop();

    let mut ext = UnifyExt::new(&mut metas, config);
    let result = ext.unify(&lhs, &rhs);
    assert!(is_success(&result));
    let has_miller = ext
        .trace()
        .iter()
        .any(|e| e.kind == TraceKind::MillerAssign);
    assert!(has_miller, "Trace should contain MillerAssign entry");
}

// ============================================================================
// Eta expansion cases
// ============================================================================

#[test]
fn test_eta_expand_lam_vs_non_lam() {
    // fun x => f x  should unify with f via eta
    let mut metas = MetaState::new();
    let f = Expr::const_str("f");
    // lam (Default) Prop (App f (BVar 0))  ~ eta-expands to match f
    let lam = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::app(f.clone(), Expr::bvar(0)),
    );

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lam, &f);
    assert!(
        is_success(&result),
        "Eta expansion should make lam=f succeed"
    );
}

#[test]
fn test_eta_expand_symmetric() {
    // f vs fun x => f x
    let mut metas = MetaState::new();
    let f = Expr::const_str("g");
    let lam = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::app(f.clone(), Expr::bvar(0)),
    );

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&f, &lam);
    assert!(is_success(&result), "Eta expansion should be symmetric");
}

#[test]
fn test_eta_disabled_in_config() {
    let mut metas = MetaState::new();
    let f = Expr::const_str("h");
    let lam = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::app(f.clone(), Expr::bvar(0)),
    );
    let config = UnifyExtConfig {
        eta_expansion: false,
        ..UnifyExtConfig::default()
    };
    let mut ext = UnifyExt::new(&mut metas, config);
    let result = ext.unify(&lam, &f);
    assert!(is_failure(&result), "Without eta, lam vs const should fail");
}

// ============================================================================
// Stuck constraints
// ============================================================================

#[test]
fn test_stuck_report_none_when_empty() {
    let mut metas = MetaState::new();
    let ext = UnifyExt::with_defaults(&mut metas);
    assert!(ext.stuck_report().is_none());
}

#[test]
fn test_stuck_report_with_constraints() {
    let mut metas = MetaState::new();
    let m1 = metas.fresh(Expr::type_());
    let m2 = metas.fresh(Expr::type_());
    // Force a stuck state via non-pattern args
    let inner = Expr::app(meta_expr(&metas, m1), Expr::bvar(0));
    let lhs = Expr::app(inner, Expr::bvar(0));
    let rhs = meta_expr(&metas, m2);

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let _ = ext.unify(&lhs, &rhs);
    let report = ext.stuck_report();
    assert!(report.is_some(), "Should have a stuck report");
    assert!(report.unwrap().contains("stuck constraints"));
}

// ============================================================================
// Edge cases
// ============================================================================

#[test]
fn test_identity_unification() {
    let mut metas = MetaState::new();
    let e = Expr::app(Expr::const_str("f"), Expr::const_str("x"));

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&e, &e);
    assert!(is_success(&result));
}

#[test]
fn test_already_assigned_metavar() {
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    metas.assign(m, Expr::prop());

    let lhs = meta_expr(&metas, m);
    let rhs = Expr::prop();

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(
        is_success(&result),
        "Already-assigned meta should unify with its value"
    );
}

#[test]
fn test_already_assigned_metavar_conflict() {
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    metas.assign(m, Expr::prop());

    let lhs = meta_expr(&metas, m);
    let rhs = Expr::type_();

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    // Prop vs Type => should fail
    assert!(is_failure(&result), "Conflicting assignment should fail");
}

#[test]
fn test_nested_metavar_assignment() {
    // ?m1 = ?m2, ?m2 = Prop => ?m1 resolves to Prop
    let mut metas = MetaState::new();
    let m1 = metas.fresh(Expr::type_());
    let m2 = metas.fresh(Expr::type_());

    let me1 = meta_expr(&metas, m1);
    let me2 = meta_expr(&metas, m2);
    let mut ext = UnifyExt::with_defaults(&mut metas);
    let r1 = ext.unify(&me1, &me2);
    assert!(is_success(&r1));

    let r2 = ext.unify(&me2, &Expr::prop());
    assert!(is_success(&r2));
    drop(ext);

    let resolved = metas.instantiate(&me1);
    assert_eq!(resolved, Expr::prop());
}

#[test]
fn test_pi_unification() {
    // Pi(Default, Prop, Prop) = Pi(Default, Prop, Prop)
    let mut metas = MetaState::new();
    let pi1 = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());
    let pi2 = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&pi1, &pi2);
    assert!(is_success(&result));
}

#[test]
fn test_pi_binder_info_mismatch_unifies_like_lean_isdefeq() {
    // BinderInfo is elaboration metadata, not term structure: Lean 4's
    // `isDefEq` and Clean's kernel defeq (`tc/def_eq/binding.rs`) both treat
    // `(x : A) → B` and `{x : A} → B` as definitionally equal, so the
    // unifier must too (Brick P1 — unblocks higher-kinded class heads over
    // the prelude's `{α : Type u} → Type u`-spelled `Option`/`List`).
    let mut metas = MetaState::new();
    let pi1 = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());
    let pi2 = Expr::pi(BinderInfo::Implicit, Expr::prop(), Expr::prop());

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&pi1, &pi2);
    assert!(
        is_success(&result),
        "binder-info-only Pi differences must unify (Lean isDefEq parity)"
    );
}

#[test]
fn test_app_unification_recursive() {
    // App(f, x) = App(f, y) where ?m = x and y = ?m
    let mut metas = MetaState::new();
    let m = metas.fresh(Expr::type_());
    let f = Expr::const_str("f");
    let x = Expr::const_str("x");

    let lhs = Expr::app(f.clone(), meta_expr(&metas, m));
    let rhs = Expr::app(f, x.clone());

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&lhs, &rhs);
    assert!(is_success(&result));
    assert_eq!(metas.get_assignment(m).unwrap(), &x);
}

#[test]
fn test_bvar_mismatch() {
    let mut metas = MetaState::new();
    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&Expr::bvar(0), &Expr::bvar(1));
    assert!(is_failure(&result));
}

#[test]
fn test_config_default_values() {
    let config = UnifyExtConfig::default();
    assert_eq!(config.max_simplify_passes, 10);
    assert!(config.eta_expansion);
    assert!(config.first_order_approx);
    assert!(!config.trace_enabled);
    assert_eq!(config.max_postponed, 256);
}

#[test]
fn test_const_with_levels_match() {
    let mut metas = MetaState::new();
    let u = Name::from_string("u_c");
    let a = Expr::const_(Name::from_string("List"), vec![Level::param(u.clone())]);
    let b = Expr::const_(Name::from_string("List"), vec![Level::zero()]);

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&a, &b);
    assert!(is_success(&result));
    let resolved = metas.instantiate_level(&Level::param(u));
    assert_eq!(resolved, Level::zero());
}

#[test]
fn test_const_name_mismatch_with_levels() {
    let mut metas = MetaState::new();
    let a = Expr::const_(Name::from_string("List"), vec![Level::zero()]);
    let b = Expr::const_(Name::from_string("Array"), vec![Level::zero()]);

    let mut ext = UnifyExt::with_defaults(&mut metas);
    let result = ext.unify(&a, &b);
    assert!(is_failure(&result));
}
