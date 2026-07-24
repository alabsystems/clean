// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended metavariable management (`meta_ext`).

use clean_kernel::expr::BinderInfo;
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

use crate::meta_ext::*;
use crate::unify::{MetaId, MetaState};

fn mk_fvar(id: u64) -> (FVarId, Expr) {
    let fv = FVarId::new(id);
    (fv, Expr::fvar(fv))
}

fn mk_local(name: &str, id: u64) -> (Name, FVarId, Expr) {
    let fv = FVarId::new(id);
    (Name::from_string(name), fv, Expr::type_())
}

// -- Config -----------------------------------------------------------------

#[test]
fn test_config_default_values() {
    let cfg = MetaExtConfig::default();
    assert_eq!(cfg.max_metas, 10_000);
    assert_eq!(cfg.solve_budget, 100_000);
    assert!(cfg.validate_on_assign);
}

#[test]
fn test_config_custom_values() {
    let cfg = MetaExtConfig {
        max_metas: 5,
        solve_budget: 10,
        validate_on_assign: false,
    };
    assert_eq!(cfg.max_metas, 5);
    assert_eq!(cfg.solve_budget, 10);
    assert!(!cfg.validate_on_assign);
}

// -- Creation with context --------------------------------------------------

#[test]
fn test_create_with_empty_context() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx
        .create_with_context(Expr::type_(), vec![])
        .expect("create");
    assert_eq!(ctx.stats().created, 1);
    assert!(ctx.local_context(id).expect("ctx").is_empty());
}

#[test]
fn test_create_with_locals() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let locals = vec![mk_local("x", 1), mk_local("y", 2)];
    let id = ctx
        .create_with_context(Expr::type_(), locals)
        .expect("create");
    let lc = ctx.local_context(id).expect("ctx");
    assert_eq!(lc.len(), 2);
    assert_eq!(lc[0].0.to_string(), "x");
}

#[test]
fn test_create_hits_limit() {
    let mut ms = MetaState::new();
    let cfg = MetaExtConfig {
        max_metas: 2,
        ..Default::default()
    };
    let mut ctx = MetaExtCtx::with_config(&mut ms, cfg);
    ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    let err = ctx.create_with_context(Expr::type_(), vec![]).unwrap_err();
    assert!(matches!(
        err,
        MetaExtError::CreationLimitReached { limit: 2 }
    ));
}

// -- Synthetic metavariables ------------------------------------------------

#[test]
fn test_create_synthetic_placeholder() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx
        .create_synthetic(Expr::type_(), SyntheticKind::Placeholder, vec![])
        .unwrap();
    assert_eq!(ctx.synthetic_kind(id), Some(SyntheticKind::Placeholder));
}

#[test]
fn test_create_synthetic_typeclass() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx
        .create_synthetic(Expr::prop(), SyntheticKind::TypeClass, vec![])
        .unwrap();
    assert_eq!(ctx.synthetic_kind(id), Some(SyntheticKind::TypeClass));
}

#[test]
fn test_create_synthetic_tactic() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx
        .create_synthetic(Expr::prop(), SyntheticKind::Tactic, vec![])
        .unwrap();
    assert_eq!(ctx.synthetic_kind(id), Some(SyntheticKind::Tactic));
}

#[test]
fn test_non_synthetic_returns_none() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    assert_eq!(ctx.synthetic_kind(id), None);
}

// -- Validated assignment ---------------------------------------------------

#[test]
fn test_assign_checked_success() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    ctx.assign_checked(id, Expr::prop()).expect("assign");
    assert_eq!(ctx.stats().assigned, 1);
}

#[test]
fn test_assign_checked_not_found() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let err = ctx.assign_checked(MetaId(99), Expr::prop()).unwrap_err();
    assert!(matches!(err, MetaExtError::NotFound(99)));
}

#[test]
fn test_assign_checked_already_assigned() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    ctx.assign_checked(id, Expr::prop()).unwrap();
    let err = ctx.assign_checked(id, Expr::type_()).unwrap_err();
    assert!(matches!(err, MetaExtError::AlreadyAssigned(_)));
}

#[test]
fn test_assign_checked_escaping_local() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let locals = vec![mk_local("x", 1)];
    let id = ctx.create_with_context(Expr::type_(), locals).unwrap();
    // Assign a value that references fvar(2) which is NOT in the local context
    let (_, bad_fvar_expr) = mk_fvar(2);
    let err = ctx.assign_checked(id, bad_fvar_expr).unwrap_err();
    assert!(matches!(err, MetaExtError::EscapingLocal { .. }));
}

#[test]
fn test_assign_checked_allowed_local() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let locals = vec![mk_local("x", 1)];
    let id = ctx.create_with_context(Expr::type_(), locals).unwrap();
    let (_, good_fvar_expr) = mk_fvar(1);
    ctx.assign_checked(id, good_fvar_expr)
        .expect("should allow in-scope fvar");
}

#[test]
fn test_assign_checked_occurs_check() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    // Assign the meta to itself (as an fvar)
    let meta_fvar = Expr::fvar(MetaState::to_fvar(id));
    let err = ctx.assign_checked(id, meta_fvar).unwrap_err();
    assert!(matches!(err, MetaExtError::ValidationFailed { .. }));
}

// -- Delayed assignment -----------------------------------------------------

#[test]
fn test_assign_delayed_basic() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    ctx.assign_delayed(id, Expr::prop(), vec![]).unwrap();
    assert_eq!(ctx.delayed_count(), 1);
    assert_eq!(ctx.stats().delayed, 1);
}

#[test]
fn test_assign_delayed_not_found() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let err = ctx
        .assign_delayed(MetaId(99), Expr::prop(), vec![])
        .unwrap_err();
    assert!(matches!(err, MetaExtError::NotFound(99)));
}

#[test]
fn test_flush_delayed_immediate() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    ctx.assign_delayed(id, Expr::prop(), vec![]).unwrap();
    let errors = ctx.flush_delayed();
    assert!(errors.is_empty());
    assert_eq!(ctx.delayed_count(), 0);
    assert_eq!(ctx.stats().assigned, 1);
}

#[test]
fn test_flush_delayed_pending_fvar() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let dep_id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    let target_id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    let dep_fvar = MetaState::to_fvar(dep_id);
    ctx.assign_delayed(target_id, Expr::prop(), vec![dep_fvar])
        .unwrap();
    // First flush: dep is unresolved, so nothing happens
    let errors = ctx.flush_delayed();
    assert!(errors.is_empty());
    assert_eq!(ctx.delayed_count(), 1);
    // Resolve the dependency
    ctx.assign_checked(dep_id, Expr::type_()).unwrap();
    // Second flush: now the delayed assignment goes through
    let errors = ctx.flush_delayed();
    assert!(errors.is_empty());
    assert_eq!(ctx.delayed_count(), 0);
}

// -- Natural ordering -------------------------------------------------------

#[test]
fn test_natural_order_no_deps() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let _a = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    let _b = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    let order = ctx.natural_order();
    assert_eq!(order.len(), 2);
}

#[test]
fn test_natural_order_with_dependency() {
    let mut ms = MetaState::new();
    // Create m0 with type Type
    let m0 = ms.fresh(Expr::type_());
    // Create m1 whose type references m0
    let m0_fvar = Expr::fvar(MetaState::to_fvar(m0));
    let m1 = ms.fresh(m0_fvar);
    let ctx = MetaExtCtx::new(&mut ms);
    let order = ctx.natural_order();
    // m0 should come before m1 in the order
    let pos0 = order.iter().position(|&id| id == m0).expect("m0 in order");
    let pos1 = order.iter().position(|&id| id == m1).expect("m1 in order");
    assert!(pos0 < pos1, "m0 should come before m1");
}

#[test]
fn test_natural_order_empty() {
    let mut ms = MetaState::new();
    let ctx = MetaExtCtx::new(&mut ms);
    assert!(ctx.natural_order().is_empty());
}

// -- Scope checking ---------------------------------------------------------

#[test]
fn test_check_scope_ok() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let locals = vec![mk_local("x", 1)];
    let id = ctx.create_with_context(Expr::type_(), locals).unwrap();
    let (_, expr) = mk_fvar(1);
    ctx.check_scope(id, &expr)
        .expect("in-scope fvar should pass");
}

#[test]
fn test_check_scope_escaping() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let locals = vec![mk_local("x", 1)];
    let id = ctx.create_with_context(Expr::type_(), locals).unwrap();
    let (_, expr) = mk_fvar(2);
    let err = ctx.check_scope(id, &expr).unwrap_err();
    assert!(matches!(err, MetaExtError::EscapingLocal { fvar: 2, .. }));
}

#[test]
fn test_check_scope_meta_fvars_ignored() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    // Meta-encoded fvars should NOT trigger escaping check
    let meta_fvar = Expr::fvar(MetaState::to_fvar(id));
    ctx.check_scope(id, &meta_fvar)
        .expect("meta fvar should not escape");
}

// -- Abstraction ------------------------------------------------------------

#[test]
fn test_abstract_meta_empty_context() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    let result = ctx.abstract_meta(id, &Expr::prop()).unwrap();
    // No locals => body returned as-is
    assert_eq!(format!("{result:?}"), format!("{:?}", Expr::prop()));
}

#[test]
fn test_abstract_meta_single_local() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let locals = vec![mk_local("x", 1)];
    let id = ctx.create_with_context(Expr::type_(), locals).unwrap();
    let (_, body) = mk_fvar(1);
    let result = ctx.abstract_meta(id, &body).unwrap();
    // Should be: lam x : Type => #0
    let expected = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    assert_eq!(format!("{result:?}"), format!("{expected:?}"));
}

#[test]
fn test_abstract_meta_two_locals() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let locals = vec![mk_local("x", 1), mk_local("y", 2)];
    let id = ctx.create_with_context(Expr::type_(), locals).unwrap();
    // body = app(fvar(1), fvar(2))  ->  app(#1, #0) under [x, y]
    let (_, fx) = mk_fvar(1);
    let (_, fy) = mk_fvar(2);
    let body = Expr::app(fx, fy);
    let result = ctx.abstract_meta(id, &body).unwrap();
    let inner = Expr::app(Expr::bvar(1), Expr::bvar(0));
    let expected = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::type_(), inner),
    );
    assert_eq!(format!("{result:?}"), format!("{expected:?}"));
}

#[test]
fn test_abstract_meta_not_found() {
    let mut ms = MetaState::new();
    let ctx = MetaExtCtx::new(&mut ms);
    let err = ctx.abstract_meta(MetaId(99), &Expr::prop()).unwrap_err();
    assert!(matches!(err, MetaExtError::NotFound(99)));
}

// -- Statistics -------------------------------------------------------------

#[test]
fn test_stats_initial() {
    let mut ms = MetaState::new();
    let ctx = MetaExtCtx::new(&mut ms);
    let s = ctx.stats();
    assert_eq!(*s, MetaStats::default());
}

#[test]
fn test_stats_display() {
    let s = MetaStats {
        created: 3,
        assigned: 1,
        delayed: 2,
        solve_steps: 10,
    };
    let display = format!("{s}");
    assert!(display.contains("created=3"));
    assert!(display.contains("assigned=1"));
    assert!(display.contains("delayed=2"));
    assert!(display.contains("steps=10"));
}

#[test]
fn test_unresolved_count() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    assert_eq!(ctx.unresolved_count(), 1);
    ctx.assign_checked(id, Expr::prop()).unwrap();
    assert_eq!(ctx.unresolved_count(), 0);
}

// -- Pretty printing --------------------------------------------------------

#[test]
fn test_pretty_meta_unassigned() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx
        .create_with_context(Expr::type_(), vec![mk_local("x", 1)])
        .unwrap();
    let pretty = ctx.pretty_meta(id);
    assert!(pretty.contains("unassigned"));
    assert!(pretty.contains("natural"));
    assert!(pretty.contains("ctx=1"));
}

#[test]
fn test_pretty_meta_assigned() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    ctx.assign_checked(id, Expr::prop()).unwrap();
    let pretty = ctx.pretty_meta(id);
    assert!(pretty.contains("assigned"));
}

#[test]
fn test_pretty_meta_synthetic() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    let id = ctx
        .create_synthetic(Expr::type_(), SyntheticKind::TypeClass, vec![])
        .unwrap();
    let pretty = ctx.pretty_meta(id);
    assert!(pretty.contains("typeclass"));
}

#[test]
fn test_pretty_meta_not_found() {
    let mut ms = MetaState::new();
    let ctx = MetaExtCtx::new(&mut ms);
    let pretty = ctx.pretty_meta(MetaId(99));
    assert!(pretty.contains("not found"));
}

#[test]
fn test_pretty_all() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    ctx.create_with_context(Expr::type_(), vec![]).unwrap();
    ctx.create_synthetic(Expr::prop(), SyntheticKind::Tactic, vec![])
        .unwrap();
    let all = ctx.pretty_all();
    assert!(all.lines().count() >= 2);
}

// -- Budget / timeout -------------------------------------------------------

#[test]
fn test_tick_solve_within_budget() {
    let mut ms = MetaState::new();
    let mut ctx = MetaExtCtx::new(&mut ms);
    for _ in 0..100 {
        ctx.tick_solve().expect("within budget");
    }
    assert_eq!(ctx.stats().solve_steps, 100);
}

#[test]
fn test_tick_solve_exhausted() {
    let mut ms = MetaState::new();
    let cfg = MetaExtConfig {
        solve_budget: 3,
        ..Default::default()
    };
    let mut ctx = MetaExtCtx::with_config(&mut ms, cfg);
    ctx.tick_solve().unwrap();
    ctx.tick_solve().unwrap();
    ctx.tick_solve().unwrap();
    let err = ctx.tick_solve().unwrap_err();
    assert!(matches!(err, MetaExtError::BudgetExhausted { limit: 3 }));
}

#[test]
fn test_remaining_budget() {
    let mut ms = MetaState::new();
    let cfg = MetaExtConfig {
        solve_budget: 10,
        ..Default::default()
    };
    let mut ctx = MetaExtCtx::with_config(&mut ms, cfg);
    assert_eq!(ctx.remaining_budget(), 10);
    ctx.tick_solve().unwrap();
    assert_eq!(ctx.remaining_budget(), 9);
}

// -- Accessors --------------------------------------------------------------

#[test]
fn test_meta_state_accessor() {
    let mut ms = MetaState::new();
    ms.fresh(Expr::type_());
    let ctx = MetaExtCtx::new(&mut ms);
    assert_eq!(ctx.meta_state().iter().count(), 1);
}

#[test]
fn test_config_accessor() {
    let mut ms = MetaState::new();
    let cfg = MetaExtConfig {
        max_metas: 42,
        ..Default::default()
    };
    let ctx = MetaExtCtx::with_config(&mut ms, cfg);
    assert_eq!(ctx.config().max_metas, 42);
}
