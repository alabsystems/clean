// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended universe polymorphism module.

use clean_kernel::expr::BinderInfo;
use clean_kernel::{Expr, Level, Name};

use crate::universe_poly_ext::*;

fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn param(s: &str) -> Level {
    Level::param(name(s))
}
fn zero() -> Level {
    Level::zero()
}
fn succ(l: Level) -> Level {
    Level::succ(l)
}
fn one() -> Level {
    succ(zero())
}
fn two() -> Level {
    succ(one())
}
fn three() -> Level {
    succ(two())
}

// ── collect_universe_vars ────────────────────────────────────────────────

#[test]
fn test_collect_universe_vars_sort_param() {
    let expr = Expr::sort(param("u"));
    let vars = collect_universe_vars(&expr);
    assert_eq!(vars, vec![name("u")]);
}

#[test]
fn test_collect_universe_vars_sort_zero() {
    let expr = Expr::sort(zero());
    let vars = collect_universe_vars(&expr);
    assert!(vars.is_empty());
}

#[test]
fn test_collect_universe_vars_const_multi() {
    let expr = Expr::const_(name("List"), vec![param("u"), param("v")]);
    let vars = collect_universe_vars(&expr);
    assert_eq!(vars, vec![name("u"), name("v")]);
}

#[test]
fn test_collect_universe_vars_dedup_sorted() {
    // Same param in two places should appear once
    let inner = Expr::sort(param("u"));
    let expr = Expr::app(inner.clone(), inner);
    let vars = collect_universe_vars(&expr);
    assert_eq!(vars, vec![name("u")]);
}

#[test]
fn test_collect_universe_vars_pi() {
    let ty = Expr::sort(param("u"));
    let body = Expr::sort(param("v"));
    let expr = Expr::pi(BinderInfo::Default, ty, body);
    let vars = collect_universe_vars(&expr);
    assert_eq!(vars, vec![name("u"), name("v")]);
}

#[test]
fn test_collect_universe_vars_lambda() {
    let ty = Expr::sort(param("a"));
    let body = Expr::sort(param("b"));
    let expr = Expr::lam(BinderInfo::Default, ty, body);
    let vars = collect_universe_vars(&expr);
    assert_eq!(vars, vec![name("a"), name("b")]);
}

#[test]
fn test_collect_universe_vars_bvar() {
    let expr = Expr::bvar(0);
    let vars = collect_universe_vars(&expr);
    assert!(vars.is_empty());
}

// ── normalize_level_ext ──────────────────────────────────────────────────

#[test]
fn test_normalize_max_same() {
    let config = UniversePolyExtConfig::default();
    let level = Level::max(param("u"), param("u"));
    assert_eq!(normalize_level_ext(&level, &config), param("u"));
}

#[test]
fn test_normalize_max_zero_left() {
    let config = UniversePolyExtConfig::default();
    let level = Level::max(zero(), param("u"));
    assert_eq!(normalize_level_ext(&level, &config), param("u"));
}

#[test]
fn test_normalize_max_zero_right() {
    let config = UniversePolyExtConfig::default();
    let level = Level::max(param("u"), zero());
    assert_eq!(normalize_level_ext(&level, &config), param("u"));
}

#[test]
fn test_normalize_imax_zero_right() {
    let config = UniversePolyExtConfig::default();
    // imax(u, 0) = 0
    let level = Level::imax(param("u"), zero());
    assert_eq!(normalize_level_ext(&level, &config), zero());
}

#[test]
fn test_normalize_imax_succ_right() {
    let config = UniversePolyExtConfig::default();
    // imax(u, succ(v)) = max(u, succ(v))
    let level = Level::imax(param("u"), succ(param("v")));
    let result = normalize_level_ext(&level, &config);
    // Should be simplified as max
    assert_eq!(result, Level::max(param("u"), succ(param("v"))));
}

#[test]
fn test_normalize_max_succ_succ() {
    let config = UniversePolyExtConfig::default();
    // max(succ(u), succ(v)) -> succ(max(u, v))
    let level = Level::max(succ(param("u")), succ(param("v")));
    let result = normalize_level_ext(&level, &config);
    assert_eq!(result, succ(Level::max(param("u"), param("v"))));
}

#[test]
fn test_normalize_nested_max() {
    let config = UniversePolyExtConfig::default();
    // max(0, max(0, u)) -> u
    let inner = Level::max(zero(), param("u"));
    let level = Level::max(zero(), inner);
    assert_eq!(normalize_level_ext(&level, &config), param("u"));
}

#[test]
fn test_normalize_depth_limit() {
    let config = UniversePolyExtConfig {
        max_norm_depth: 2,
        ..Default::default()
    };
    // Build a chain deeper than the limit; should not panic
    let level = succ(succ(succ(param("u"))));
    let _ = normalize_level_ext(&level, &config);
}

#[test]
fn test_normalize_ground_levels() {
    let config = UniversePolyExtConfig::default();
    // max(1, 2) should normalize to 2
    let level = Level::max(one(), two());
    let result = normalize_level_ext(&level, &config);
    assert_eq!(result, two());
}

// ── cumulative subtyping ─────────────────────────────────────────────────

#[test]
fn test_universe_subtype_reflexive() {
    assert!(universe_subtype(&one(), &one()));
}

#[test]
fn test_universe_subtype_zero_leq_any() {
    assert!(universe_subtype(&zero(), &two()));
}

#[test]
fn test_universe_subtype_not_greater() {
    assert!(!universe_subtype(&two(), &one()));
}

#[test]
fn test_universe_strict_lt_basic() {
    // 0 < 1 means succ(0) <= 1, i.e., 1 <= 1
    assert!(universe_strict_lt(&zero(), &one()));
}

#[test]
fn test_universe_strict_lt_not_equal() {
    // 1 < 1 is false (succ(1) = 2, 2 <= 1 is false)
    assert!(!universe_strict_lt(&one(), &one()));
}

// ── UniverseMetaCtx ─────────────────────────────────────────────────────

#[test]
fn test_meta_ctx_fresh_generates_unique() {
    let mut ctx = UniverseMetaCtx::new();
    let m0 = ctx.fresh_meta();
    let m1 = ctx.fresh_meta();
    assert_ne!(m0, m1);
}

#[test]
fn test_meta_ctx_assign_and_lookup() {
    let mut ctx = UniverseMetaCtx::new();
    let n = name("_uext.0");
    ctx.assign(&n, one()).unwrap();
    assert_eq!(ctx.get_assignment(&n), Some(&one()));
}

#[test]
fn test_meta_ctx_cyclic_assignment_rejected() {
    let mut ctx = UniverseMetaCtx::new();
    let n = name("u");
    let cyclic = succ(param("u"));
    let result = ctx.assign(&n, cyclic);
    assert!(result.is_err());
}

#[test]
fn test_meta_ctx_apply_assignments() {
    let mut ctx = UniverseMetaCtx::new();
    ctx.assign(&name("u"), one()).unwrap();
    let level = succ(param("u"));
    let result = ctx.apply_assignments(&level);
    assert_eq!(result, two());
}

#[test]
fn test_meta_ctx_solve_simple() {
    let mut ctx = UniverseMetaCtx::new();
    // u = 1
    ctx.add_eq_constraint(param("u"), one());
    let solution = ctx.solve().unwrap();
    assert_eq!(solution.get(&name("u")), Some(&one()));
}

#[test]
fn test_meta_ctx_solve_chain() {
    let mut ctx = UniverseMetaCtx::new();
    // u = v, v = 1 => u = 1 (via second-pass substitution)
    ctx.add_eq_constraint(param("u"), param("v"));
    ctx.add_eq_constraint(param("v"), one());
    let solution = ctx.solve().unwrap();
    assert_eq!(solution.get(&name("v")), Some(&one()));
    // u was bound to param("v"), which then gets substituted
    assert!(solution.contains_key(&name("u")));
}

#[test]
fn test_meta_ctx_solve_cyclic_error() {
    let mut ctx = UniverseMetaCtx::new();
    // u = succ(u) is cyclic
    ctx.add_eq_constraint(param("u"), succ(param("u")));
    assert!(ctx.solve().is_err());
}

#[test]
fn test_meta_ctx_assignment_count() {
    let mut ctx = UniverseMetaCtx::new();
    assert_eq!(ctx.assignment_count(), 0);
    ctx.assign(&name("u"), zero()).unwrap();
    assert_eq!(ctx.assignment_count(), 1);
}

#[test]
fn test_meta_ctx_is_meta_name() {
    let ctx = UniverseMetaCtx::new();
    assert!(ctx.is_meta_name(&name("_uext.0")));
    assert!(!ctx.is_meta_name(&name("u")));
}

// ── auto_bound_universe_params ──────────────────────────────────────────

#[test]
fn test_auto_bound_filters_declared() {
    let expr = Expr::sort(param("u"));
    let result = auto_bound_universe_params(&expr, &[name("u")]);
    assert!(result.is_empty());
}

#[test]
fn test_auto_bound_returns_undeclared() {
    let expr = Expr::sort(param("u"));
    let result = auto_bound_universe_params(&expr, &[]);
    assert_eq!(result, vec![name("u")]);
}

#[test]
fn test_auto_bound_filters_underscored() {
    let expr = Expr::sort(param("_internal"));
    let result = auto_bound_universe_params(&expr, &[]);
    assert!(result.is_empty());
}

#[test]
fn test_auto_bound_mixed() {
    let ty = Expr::sort(param("u"));
    let body = Expr::sort(param("_m"));
    let expr = Expr::pi(BinderInfo::Default, ty, body);
    // u is undeclared and not underscored; _m is filtered out
    let result = auto_bound_universe_params(&expr, &[]);
    assert_eq!(result, vec![name("u")]);
}

// ── consistency checking ─────────────────────────────────────────────────

#[test]
fn test_consistency_trivially_consistent() {
    let constraints = vec![UniverseEqConstraint {
        lhs: param("u"),
        rhs: one(),
    }];
    let solution = check_consistency(&constraints).unwrap();
    assert_eq!(solution.get(&name("u")), Some(&one()));
}

#[test]
fn test_consistency_inconsistent_ground() {
    let constraints = vec![UniverseEqConstraint {
        lhs: one(),
        rhs: two(),
    }];
    assert!(check_consistency(&constraints).is_err());
}

#[test]
fn test_consistency_multi_constraint() {
    let constraints = vec![
        UniverseEqConstraint {
            lhs: param("u"),
            rhs: one(),
        },
        UniverseEqConstraint {
            lhs: param("v"),
            rhs: two(),
        },
    ];
    let solution = check_consistency(&constraints).unwrap();
    assert_eq!(solution.get(&name("u")), Some(&one()));
    assert_eq!(solution.get(&name("v")), Some(&two()));
}

#[test]
fn test_consistency_display() {
    let c = UniverseEqConstraint {
        lhs: param("u"),
        rhs: one(),
    };
    let s = format!("{c}");
    assert!(s.contains("u"));
    assert!(s.contains("1"));
}

// ── level inference ──────────────────────────────────────────────────────

#[test]
fn test_infer_pi_universe_prop_to_prop() {
    // imax(0, 0) = 0 (Prop -> Prop : Prop)
    let result = infer_pi_universe(&zero(), &zero());
    assert_eq!(result, zero());
}

#[test]
fn test_infer_pi_universe_type_to_type() {
    // imax(1, 1) = max(1, 1) = 1
    let result = infer_pi_universe(&one(), &one());
    assert_eq!(result, one());
}

#[test]
fn test_infer_pi_universe_prop_to_type() {
    // imax(0, 1) = max(0, 1) = 1
    let result = infer_pi_universe(&zero(), &one());
    assert_eq!(result, one());
}

#[test]
fn test_infer_sort_level_empty() {
    assert_eq!(infer_sort_level(&[]), zero());
}

#[test]
fn test_infer_sort_level_single() {
    assert_eq!(infer_sort_level(&[one()]), one());
}

#[test]
fn test_infer_sort_level_multiple() {
    let result = infer_sort_level(&[one(), two(), zero()]);
    assert_eq!(result, two());
}

// ── pretty_level ─────────────────────────────────────────────────────────

#[test]
fn test_pretty_zero() {
    assert_eq!(pretty_level(&zero()), "0");
}

#[test]
fn test_pretty_numeric() {
    assert_eq!(pretty_level(&three()), "3");
}

#[test]
fn test_pretty_param() {
    assert_eq!(pretty_level(&param("u")), "u");
}

#[test]
fn test_pretty_succ_param() {
    assert_eq!(pretty_level(&succ(param("u"))), "u + 1");
}

#[test]
fn test_pretty_succ_param_offset2() {
    assert_eq!(pretty_level(&succ(succ(param("u")))), "u + 2");
}

#[test]
fn test_pretty_max() {
    let level = Level::max(param("u"), param("v"));
    assert_eq!(pretty_level(&level), "max(u, v)");
}

#[test]
fn test_pretty_imax() {
    let level = Level::imax(param("u"), param("v"));
    assert_eq!(pretty_level(&level), "imax(u, v)");
}

#[test]
fn test_pretty_nested_max() {
    let level = Level::max(param("u"), Level::max(param("v"), param("w")));
    assert_eq!(pretty_level(&level), "max(u, max(v, w))");
}

// ── error Display ────────────────────────────────────────────────────────

#[test]
fn test_error_display_unsatisfiable() {
    let e = UniversePolyExtError::Unsatisfiable("1 != 2".to_owned());
    assert!(e.to_string().contains("unsatisfiable"));
}

#[test]
fn test_error_display_cyclic() {
    let e = UniversePolyExtError::Cyclic("u".to_owned());
    assert!(e.to_string().contains("cyclic"));
}

#[test]
fn test_error_display_depth_exceeded() {
    let e = UniversePolyExtError::NormDepthExceeded(200);
    assert!(e.to_string().contains("200"));
}

#[test]
fn test_error_display_unassigned() {
    let e = UniversePolyExtError::UnassignedMeta("_uext.0".to_owned());
    assert!(e.to_string().contains("unassigned"));
}

// ── config ───────────────────────────────────────────────────────────────

#[test]
fn test_config_default() {
    let config = UniversePolyExtConfig::default();
    assert_eq!(config.max_solve_iterations, 100);
    assert_eq!(config.max_norm_depth, 200);
    assert!(config.cumulative_enabled);
    assert_eq!(config.meta_prefix, "_uext");
}

#[test]
fn test_config_custom_prefix() {
    let config = UniversePolyExtConfig {
        meta_prefix: "_custom".to_owned(),
        ..Default::default()
    };
    let mut ctx = UniverseMetaCtx::with_config(config);
    let m = ctx.fresh_meta();
    assert!(matches!(m, Level::Param(n) if n.to_string().starts_with("_custom")));
}
