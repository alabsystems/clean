// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for universe polymorphism elaboration support.

use super::universe_poly::*;
use clean_kernel::{BinderInfo, Expr, Level, Name};
use clean_parser::{LevelExpr, UniverseExpr};

// ═══════════════════════════════════════════════════════════════════════════
// UniverseInferCtx::fresh_universe
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_fresh_universe_generates_unique_names() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let u0 = ctx.fresh_universe();
    let u1 = ctx.fresh_universe();
    let u2 = ctx.fresh_universe();
    assert_ne!(u0, u1);
    assert_ne!(u1, u2);
    assert_ne!(u0, u2);
}

#[test]
fn test_fresh_universe_is_param() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let fresh = ctx.fresh_universe();
    assert!(matches!(fresh, Level::Param(_)));
}

#[test]
fn test_fresh_universe_naming_convention() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let u0 = ctx.fresh_universe();
    assert_eq!(u0, Level::param(Name::from_string("_u.0")));
    let u1 = ctx.fresh_universe();
    assert_eq!(u1, Level::param(Name::from_string("_u.1")));
}

// ═══════════════════════════════════════════════════════════════════════════
// Constraint recording
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_add_eq_constraint() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    ctx.add_eq(u.clone(), v.clone());
    assert_eq!(ctx.constraints().len(), 1);
    assert_eq!(ctx.constraints()[0], UniverseConstraint::Eq(u, v));
}

#[test]
fn test_add_le_constraint() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let u = Level::param(Name::from_string("u"));
    ctx.add_le(Level::zero(), u.clone());
    assert_eq!(ctx.constraints().len(), 1);
    assert_eq!(
        ctx.constraints()[0],
        UniverseConstraint::Le(Level::zero(), u)
    );
}

#[test]
fn test_add_multiple_constraints() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    ctx.add_eq(Level::zero(), Level::zero());
    ctx.add_le(Level::zero(), Level::succ(Level::zero()));
    ctx.add_eq(
        Level::param(Name::from_string("u")),
        Level::succ(Level::zero()),
    );
    assert_eq!(ctx.constraints().len(), 3);
}

// ═══════════════════════════════════════════════════════════════════════════
// Constraint solving — simple cases
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_solve_empty_constraints() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let result = ctx.solve();
    assert!(result.is_ok());
    assert!(result.unwrap().is_empty());
}

#[test]
fn test_solve_trivial_eq() {
    let mut ctx = UniverseInferCtx::new(vec![Name::from_string("u")]);
    ctx.add_eq(
        Level::param(Name::from_string("u")),
        Level::succ(Level::zero()),
    );
    let solutions = ctx.solve().expect("should solve trivial eq");
    assert_eq!(
        solutions.get(&Name::from_string("u")),
        Some(&Level::succ(Level::zero()))
    );
}

#[test]
fn test_solve_eq_zero() {
    let mut ctx = UniverseInferCtx::new(vec![Name::from_string("u")]);
    ctx.add_eq(Level::param(Name::from_string("u")), Level::zero());
    let solutions = ctx.solve().expect("should solve u = 0");
    assert_eq!(solutions.get(&Name::from_string("u")), Some(&Level::zero()));
}

#[test]
fn test_solve_eq_reversed() {
    // u = 1 expressed as 1 = u (reversed)
    let mut ctx = UniverseInferCtx::new(vec![Name::from_string("u")]);
    ctx.add_eq(
        Level::succ(Level::zero()),
        Level::param(Name::from_string("u")),
    );
    let solutions = ctx.solve().expect("should solve 1 = u");
    assert_eq!(
        solutions.get(&Name::from_string("u")),
        Some(&Level::succ(Level::zero()))
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Constraint solving — max, imax, nested
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_solve_eq_to_max() {
    // u = max(1, 2) => u should resolve to max(1, 2) = 2
    let mut ctx = UniverseInferCtx::new(vec![Name::from_string("u")]);
    let max_level = Level::max(
        Level::succ(Level::zero()),
        Level::succ(Level::succ(Level::zero())),
    );
    ctx.add_eq(Level::param(Name::from_string("u")), max_level.clone());
    let solutions = ctx.solve().expect("should solve u = max(1, 2)");
    let resolved = solutions
        .get(&Name::from_string("u"))
        .expect("u should be resolved");
    // max(1, 2) simplifies to 2
    assert_eq!(*resolved, Level::succ(Level::succ(Level::zero())));
}

#[test]
fn test_solve_eq_to_imax() {
    // u = imax(0, v) and v = 1  => u = imax(0, 1) = max(0, 1) = 1
    let mut ctx = UniverseInferCtx::new(vec![Name::from_string("u"), Name::from_string("v")]);
    ctx.add_eq(
        Level::param(Name::from_string("v")),
        Level::succ(Level::zero()),
    );
    ctx.add_eq(
        Level::param(Name::from_string("u")),
        Level::imax(Level::zero(), Level::param(Name::from_string("v"))),
    );
    let solutions = ctx.solve().expect("should solve imax constraints");
    assert_eq!(
        solutions.get(&Name::from_string("v")),
        Some(&Level::succ(Level::zero()))
    );
    // u = imax(0, v) where v=1 => after substitution, imax(0, 1) = 1
    let u_sol = solutions.get(&Name::from_string("u")).expect("u solved");
    let subst: Vec<(Name, Level)> = solutions
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let fully_resolved = u_sol.substitute(&subst);
    assert!(Level::is_def_eq(
        &fully_resolved,
        &Level::succ(Level::zero())
    ));
}

#[test]
fn test_solve_chain_eq() {
    // u = v, v = 2 => u = 2
    let mut ctx = UniverseInferCtx::new(vec![Name::from_string("u"), Name::from_string("v")]);
    ctx.add_eq(
        Level::param(Name::from_string("u")),
        Level::param(Name::from_string("v")),
    );
    ctx.add_eq(
        Level::param(Name::from_string("v")),
        Level::succ(Level::succ(Level::zero())),
    );
    let solutions = ctx.solve().expect("should solve chained eq");
    assert_eq!(
        solutions.get(&Name::from_string("v")),
        Some(&Level::succ(Level::succ(Level::zero())))
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Constraint solving — Le constraints
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_solve_le_satisfied() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    ctx.add_le(Level::zero(), Level::succ(Level::zero()));
    let result = ctx.solve();
    assert!(result.is_ok());
}

#[test]
fn test_solve_le_trivial_zero() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    ctx.add_le(Level::zero(), Level::zero());
    let result = ctx.solve();
    assert!(result.is_ok());
}

#[test]
fn test_solve_le_violated() {
    // 2 <= 1 should fail
    let mut ctx = UniverseInferCtx::new(vec![]);
    ctx.add_le(
        Level::succ(Level::succ(Level::zero())),
        Level::succ(Level::zero()),
    );
    let result = ctx.solve();
    assert!(result.is_err());
}

// ═══════════════════════════════════════════════════════════════════════════
// Constraint solving — error cases
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_solve_cyclic_constraint() {
    // u = succ(u) is cyclic
    let mut ctx = UniverseInferCtx::new(vec![Name::from_string("u")]);
    ctx.add_eq(
        Level::param(Name::from_string("u")),
        Level::succ(Level::param(Name::from_string("u"))),
    );
    let result = ctx.solve();
    assert!(result.is_err());
    match result.unwrap_err() {
        UniversePolyError::CyclicConstraint(name) => {
            assert_eq!(name, "u");
        }
        other => panic!("expected CyclicConstraint, got: {other:?}"),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Level::zero, Level::succ, Level::max, Level::imax handling
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_level_expr_to_level_lit_zero() {
    let level = level_expr_to_level(&LevelExpr::Lit(0));
    assert_eq!(level, Level::zero());
}

#[test]
fn test_level_expr_to_level_lit_three() {
    let level = level_expr_to_level(&LevelExpr::Lit(3));
    let expected = Level::succ(Level::succ(Level::succ(Level::zero())));
    assert_eq!(level, expected);
}

#[test]
fn test_level_expr_to_level_param() {
    let level = level_expr_to_level(&LevelExpr::Param("u".to_string()));
    assert_eq!(level, Level::param(Name::from_string("u")));
}

#[test]
fn test_level_expr_to_level_succ() {
    let inner = LevelExpr::Param("u".to_string());
    let level = level_expr_to_level(&LevelExpr::Succ(Box::new(inner)));
    assert_eq!(level, Level::succ(Level::param(Name::from_string("u"))));
}

#[test]
fn test_level_expr_to_level_max() {
    let a = LevelExpr::Param("u".to_string());
    let b = LevelExpr::Param("v".to_string());
    let level = level_expr_to_level(&LevelExpr::Max(Box::new(a), Box::new(b)));
    assert_eq!(
        level,
        Level::max(
            Level::param(Name::from_string("u")),
            Level::param(Name::from_string("v"))
        )
    );
}

#[test]
fn test_level_expr_to_level_imax() {
    let a = LevelExpr::Lit(0);
    let b = LevelExpr::Param("v".to_string());
    let level = level_expr_to_level(&LevelExpr::IMax(Box::new(a), Box::new(b)));
    // imax(0, v) = v (smart constructor simplification)
    assert_eq!(level, Level::param(Name::from_string("v")));
}

// ═══════════════════════════════════════════════════════════════════════════
// UniverseExpr conversion
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_universe_expr_prop() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let level = universe_expr_to_level(&UniverseExpr::Prop, &mut ctx);
    assert_eq!(level, Level::zero());
}

#[test]
fn test_universe_expr_type() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let level = universe_expr_to_level(&UniverseExpr::Type, &mut ctx);
    assert_eq!(level, Level::succ(Level::zero()));
}

#[test]
fn test_universe_expr_type_level() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let level_expr = LevelExpr::Param("u".to_string());
    let level = universe_expr_to_level(&UniverseExpr::TypeLevel(Box::new(level_expr)), &mut ctx);
    // Type u = Sort (u + 1)
    assert_eq!(level, Level::succ(Level::param(Name::from_string("u"))));
}

#[test]
fn test_universe_expr_type_implicit() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let level = universe_expr_to_level(&UniverseExpr::TypeImplicit, &mut ctx);
    // Should be succ of a fresh param
    match level {
        Level::Succ(inner) => {
            assert!(matches!(&*inner, Level::Param(_)));
        }
        other => panic!("expected Succ(Param(_)), got {other:?}"),
    }
}

#[test]
fn test_universe_expr_sort_implicit() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let level = universe_expr_to_level(&UniverseExpr::SortImplicit, &mut ctx);
    // Should be a fresh param
    assert!(matches!(level, Level::Param(_)));
}

#[test]
fn test_universe_expr_sort_star() {
    // `Sort*` (Mathlib) is the `Sort` analogue of `Type*`: a fresh universe
    // parameter (NOT `succ`, unlike `Type*`), matching bare `Sort`/`SortImplicit`.
    let mut ctx = UniverseInferCtx::new(vec![]);
    let level = universe_expr_to_level(&UniverseExpr::SortStar, &mut ctx);
    assert!(matches!(level, Level::Param(_)));
}

#[test]
fn test_universe_expr_sort_explicit() {
    let mut ctx = UniverseInferCtx::new(vec![]);
    let level_expr = LevelExpr::Lit(2);
    let level = universe_expr_to_level(&UniverseExpr::Sort(Box::new(level_expr)), &mut ctx);
    assert_eq!(level, Level::succ(Level::succ(Level::zero())));
}

// ═══════════════════════════════════════════════════════════════════════════
// collect_universe_params from SurfaceDecl
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_collect_universe_params_empty_import() {
    let decl = clean_parser::SurfaceDecl::Import {
        span: clean_parser::Span::dummy(),
        paths: vec![],
    };
    let params = collect_universe_params(&decl);
    assert!(params.names.is_empty());
}

// ═══════════════════════════════════════════════════════════════════════════
// apply_solution on expressions
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_apply_solution_sort() {
    let mut ctx = UniverseInferCtx::new(vec![Name::from_string("u")]);
    ctx.add_eq(
        Level::param(Name::from_string("u")),
        Level::succ(Level::zero()),
    );
    ctx.solve().expect("should solve");

    let expr = Expr::sort(Level::param(Name::from_string("u")));
    let result = ctx.apply_solution(&expr);
    assert_eq!(result, Expr::sort(Level::succ(Level::zero())));
}

#[test]
fn test_apply_solution_const() {
    let mut ctx = UniverseInferCtx::new(vec![Name::from_string("u")]);
    ctx.add_eq(Level::param(Name::from_string("u")), Level::zero());
    ctx.solve().expect("should solve");

    let expr = Expr::const_(
        Name::from_string("List"),
        vec![Level::param(Name::from_string("u"))],
    );
    let result = ctx.apply_solution(&expr);
    assert_eq!(
        result,
        Expr::const_(Name::from_string("List"), vec![Level::zero()])
    );
}

#[test]
fn test_apply_solution_no_change() {
    let ctx = UniverseInferCtx::new(vec![]);
    let expr = Expr::sort(Level::zero());
    let result = ctx.apply_solution(&expr);
    assert_eq!(result, expr);
}

#[test]
fn test_apply_solution_pi() {
    let mut ctx = UniverseInferCtx::new(vec![Name::from_string("u")]);
    ctx.add_eq(
        Level::param(Name::from_string("u")),
        Level::succ(Level::zero()),
    );
    ctx.solve().expect("should solve");

    // (x : Sort u) -> Sort u
    let pi = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::param(Name::from_string("u"))),
        Expr::sort(Level::param(Name::from_string("u"))),
    );
    let result = ctx.apply_solution(&pi);
    let expected = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::succ(Level::zero())),
        Expr::sort(Level::succ(Level::zero())),
    );
    assert_eq!(result, expected);
}

#[test]
fn test_apply_solution_lambda() {
    let mut ctx = UniverseInferCtx::new(vec![Name::from_string("u")]);
    ctx.add_eq(Level::param(Name::from_string("u")), Level::zero());
    ctx.solve().expect("should solve");

    let lam = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::param(Name::from_string("u"))),
        Expr::bvar(0),
    );
    let result = ctx.apply_solution(&lam);
    let expected = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::bvar(0),
    );
    assert_eq!(result, expected);
}

// ═══════════════════════════════════════════════════════════════════════════
// auto_level_definition
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_auto_level_no_params() {
    // A type with no universe parameters.
    let type_expr = Expr::sort(Level::zero());
    let result = auto_level_definition(&type_expr, None, &[]).expect("should succeed");
    assert!(result.universe_params.is_empty());
}

#[test]
fn test_auto_level_with_declared_params() {
    let u = Name::from_string("u");
    let type_expr = Expr::sort(Level::param(u.clone()));
    let result =
        auto_level_definition(&type_expr, None, std::slice::from_ref(&u)).expect("should succeed");
    assert_eq!(result.universe_params, vec![u]);
}

#[test]
fn test_auto_level_discovers_params_from_type() {
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    // Pi (x : Sort u) -> Sort v
    let type_expr = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::param(u.clone())),
        Expr::sort(Level::param(v.clone())),
    );
    let result = auto_level_definition(&type_expr, None, &[]).expect("should succeed");
    // Both u and v should be discovered.
    assert!(result.universe_params.contains(&u));
    assert!(result.universe_params.contains(&v));
}

#[test]
fn test_auto_level_discovers_params_from_value() {
    let u = Name::from_string("u");
    let type_expr = Expr::sort(Level::succ(Level::zero()));
    let value_expr = Expr::sort(Level::param(u.clone()));
    let result = auto_level_definition(&type_expr, Some(&value_expr), &[]).expect("should succeed");
    assert!(result.universe_params.contains(&u));
}

#[test]
fn test_auto_level_deduplicates() {
    let u = Name::from_string("u");
    // u appears in both type and value.
    let type_expr = Expr::sort(Level::param(u.clone()));
    let value_expr = Expr::sort(Level::param(u.clone()));
    let result = auto_level_definition(&type_expr, Some(&value_expr), std::slice::from_ref(&u))
        .expect("should succeed");
    // u should appear exactly once.
    assert_eq!(
        result.universe_params.iter().filter(|p| **p == u).count(),
        1
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// collect_level_params_from_expr
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_collect_params_from_sort() {
    let expr = Expr::sort(Level::param(Name::from_string("u")));
    let mut params = Vec::new();
    collect_level_params_from_expr(&expr, &mut params);
    assert_eq!(params, vec![Name::from_string("u")]);
}

#[test]
fn test_collect_params_from_const() {
    let expr = Expr::const_(
        Name::from_string("List"),
        vec![Level::param(Name::from_string("u"))],
    );
    let mut params = Vec::new();
    collect_level_params_from_expr(&expr, &mut params);
    assert_eq!(params, vec![Name::from_string("u")]);
}

#[test]
fn test_collect_params_from_nested_pi() {
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let pi = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::param(u.clone())),
        Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::param(v.clone())),
            Expr::sort(Level::max(Level::param(u.clone()), Level::param(v.clone()))),
        ),
    );
    let mut params = Vec::new();
    collect_level_params_from_expr(&pi, &mut params);
    assert!(params.contains(&u));
    assert!(params.contains(&v));
}

#[test]
fn test_collect_params_no_duplicates() {
    let u = Name::from_string("u");
    let app = Expr::app(
        Expr::sort(Level::param(u.clone())),
        Expr::sort(Level::param(u.clone())),
    );
    let mut params = Vec::new();
    collect_level_params_from_expr(&app, &mut params);
    // u should appear only once (Level::collect_params deduplicates).
    assert_eq!(params.iter().filter(|p| **p == u).count(), 1);
}

#[test]
fn test_collect_params_from_bvar() {
    let expr = Expr::bvar(0);
    let mut params = Vec::new();
    collect_level_params_from_expr(&expr, &mut params);
    assert!(params.is_empty());
}
