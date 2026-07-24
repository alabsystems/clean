// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended universe constraint solving module.

use clean_kernel::{Expr, Level, Name};

use crate::universe_constraint_ext::{
    check_universe_consistent, collect_universe_constraints, infer_universe_level, normalize_level,
    occurs_check, ConstraintSet, UniverseConstraintExt, UniverseMetaVar, UniverseSolution,
};

// ═══════════════════════════════════════════════════════════════════════════
// Helper constructors
// ═══════════════════════════════════════════════════════════════════════════

fn zero() -> Level {
    Level::zero()
}

fn succ(l: Level) -> Level {
    Level::succ(l)
}

fn param(s: &str) -> Level {
    Level::param(Name::from_string(s))
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

// ═══════════════════════════════════════════════════════════════════════════
// UniverseConstraintExt construction and display
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_constraint_ext_le_display() {
    let c = UniverseConstraintExt::Le(zero(), succ(zero()));
    let s = format!("{c}");
    assert!(s.contains("<="), "Le display should contain <=: {s}");
}

#[test]
fn test_constraint_ext_eq_display() {
    let c = UniverseConstraintExt::Eq(param("u"), param("v"));
    let s = format!("{c}");
    assert!(s.contains("="), "Eq display should contain =: {s}");
}

#[test]
fn test_constraint_ext_max_display() {
    let c = UniverseConstraintExt::Max(param("u"), param("v"), param("w"));
    let s = format!("{c}");
    assert!(s.contains("max"), "Max display should contain max: {s}");
}

#[test]
fn test_constraint_ext_imax_display() {
    let c = UniverseConstraintExt::IMax(param("u"), param("v"), param("w"));
    let s = format!("{c}");
    assert!(s.contains("imax"), "IMax display should contain imax: {s}");
}

#[test]
fn test_constraint_ext_eq_clone() {
    let c = UniverseConstraintExt::Eq(param("u"), succ(zero()));
    let c2 = c.clone();
    assert_eq!(c, c2);
}

// ═══════════════════════════════════════════════════════════════════════════
// UniverseMetaVar
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_metavar_display_with_name() {
    let mv = UniverseMetaVar::new(0, Some(name("u")));
    let s = format!("{mv}");
    assert!(s.contains("u"), "named metavar display: {s}");
}

#[test]
fn test_metavar_display_anonymous() {
    let mv = UniverseMetaVar::new(42, None);
    let s = format!("{mv}");
    assert!(s.contains("42"), "anonymous metavar display: {s}");
}

#[test]
fn test_metavar_to_level() {
    let mv = UniverseMetaVar::new(0, Some(name("u")));
    let l = mv.to_level();
    assert_eq!(l, param("u"));
}

#[test]
fn test_metavar_to_level_anonymous() {
    let mv = UniverseMetaVar::new(7, None);
    let l = mv.to_level();
    assert_eq!(l, Level::param(Name::from_string("_umv.7")));
}

#[test]
fn test_metavar_equality() {
    let a = UniverseMetaVar::new(1, Some(name("u")));
    let b = UniverseMetaVar::new(1, Some(name("u")));
    let c = UniverseMetaVar::new(2, Some(name("u")));
    assert_eq!(a, b);
    assert_ne!(a, c);
}

// ═══════════════════════════════════════════════════════════════════════════
// UniverseSolution
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_solution_empty() {
    let sol = UniverseSolution::new();
    assert!(sol.is_empty());
    assert_eq!(sol.len(), 0);
}

#[test]
fn test_solution_insert_get() {
    let mut sol = UniverseSolution::new();
    sol.insert(name("u"), succ(zero()));
    assert!(sol.contains(&name("u")));
    assert_eq!(sol.get(&name("u")), Some(&succ(zero())));
    assert!(!sol.contains(&name("v")));
    assert_eq!(sol.len(), 1);
}

#[test]
fn test_solution_apply_to_level_param() {
    let mut sol = UniverseSolution::new();
    sol.insert(name("u"), succ(zero()));
    let result = sol.apply_to_level(&param("u"));
    assert_eq!(result, succ(zero()));
}

#[test]
fn test_solution_apply_to_level_unbound() {
    let sol = UniverseSolution::new();
    let result = sol.apply_to_level(&param("u"));
    assert_eq!(result, param("u"));
}

#[test]
fn test_solution_apply_to_level_nested() {
    let mut sol = UniverseSolution::new();
    sol.insert(name("u"), succ(zero()));
    let level = Level::succ(param("u"));
    let result = sol.apply_to_level(&level);
    assert_eq!(result, succ(succ(zero())));
}

#[test]
fn test_solution_iter() {
    let mut sol = UniverseSolution::new();
    sol.insert(name("u"), zero());
    sol.insert(name("v"), succ(zero()));
    let entries: Vec<_> = sol.iter().collect();
    assert_eq!(entries.len(), 2);
}

#[test]
fn test_solution_from_map() {
    let mut map = std::collections::HashMap::new();
    map.insert(name("u"), succ(zero()));
    let sol = UniverseSolution::from_map(map);
    assert_eq!(sol.len(), 1);
    assert!(sol.contains(&name("u")));
}

// ═══════════════════════════════════════════════════════════════════════════
// ConstraintSet basics
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_constraint_set_empty() {
    let cs = ConstraintSet::new();
    assert!(cs.is_empty());
    assert!(cs.is_consistent());
}

#[test]
fn test_constraint_set_add() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Eq(param("u"), succ(zero())));
    assert_eq!(cs.len(), 1);
}

// ═══════════════════════════════════════════════════════════════════════════
// ConstraintSet consistency
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_consistent_trivial_le() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Le(zero(), succ(zero())));
    assert!(cs.is_consistent());
}

#[test]
fn test_inconsistent_le_ground() {
    let mut cs = ConstraintSet::new();
    // succ(succ(0)) <= succ(0) is false
    cs.add_constraint(UniverseConstraintExt::Le(succ(succ(zero())), succ(zero())));
    assert!(!cs.is_consistent());
}

#[test]
fn test_consistent_eq_ground() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Eq(succ(zero()), succ(zero())));
    assert!(cs.is_consistent());
}

#[test]
fn test_inconsistent_eq_ground() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Eq(zero(), succ(zero())));
    assert!(!cs.is_consistent());
}

#[test]
fn test_consistent_max_ground() {
    let mut cs = ConstraintSet::new();
    // max(0, succ(0)) = succ(0) — correct
    cs.add_constraint(UniverseConstraintExt::Max(
        zero(),
        succ(zero()),
        succ(zero()),
    ));
    assert!(cs.is_consistent());
}

#[test]
fn test_inconsistent_max_ground() {
    let mut cs = ConstraintSet::new();
    // max(succ(0), succ(0)) = 0 — wrong
    cs.add_constraint(UniverseConstraintExt::Max(
        succ(zero()),
        succ(zero()),
        zero(),
    ));
    assert!(!cs.is_consistent());
}

#[test]
fn test_consistent_imax_zero_rhs() {
    let mut cs = ConstraintSet::new();
    // imax(succ(0), 0) = 0 — correct by imax definition
    cs.add_constraint(UniverseConstraintExt::IMax(succ(zero()), zero(), zero()));
    assert!(cs.is_consistent());
}

#[test]
fn test_consistent_with_params() {
    // Params are non-ground, so consistency check passes conservatively.
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Le(param("u"), zero()));
    assert!(cs.is_consistent());
}

// ═══════════════════════════════════════════════════════════════════════════
// ConstraintSet simplify
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_simplify_removes_trivial_eq() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Eq(succ(zero()), succ(zero())));
    cs.add_constraint(UniverseConstraintExt::Eq(param("u"), succ(zero())));
    cs.simplify();
    assert_eq!(cs.len(), 1);
}

#[test]
fn test_simplify_removes_zero_le() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Le(zero(), param("u")));
    cs.simplify();
    assert_eq!(cs.len(), 0);
}

#[test]
fn test_simplify_removes_reflexive_le() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Le(succ(zero()), succ(zero())));
    cs.simplify();
    assert_eq!(cs.len(), 0);
}

#[test]
fn test_simplify_removes_satisfied_ground_le() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Le(zero(), succ(succ(zero()))));
    cs.simplify();
    assert_eq!(cs.len(), 0, "0 <= 2 is trivially true");
}

#[test]
fn test_simplify_keeps_non_trivial() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Le(param("u"), param("v")));
    cs.simplify();
    assert_eq!(cs.len(), 1, "non-ground Le should be kept");
}

// ═══════════════════════════════════════════════════════════════════════════
// ConstraintSet solve
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_solve_empty() {
    let cs = ConstraintSet::new();
    let sol = cs.solve().expect("empty should solve");
    assert!(sol.is_empty());
}

#[test]
fn test_solve_single_eq() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Eq(param("u"), succ(zero())));
    let sol = cs.solve().expect("should solve");
    assert_eq!(sol.get(&name("u")), Some(&succ(zero())));
}

#[test]
fn test_solve_chain_eq() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Eq(param("u"), param("v")));
    cs.add_constraint(UniverseConstraintExt::Eq(param("v"), succ(zero())));
    let sol = cs.solve().expect("should solve chain");
    assert_eq!(sol.get(&name("v")), Some(&succ(zero())));
    // u should map to v, and v maps to succ(zero)
    assert!(sol.contains(&name("u")));
}

#[test]
fn test_solve_max_result_binding() {
    let mut cs = ConstraintSet::new();
    // max(succ(0), 0) = w => w should bind to succ(0)
    cs.add_constraint(UniverseConstraintExt::Max(succ(zero()), zero(), param("w")));
    let sol = cs.solve().expect("should solve max");
    assert!(sol.contains(&name("w")));
}

#[test]
fn test_solve_imax_result_binding() {
    let mut cs = ConstraintSet::new();
    // imax(succ(0), 0) = w => w should bind to imax(succ(0), 0) = 0
    cs.add_constraint(UniverseConstraintExt::IMax(
        succ(zero()),
        zero(),
        param("w"),
    ));
    let sol = cs.solve().expect("should solve imax");
    assert!(sol.contains(&name("w")));
}

#[test]
fn test_solve_le_verified() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Le(zero(), succ(zero())));
    let sol = cs.solve().expect("should solve");
    assert!(sol.is_empty());
}

#[test]
fn test_solve_le_fails() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Le(succ(succ(zero())), zero()));
    let result = cs.solve();
    assert!(result.is_err(), "succ(succ(0)) <= 0 should fail");
}

#[test]
fn test_solve_cyclic_eq_fails() {
    let mut cs = ConstraintSet::new();
    cs.add_constraint(UniverseConstraintExt::Eq(
        param("u"),
        Level::succ(param("u")),
    ));
    let result = cs.solve();
    assert!(result.is_err(), "u = succ(u) is cyclic");
}

// ═══════════════════════════════════════════════════════════════════════════
// collect_universe_constraints
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_collect_from_sort() {
    let expr = Expr::sort(succ(zero()));
    let cs = collect_universe_constraints(&expr);
    assert_eq!(cs.len(), 1);
    assert!(matches!(&cs[0], UniverseConstraintExt::Le(l, _) if l.is_zero()));
}

#[test]
fn test_collect_from_const_multi_level() {
    let expr = Expr::const_(Name::from_string("List"), vec![param("u"), param("v")]);
    let cs = collect_universe_constraints(&expr);
    assert_eq!(cs.len(), 1, "one pairwise Le for two levels");
}

#[test]
fn test_collect_from_bvar() {
    let expr = Expr::bvar(0);
    let cs = collect_universe_constraints(&expr);
    assert!(cs.is_empty());
}

#[test]
fn test_collect_recursive_app() {
    let sort_expr = Expr::sort(param("u"));
    let app_expr = Expr::app(sort_expr.clone(), Expr::bvar(0));
    let cs = collect_universe_constraints(&app_expr);
    assert_eq!(cs.len(), 1);
}

// ═══════════════════════════════════════════════════════════════════════════
// check_universe_consistent
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_check_consistent_ok() {
    let cs = vec![
        UniverseConstraintExt::Le(zero(), succ(zero())),
        UniverseConstraintExt::Eq(succ(zero()), succ(zero())),
    ];
    assert!(check_universe_consistent(&cs).is_ok());
}

#[test]
fn test_check_consistent_finds_bad() {
    let cs = vec![
        UniverseConstraintExt::Eq(zero(), succ(zero())),
        UniverseConstraintExt::Le(zero(), succ(zero())),
    ];
    let err = check_universe_consistent(&cs).unwrap_err();
    assert_eq!(err.len(), 1);
}

// ═══════════════════════════════════════════════════════════════════════════
// infer_universe_level
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_infer_empty() {
    let result = infer_universe_level(&[]);
    assert_eq!(result, zero());
}

#[test]
fn test_infer_single() {
    let result = infer_universe_level(&[succ(zero())]);
    assert_eq!(result, succ(zero()));
}

#[test]
fn test_infer_multiple_ground() {
    let result = infer_universe_level(&[zero(), succ(zero()), succ(succ(zero()))]);
    // max(max(0, 1), 2) normalized = 2
    assert_eq!(result, succ(succ(zero())));
}

#[test]
fn test_infer_with_params() {
    let result = infer_universe_level(&[param("u"), succ(zero())]);
    // max(u, 1) — cannot reduce further but should normalize
    let expected = Level::max(param("u"), succ(zero())).normalize();
    assert_eq!(result, expected);
}

// ═══════════════════════════════════════════════════════════════════════════
// normalize_level
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_normalize_level_substitutes() {
    let mut sol = UniverseSolution::new();
    sol.insert(name("u"), succ(zero()));
    let result = normalize_level(&param("u"), &sol);
    assert_eq!(result, succ(zero()));
}

#[test]
fn test_normalize_level_ground() {
    let sol = UniverseSolution::new();
    let result = normalize_level(&succ(zero()), &sol);
    assert_eq!(result, succ(zero()));
}

#[test]
fn test_normalize_level_nested_max() {
    let mut sol = UniverseSolution::new();
    sol.insert(name("u"), zero());
    let level = Level::max(param("u"), succ(zero()));
    let result = normalize_level(&level, &sol);
    // max(0, 1) normalized = 1
    assert_eq!(result, succ(zero()));
}

// ═══════════════════════════════════════════════════════════════════════════
// occurs_check
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_occurs_check_direct() {
    let mv = UniverseMetaVar::new(0, Some(name("u")));
    assert!(occurs_check(&mv, &param("u")));
}

#[test]
fn test_occurs_check_nested() {
    let mv = UniverseMetaVar::new(0, Some(name("u")));
    assert!(occurs_check(&mv, &Level::succ(param("u"))));
}

#[test]
fn test_occurs_check_absent() {
    let mv = UniverseMetaVar::new(0, Some(name("u")));
    assert!(!occurs_check(&mv, &succ(zero())));
}

#[test]
fn test_occurs_check_anonymous() {
    let mv = UniverseMetaVar::new(3, None);
    let target = Level::param(Name::from_string("_umv.3"));
    assert!(occurs_check(&mv, &target));
}

#[test]
fn test_occurs_check_in_max() {
    let mv = UniverseMetaVar::new(0, Some(name("u")));
    let level = Level::max(param("u"), succ(zero()));
    assert!(occurs_check(&mv, &level));
}

#[test]
fn test_occurs_check_in_imax() {
    let mv = UniverseMetaVar::new(0, Some(name("u")));
    let level = Level::imax(succ(zero()), param("u"));
    assert!(occurs_check(&mv, &level));
}
