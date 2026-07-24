// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for Proj/MData/Squash catch-all bug (#2143).
//!
//! These tests verify that expression traversal functions correctly recurse
//! into Proj, MData, and Squash wrappers. The bug: functions using
//! `_ => expr.clone()` or `_ => false` catch-all arms silently skip recursion
//! into these wrapper variants.
//!
//! See also: #2128 (BVar operations fix), #2141 (ExprFolderOpt refactoring design).

use std::sync::Arc;

use super::*;
use crate::tactic::arith_field_simp::clear_denominators;
use crate::tactic::arith_norm_cast::normalize_casts;
use crate::tactic::cast::{push_casts_to_leaves, qify_expr, zify_expr};
use crate::tactic::equality::{abstract_over, contains_expr, replace_expr};
use clean_kernel::{BinderInfo, ExprKind};

// --- replace_expr tests ---

#[test]
fn test_replace_expr_inside_proj() {
    // replace_expr should find and replace targets inside Proj wrappers
    let target = Expr::const_(Name::from_string("old"), vec![]);
    let replacement = Expr::const_(Name::from_string("new"), vec![]);
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, target.clone());
    let result = replace_expr(&proj, &target, &replacement);
    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, replacement);
    assert_eq!(result, expected, "replace_expr must recurse into Proj");
}

#[test]
fn test_replace_expr_inside_mdata() {
    // replace_expr should find and replace targets inside MData wrappers
    let target = Expr::const_(Name::from_string("old"), vec![]);
    let replacement = Expr::const_(Name::from_string("new"), vec![]);
    let mdata = Expr::mdata(vec![], target.clone());
    let result = replace_expr(&mdata, &target, &replacement);
    let expected = Expr::mdata(vec![], replacement);
    assert_eq!(result, expected, "replace_expr must recurse into MData");
}

// --- contains_expr tests ---

#[test]
fn test_contains_expr_inside_proj() {
    // contains_expr should find targets inside Proj wrappers
    let needle = Expr::const_(Name::from_string("a"), vec![]);
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, needle.clone());
    assert!(
        contains_expr(&proj, &needle),
        "contains_expr must recurse into Proj"
    );
}

#[test]
fn test_contains_expr_inside_mdata() {
    // contains_expr should find targets inside MData wrappers
    let needle = Expr::const_(Name::from_string("a"), vec![]);
    let mdata = Expr::mdata(vec![], needle.clone());
    assert!(
        contains_expr(&mdata, &needle),
        "contains_expr must recurse into MData"
    );
}

// --- abstract_over tests ---

#[test]
fn test_abstract_over_inside_proj() {
    // abstract_over should replace occurrences of term inside Proj wrappers
    let term = Expr::const_(Name::from_string("a"), vec![]);
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, term.clone());
    let result = abstract_over(&proj, &term);
    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, Expr::bvar(0));
    assert_eq!(result, expected, "abstract_over must recurse into Proj");
}

#[test]
fn test_abstract_over_inside_mdata() {
    // abstract_over should replace occurrences of term inside MData wrappers
    let term = Expr::const_(Name::from_string("a"), vec![]);
    let mdata = Expr::mdata(vec![], term.clone());
    let result = abstract_over(&mdata, &term);
    let expected = Expr::mdata(vec![], Expr::bvar(0));
    assert_eq!(result, expected, "abstract_over must recurse into MData");
}

// --- substitute_const tests ---

#[test]
fn test_substitute_const_inside_proj() {
    // substitute_const should replace constants inside Proj wrappers
    let name = Name::from_string("old");
    let value = Expr::const_(Name::from_string("new"), vec![]);
    let proj = Expr::proj(
        Name::from_string("Prod.fst"),
        0,
        Expr::const_(name.clone(), vec![]),
    );
    let result = substitute_const(&proj, &name, &value);
    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, value);
    assert_eq!(result, expected, "substitute_const must recurse into Proj");
}

#[test]
fn test_substitute_const_inside_mdata() {
    // substitute_const should replace constants inside MData wrappers
    let name = Name::from_string("old");
    let value = Expr::const_(Name::from_string("new"), vec![]);
    let mdata = Expr::mdata(vec![], Expr::const_(name.clone(), vec![]));
    let result = substitute_const(&mdata, &name, &value);
    let expected = Expr::mdata(vec![], value);
    assert_eq!(result, expected, "substitute_const must recurse into MData");
}

// --- Squash tests ---
// Squash is a clean-specific wrapper (not in Lean 4 C++). Like MData, it wraps
// a sub-expression without introducing a binder, so all traversals must recurse
// into it with unchanged offset.

fn make_squash(inner: Expr) -> Expr {
    Expr::from_kind(ExprKind::Squash(Arc::new(inner)))
}

#[test]
fn test_replace_expr_inside_squash() {
    let target = Expr::const_(Name::from_string("old"), vec![]);
    let replacement = Expr::const_(Name::from_string("new"), vec![]);
    let squash = make_squash(target.clone());
    let result = replace_expr(&squash, &target, &replacement);
    let expected = make_squash(replacement);
    assert_eq!(result, expected, "replace_expr must recurse into Squash");
}

#[test]
fn test_contains_expr_inside_squash() {
    let needle = Expr::const_(Name::from_string("a"), vec![]);
    let squash = make_squash(needle.clone());
    assert!(
        contains_expr(&squash, &needle),
        "contains_expr must recurse into Squash"
    );
}

#[test]
fn test_abstract_over_inside_squash() {
    let term = Expr::const_(Name::from_string("a"), vec![]);
    let squash = make_squash(term.clone());
    let result = abstract_over(&squash, &term);
    let expected = make_squash(Expr::bvar(0));
    assert_eq!(result, expected, "abstract_over must recurse into Squash");
}

#[test]
fn test_substitute_const_inside_squash() {
    let name = Name::from_string("old");
    let value = Expr::const_(Name::from_string("new"), vec![]);
    let squash = make_squash(Expr::const_(name.clone(), vec![]));
    let result = substitute_const(&squash, &name, &value);
    let expected = make_squash(value);
    assert_eq!(
        result, expected,
        "substitute_const must recurse into Squash"
    );
}

// ==========================================================================
// Regression tests for #2153: 9 untested Proj/MData/Squash functions
// ==========================================================================

// --- push_negations_in_expr tests (wlog.rs) ---
// Double negation Not(Not(P)) should simplify to P inside wrappers.

#[test]
fn test_push_negations_in_expr_inside_proj() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let not = Expr::const_(Name::from_string("Not"), vec![]);
    let not_not_p = Expr::app(not.clone(), Expr::app(not, p.clone()));
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, not_not_p);
    let result = push_negations_in_expr(&proj);
    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, p);
    assert_eq!(
        result, expected,
        "push_negations_in_expr must recurse into Proj"
    );
}

#[test]
fn test_push_negations_in_expr_inside_mdata() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let not = Expr::const_(Name::from_string("Not"), vec![]);
    let not_not_p = Expr::app(not.clone(), Expr::app(not, p.clone()));
    let mdata = Expr::mdata(vec![], not_not_p);
    let result = push_negations_in_expr(&mdata);
    let expected = Expr::mdata(vec![], p);
    assert_eq!(
        result, expected,
        "push_negations_in_expr must recurse into MData"
    );
}

#[test]
fn test_push_negations_in_expr_inside_squash() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let not = Expr::const_(Name::from_string("Not"), vec![]);
    let not_not_p = Expr::app(not.clone(), Expr::app(not, p.clone()));
    let squash = make_squash(not_not_p);
    let result = push_negations_in_expr(&squash);
    let expected = make_squash(p);
    assert_eq!(
        result, expected,
        "push_negations_in_expr must recurse into Squash"
    );
}

// --- normalize_numerals tests (wlog.rs) ---
// Nat.add(2, 3) should normalize to Lit(5) inside wrappers.

#[test]
fn test_normalize_numerals_inside_proj() {
    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let add_2_3 = Expr::app(Expr::app(add, Expr::nat_lit(2)), Expr::nat_lit(3));
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, add_2_3);
    let result = normalize_numerals(&proj);
    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, Expr::nat_lit(5));
    assert_eq!(
        result, expected,
        "normalize_numerals must recurse into Proj"
    );
}

#[test]
fn test_normalize_numerals_inside_mdata() {
    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let add_2_3 = Expr::app(Expr::app(add, Expr::nat_lit(2)), Expr::nat_lit(3));
    let mdata = Expr::mdata(vec![], add_2_3);
    let result = normalize_numerals(&mdata);
    let expected = Expr::mdata(vec![], Expr::nat_lit(5));
    assert_eq!(
        result, expected,
        "normalize_numerals must recurse into MData"
    );
}

// --- extract_denominators tests (arith_field_simp.rs) ---
// Division App(App(HDiv.hDiv, a), b) inside wrappers: denominator b should be found.

#[test]
fn test_extract_denominators_inside_proj() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let div = Expr::const_(Name::from_string("HDiv.hDiv"), vec![]);
    let a_div_b = Expr::app(Expr::app(div, a), b.clone());
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, a_div_b);
    let denoms = extract_denominators(&proj);
    assert!(
        !denoms.is_empty(),
        "extract_denominators must recurse into Proj to find denominators"
    );
    assert_eq!(denoms[0], b);
}

#[test]
fn test_extract_denominators_inside_mdata() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let div = Expr::const_(Name::from_string("HDiv.hDiv"), vec![]);
    let a_div_b = Expr::app(Expr::app(div, a), b.clone());
    let mdata = Expr::mdata(vec![], a_div_b);
    let denoms = extract_denominators(&mdata);
    assert!(
        !denoms.is_empty(),
        "extract_denominators must recurse into MData to find denominators"
    );
    assert_eq!(denoms[0], b);
}

// --- clear_denominators tests (arith_field_simp.rs) ---
// Division a/b inside wrappers should be cleared to just a.

#[test]
fn test_clear_denominators_inside_proj() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let div = Expr::const_(Name::from_string("HDiv.hDiv"), vec![]);
    let a_div_b = Expr::app(Expr::app(div, a.clone()), b);
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, a_div_b);
    let result = clear_denominators(&proj);
    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, a);
    assert_eq!(
        result, expected,
        "clear_denominators must recurse into Proj"
    );
}

#[test]
fn test_clear_denominators_inside_mdata() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let div = Expr::const_(Name::from_string("HDiv.hDiv"), vec![]);
    let a_div_b = Expr::app(Expr::app(div, a.clone()), b);
    let mdata = Expr::mdata(vec![], a_div_b);
    let result = clear_denominators(&mdata);
    let expected = Expr::mdata(vec![], a);
    assert_eq!(
        result, expected,
        "clear_denominators must recurse into MData"
    );
}

// --- normalize_casts tests (arith_field_simp.rs) ---
// Nested casts cast(cast(x)) should collapse to cast(x) inside wrappers.

#[test]
fn test_normalize_casts_inside_proj() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let cast_fn = Expr::const_(Name::from_string("Nat.cast"), vec![]);
    let cast_x = Expr::app(cast_fn.clone(), x);
    let cast_cast_x = Expr::app(cast_fn, cast_x.clone());
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, cast_cast_x);
    let result = normalize_casts(&proj);
    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, cast_x);
    assert_eq!(
        result, expected,
        "normalize_casts must recurse into Proj and collapse nested casts"
    );
}

#[test]
fn test_normalize_casts_inside_mdata() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let cast_fn = Expr::const_(Name::from_string("Nat.cast"), vec![]);
    let cast_x = Expr::app(cast_fn.clone(), x);
    let cast_cast_x = Expr::app(cast_fn, cast_x.clone());
    let mdata = Expr::mdata(vec![], cast_cast_x);
    let result = normalize_casts(&mdata);
    let expected = Expr::mdata(vec![], cast_x);
    assert_eq!(
        result, expected,
        "normalize_casts must recurse into MData and collapse nested casts"
    );
}

// --- exprs_syntactically_equal tests (arith_field_simp.rs) ---
// Identical Proj/MData/Squash pairs should be recognized as equal.

#[test]
fn test_exprs_syntactically_equal_proj() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let proj1 = Expr::proj(Name::from_string("Prod.fst"), 0, x.clone());
    let proj2 = Expr::proj(Name::from_string("Prod.fst"), 0, x);
    assert!(
        exprs_syntactically_equal(&proj1, &proj2),
        "exprs_syntactically_equal must handle Proj"
    );
}

#[test]
fn test_exprs_syntactically_equal_mdata() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let mdata1 = Expr::mdata(vec![], x.clone());
    let mdata2 = Expr::mdata(vec![], x);
    assert!(
        exprs_syntactically_equal(&mdata1, &mdata2),
        "exprs_syntactically_equal must handle MData"
    );
}

#[test]
fn test_exprs_syntactically_equal_squash() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let squash1 = make_squash(x.clone());
    let squash2 = make_squash(x);
    assert!(
        exprs_syntactically_equal(&squash1, &squash2),
        "exprs_syntactically_equal must handle Squash"
    );
}

#[test]
fn test_exprs_syntactically_equal_proj_different_inner() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let proj1 = Expr::proj(Name::from_string("Prod.fst"), 0, x);
    let proj2 = Expr::proj(Name::from_string("Prod.fst"), 0, y);
    assert!(
        !exprs_syntactically_equal(&proj1, &proj2),
        "exprs_syntactically_equal must recurse into Proj inner expressions"
    );
}

// --- push_casts_to_leaves tests (cast.rs) ---
// cast(a + b) inside wrappers should become add(cast(a), cast(b)).

#[test]
fn test_push_casts_to_leaves_inside_proj() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let cast_fn = Expr::const_(Name::from_string("Nat.cast"), vec![]);
    // cast(a + b)
    let a_plus_b = Expr::app(Expr::app(add.clone(), a.clone()), b.clone());
    let cast_sum = Expr::app(cast_fn.clone(), a_plus_b);
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, cast_sum);
    let result = push_casts_to_leaves(&proj);
    // Expected: Proj(add(cast(a), cast(b)))
    let expected = Expr::proj(
        Name::from_string("Prod.fst"),
        0,
        Expr::app(
            Expr::app(add, Expr::app(cast_fn.clone(), a)),
            Expr::app(cast_fn, b),
        ),
    );
    assert_eq!(
        result, expected,
        "push_casts_to_leaves must recurse into Proj"
    );
}

#[test]
fn test_push_casts_to_leaves_inside_mdata() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let cast_fn = Expr::const_(Name::from_string("Nat.cast"), vec![]);
    let a_plus_b = Expr::app(Expr::app(add.clone(), a.clone()), b.clone());
    let cast_sum = Expr::app(cast_fn.clone(), a_plus_b);
    let mdata = Expr::mdata(vec![], cast_sum);
    let result = push_casts_to_leaves(&mdata);
    let expected = Expr::mdata(
        vec![],
        Expr::app(
            Expr::app(add, Expr::app(cast_fn.clone(), a)),
            Expr::app(cast_fn, b),
        ),
    );
    assert_eq!(
        result, expected,
        "push_casts_to_leaves must recurse into MData"
    );
}

// --- zify_expr tests (cast.rs) ---
// Nat.sub inside wrappers should be transformed to Int operations.

#[test]
fn test_zify_expr_inside_proj() {
    let env = setup_env();
    let mut state = ProofState::new(env, Expr::type_());
    let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let inner = Expr::app(nat_sub, nat_zero);
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, inner);
    let result = zify_expr(&proj, &mut state);
    // The Nat.sub should trigger zification — result should differ from input
    assert_ne!(
        result, proj,
        "zify_expr must recurse into Proj and transform Nat.sub"
    );
    // The outer wrapper should be preserved as Proj
    assert!(
        matches!(result.kind(), ExprKind::Proj(name, 0, _) if name.to_string() == "Prod.fst"),
        "zify_expr should preserve Proj wrapper"
    );
}

#[test]
fn test_zify_expr_inside_mdata() {
    let env = setup_env();
    let mut state = ProofState::new(env, Expr::type_());
    let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let inner = Expr::app(nat_sub, nat_zero);
    let mdata = Expr::mdata(vec![], inner);
    let result = zify_expr(&mdata, &mut state);
    assert_ne!(
        result, mdata,
        "zify_expr must recurse into MData and transform Nat.sub"
    );
    assert!(
        matches!(result.kind(), ExprKind::MData(_, _)),
        "zify_expr should preserve MData wrapper"
    );
}

// --- qify_expr tests (cast.rs) ---
// Int.div inside wrappers should be transformed to Rat operations.

#[test]
fn test_qify_expr_inside_proj() {
    let env = setup_env();
    let mut state = ProofState::new(env, Expr::type_());
    let int_div = Expr::const_(Name::from_string("Int.div"), vec![]);
    let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
    let inner = Expr::app(int_div, int_zero);
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, inner);
    let result = qify_expr(&proj, &mut state);
    assert_ne!(
        result, proj,
        "qify_expr must recurse into Proj and transform Int.div"
    );
    assert!(
        matches!(result.kind(), ExprKind::Proj(name, 0, _) if name.to_string() == "Prod.fst"),
        "qify_expr should preserve Proj wrapper"
    );
}

#[test]
fn test_qify_expr_inside_mdata() {
    let env = setup_env();
    let mut state = ProofState::new(env, Expr::type_());
    let int_div = Expr::const_(Name::from_string("Int.div"), vec![]);
    let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
    let inner = Expr::app(int_div, int_zero);
    let mdata = Expr::mdata(vec![], inner);
    let result = qify_expr(&mdata, &mut state);
    assert_ne!(
        result, mdata,
        "qify_expr must recurse into MData and transform Int.div"
    );
    assert!(
        matches!(result.kind(), ExprKind::MData(_, _)),
        "qify_expr should preserve MData wrapper"
    );
}

// --- substitute_fvar tests (finite_cases.rs) ---
// FVar inside wrappers should be substituted with replacement.

#[test]
fn test_substitute_fvar_inside_proj() {
    let fvar_id = FVarId::new(42);
    let target = Expr::fvar(fvar_id);
    let replacement = Expr::const_(Name::from_string("replaced"), vec![]);
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, target);
    let result = substitute_fvar(&proj, fvar_id, &replacement);
    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, replacement);
    assert_eq!(result, expected, "substitute_fvar must recurse into Proj");
}

#[test]
fn test_substitute_fvar_inside_mdata() {
    let fvar_id = FVarId::new(42);
    let target = Expr::fvar(fvar_id);
    let replacement = Expr::const_(Name::from_string("replaced"), vec![]);
    let mdata = Expr::mdata(vec![], target);
    let result = substitute_fvar(&mdata, fvar_id, &replacement);
    let expected = Expr::mdata(vec![], replacement);
    assert_eq!(result, expected, "substitute_fvar must recurse into MData");
}

#[test]
fn test_substitute_fvar_inside_squash() {
    let fvar_id = FVarId::new(42);
    let target = Expr::fvar(fvar_id);
    let replacement = Expr::const_(Name::from_string("replaced"), vec![]);
    let squash = make_squash(target);
    let result = substitute_fvar(&squash, fvar_id, &replacement);
    let expected = make_squash(replacement);
    assert_eq!(result, expected, "substitute_fvar must recurse into Squash");
}

// --- beta_reduce_all tests (debug.rs) ---
// Beta-redex (fun x => x) a inside wrappers should reduce to a.

#[test]
fn test_beta_reduce_all_inside_proj() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    // (fun _ : Type => #0) a  →  a
    let lam = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let redex = Expr::app(lam, a.clone());
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, redex);
    let result = beta_reduce_all(&proj);
    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, a);
    assert_eq!(result, expected, "beta_reduce_all must recurse into Proj");
}

#[test]
fn test_beta_reduce_all_inside_mdata() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let lam = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let redex = Expr::app(lam, a.clone());
    let mdata = Expr::mdata(vec![], redex);
    let result = beta_reduce_all(&mdata);
    let expected = Expr::mdata(vec![], a);
    assert_eq!(result, expected, "beta_reduce_all must recurse into MData");
}

#[test]
fn test_beta_reduce_all_inside_squash() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let lam = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let redex = Expr::app(lam, a.clone());
    let squash = make_squash(redex);
    let result = beta_reduce_all(&squash);
    let expected = make_squash(a);
    assert_eq!(result, expected, "beta_reduce_all must recurse into Squash");
}
