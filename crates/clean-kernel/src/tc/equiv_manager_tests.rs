// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the union-find equivalence manager.
//!
//! Split from `equiv_manager.rs` for the 500-line file size limit (#2548).

use super::equiv_manager::*;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::Level;
use std::sync::Arc;

fn mk_bvar(idx: u32) -> Expr {
    Expr::from_kind(ExprKind::BVar(idx))
}

fn mk_sort(n: u32) -> Expr {
    Expr::from_kind(ExprKind::Sort(Level::zero().add_offset(n)))
}

fn mk_app(f: &Expr, a: &Expr) -> Expr {
    Expr::from_kind(ExprKind::App(Arc::new(f.clone()), Arc::new(a.clone())))
}

fn mk_lam(ty: &Expr, body: &Expr) -> Expr {
    Expr::from_kind(ExprKind::Lam(
        BinderInfo::Default.into(),
        Arc::new(ty.clone()),
        Arc::new(body.clone()),
    ))
}

#[test]
fn test_basic_equiv() {
    let mut em = EquivManager::new();
    let (a, b) = (mk_sort(0), mk_sort(1));
    assert!(!em.is_equiv(&a, &b, true));
    em.add_equiv(&a, &b);
    assert!(em.is_equiv(&a, &b, true));
}

#[test]
fn test_transitivity() {
    let mut em = EquivManager::new();
    let (a, b, c) = (mk_sort(0), mk_sort(1), mk_sort(2));
    em.add_equiv(&a, &b);
    em.add_equiv(&b, &c);
    assert!(em.is_equiv(&a, &c, true));
}

#[test]
fn test_symmetry() {
    let mut em = EquivManager::new();
    let (a, b) = (mk_sort(0), mk_sort(1));
    em.add_equiv(&a, &b);
    assert!(em.is_equiv(&b, &a, true));
}

#[test]
fn test_clear() {
    let mut em = EquivManager::new();
    let (a, b) = (mk_sort(0), mk_sort(1));
    em.add_equiv(&a, &b);
    assert!(em.is_equiv(&a, &b, true));
    em.clear();
    assert!(!em.is_equiv(&a, &b, true));
}

#[test]
fn test_structural_fallback() {
    let mut em = EquivManager::new();
    let inner = mk_sort(0);
    let a = mk_app(&inner, &mk_bvar(0));
    let b = mk_app(&inner, &mk_bvar(0));
    assert!(em.is_equiv(&a, &b, true)); // structural match
    assert!(em.is_equiv(&a, &b, true)); // union-find hit
}

#[test]
fn test_structural_mismatch() {
    let mut em = EquivManager::new();
    assert!(!em.is_equiv(
        &mk_app(&mk_sort(0), &mk_bvar(0)),
        &mk_app(&mk_sort(0), &mk_bvar(1)),
        true
    ));
}

#[test]
fn test_hash_prefilter() {
    let mut em = EquivManager::new();
    assert!(!em.is_equiv(&mk_sort(0), &mk_sort(1), true));
}

/// #1390: add_equiv must override hash pre-filter.
#[test]
fn test_add_equiv_overrides_hash_prefilter() {
    let mut em = EquivManager::new();
    let (a, b) = (mk_sort(0), mk_sort(1));
    assert!(!em.is_equiv(&a, &b, true));
    em.add_equiv(&a, &b);
    assert!(
        em.is_equiv(&a, &b, true),
        "add_equiv must override hash pre-filter"
    );
    assert!(
        em.is_equiv(&b, &a, true),
        "symmetry must override hash pre-filter"
    );
}

#[test]
fn test_bvar_fast_path() {
    let mut em = EquivManager::new();
    assert!(em.is_equiv(&mk_bvar(5), &mk_bvar(5), true));
    assert!(!em.is_equiv(&mk_bvar(5), &mk_bvar(6), true));
}

#[test]
fn test_deep_compound() {
    let mut em = EquivManager::new();
    let base = mk_sort(0);
    assert!(em.is_equiv(
        &mk_lam(&base, &mk_lam(&base, &mk_bvar(0))),
        &mk_lam(&base, &mk_lam(&base, &mk_bvar(0))),
        true,
    ));
}

/// #1777 pinned the pinned v4.30.0-rc2 `equiv_manager.cpp:103`, whose `Proj`
/// arm compared only the index and the subject. Lean v4.33.1 compares the
/// structure name too (leanprover/lean4#14631), and so does Clean since
/// decision R147: an index means a field of one structure's layout.
#[test]
fn test_proj_compares_struct_name() {
    use crate::Name;
    let mut em = EquivManager::new();
    let inner = Arc::new(mk_sort(0));
    let mk_proj = |name: &str, idx: u32| {
        Expr::from_kind(ExprKind::Proj(Name::from_string(name), idx, inner.clone()))
    };
    // Same structure and index → equiv.
    assert!(em.is_equiv(&mk_proj("Prod", 0), &mk_proj("Prod", 0), false));
    // Same index, different structure → not equiv.
    assert!(!em.is_equiv(&mk_proj("Prod", 0), &mk_proj("PProd", 0), false));
    // Different index → not equiv.
    assert!(!em.is_equiv(&mk_proj("Prod", 0), &mk_proj("Prod", 1), false));
}

#[test]
fn test_len_and_growth() {
    let mut em = EquivManager::new();
    assert_eq!(em.len(), 0);

    let a = mk_sort(0);
    let b = mk_sort(1);
    em.add_equiv(&a, &b);
    assert_eq!(em.len(), 2);

    let c = mk_sort(2);
    em.add_equiv(&b, &c);
    assert_eq!(em.len(), 3);

    em.clear();
    assert_eq!(em.len(), 0);
}

/// EquivManager grows without bound (eviction is in SlidingEquivManager).
#[test]
fn test_equiv_manager_grows_without_bound() {
    let mut em = EquivManager::new();

    // Insert 10K unique expression pairs — the map grows monotonically.
    for i in 0..10_000u32 {
        let a = mk_app(&mk_sort(i), &mk_bvar(0));
        let b = mk_app(&mk_sort(i), &mk_bvar(1));
        em.add_equiv(&a, &b);
    }

    // EquivManager has 20K entries (2 per pair) with no internal trim.
    assert!(
        em.len() >= 20_000,
        "should accumulate >=20K entries, got {}",
        em.len()
    );
}

/// Lean v4.33.1 (leanprover/lean4#14631) dropped the union-find for pair caches
/// keyed on full expression equality, which compares a projection's structure
/// name. Clean keeps the union-find, so its `Proj` arm must compare the name:
/// `Proj(A, 0, x)` and `Proj(B, 0, x)` select different field layouts and are
/// not structurally equal. The same-name pair is the control.
#[test]
fn equiv_manager_does_not_equate_projections_of_different_structures() {
    use crate::name::Name;

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let proj_a = Expr::proj(Name::from_string("A"), 0, x.clone());
    let proj_a_again = Expr::proj(Name::from_string("A"), 0, x.clone());
    let proj_b = Expr::proj(Name::from_string("B"), 0, x);

    let mut em = EquivManager::new();
    assert!(
        em.is_equiv(&proj_a, &proj_a_again, true),
        "control: two A.0 projections of the same term are equivalent"
    );
    let mut em = EquivManager::new();
    assert!(
        !em.is_equiv(&proj_a, &proj_b, true),
        "A.0 x and B.0 x must not be structurally equivalent"
    );
    let mut em = EquivManager::new();
    assert!(
        !em.is_equiv(&proj_a, &proj_b, false),
        "A.0 x and B.0 x must not be structurally equivalent (no hash pre-filter)"
    );
}
