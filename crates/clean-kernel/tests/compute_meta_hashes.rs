// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for compute_meta hash quality fixes (#1356).
//!
//! Verifies that distinct expression kinds produce distinct hashes,
//! and that child metadata (fvar, mvar flags, bvar range) propagates
//! through all clean-only extension variants.

use clean_kernel::{Expr, ExprKind, FVarId, Level, Name};
use std::sync::Arc;

// ============================================================================
// Hash distinctness tests — leaf extensions
// ============================================================================

#[test]
fn leaf_extensions_have_distinct_hashes() {
    let sprop = Expr::from_kind(ExprKind::SProp);
    let interval = Expr::from_kind(ExprKind::CubicalInterval);
    let i0 = Expr::from_kind(ExprKind::CubicalI0);
    let i1 = Expr::from_kind(ExprKind::CubicalI1);

    let hashes: Vec<u32> = [&sprop, &interval, &i0, &i1]
        .iter()
        .map(|e| e.hash_cached())
        .collect();

    // All four must be non-zero and pairwise distinct.
    for (idx, h) in hashes.iter().enumerate() {
        assert_ne!(*h, 0, "leaf extension hash at index {idx} must not be zero");
    }
    for i in 0..hashes.len() {
        for j in (i + 1)..hashes.len() {
            assert_ne!(
                hashes[i], hashes[j],
                "leaf extensions at indices {i} and {j} must have distinct hashes"
            );
        }
    }
}

// ============================================================================
// Hash distinctness tests — multi-child extensions
// ============================================================================

#[test]
fn cubical_path_has_nonzero_hash() {
    let child1 = Expr::prop();
    let child2 = Expr::fvar(FVarId::new(1));
    let child3 = Expr::fvar(FVarId::new(2));
    let path = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(child1),
        left: Arc::new(child2),
        right: Arc::new(child3),
    });
    assert_ne!(path.hash_cached(), 0, "CubicalPath hash must not be zero");
}

#[test]
fn cubical_hcomp_has_nonzero_hash() {
    let ty = Expr::prop();
    let phi = Expr::fvar(FVarId::new(10));
    let u = Expr::fvar(FVarId::new(11));
    let base = Expr::fvar(FVarId::new(12));
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(ty),
        phi: Arc::new(phi),
        u: Arc::new(u),
        base: Arc::new(base),
    });
    assert_ne!(hcomp.hash_cached(), 0, "CubicalHComp hash must not be zero");
}

#[test]
fn cubical_transp_has_nonzero_hash() {
    let ty = Expr::prop();
    let phi = Expr::fvar(FVarId::new(20));
    let base = Expr::fvar(FVarId::new(21));
    let transp = Expr::from_kind(ExprKind::CubicalTransp {
        ty: Arc::new(ty),
        phi: Arc::new(phi),
        base: Arc::new(base),
    });
    assert_ne!(
        transp.hash_cached(),
        0,
        "CubicalTransp hash must not be zero"
    );
}

// ============================================================================
// Metadata propagation tests — formerly-wildcard variants
// ============================================================================

#[test]
fn zfc_mem_propagates_fvar_flag() {
    let fvar_expr = Expr::fvar(FVarId::new(50));
    let mem = Expr::from_kind(ExprKind::ZFCMem {
        element: Arc::new(fvar_expr),
        set: Arc::new(Expr::prop()),
    });
    assert!(
        mem.has_fvar_quick(),
        "ZFCMem must propagate has_fvar from element"
    );
    assert_ne!(mem.hash_cached(), 0, "ZFCMem hash must not be zero");
}

#[test]
fn zfc_comprehension_propagates_fvar_flag() {
    let fvar_expr = Expr::fvar(FVarId::new(60));
    let comp = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::prop()),
        pred: Arc::new(fvar_expr),
    });
    assert!(
        comp.has_fvar_quick(),
        "ZFCComprehension must propagate has_fvar from pred"
    );
    assert_ne!(
        comp.hash_cached(),
        0,
        "ZFCComprehension hash must not be zero"
    );
}

// ============================================================================
// Metadata propagation tests — bvar range
// ============================================================================

#[test]
fn zfc_mem_propagates_bvar_range() {
    let bvar = Expr::from_kind(ExprKind::BVar(5));
    let mem = Expr::from_kind(ExprKind::ZFCMem {
        element: Arc::new(bvar),
        set: Arc::new(Expr::prop()),
    });
    assert!(
        mem.loose_bvar_range() >= 6,
        "ZFCMem must propagate bvar range from element; got {}",
        mem.loose_bvar_range()
    );
}

// ============================================================================
// Hash quality — different children produce different hashes
// ============================================================================

#[test]
fn cubical_path_different_children_different_hashes() {
    let p1 = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(Expr::prop()),
        left: Arc::new(Expr::fvar(FVarId::new(1))),
        right: Arc::new(Expr::fvar(FVarId::new(2))),
    });
    let p2 = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(Expr::prop()),
        left: Arc::new(Expr::fvar(FVarId::new(3))),
        right: Arc::new(Expr::fvar(FVarId::new(4))),
    });
    assert_ne!(
        p1.hash_cached(),
        p2.hash_cached(),
        "CubicalPath with different children should have different hashes"
    );
}

#[test]
fn different_const_names_different_hashes() {
    // Sanity: Lean 4-compatible variants already handled correctly
    let c1 = Expr::const_(Name::from_string("Foo"), vec![]);
    let c2 = Expr::const_(Name::from_string("Bar"), vec![]);
    assert_ne!(
        c1.hash_cached(),
        c2.hash_cached(),
        "distinct Const names should produce distinct hashes"
    );
}

#[test]
fn different_fvar_ids_different_hashes() {
    let f1 = Expr::fvar(FVarId::new(100));
    let f2 = Expr::fvar(FVarId::new(200));
    assert_ne!(
        f1.hash_cached(),
        f2.hash_cached(),
        "distinct FVarIds should produce distinct hashes"
    );
}

#[test]
fn different_sorts_different_hashes() {
    let s1 = Expr::sort(Level::zero());
    let s2 = Expr::sort(Level::succ(Level::zero()));
    assert_ne!(
        s1.hash_cached(),
        s2.hash_cached(),
        "distinct Sort levels should produce distinct hashes"
    );
}
