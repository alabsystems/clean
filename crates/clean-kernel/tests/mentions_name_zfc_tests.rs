// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test that mentions_name correctly traverses ZFC expression variants.
//!
//! Prior to #1824 (ExprVisitor migration, W3-731), mentions_name returned
//! false unconditionally for all ZFC expressions. This test verifies the
//! ExprVisitor-based implementation recurses into ZFC children.
//!
//! Part of #1824

use std::sync::Arc;

use clean_kernel::expr::{Expr, ExprKind, ZFCSetExpr};
use clean_kernel::inductive::mentions_name;
use clean_kernel::Name;

#[test]
fn test_mentions_name_zfc_singleton() {
    let target = Name::from_string("MyType");
    let target_ref = Expr::const_(target.clone(), vec![]);

    let singleton = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(Arc::new(
        target_ref,
    ))));
    assert!(
        mentions_name(&singleton, &target),
        "Should find name inside ZFCSet(Singleton(Const(target)))"
    );
}

#[test]
fn test_mentions_name_zfc_pair() {
    let target = Name::from_string("MyType");
    let target_ref = Expr::const_(target.clone(), vec![]);
    let other = Expr::const_(Name::from_string("Other"), vec![]);

    let pair = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
        Arc::new(other),
        Arc::new(target_ref),
    )));
    assert!(
        mentions_name(&pair, &target),
        "Should find name inside ZFCSet(Pair(_, Const(target)))"
    );
}

#[test]
fn test_mentions_name_zfc_mem_element() {
    let target = Name::from_string("MyType");
    let target_ref = Expr::const_(target.clone(), vec![]);
    let other = Expr::const_(Name::from_string("Other"), vec![]);

    let mem = Expr::from_kind(ExprKind::ZFCMem {
        element: Arc::new(target_ref),
        set: Arc::new(other),
    });
    assert!(
        mentions_name(&mem, &target),
        "Should find name in ZFCMem element"
    );
}

#[test]
fn test_mentions_name_zfc_mem_set() {
    let target = Name::from_string("MyType");
    let target_ref = Expr::const_(target.clone(), vec![]);
    let other = Expr::const_(Name::from_string("Other"), vec![]);

    let mem_in_set = Expr::from_kind(ExprKind::ZFCMem {
        element: Arc::new(other),
        set: Arc::new(target_ref),
    });
    assert!(
        mentions_name(&mem_in_set, &target),
        "Should find name in ZFCMem set"
    );
}

#[test]
fn test_mentions_name_zfc_comprehension() {
    let target = Name::from_string("MyType");
    let target_ref = Expr::const_(target.clone(), vec![]);
    let other = Expr::const_(Name::from_string("Other"), vec![]);

    let comp = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(target_ref),
        pred: Arc::new(other),
    });
    assert!(
        mentions_name(&comp, &target),
        "Should find name in ZFCComprehension domain"
    );
}

#[test]
fn test_mentions_name_zfc_negative() {
    let target = Name::from_string("MyType");
    let other = Expr::const_(Name::from_string("Other"), vec![]);

    let no_match = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(Arc::new(other))));
    assert!(
        !mentions_name(&no_match, &target),
        "Should not find name when absent from ZFC expression"
    );
}

#[test]
fn test_mentions_name_zfc_separation_nested() {
    let target = Name::from_string("MyType");
    let target_ref = Expr::const_(target.clone(), vec![]);
    let other = Expr::const_(Name::from_string("Other"), vec![]);

    let separation = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
        set: Arc::new(other),
        pred: Arc::new(target_ref),
    }));
    assert!(
        mentions_name(&separation, &target),
        "Should find name in nested ZFCSet Separation pred"
    );
}
