// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for ZFC positivity checker soundness (#2152).
//!
//! Verifies that `mentions_name` (fixed in #1824 via ExprVisitor) and
//! `check_strictly_positive_impl` (fixed in #2152) correctly recurse
//! into ZFC expression children.

use clean_kernel::expr::{ExprKind, ZFCSetExpr};
use clean_kernel::inductive::{check_positivity, mentions_name};
use clean_kernel::name::Name;
use clean_kernel::Expr;
use std::sync::Arc;

#[test]
fn test_mentions_name_zfc_mem_contains_name() {
    let foo = Name::from_string("Foo");
    let foo_ref = Expr::const_(foo.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);

    // ZFCMem { element: Foo, set: Nat }
    let mem_expr = Expr::from_kind(ExprKind::ZFCMem {
        element: Arc::new(foo_ref),
        set: Arc::new(nat_ref),
    });

    assert!(
        mentions_name(&mem_expr, &foo),
        "mentions_name should find Foo inside ZFCMem element"
    );
}

#[test]
fn test_mentions_name_zfc_comprehension_contains_name() {
    let foo = Name::from_string("Foo");
    let foo_ref = Expr::const_(foo.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);

    // ZFCComprehension { domain: Foo, pred: Nat }
    let comp_expr = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(foo_ref),
        pred: Arc::new(nat_ref),
    });

    assert!(
        mentions_name(&comp_expr, &foo),
        "mentions_name should find Foo inside ZFCComprehension domain"
    );
}

#[test]
fn test_mentions_name_zfc_set_singleton_contains_name() {
    let foo = Name::from_string("Foo");
    let foo_ref = Expr::const_(foo.clone(), vec![]);

    let set_expr = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(Arc::new(foo_ref))));

    assert!(
        mentions_name(&set_expr, &foo),
        "mentions_name should find Foo inside ZFCSet(Singleton)"
    );
}

#[test]
fn test_positivity_zfc_mem_hides_negative_occurrence() {
    // A constructor like (ZFCMem { element: (Foo -> Nat), set: S }) -> Foo
    // has Foo in negative position inside the ZFCMem element field.
    let foo = Name::from_string("Foo");
    let foo_ref = Expr::const_(foo.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let set_ref = Expr::const_(Name::from_string("S"), vec![]);

    // element = (Foo -> Nat) -- Foo in negative position
    let element = Expr::arrow(foo_ref.clone(), nat_ref);

    // ZFCMem { element: (Foo -> Nat), set: S }
    let mem_expr = Expr::from_kind(ExprKind::ZFCMem {
        element: Arc::new(element),
        set: Arc::new(set_ref),
    });

    // Constructor: ZFCMem{...} -> Foo
    let ctor_type = Expr::arrow(mem_expr, foo_ref);

    // check_strictly_positive_impl now recurses into ZFCMem children,
    // detecting the negative occurrence of Foo in (Foo -> Nat).
    let result = check_positivity(&foo, &ctor_type, 0, &[&foo]);
    assert!(
        result.is_err(),
        "Positivity checker should detect Foo->Nat inside ZFCMem element as non-positive"
    );
}
