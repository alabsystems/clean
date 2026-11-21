// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Syntactic eligibility never substitutes for argument/universe unification.

use super::*;
use clean_kernel::{BinderInfo, Level};

#[test]
fn same_head_probe_keeps_arity_and_complete_owner_identity() {
    for arity in [1, 2, 64, 1024] {
        let left = Expr::apps(
            Expr::const_str("Owner.shared"),
            (0..arity).map(|_| Expr::nat_lit(1)),
        );
        let right = Expr::apps(
            Expr::const_str("Owner.shared"),
            (0..arity).map(|_| Expr::nat_lit(2)),
        );
        // Different arguments still admit a probe; the real unifier must
        // inspect them. A matching head does not assert their equality.
        assert!(same_constant_head(&left, &right));
        assert!(!same_constant_head(
            &left,
            &Expr::app(right, Expr::nat_lit(3))
        ));
        assert!(!same_constant_head(
            &left,
            &Expr::apps(
                Expr::const_str("OtherOwner.shared"),
                (0..arity).map(|_| Expr::nat_lit(1)),
            )
        ));
    }
}

#[test]
fn same_head_probe_declines_bare_constants_and_nonconstant_spines() {
    let head = Expr::const_str("Owner.shared");
    let application = Expr::app(head.clone(), Expr::nat_lit(1));
    assert!(!same_constant_head(&head, &head));
    assert!(!same_constant_head(&head, &application));
    assert!(!same_constant_head(&application, &head));
    for function in [
        Expr::bvar(0),
        Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0)),
    ] {
        let other = Expr::app(function, Expr::nat_lit(1));
        assert!(!same_constant_head(&application, &other));
        assert!(!same_constant_head(&other, &application));
    }
}

#[test]
fn same_head_probe_leaves_universe_comparison_to_the_actual_unifier() {
    let name = Name::from_string("Owner.shared");
    let left = Expr::app(
        Expr::const_(name.clone(), vec![Level::zero()]),
        Expr::nat_lit(1),
    );
    let right = Expr::app(
        Expr::const_(name, vec![Level::succ(Level::zero())]),
        Expr::nat_lit(1),
    );
    assert!(same_constant_head(&left, &right));
}
