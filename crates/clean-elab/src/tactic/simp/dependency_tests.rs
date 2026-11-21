// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::{argument_has_dependents, beta_reduce, mentions_fvar, mentions_fvar_after_beta};
use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId};
use std::cell::Cell;
use std::sync::Arc;

thread_local! {
    pub(super) static BETA_FOLDS: Cell<usize> = const { Cell::new(0) };
}

#[test]
fn large_unrelated_domain_skips_the_old_beta_fold() {
    // ∀ (P : Prop) (i : Nat) (_ : P), (fun _ : Nat => True) i.
    // Checking whether i is frozen visits both the supplied P and the result.
    let nat = Expr::const_str("Nat");
    let constant_motive = Expr::lam(BinderInfo::Default, nat.clone(), Expr::const_str("True"));
    let telescope = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(
            BinderInfo::Default,
            nat,
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::app(constant_motive, Expr::bvar(1)),
            ),
        ),
    );
    let mut proposition = Expr::fvar(FVarId::new(1));
    for _ in 0..10 {
        proposition = Expr::apps(Expr::const_str("And"), [proposition.clone(), proposition]);
    }
    let sentinel = FVarId::new((1u64 << 63) - 1);
    assert!(!mentions_fvar(&beta_reduce(&proposition), sentinel));
    BETA_FOLDS.set(0);
    assert!(!mentions_fvar_after_beta(&proposition, sentinel));
    assert_eq!(BETA_FOLDS.get(), 0, "1024 unrelated leaf occurrences");
    let i = Expr::nat_lit(7);
    let evidence = Expr::fvar(FVarId::new(2));
    assert!(!argument_has_dependents(
        &telescope,
        &[&proposition, &i, &evidence],
        1
    ));
    assert_eq!(BETA_FOLDS.get(), 1, "the result still needs beta reduction");
}

#[test]
fn possible_and_unknown_bounds_keep_the_exact_reduced_occurrence_test() {
    let sentinel = FVarId::new((1u64 << 63) - 1);
    let local = Expr::fvar(sentinel);
    let identity = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let constant = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::const_str("True"));
    let unknown = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(Arc::new(
        Expr::fvar(FVarId::new(1)),
    ))));
    for (input, expected) in [
        (Expr::app(identity, local.clone()), true),
        (Expr::app(constant, local), false),
        (Expr::fvar(FVarId::new(u64::MAX)), false),
        (unknown, false),
    ] {
        BETA_FOLDS.set(0);
        assert_eq!(mentions_fvar_after_beta(&input, sentinel), expected);
        assert_eq!(mentions_fvar(&beta_reduce(&input), sentinel), expected);
        assert_eq!(BETA_FOLDS.get(), 1);
    }
}
