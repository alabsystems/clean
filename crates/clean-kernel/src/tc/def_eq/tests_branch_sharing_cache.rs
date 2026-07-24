// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Branch-sharing verified-pair cache behavioral tests (#3402).
//!
//! These tests exercise the amortization and consistency properties of
//! `BranchSharingCache::verified_pairs`. Correctness tests for the
//! `try_branch_sharing_def_eq` entry point live in `tests.rs`.

use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;
use crate::tc::TypeChecker;

/// The verified-pair cache grows on the first shared-prefix spine
/// comparison and then stays bounded as 48 more cross-branch pairs run.
///
/// Constructs branch(i) = `semBinOp bind0 bind1 bind2 bind3 i` and
/// compares `branch(0)` against `branch(1..=49)`. Suffixes differ so
/// each comparison descends through `is_def_eq_app_spine`, hitting
/// `branch_sharing_compare` on every prefix arg. The shared 4-arg
/// prefix gets recorded on the first call and served from the
/// verified-pair cache thereafter, so cache growth across the
/// remaining 48 comparisons must be sub-linear in prefix size.
#[test]
fn test_branch_sharing_verified_pair_cache_grows_sublinearly() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("semBinOp"), vec![]);
    let make_shared = || {
        (0..4u64)
            .map(|i| {
                Expr::app(
                    Expr::const_(Name::from_string(&format!("bind{}", i)), vec![]),
                    Expr::nat_lit(i),
                )
            })
            .collect::<Vec<Expr>>()
    };
    let branch = |suffix: u64| {
        let mut args = make_shared();
        args.push(Expr::nat_lit(suffix));
        Expr::apps(f.clone(), args)
    };

    let initial = tc.branch_sharing_verified_pair_count();
    assert!(
        !tc.is_def_eq(&branch(0), &branch(1)),
        "different suffixes must not be def-eq"
    );
    let after_first = tc.branch_sharing_verified_pair_count();
    assert!(
        after_first > initial,
        "verified-pair cache should grow on first shared-prefix spine compare: \
         before={}, after={}",
        initial,
        after_first
    );

    for i in 2..50u64 {
        assert!(
            !tc.is_def_eq(&branch(0), &branch(i)),
            "branch(0) vs branch({}) must not be def-eq",
            i
        );
    }
    let after_all = tc.branch_sharing_verified_pair_count();

    // With sharing, growth should be <= 2 entries per additional
    // branch (suffix pair + any branch-root bookkeeping). Without
    // sharing, growth would be 4 entries/branch = 192 new entries.
    let bound = after_first + 48 * 2;
    assert!(
        after_all <= bound,
        "per-branch cache growth exceeded 2 entries/branch — sharing is not \
         amortizing shared-prefix verification: after_first={}, after_all={}, bound={}",
        after_first,
        after_all,
        bound
    );
}

/// A warm TypeChecker (with cache state) must never disagree with a
/// fresh TypeChecker (no cache) for the same `is_def_eq` query.
///
/// Runs 20 mixed EQ/NEQ branch comparisons on a warm TC, then re-runs
/// each pair on a fresh TC. Any cache soundness bug would surface as a
/// disagreement between the two. Exercises both the positive path
/// (verified-pair hits returning true) and the negative path (cached
/// def_eq_cache returning false).
#[test]
fn test_branch_sharing_cache_consistency_with_fresh_tc() {
    let env = Environment::new();
    let warm_tc = TypeChecker::new(&env);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let f = Expr::const_(Name::from_string("dispatch"), vec![]);
    let g = Expr::const_(Name::from_string("other"), vec![]);
    let shared: Vec<Expr> = (0..4u64)
        .map(|i| Expr::const_(Name::from_string(&format!("prefix{}", i)), vec![]))
        .collect();

    let make_branch = |head: &Expr, suffix: u64| {
        let mut args = shared.clone();
        args.push(Expr::nat_lit(suffix));
        Expr::lam(
            BinderInfo::Default,
            nat_ty.clone(),
            Expr::apps(head.clone(), args),
        )
    };

    let cases: Vec<(Expr, Expr, bool)> = (0..20u64)
        .map(|i| {
            let a = make_branch(&f, i);
            let (b, expected) = if i % 2 == 0 {
                (make_branch(&f, i), true)
            } else {
                (make_branch(&g, i), false)
            };
            (a, b, expected)
        })
        .collect();

    for (i, (a, b, expected)) in cases.iter().enumerate() {
        let warm = warm_tc.is_def_eq(a, b);
        assert_eq!(
            warm, *expected,
            "warm-cache answer mismatch on branch {} (expected {})",
            i, expected
        );

        let fresh_tc = TypeChecker::new(&env);
        let fresh = fresh_tc.is_def_eq(a, b);
        assert_eq!(
            warm, fresh,
            "cache disagreement on branch {}: warm={} fresh={}",
            i, warm, fresh
        );
    }
}

/// Regression: the branch-sharing WHNF memo (`BranchSharingCache::entries`)
/// must be keyed by full structural `Expr` equality, NOT a truncated 32-bit
/// `hash_cached()`. The same-const-head arm of `is_def_eq_app_spine` routes
/// every argument through `branch_sharing_compare`, which memoizes no-delta
/// WHNF results; a hash-only key made a 32-bit collision return the WRONG
/// reduced expression, so a congruence that only holds AFTER argument
/// reduction was spuriously rejected. This is the LieDerivation
/// `SMulCommClass` failure in miniature: the arguments are beta-redexes that
/// reduce to a shared normal form, and `branch_sharing_compare` MUST agree
/// with `is_def_eq_impl` for each of them.
#[test]
fn test_branch_sharing_whnf_memo_congruence_with_reducing_args() {
    use crate::expr::BinderInfo;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Same Const head on both sides -> the branch-sharing arg loop is used.
    let c = Expr::const_(Name::from_string("C"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    // arg_redex = (fun (x : Nat) => x) 0   --beta-->   0 = arg_norm
    let id_fun = Expr::lam(BinderInfo::Default, nat_ty, Expr::bvar(0));
    let arg_redex = Expr::app(id_fun, Expr::nat_lit(0));
    let arg_norm = Expr::nat_lit(0);

    // Each argument is def-eq only after WHNF; branch_sharing_compare must
    // reduce and match, and must never disagree with is_def_eq_impl.
    assert!(tc.is_def_eq_impl(&arg_redex, &arg_norm));
    assert!(tc.branch_sharing_compare(&arg_redex, &arg_norm));
    assert_eq!(
        tc.is_def_eq_impl(&arg_redex, &arg_norm),
        tc.branch_sharing_compare(&arg_redex, &arg_norm),
        "branch_sharing_compare must agree with is_def_eq_impl"
    );

    // Full congruence through the same-const-head app spine.
    let lhs = Expr::apps(c.clone(), [arg_redex.clone(), arg_redex.clone()]);
    let rhs = Expr::apps(c.clone(), [arg_norm.clone(), arg_norm.clone()]);
    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "congruence must hold: C (id 0) (id 0) =?= C 0 0"
    );

    // A genuine mismatch must still be rejected (no over-acceptance).
    let rhs_bad = Expr::apps(c, [arg_norm.clone(), Expr::nat_lit(1)]);
    assert!(
        !tc.is_def_eq(&lhs, &rhs_bad),
        "C (id 0) (id 0) must NOT equal C 0 1"
    );
}
