// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Branch-sharing verified-pair cache behavioral tests (#3402).
//!
//! These tests exercise demand-driven normalization, bounded verified-pair
//! admission, and cache consistency. Additional recursor-congruence tests
//! live in `tests.rs`.

use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;
use std::sync::Arc;

/// A closed type that reduces to Nat, with a constructor-form major so that
/// demanding its iota reduction is visible to the full-WHNF call counter.
fn branch_sharing_type_probe() -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), Expr::type_());
    let step = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
    );
    Expr::apps(
        Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::succ(Level::zero()))],
        ),
        [
            motive,
            nat,
            step,
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ],
    )
}

/// T(0) reduces to Nat; T(n + 1) = T(n) -> T(n). Both Pi children share
/// one Arc, so the apparent binary type tree has only O(depth) allocations.
/// The accompanying closed inhabitant is zero, then successive constant
/// functions. No declarations or axioms are introduced by this fixture.
fn branch_sharing_type_dag(depth: usize) -> (Arc<Expr>, Arc<Expr>) {
    let mut ty = Arc::new(branch_sharing_type_probe());
    let mut value = Arc::new(Expr::const_(Name::from_string("Nat.zero"), vec![]));
    for _ in 0..depth {
        value = Arc::new(Expr::lam_arc(BinderInfo::Default, ty.clone(), value));
        ty = Arc::new(Expr::pi_arc(BinderInfo::Default, ty.clone(), ty));
    }
    (ty, value)
}

fn branch_sharing_ignored_type_redex(depth: usize) -> Expr {
    let (ty, value) = branch_sharing_type_dag(depth);
    let function = Expr::lam_arc(
        BinderInfo::Default,
        ty,
        Arc::new(Expr::const_(Name::from_string("Nat.zero"), vec![])),
    );
    Expr::app_arc(Arc::new(function), value)
}

#[test]
fn test_branch_sharing_identical_shared_dag_demands_no_whnf() {
    let mut env = Environment::new();
    env.init_nat().expect("initialize checked Nat vocabulary");
    let probe = branch_sharing_type_probe();
    let probe_tc = TypeChecker::new(&env);
    probe_tc
        .check_type(&probe, &Expr::type_())
        .expect("the hidden recursor is a closed type");

    // A fresh checker establishes that the counter detects this probe when
    // it is demanded. A Pi-only fixture would make zero-WHNF vacuous: normal
    // Pi/Lam leaves never increment the full-WHNF counter, even if visited.
    let control_tc = TypeChecker::new(&env);
    control_tc.reset_whnf_impl_call_count_for_tests();
    assert_eq!(
        control_tc.whnf_core_no_delta(&probe, true),
        Expr::const_(Name::from_string("Nat"), vec![])
    );
    assert!(control_tc.whnf_impl_call_count_for_tests() > 0);

    let (shared, _) = branch_sharing_type_dag(32);
    let same_structure = shared.as_ref().clone();
    assert!(!std::ptr::eq(shared.as_ref(), &same_structure));
    for same_pointer in [true, false] {
        let tc = TypeChecker::new(&env);
        tc.reset_whnf_impl_call_count_for_tests();
        let rhs = if same_pointer {
            shared.as_ref()
        } else {
            &same_structure
        };
        assert!(tc.branch_sharing_compare(shared.as_ref(), rhs));
        assert_eq!(
            tc.whnf_impl_call_count_for_tests(),
            0,
            "exact equality must not normalize the hidden recursor"
        );
        assert_eq!(tc.branch_sharing_verified_pair_count(), 1);
    }
}

#[test]
fn test_branch_sharing_beta_equality_does_not_prewarm_ignored_type_dag() {
    let mut env = Environment::new();
    env.init_nat().expect("initialize checked Nat vocabulary");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Validate the fixture recipe in a separate checker at shallow depth.
    // Inferring the large Pi DAG itself is not the work measured below.
    TypeChecker::new(&env)
        .check_type(&branch_sharing_ignored_type_redex(3), &nat)
        .expect("constant function and shared-type argument are well-typed");

    for depth in [0, 8, 32] {
        let redex = branch_sharing_ignored_type_redex(depth);
        assert_ne!(redex, zero, "this control must demand beta reduction");
        let tc = TypeChecker::new(&env);
        tc.reset_whnf_impl_call_count_for_tests();
        assert!(tc.branch_sharing_compare(&redex, &zero));
        assert_eq!(
            tc.whnf_impl_call_count_for_tests(),
            0,
            "beta equality must leave the ignored type probe untouched at depth {depth}"
        );
    }
}

#[test]
fn test_branch_sharing_verified_pair_admission_respects_zero_and_full_capacity() {
    let env = Environment::new();
    for capacity in [0, 1, 3] {
        let mut tc = TypeChecker::new(&env);
        tc.set_max_cache_entries(capacity);
        tc.reset_whnf_impl_call_count_for_tests();
        for i in 0..16 {
            let value = Expr::nat_lit(i as u64);
            assert!(tc.branch_sharing_compare(&value, &value));
            assert_eq!(
                tc.branch_sharing_verified_pair_count(),
                capacity.min(i + 1),
                "admission must stop without discarding existing pairs at capacity {capacity}"
            );
        }
        assert_eq!(tc.whnf_impl_call_count_for_tests(), 0);
    }
}

#[test]
fn test_branch_sharing_verified_nonstructural_hit_survives_full_admission() {
    let mut env = Environment::new();
    env.init_nat().expect("initialize checked Nat vocabulary");
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let name = Name::from_string("branchSharingCacheValue");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
        value: zero.clone(),
        is_reducible: true,
    })
    .expect("register a checked definition, not an equality axiom");
    let alias = Expr::const_(name, vec![]);
    assert_ne!(alias, zero);

    let mut tc = TypeChecker::new(&env);
    tc.set_max_cache_entries(2);
    tc.set_heartbeat_limit(10_000);
    assert!(tc.branch_sharing_compare(&alias, &zero));
    assert!(tc.heartbeat_remaining() < tc.heartbeat_limit());
    assert_eq!(tc.branch_sharing_verified_pair_count(), 1);
    let fill = Expr::nat_lit(7);
    assert!(tc.branch_sharing_compare(&fill, &fill));
    assert_eq!(tc.branch_sharing_verified_pair_count(), 2);
    let overflow = Expr::nat_lit(8);
    assert!(tc.branch_sharing_compare(&overflow, &overflow));
    assert_eq!(tc.branch_sharing_verified_pair_count(), 2);

    // Remove other equality shortcuts, leaving branch WHNF entries and the
    // verified pair intact. The cached roots are still alias versus zero,
    // so root-cache reuse alone would enter def-eq and consume a heartbeat.
    tc.def_eq_cache.borrow_mut().clear();
    tc.equiv_manager.borrow_mut().clear();
    tc.reset_heartbeat();
    tc.reset_whnf_impl_call_count_for_tests();
    assert!(tc.branch_sharing_compare(&alias, &zero));
    assert_eq!(tc.heartbeat_remaining(), tc.heartbeat_limit());
    assert_eq!(tc.whnf_impl_call_count_for_tests(), 0);
    assert_eq!(tc.branch_sharing_verified_pair_count(), 2);
}

#[test]
fn test_branch_sharing_genuine_inequality_under_cache_pressure() {
    let mut env = Environment::new();
    env.init_nat().expect("initialize checked Nat vocabulary");
    let id = Expr::lam(
        BinderInfo::Default,
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::bvar(0),
    );
    for capacity in [0, 1, 2] {
        let mut tc = TypeChecker::new(&env);
        tc.set_max_cache_entries(capacity);
        tc.set_heartbeat_limit(10_000);
        for value in 0..16 {
            tc.reset_heartbeat();
            let redex = Expr::app(id.clone(), Expr::nat_lit(value));
            assert!(tc.branch_sharing_compare(&redex, &Expr::nat_lit(value)));
            assert!(!tc.branch_sharing_compare(&redex, &Expr::nat_lit(value + 1)));
            assert!(
                tc.heartbeat_remaining() > 0,
                "inequality must not be a resource-exhaustion result"
            );
            assert!(tc.branch_sharing_verified_pair_count() <= capacity);
            let fresh_tc = TypeChecker::new(&env);
            assert!(!fresh_tc.branch_sharing_compare(&redex, &Expr::nat_lit(value + 1)));
        }
    }
}

#[test]
fn test_branch_sharing_different_unused_recursor_minors_defer_to_equal_result() {
    let mut env = Environment::new();
    env.init_nat().expect("initialize checked Nat vocabulary");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let minor = |result| {
        Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::lam(BinderInfo::Default, nat.clone(), Expr::nat_lit(result)),
        )
    };
    let lhs = Expr::apps(
        rec.clone(),
        [motive.clone(), zero.clone(), minor(0), zero.clone()],
    );
    let rhs = Expr::apps(rec, [motive, zero.clone(), minor(1), zero]);

    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(10_000);
    tc.check_type(&lhs, &nat).expect("left recursor is typed");
    tc.check_type(&rhs, &nat).expect("right recursor is typed");
    assert_eq!(
        tc.try_branch_sharing_def_eq(&lhs, &rhs),
        None,
        "different unused minors are a failed congruence attempt, not inequality"
    );
    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "both recursors select the shared zero case"
    );
    assert!(tc.heartbeat_remaining() > 0);
}

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
