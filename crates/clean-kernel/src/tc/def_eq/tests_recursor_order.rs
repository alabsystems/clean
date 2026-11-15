// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioral controls for major-before-minors structural congruence.

use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

fn motive(ty: Expr) -> Expr {
    lam(nat(), ty)
}

fn zero_step() -> Expr {
    lam(nat(), lam(nat(), Expr::nat_lit(0)))
}

fn rec(name: &str, motive: Expr, zero: Expr, step: Expr, major: Expr) -> Expr {
    let head = Expr::const_(Name::from_string(name), vec![Level::succ(Level::zero())]);
    if name == "Nat.recOn" {
        Expr::apps(head, [motive, major, zero, step])
    } else {
        Expr::apps(head, [motive, zero, step, major])
    }
}

fn nat_redex() -> Expr {
    rec(
        "Nat.rec",
        motive(nat()),
        Expr::nat_lit(0),
        zero_step(),
        // Literal majors return before the WHNF counter. A constructor
        // major keeps this genuine iota redex visible to the canary below.
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    )
}

fn fresh_nat(tc: &TypeChecker<'_>, name: &str) -> Expr {
    let id = tc
        .ctx_mut()
        .push(Name::from_string(name), nat(), BinderInfo::Default);
    Expr::fvar(id)
}

fn mismatch_fixture(tc: &TypeChecker<'_>, name: &str) -> (Expr, Expr, Expr, Expr) {
    let x = fresh_nat(tc, "x");
    let y = fresh_nat(tc, "y");
    let lhs = rec(name, motive(nat()), nat_redex(), zero_step(), x.clone());
    let rhs = rec(
        name,
        motive(nat()),
        Expr::nat_lit(0),
        zero_step(),
        y.clone(),
    );
    (lhs, rhs, x, y)
}

#[test]
fn test_recursor_structural_comparison_skips_minors_after_major_mismatch() {
    let mut env = Environment::new();
    env.init_nat().expect("checked Nat vocabulary");

    // A forced minor really does reduce and the counter detects it. This
    // checker is separate so it cannot prewarm the comparisons measured below.
    let control_tc = TypeChecker::new(&env);
    control_tc
        .check_type(&nat_redex(), &nat())
        .expect("typed minor");
    let control_tc = TypeChecker::new(&env);
    control_tc.reset_whnf_impl_call_count_for_tests();
    assert!(control_tc.is_def_eq(&nat_redex(), &Expr::nat_lit(0)));
    assert!(control_tc.whnf_impl_call_count_for_tests() > 0);

    for name in ["Nat.rec", "Nat.recOn"] {
        let typing_tc = TypeChecker::new(&env);
        let (lhs, rhs, _, _) = mismatch_fixture(&typing_tc, name);
        typing_tc
            .check_type(&lhs, &nat())
            .expect("typed left recursor");
        typing_tc
            .check_type(&rhs, &nat())
            .expect("typed right recursor");

        for cache_enabled in [false, true] {
            let mut tc = TypeChecker::new(&env);
            tc.set_heartbeat_limit(10_000);
            if !cache_enabled {
                tc.branch_sharing_cache = None;
            }
            let (lhs, rhs, x, y) = mismatch_fixture(&tc, name);
            assert!(!tc.is_def_eq(&x, &y));
            // This is the ordinary early congruence result, before the generic
            // structural attempt. It must remain a deferral, never inequality.
            assert_eq!(tc.try_branch_sharing_def_eq(&lhs, &rhs), None);
            tc.reset_whnf_impl_call_count_for_tests();
            assert!(!tc.is_def_eq_structural(&lhs, &rhs));
            assert_eq!(
                tc.whnf_impl_call_count_for_tests(),
                0,
                "{name} must reuse the major mismatch before demanding the minor"
            );
            assert!(!tc.heartbeat_spent());
        }
    }
}

#[test]
fn test_recursor_partial_application_keeps_supplied_argument_congruence() {
    let mut env = Environment::new();
    env.init_nat().expect("checked Nat vocabulary");
    for name in ["Nat.rec", "Nat.recOn"] {
        for cache_enabled in [false, true] {
            let mut tc = TypeChecker::new(&env);
            if !cache_enabled {
                tc.branch_sharing_cache = None;
            }
            let head = Expr::const_(Name::from_string(name), vec![Level::succ(Level::zero())]);
            // Both layouts accept Nat as their second argument, but neither
            // two-argument application has the complete recursor telescope.
            let partial = |value| Expr::apps(head.clone(), [motive(nat()), value]);
            let lhs = partial(nat_redex());
            let equal = partial(Expr::nat_lit(0));
            let different = partial(Expr::nat_lit(1));
            let ty = tc.infer_type(&lhs).expect("typed partial recursor");
            tc.check_type(&equal, &ty)
                .expect("typed equal partial recursor");
            tc.check_type(&different, &ty)
                .expect("typed different partial recursor");
            assert_eq!(tc.try_branch_sharing_def_eq(&lhs, &equal), None);
            assert!(tc.is_def_eq_structural(&lhs, &equal));
            assert!(!tc.is_def_eq_structural(&lhs, &different));
            assert!(tc.is_def_eq(&lhs, &equal));
            assert!(!tc.heartbeat_spent());
        }
    }
}

#[test]
fn test_recursor_overapplication_compares_extras_and_preserves_beta_reduction() {
    let mut env = Environment::new();
    env.init_nat().expect("checked Nat vocabulary");
    let function_ty = Expr::arrow(nat(), nat());
    let identity = lam(nat(), Expr::bvar(0));
    let step = lam(nat(), lam(function_ty.clone(), Expr::bvar(0)));
    for name in ["Nat.rec", "Nat.recOn"] {
        for cache_enabled in [false, true] {
            let mut tc = TypeChecker::new(&env);
            tc.set_heartbeat_limit(10_000);
            if !cache_enabled {
                tc.branch_sharing_cache = None;
            }
            let major = fresh_nat(&tc, "major");
            let core = rec(
                name,
                motive(function_ty.clone()),
                identity.clone(),
                step.clone(),
                major,
            );
            let lhs = Expr::app(core.clone(), nat_redex());
            let equal = Expr::app(core.clone(), Expr::nat_lit(0));
            let different = Expr::app(core, Expr::nat_lit(1));
            for term in [&lhs, &equal, &different] {
                tc.check_type(term, &nat())
                    .expect("typed overapplied recursor");
            }
            assert!(tc.is_def_eq_structural(&lhs, &equal));
            assert!(!tc.is_def_eq_structural(&lhs, &different));
            assert!(tc.is_def_eq(&lhs, &equal));

            // Once iota selects a constant function, different extra arguments
            // can be ignored by beta. Failed congruence must still allow that.
            let constant_core = rec(
                name,
                motive(function_ty.clone()),
                lam(nat(), Expr::nat_lit(0)),
                step.clone(),
                Expr::nat_lit(0),
            );
            let left = Expr::app(constant_core.clone(), Expr::nat_lit(0));
            let right = Expr::app(constant_core, Expr::nat_lit(1));
            assert_eq!(tc.try_branch_sharing_def_eq(&left, &right), None);
            assert!(tc.is_def_eq(&left, &right));
            assert!(!tc.heartbeat_spent());
        }
    }
}

#[test]
fn test_recursor_different_majors_defer_to_equal_reduced_results() {
    let mut env = Environment::new();
    env.init_nat().expect("checked Nat vocabulary");
    for name in ["Nat.rec", "Nat.recOn"] {
        let tc = TypeChecker::new(&env);
        let make = |major| rec(name, motive(nat()), Expr::nat_lit(0), zero_step(), major);
        let lhs = make(Expr::nat_lit(0));
        let rhs = make(Expr::nat_lit(1));
        tc.check_type(&lhs, &nat())
            .expect("typed zero-major recursor");
        tc.check_type(&rhs, &nat())
            .expect("typed successor-major recursor");
        assert_eq!(tc.try_branch_sharing_def_eq(&lhs, &rhs), None);
        assert!(tc.is_def_eq(&lhs, &rhs));
        assert!(!tc.heartbeat_spent());
    }
}
