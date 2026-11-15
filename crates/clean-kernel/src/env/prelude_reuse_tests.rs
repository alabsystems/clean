// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cache mechanics use tiny private builders, never process-environment edits.
//! The final test checks the real constructor and public borrowing boundary.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Barrier};

use super::{build_on_worker, unavailable, ConstructionPolicy, Environment, PreludeCell};
use crate::env::{
    mm_axiom_only, mm_two_pass_active, set_mm_axiom_only, Declaration, MmAxiomOnlyGuard,
};
use crate::{Expr, Level, LocalContext, Name, TypeChecker};

#[test]
fn concurrent_first_requests_construct_once() {
    let cell = Arc::new(PreludeCell::new());
    let barrier = Arc::new(Barrier::new(8));
    let builds = Arc::new(AtomicUsize::new(0));
    let threads: Vec<_> = (0..8)
        .map(|_| {
            let cell = Arc::clone(&cell);
            let barrier = Arc::clone(&barrier);
            let builds = Arc::clone(&builds);
            std::thread::spawn(move || {
                barrier.wait();
                cell.with(
                    ConstructionPolicy::Shared,
                    move || {
                        builds.fetch_add(1, Ordering::SeqCst);
                        Ok(Environment::default())
                    },
                    |environment| std::ptr::from_ref(environment) as usize,
                )
                .expect("shared construction")
            })
        })
        .collect();
    let addresses: Vec<_> = threads
        .into_iter()
        .map(|thread| thread.join().unwrap())
        .collect();
    assert!(addresses.iter().all(|address| *address == addresses[0]));
    assert_eq!(builds.load(Ordering::SeqCst), 1);
}

#[test]
fn construction_error_is_not_cached() {
    let cell = PreludeCell::new();
    let first = cell.with(
        ConstructionPolicy::Shared,
        || Err(unavailable("fixture failure")),
        |_| (),
    );
    assert!(first.unwrap_err().to_string().contains("fixture failure"));
    assert!(cell.value.get().is_none());
    assert_eq!(
        cell.with(
            ConstructionPolicy::Shared,
            || Ok(Environment::default()),
            |_| 7
        )
        .unwrap(),
        7
    );
}

#[test]
fn worker_panic_is_not_cached_or_a_poisoned_lock() {
    let cell = PreludeCell::new();
    let first = cell.with(
        ConstructionPolicy::Shared,
        || panic!("fixture panic"),
        |_| (),
    );
    assert!(first.unwrap_err().to_string().contains("worker panicked"));
    assert!(cell.value.get().is_none());
    assert!(cell
        .with(
            ConstructionPolicy::Shared,
            || Ok(Environment::default()),
            |_| ()
        )
        .is_ok());
}

#[test]
fn initializer_reentry_is_refused_on_shared_and_fresh_paths() {
    for policy in [ConstructionPolicy::Shared, ConstructionPolicy::Fresh] {
        let cell = PreludeCell::new();
        cell.with(
            policy,
            || {
                let error = Environment::with_reusable_prelude(|_| ()).unwrap_err();
                assert!(error.to_string().contains("recursive"));
                Ok(Environment::default())
            },
            |_| (),
        )
        .unwrap();
        // The fresh path must restore its caller's TLS on return as well.
        assert!(!super::BUILDING_PRELUDE.with(std::cell::Cell::get));
    }
}

#[test]
fn callbacks_can_reenter_after_initialization() {
    let cell = PreludeCell::new();
    cell.with(
        ConstructionPolicy::Shared,
        || Ok(Environment::default()),
        |outer| {
            cell.with(
                ConstructionPolicy::Shared,
                || panic!("a warm hit must not build"),
                |inner| assert!(std::ptr::eq(outer, inner)),
            )
            .unwrap();
        },
    )
    .unwrap();
}

#[test]
fn warm_cache_does_not_bypass_strict_sorry_or_budget_policy() {
    let cell = PreludeCell::new();
    cell.with(
        ConstructionPolicy::Shared,
        || Ok(Environment::default()),
        |_| (),
    )
    .unwrap();
    for (strict, deny_sorry, budget) in [(true, false, 0), (false, true, 0), (false, false, 1)] {
        let policy =
            ConstructionPolicy::from_controls(strict, deny_sorry, budget, false, false).unwrap();
        assert_eq!(policy, ConstructionPolicy::Fresh);
        let result = cell.with(policy, || Err(unavailable("fresh policy refusal")), |_| ());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("fresh policy refusal"));
    }
    // Refused fresh attempts neither replace nor invalidate the ordinary cell.
    cell.with(
        ConstructionPolicy::Shared,
        || panic!("warm cache lost"),
        |_| (),
    )
    .unwrap();
}

#[test]
fn platform_policy_preserves_refusals_and_never_enables_reuse() {
    // This is a host-side dispatch regression, not WASM execution evidence.
    for policy in [ConstructionPolicy::Shared, ConstructionPolicy::Fresh] {
        assert_eq!(policy.for_worker_support(true), policy);
        assert_eq!(policy.for_worker_support(false), ConstructionPolicy::Fresh);
    }
    for worker_supported in [false, true] {
        assert!(
            ConstructionPolicy::from_controls(false, false, 0, true, true)
                .map(|policy| policy.for_worker_support(worker_supported))
                .is_err()
        );
    }
}

#[test]
fn no_thread_policy_builds_on_caller_even_with_a_warm_cache() {
    let cell = PreludeCell::new();
    let cached_address = cell
        .with(
            ConstructionPolicy::Shared,
            || Ok(Environment::default()),
            |environment| std::ptr::from_ref(environment) as usize,
        )
        .unwrap();
    let caller = std::thread::current().id();
    let policy = ConstructionPolicy::from_controls(false, false, 0, false, false)
        .unwrap()
        .for_worker_support(false);
    cell.with(
        policy,
        move || {
            assert_eq!(std::thread::current().id(), caller);
            Ok(Environment::default())
        },
        |environment| {
            assert_eq!(std::thread::current().id(), caller);
            assert_ne!(std::ptr::from_ref(environment) as usize, cached_address);
        },
    )
    .unwrap();
    cell.with(
        ConstructionPolicy::Shared,
        || panic!("fresh platform construction replaced the native cache"),
        |environment| assert_eq!(std::ptr::from_ref(environment) as usize, cached_address),
    )
    .unwrap();
}

#[test]
fn active_budget_stays_on_caller_and_is_not_refilled() {
    std::thread::spawn(|| {
        let cell = PreludeCell::new();
        cell.with(
            ConstructionPolicy::Shared,
            || Ok(Environment::default()),
            |_| (),
        )
        .unwrap();
        crate::tc::set_declaration_budget(17);
        let caller = std::thread::current().id();
        let policy = ConstructionPolicy::current().unwrap();
        assert_eq!(policy, ConstructionPolicy::Fresh);
        cell.with(
            policy,
            move || {
                assert_eq!(std::thread::current().id(), caller);
                assert_eq!(crate::tc::declaration_budget_limit(), 17);
                assert_eq!(crate::tc::declaration_budget_remaining(), 17);
                // A real checker consumes this same ambient budget.
                let environment = Environment::default();
                let checker = TypeChecker::with_context(&environment, LocalContext::new());
                let _ = checker.infer_type(&Expr::sort(Level::zero()));
                assert!(crate::tc::declaration_budget_remaining() < 17);
                drop(checker);
                Ok(environment)
            },
            |_| assert!(crate::tc::declaration_budget_remaining() < 17),
        )
        .unwrap();
        assert_eq!(crate::tc::declaration_budget_limit(), 17);
        assert!(crate::tc::declaration_budget_remaining() < 17);
    })
    .join()
    .unwrap();
}

#[test]
fn metamath_modes_are_refused_before_a_cache_can_be_used() {
    for (axiom_only, two_pass) in [(true, false), (false, true), (true, true)] {
        assert!(ConstructionPolicy::from_controls(false, false, 0, axiom_only, two_pass).is_err());
    }
    std::thread::spawn(|| {
        let _two_pass = MmAxiomOnlyGuard::enter();
        assert!(Environment::with_reusable_prelude(|_| panic!("MM callback admitted")).is_err());
        set_mm_axiom_only(true);
        assert!(
            Environment::with_reusable_prelude(|_| panic!("MM axiom callback admitted")).is_err()
        );
    })
    .join()
    .unwrap();
}

#[test]
fn construction_worker_has_fresh_thread_local_state() {
    std::thread::spawn(|| {
        let _two_pass = MmAxiomOnlyGuard::enter();
        set_mm_axiom_only(true);
        crate::tc::set_declaration_budget(17);
        // Exercise the private worker directly: the public API refuses this
        // caller's MM context instead of ever routing it to construction.
        build_on_worker(|| {
            assert_eq!(
                std::thread::current().name(),
                Some("clean-ordinary-prelude")
            );
            assert!(!mm_axiom_only());
            assert!(!mm_two_pass_active());
            assert_eq!(crate::tc::declaration_budget_limit(), 0);
            Ok(Environment::default())
        })
        .unwrap();
        assert!(mm_axiom_only());
        assert!(mm_two_pass_active());
        assert_eq!(crate::tc::declaration_budget_remaining(), 17);
    })
    .join()
    .unwrap();
}

#[test]
fn fresh_failure_restores_reentry_guard() {
    let cell = PreludeCell::new();
    assert!(cell
        .with(
            ConstructionPolicy::Fresh,
            || Err(unavailable("fresh error")),
            |_| ()
        )
        .is_err());
    assert!(!super::BUILDING_PRELUDE.with(std::cell::Cell::get));
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = cell.with(ConstructionPolicy::Fresh, || panic!("fresh panic"), |_| ());
    }));
    assert!(panic.is_err());
    assert!(!super::BUILDING_PRELUDE.with(std::cell::Cell::get));
}

#[test]
fn ordinary_vocabulary_clone_isolation_and_actual_checks_match_fresh() {
    let fresh = Environment::try_with_prelude().expect("fresh ordinary prelude");
    Environment::with_reusable_prelude(|shared| {
        assert_eq!(fresh.num_constants(), shared.num_constants());
        assert_eq!(fresh.num_inductives(), shared.num_inductives());
        assert_eq!(fresh.num_constructors(), shared.num_constructors());
        assert_eq!(fresh.num_recursors(), shared.num_recursors());
        assert_eq!(fresh.num_quotients(), shared.num_quotients());
        assert_eq!(fresh.mode, shared.mode);
        assert_eq!(fresh.options, shared.options);
        assert_eq!(fresh.constant_origins, shared.constant_origins);
        assert_eq!(
            fresh.declaration_verification,
            shared.declaration_verification
        );
        assert!(!shared.has_constant_source());
        for expected in fresh.constants() {
            let actual = shared
                .get_const(&expected.name)
                .expect("same declaration names");
            assert_eq!(actual.name, expected.name);
            assert_eq!(actual.level_params, expected.level_params);
            assert_eq!(actual.type_, expected.type_);
            assert_eq!(actual.value, expected.value);
            assert_eq!(actual.kind, expected.kind);
            assert_eq!(actual.reducibility, expected.reducibility);
            assert_eq!(actual.is_reducible, expected.is_reducible);
        }

        let name = Name::from_string("PreludeReuse.privateClone");
        let mut private = shared.clone();
        private
            .add_decl(Declaration::Definition {
                name: name.clone(),
                level_params: vec![],
                type_: Expr::const_str("Nat"),
                value: Expr::nat_lit(7),
                is_reducible: true,
            })
            .expect("checked private declaration");
        assert!(private.get_const(&name).is_some());
        assert!(shared.get_const(&name).is_none());

        let refl = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![Level::succ(Level::zero())]),
            [Expr::const_str("Bool"), Expr::const_str("Bool.true")],
        );
        let goal = |rhs| {
            Expr::apps(
                Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                [
                    Expr::const_str("Bool"),
                    Expr::const_str("Bool.true"),
                    Expr::const_str(rhs),
                ],
            )
        };
        // A new checker for every attempt, including changed proof/claim
        // mutants after a successful check of the same ordinary environment.
        for environment in [&fresh, shared] {
            for (proof, claim, accepted) in [
                (refl.clone(), goal("Bool.true"), true),
                (refl.clone(), goal("Bool.false"), false),
                (Expr::const_str("Bool.true"), goal("Bool.true"), false),
                (refl.clone(), goal("Bool.true"), true),
            ] {
                let checker = TypeChecker::with_context(environment, LocalContext::new());
                assert_eq!(checker.check_type(&proof, &claim).is_ok(), accepted);
            }
        }
    })
    .expect("reusable ordinary prelude");
}
