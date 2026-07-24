// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{Environment, Expr};
use std::panic::{catch_unwind, AssertUnwindSafe};

// =========================================================================
// with_sorry_location_key tests (#2770)
// =========================================================================

#[test]
fn test_sorry_location_key_override_records_key_instead_of_caller() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    enable_sorry_location_tracking();
    reset_sorry_locations();

    let env = Environment::new();
    with_sorry_location_key("fixture:sorry:test:override", || {
        let _ = create_sorry_term(&env, &Expr::prop());
    });

    let map = sorry_locations().expect("tracking should be enabled");
    assert!(
        map.contains_key("fixture:sorry:test:override"),
        "override key should be recorded instead of file:line, got keys: {:?}",
        map.keys().collect::<Vec<_>>()
    );
    assert_eq!(
        map.get("fixture:sorry:test:override"),
        Some(&1),
        "override key should have exactly 1 count"
    );
}

#[test]
fn test_sorry_location_key_nested_restores_outer() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    enable_sorry_location_tracking();
    reset_sorry_locations();

    let env = Environment::new();
    with_sorry_location_key("fixture:sorry:outer", || {
        let _ = create_sorry_term(&env, &Expr::prop());
        with_sorry_location_key("fixture:sorry:inner", || {
            let _ = create_sorry_term(&env, &Expr::prop());
        });
        // After inner returns, outer key should be active again
        let _ = create_sorry_term(&env, &Expr::prop());
    });

    let map = sorry_locations().expect("tracking should be enabled");
    assert_eq!(
        map.get("fixture:sorry:outer"),
        Some(&2),
        "outer key should have 2 counts (before and after inner)"
    );
    assert_eq!(
        map.get("fixture:sorry:inner"),
        Some(&1),
        "inner key should have exactly 1 count"
    );
}

#[test]
fn test_sorry_location_key_restores_after_inner_panic() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    enable_sorry_location_tracking();
    reset_sorry_locations();

    let env = Environment::new();
    with_sorry_location_key("fixture:sorry:outer", || {
        let _ = create_sorry_term(&env, &Expr::prop());

        let panic_result = catch_unwind(AssertUnwindSafe(|| {
            with_sorry_location_key("fixture:sorry:inner", || {
                let _ = create_sorry_term(&env, &Expr::prop());
                panic!("inner fixture panic");
            });
        }));
        assert!(
            panic_result.is_err(),
            "inner fixture should panic for this test"
        );

        // The outer fixture key should still be active after the inner unwind.
        let _ = create_sorry_term(&env, &Expr::prop());
    });

    // After the outer scope returns, raw caller locations should resume.
    let _ = create_sorry_term(&env, &Expr::prop());

    let map = sorry_locations().expect("tracking should be enabled");
    assert_eq!(
        map.get("fixture:sorry:outer"),
        Some(&2),
        "outer key should remain active before and after the inner panic"
    );
    assert_eq!(
        map.get("fixture:sorry:inner"),
        Some(&1),
        "inner key should only record the panicking scope"
    );

    let non_fixture_count: u64 = map
        .iter()
        .filter(|(k, _)| !k.starts_with("fixture:"))
        .map(|(_, v)| *v)
        .sum();
    assert!(
        non_fixture_count >= 1,
        "raw file:line tracking should resume after both scopes unwind"
    );
}

#[test]
fn test_sorry_location_key_raw_caller_resumes_after_override() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    enable_sorry_location_tracking();
    reset_sorry_locations();

    let env = Environment::new();

    // Record one with override key
    with_sorry_location_key("fixture:sorry:scoped", || {
        let _ = create_sorry_term(&env, &Expr::prop());
    });

    // Record one without override — should use file:line
    let _ = create_sorry_term(&env, &Expr::prop());

    let map = sorry_locations().expect("tracking should be enabled");
    assert_eq!(
        map.get("fixture:sorry:scoped"),
        Some(&1),
        "scoped key should have 1 count"
    );

    // The raw file:line entry should exist (not under the fixture key)
    let non_fixture_count: u64 = map
        .iter()
        .filter(|(k, _)| !k.starts_with("fixture:"))
        .map(|(_, v)| *v)
        .sum();
    assert!(
        non_fixture_count >= 1,
        "at least 1 sorry should be recorded under raw file:line, got {non_fixture_count}"
    );
}
