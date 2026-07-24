// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::Expr;

/// Build a minimal proof state for testing tactic dispatch.
fn test_proof_state() -> ProofState {
    use clean_kernel::Environment;
    let mut env = Environment::new();
    env.init_eq().expect("init_eq should succeed");
    ProofState::new(env, Expr::prop())
}

#[test]
fn test_registry_new_is_empty() {
    let reg = UserTacticRegistry::new();
    assert!(reg.is_empty());
    assert_eq!(reg.len(), 0);
}

#[test]
fn test_register_and_lookup() {
    let mut reg = UserTacticRegistry::new();
    reg.register(
        "my_tactic",
        |_args, _ps| Ok(()),
        "A test tactic that does nothing",
    );

    assert!(reg.is_registered("my_tactic"));
    assert!(!reg.is_registered("nonexistent"));

    let entry = reg.get("my_tactic").expect("should find registered tactic");
    assert_eq!(entry.name(), "my_tactic");
    assert_eq!(entry.description(), "A test tactic that does nothing");
}

#[test]
fn test_register_overwrites_previous() {
    let mut reg = UserTacticRegistry::new();
    reg.register("t", |_args, _ps| Ok(()), "first version");
    reg.register("t", |_args, _ps| Ok(()), "second version");

    assert_eq!(reg.len(), 1);
    let entry = reg.get("t").expect("should find tactic");
    assert_eq!(entry.description(), "second version");
}

#[test]
fn test_dispatch_success() {
    let mut reg = UserTacticRegistry::new();
    reg.register("noop", |_args, _ps| Ok(()), "No-op tactic for testing");

    let mut ps = test_proof_state();
    let result = reg.dispatch("noop", &[], &mut ps);
    assert!(
        result.is_ok(),
        "dispatch of registered noop tactic should succeed"
    );
}

#[test]
fn test_dispatch_unknown_tactic_error() {
    let reg = UserTacticRegistry::new();
    let mut ps = test_proof_state();

    let result = reg.dispatch("nonexistent", &[], &mut ps);
    assert!(result.is_err(), "dispatch of unknown tactic should fail");
    match result.unwrap_err() {
        TacticError::UnknownTactic(name) => {
            assert_eq!(name, "nonexistent");
        }
        other => panic!("expected UnknownTactic error, got: {other:?}"),
    }
}

#[test]
fn test_dispatch_handler_receives_args() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let call_count = Arc::new(AtomicUsize::new(0));
    let call_count_clone = call_count.clone();

    let mut reg = UserTacticRegistry::new();
    reg.register(
        "counter",
        move |_args, _ps| {
            call_count_clone.fetch_add(1, Ordering::SeqCst);
            Ok(())
        },
        "Counts invocations",
    );

    let mut ps = test_proof_state();
    reg.dispatch("counter", &[], &mut ps)
        .expect("dispatch should succeed");
    reg.dispatch("counter", &[], &mut ps)
        .expect("dispatch should succeed");

    assert_eq!(call_count.load(Ordering::SeqCst), 2);
}

#[test]
fn test_with_builtins_registers_core_tactics() {
    let reg = UserTacticRegistry::with_builtins();

    let expected = [
        "intro",
        "intros",
        "exact",
        "apply",
        "rfl",
        "assumption",
        "constructor",
        "cases",
        "induction",
        "simp",
        "cert_simp",
        "cert_mathverse",
        "sorry",
    ];
    for name in expected {
        assert!(
            reg.is_registered(name),
            "built-in tactic '{name}' should be pre-registered"
        );
    }
}

#[test]
fn test_with_builtins_has_descriptions() {
    let reg = UserTacticRegistry::with_builtins();

    for name in ["assumption", "constructor", "rfl", "sorry"] {
        let entry = reg.get(name).unwrap_or_else(|| panic!("'{name}' missing"));
        assert!(
            !entry.description().is_empty(),
            "built-in tactic '{name}' should have a description"
        );
    }
}

#[test]
fn test_user_tactic_overrides_builtin() {
    let mut reg = UserTacticRegistry::with_builtins();

    reg.register(
        "sorry",
        |_args, _ps| {
            Err(TacticError::InvalidTarget {
                tactic: "sorry".into(),
                detail: "sorry is disabled in this context".into(),
            })
        },
        "Disabled sorry",
    );

    let entry = reg.get("sorry").expect("should find sorry");
    assert_eq!(entry.description(), "Disabled sorry");

    let mut ps = test_proof_state();
    let result = reg.dispatch("sorry", &[], &mut ps);
    assert!(result.is_err(), "overridden sorry should fail");
}

#[test]
fn test_names_iterator() {
    let mut reg = UserTacticRegistry::new();
    reg.register("alpha", |_a, _p| Ok(()), "a");
    reg.register("beta", |_a, _p| Ok(()), "b");
    reg.register("gamma", |_a, _p| Ok(()), "c");

    let mut names: Vec<&str> = reg.names().collect();
    names.sort();
    assert_eq!(names, vec!["alpha", "beta", "gamma"]);
}

#[test]
fn test_dispatch_error_propagation() {
    let mut reg = UserTacticRegistry::new();
    reg.register(
        "fail_tactic",
        |_args, _ps| {
            Err(TacticError::InvalidTarget {
                tactic: "fail_tactic".into(),
                detail: "intentional failure".into(),
            })
        },
        "Always fails",
    );

    let mut ps = test_proof_state();
    let result = reg.dispatch("fail_tactic", &[], &mut ps);
    assert!(result.is_err());
    match result.unwrap_err() {
        TacticError::InvalidTarget { tactic, detail } => {
            assert_eq!(tactic, "fail_tactic");
            assert_eq!(detail, "intentional failure");
        }
        other => panic!("expected InvalidTarget, got: {other:?}"),
    }
}
