// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WF recursion phase 1 — the first genuinely well-founded definitions that
//! compile end-to-end (elaborate → kernel-check → register), pinned.
//!
//! The class: `termination_by` with a `Nat` measure where each recursive
//! call's decrease is dischargeable from hypotheses in scope (the `dite`
//! branch's `h : 0 < n` plus `Nat.sub_lt`). Both fixtures elaborate through
//! `WellFounded.fix` with a per-call-site decreasing proof — no sorry, no
//! axiom, kernel re-checked at registration.
//!
//! CONTROLS: a genuinely undischargeable `termination_by` (no hypothesis
//! bounds the argument) must still be refused LOUDLY by the elaborator with a
//! diagnostic naming the construct — never compiled, never `sorry`-laundered.
//! The pre-existing fail-closed battery in `wf_termination_by_fail_closed.rs`
//! (bare `init_nat` environment) must keep passing alongside this file.

use clean_elab::{
    elaborate_decl, elaborate_decl_and_register, preprocess_decl_with_context, ElabError,
    ElabResult, FileContext,
};
use clean_kernel::name::Name;
use clean_kernel::Environment;
use clean_parser::parse_file;

/// Single recursive call: `n + countdownSum (n - 1)` under `h : 0 < n`.
const COUNTDOWN: &str = "def countdownSum (n : Nat) : Nat := \
     if h : 0 < n then n + countdownSum (n - 1) else 0\n\
     termination_by n";

/// Double (fib-class) recursion: `fibLike (n - 1) + fibLike (n - 2)` under
/// `h : 0 < n` (both subtraction decreases follow from `0 < n` via
/// `Nat.sub_lt`).
const FIB_LIKE: &str = "def fibLike (n : Nat) : Nat := \
     if h : 0 < n then \
       (if h2 : 1 < n then fibLike (n - 1) + fibLike (n - 2) else 1) \
     else 0\n\
     termination_by n";

/// Undischargeable: `Nat.pred n` is NOT `< n` at `n = 0` and no hypothesis is
/// in scope. Must reject loudly even with the full prelude available.
const UNDISCHARGEABLE: &str = "def wfBad (n : Nat) : Nat := wfBad (Nat.pred n)\n\
     termination_by n";

/// Parse → preprocess → elaborate one declaration, mirroring `clean check`.
fn elab_one(env: &Environment, source: &str) -> Result<ElabResult, ElabError> {
    let decls = parse_file(source).expect("source should parse");
    assert_eq!(decls.len(), 1, "fixture must be exactly one declaration");
    let mut file_ctx = FileContext::new();
    let processed = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl(env, &processed)
}

/// Parse → preprocess → elaborate → KERNEL-CHECK → register.
fn register_one(env: &mut Environment, source: &str) -> Result<ElabResult, ElabError> {
    let decls = parse_file(source).expect("source should parse");
    assert_eq!(decls.len(), 1, "fixture must be exactly one declaration");
    let mut file_ctx = FileContext::new();
    let processed = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl_and_register(env, &processed)
}

/// Assert `name` registered as a kernel-checked, sorry-free `WellFounded.fix`
/// definition whose transitive axiom closure is foundational-only.
fn assert_wf_definition_registered(env: &Environment, name: &str) {
    let constant = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered after kernel check"));
    let value = constant
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should keep its definition value"));
    assert!(
        !value.has_sorry(),
        "{name} must be sorry-free, got {value:?}"
    );
    let printed = format!("{value:?}");
    assert!(
        printed.contains("WellFounded.fix"),
        "{name} must be lowered through WellFounded.fix, got {printed}"
    );
    // "Prove"-grade: nothing outside the foundational axioms in the closure.
    let foundational = ["propext", "Quot.sound", "Classical.choice"];
    let closure = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should have an axiom closure"));
    let offending: Vec<String> = closure
        .iter()
        .map(ToString::to_string)
        .filter(|ax| !foundational.contains(&ax.as_str()))
        .collect();
    assert!(
        offending.is_empty(),
        "{name} must have a foundational-only axiom closure, got extra {offending:?}"
    );
}

// ---------------------------------------------------------------------------
// The genuine WF class compiles end-to-end.
// ---------------------------------------------------------------------------

#[test]
fn test_countdown_subtraction_measure_elaborates_and_kernel_verifies() {
    let mut env = Environment::with_prelude();
    let result = register_one(&mut env, COUNTDOWN);
    assert!(
        result.is_ok(),
        "countdownSum (genuine WF recursion, `n - 1` under `0 < n`) must \
         elaborate and kernel-verify; got {:?}",
        result.err()
    );
    assert_wf_definition_registered(&env, "countdownSum");
}

#[test]
fn test_fib_class_double_recursion_elaborates_and_kernel_verifies() {
    let mut env = Environment::with_prelude();
    let result = register_one(&mut env, FIB_LIKE);
    assert!(
        result.is_ok(),
        "fibLike (fib-class double WF recursion, `n - 1` and `n - 2` under \
         `0 < n`) must elaborate and kernel-verify; got {:?}",
        result.err()
    );
    assert_wf_definition_registered(&env, "fibLike");
}

// ---------------------------------------------------------------------------
// CONTROL: undischargeable stays loudly rejected — with the FULL prelude.
// ---------------------------------------------------------------------------

#[test]
fn test_undischargeable_termination_by_still_rejects_loudly() {
    let env = Environment::with_prelude();
    let err = elab_one(&env, UNDISCHARGEABLE)
        .expect_err("wfBad decreases only for n > 0; it must be refused, not compiled");

    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };
    assert!(
        feature.contains("termination_by"),
        "diagnostic must name `termination_by`, got: {feature}"
    );
    assert!(
        feature.contains("well-founded recursion"),
        "diagnostic must name well-founded recursion, got: {feature}"
    );
    assert!(
        feature.contains("wfBad"),
        "diagnostic must name the declaration, got: {feature}"
    );
    // Never surface internal kernel constants/messages as the diagnostic.
    assert!(
        !feature.contains("invImage")
            && !feature.contains("Level count mismatch")
            && !feature.contains("Unbound variable"),
        "must not leak an internal kernel message: {feature}"
    );
}

#[test]
fn test_undischargeable_termination_by_registers_nothing() {
    let mut env = Environment::with_prelude();
    let result = register_one(&mut env, UNDISCHARGEABLE);
    assert!(
        result.is_err(),
        "an undischargeable `termination_by` must not register anything"
    );
    for derived in ["wfBad", "wfBad._unary", "wfBad._eq_1", "wfBad._sorry"] {
        assert!(
            env.get_const(&Name::from_string(derived)).is_none(),
            "refused WF definition leaked `{derived}` into the environment"
        );
    }
}
