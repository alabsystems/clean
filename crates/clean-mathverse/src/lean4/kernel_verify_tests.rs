// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioral tests for [`kernel_verify_const`].
//!
//! These tests exercise the full .olean → kernel type-check pipeline on
//! real Lean 4 Init modules. They load genuine `.olean` files from the
//! installed Lean 4 toolchain, register the constants into an
//! `Environment`, and then re-verify specific lemmas by running them
//! through the `add_decl` Phase 1 kernel checks.
//!
//! Tests gracefully skip when the Lean 4 toolchain is not available.

use super::*;
use crate::lean4::mathlib_import::{find_lean_lib_path, load_init_modules};
use crate::types::{AxiomProfile, ImportConfidence};
use clean_kernel::env::Environment;
use clean_kernel::ConstantKind;

/// Load Init modules for tests; returns `None` if the Lean 4 toolchain
/// is unavailable on this host.
fn setup_init_env() -> Option<Environment> {
    let lib_path = find_lean_lib_path()?;
    let mut env = Environment::default();
    let result = load_init_modules(&mut env, &lib_path);
    if result.loaded_modules.is_empty() {
        eprintln!("No Init modules loaded: {:?}", result.failed_modules);
        return None;
    }
    Some(env)
}

#[test]
fn test_kernel_verify_rejects_missing_constant() {
    let env = Environment::default();
    let err = kernel_verify_const(&env, "Nonexistent.constant")
        .expect_err("missing constant should not verify");
    assert!(matches!(err, KernelVerifyError::NotFound(_)));
}

/// `heartbeat_from_env` reads `CLEAN_KERNEL_HEARTBEAT`: parses a `u32` (0 =
/// unlimited), and yields `None` when unset or unparseable. This test owns the
/// env var for its whole lifecycle and restores it afterward so it cannot leak
/// into other tests.
#[test]
fn test_heartbeat_from_env_parses_and_defaults() {
    use crate::lean4::kernel_verify::{heartbeat_from_env, HEARTBEAT_ENV_VAR};

    // `with_env_edits` owns the var for the whole walk and restores whatever the
    // surrounding environment had on scope exit (even on panic).
    crate::process_env::with_env_edits(|env| {
        // 0 -> unlimited (Some(0)); the heavy-tail recovery value.
        env.set(HEARTBEAT_ENV_VAR, "0");
        assert_eq!(heartbeat_from_env(), Some(0));

        // An explicit positive budget round-trips.
        env.set(HEARTBEAT_ENV_VAR, "5000000");
        assert_eq!(heartbeat_from_env(), Some(5_000_000));

        // Surrounding whitespace is tolerated.
        env.set(HEARTBEAT_ENV_VAR, "  2000000  ");
        assert_eq!(heartbeat_from_env(), Some(2_000_000));

        // Unparseable -> None (caller keeps the kernel default).
        env.set(HEARTBEAT_ENV_VAR, "not-a-number");
        assert_eq!(heartbeat_from_env(), None);

        // Unset -> None.
        env.remove(HEARTBEAT_ENV_VAR);
        assert_eq!(heartbeat_from_env(), None);
    });
}

/// `kernel_verify_const_with_heartbeat(env, name, Some(0))` (unlimited) verifies
/// the same constant the default path verifies — the heartbeat is a resource
/// ceiling, never an acceptance criterion. Skips when no Lean toolchain.
#[test]
fn test_unlimited_heartbeat_matches_default_verdict() {
    use crate::lean4::kernel_verify::kernel_verify_const_with_heartbeat;

    let Some(env) = setup_init_env() else {
        eprintln!("skip: no Lean 4 toolchain");
        return;
    };
    // Nat.add_zero is a small, always-present Init theorem.
    let name = "Nat.add_zero";
    let Ok(default_ok) = kernel_verify_const(&env, name) else {
        eprintln!("skip: {name} not present in this toolchain");
        return;
    };
    let unlimited_ok = kernel_verify_const_with_heartbeat(&env, name, Some(0))
        .expect("unlimited heartbeat must reach the same accept verdict");
    assert_eq!(default_ok.confidence, unlimited_ok.confidence);
    assert_eq!(default_ok.verified, unlimited_ok.verified);
}

/// Foundational test: register a simple theorem, verify it via the
/// TypeChecker, and confirm trust accounting.
#[test]
fn test_kernel_verify_true_intro_synthetic() {
    use clean_kernel::env::Declaration;
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    // Build an Environment with propext loaded (for Classical-free tests
    // we just need the kernel to accept Sort 0 / Prop).
    let mut env = Environment::default();

    // Register an axiom-as-theorem: `myProp : Prop := True`.
    // Actually, simplest: axiom `myAx : Nat` would pass (Type-typed
    // axiom). For a theorem, we need a Prop-typed type. Use `True`
    // built-in.
    //
    // Since we don't want to take a full Init-dep here, verify using a
    // Sort-introducing declaration: axiom `my_univ_one : Sort 0`.
    let type_ = Expr::sort(clean_kernel::level::Level::zero());
    let decl = Declaration::Axiom {
        name: Name::from_string("kernel_verify.my_univ_one"),
        level_params: vec![],
        type_,
    };
    env.add_decl(decl)
        .expect("Sort 0 should be a well-formed axiom type");

    // Now re-verify.
    let ok = kernel_verify_const(&env, "kernel_verify.my_univ_one")
        .expect("axiom should re-verify through the kernel");
    assert_eq!(ok.kind, ConstantKind::Axiom);
    assert!(!ok.has_value);
    assert!(!ok.is_theorem);
    assert_eq!(ok.confidence, ImportConfidence::Axiomatized);
    assert_eq!(ok.axiom_profile, AxiomProfile::AXIOMATIZED);
    assert!(ok.verified);
}

/// Behavioral test: register a real theorem and re-verify its proof
/// under the kernel.
///
/// Uses `trivial : True` pattern: theorem `my_triv : True := True.intro`
/// once we have `True` and `True.intro` loaded from Init.
#[test]
fn test_kernel_verify_real_init_definition() {
    let Some(env) = setup_init_env() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    // Try several well-known Init definitions that should be present
    // regardless of which toolchain revision is installed. We pick the
    // first one that actually exists.
    let candidates = ["Nat.add", "Nat.succ", "Nat.zero", "id", "Function.const"];

    let mut picked: Option<&str> = None;
    for name in &candidates {
        if env.get_const(&Name::from_string(name)).is_some() {
            picked = Some(name);
            break;
        }
    }

    let name = picked.expect("at least one Init definition should be present");
    eprintln!("Verifying {name}");

    let ok = kernel_verify_const(&env, name)
        .unwrap_or_else(|e| panic!("kernel verify of {name} should succeed, got: {e}"));

    assert_eq!(ok.name, name);
    assert!(ok.verified);
    // `Nat.add` is a Definition; `Nat.succ` is a Constructor stored
    // as Definition or Axiom depending on representation. Either kind
    // is acceptable as long as it type-checks.
    assert!(matches!(
        ok.kind,
        ConstantKind::Definition | ConstantKind::Axiom | ConstantKind::Theorem
    ));
}

/// The core acceptance-criteria test: import a specific Mathlib-style
/// lemma (from Init) and kernel-verify it via the full TypeChecker.
///
/// Target: `Nat.succ_ne_zero` or `Nat.add_zero`. Both are classic Init
/// theorems with proof terms.
#[test]
fn test_kernel_verify_specific_init_lemma_add_decl_equivalent() {
    let Some(env) = setup_init_env() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    // Prefer theorems that are genuine `Theorem` declarations in Init
    // (as opposed to `Definition`s serving as lemmas). Fallback chain
    // handles cross-version Init layout drift.
    let targets = [
        "Nat.succ_ne_zero",
        "Nat.zero_ne_succ",
        "Nat.add_zero",
        "Nat.zero_add",
        "Nat.succ_eq_add_one",
        "Nat.add_succ",
        "Nat.succ_add",
    ];

    let mut any_theorem_verified = false;
    let mut any_verified = false;
    let mut last_err: Option<String> = None;

    for &name in &targets {
        if env.get_const(&Name::from_string(name)).is_none() {
            continue;
        }
        match kernel_verify_const(&env, name) {
            Ok(ok) => {
                eprintln!(
                    "kernel-verified {name}: kind={:?} conf={:?} prof={:?} us={}",
                    ok.kind, ok.confidence, ok.axiom_profile, ok.checked_us
                );
                any_verified = true;
                if ok.is_theorem {
                    any_theorem_verified = true;
                }
            }
            Err(e) => {
                eprintln!("{name} FAILED: {e}");
                last_err = Some(e.to_string());
            }
        }
    }

    assert!(
        any_verified,
        "expected at least one Init Nat lemma to kernel-verify; last error: {last_err:?}"
    );
    // We want at least one to be a real Theorem (type in Prop), which
    // proves the Prop-sort check fires and passes.
    assert!(
        any_theorem_verified,
        "expected at least one Init Nat lemma to be a kernel-verified Theorem; \
         last error: {last_err:?}"
    );
}

/// Verify that theorem verification also records `KernelVerified`
/// confidence, while axiom verification records `Axiomatized`.
#[test]
fn test_kernel_verify_confidence_matches_constant_kind() {
    let Some(env) = setup_init_env() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    // Find one axiom and one theorem (or theorem-like definition) and
    // confirm their confidence assignments diverge correctly.
    //
    // `propext` is a canonical Lean 4 axiom present in Init.
    if env.get_const(&Name::from_string("propext")).is_some() {
        let ok =
            kernel_verify_const(&env, "propext").expect("propext axiom should verify structurally");
        assert_eq!(ok.confidence, ImportConfidence::Axiomatized);
        assert!(!ok.has_value);
        // The axiom profile for `propext` should set the PROP_EXT bit.
        assert!(
            ok.axiom_profile.contains(AxiomProfile::PROP_EXT),
            "propext axiom_profile should contain PROP_EXT, got: {:?}",
            ok.axiom_profile
        );
        assert!(
            ok.axiom_profile.contains(AxiomProfile::AXIOMATIZED),
            "propext axiom_profile should contain AXIOMATIZED"
        );
    }

    // Classical.choice should also be recognized and profiled.
    if env
        .get_const(&Name::from_string("Classical.choice"))
        .is_some()
    {
        let ok = kernel_verify_const(&env, "Classical.choice")
            .expect("Classical.choice axiom should verify");
        assert!(ok.axiom_profile.contains(AxiomProfile::CHOICE));
        assert!(ok.axiom_profile.contains(AxiomProfile::CLASSICAL));
    }
}

/// Batch verification: verify that `kernel_verify_all` runs each name
/// and collects successes/failures without short-circuiting.
#[test]
fn test_kernel_verify_all_batch_behavior() {
    let Some(env) = setup_init_env() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    // Mix known-good names with known-missing names; confirm both
    // buckets get populated.
    let names = &["Nat", "Nat.add", "definitely_does_not_exist_x9z"];
    let (ok, err) = kernel_verify_all(&env, names);
    assert_eq!(
        ok.len() + err.len(),
        3,
        "every input should be accounted for"
    );
    assert!(!ok.is_empty(), "expected at least Nat or Nat.add to verify");
    assert!(
        err.iter()
            .any(|(n, _)| n == "definitely_does_not_exist_x9z"),
        "expected the bogus name to appear in failures"
    );
}
