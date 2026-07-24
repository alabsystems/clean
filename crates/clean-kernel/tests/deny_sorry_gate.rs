// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DENY_SORRY enforcement gate — subprocess-backed integration tests.
//!
//! Proves two things:
//!
//! 1. `DENY_SORRY=1` actually panics when `create_sorry_term` is called
//! 2. clean paths (no sorry creation) pass under `DENY_SORRY=1`
//!
//! Uses a parent/child subprocess pattern because `deny_sorry_enabled()` caches
//! the environment variable with `Once` — it cannot be toggled within a single
//! process. Each child gets a fresh process with `DENY_SORRY=1` set before
//! startup.
//!
//! Part of #2085 GAP 4.
//!
//! Run: `cargo test -p clean-kernel --test deny_sorry_gate`
//!
//! Also invoked by: `./scripts/deny_sorry_gate.sh` (curated clean gate)

use std::process::Command;

use clean_kernel::sorry::{create_sorry_term, deny_sorry_enabled};
use clean_kernel::tc::TypeChecker;
use clean_kernel::{Environment, Expr};

// ============================================================================
// Child-mode test functions
//
// These tests are no-ops in normal (parent) mode. They only execute when the
// corresponding `DENY_SORRY_GATE_CHILD` env var is set, which the parent tests
// arrange by re-executing the same binary.
// ============================================================================

/// Child: attempts to create a sorry term. Should panic under DENY_SORRY=1.
#[test]
fn deny_sorry_child_create_sorry() {
    if std::env::var("DENY_SORRY_GATE_CHILD").as_deref() != Ok("create_sorry") {
        return;
    }
    let env = Environment::new();
    let _ = create_sorry_term(&env, &Expr::prop());
}

/// Child: initializes C009, which creates canonical sorry placeholders.
/// Should panic under DENY_SORRY=1.
#[test]
fn deny_sorry_child_c009_init() {
    if std::env::var("DENY_SORRY_GATE_CHILD").as_deref() != Ok("c009_init") {
        return;
    }
    let mut env = Environment::new();
    env.init_nn_verification_c009()
        .expect("C009 init should be blocked before returning");
}

/// Child: initializes C008. Since the 2026-06-12 R-weak unlock, C008's
/// base/step are constructive sorry-free Theorems (not sorry-inhabited
/// Opaques), so init creates NO sorry placeholder and must SUCCEED under
/// DENY_SORRY=1. This is the clean-path counterpart of `deny_sorry_child_c009_init`.
#[test]
fn deny_sorry_child_c008_init() {
    if std::env::var("DENY_SORRY_GATE_CHILD").as_deref() != Ok("c008_init") {
        return;
    }
    let mut env = Environment::new();
    env.init_nn_verify_ibp_tightness()
        .expect("C008 init should succeed (sorry-free) under DENY_SORRY=1");
}

/// Child: runs a clean type-checking path with no sorry. Should pass under DENY_SORRY=1.
#[test]
fn deny_sorry_child_clean_path() {
    if std::env::var("DENY_SORRY_GATE_CHILD").as_deref() != Ok("clean_path") {
        return;
    }
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let result = tc.infer_type(&Expr::prop());
    assert!(
        result.is_ok(),
        "Type-checking Prop should succeed without sorry: {:?}",
        result.err()
    );
}

/// Child: verifies `deny_sorry_enabled()` returns true under DENY_SORRY=1.
#[test]
fn deny_sorry_child_flag_check() {
    if std::env::var("DENY_SORRY_GATE_CHILD").as_deref() != Ok("flag_check") {
        return;
    }
    assert!(
        deny_sorry_enabled(),
        "deny_sorry_enabled() should return true when DENY_SORRY=1 is set"
    );
}

// ============================================================================
// Parent-mode test functions
//
// These spawn child processes with DENY_SORRY=1 and assert on exit status.
// ============================================================================

/// Spawn the same test binary as a child with DENY_SORRY=1 and the given child mode.
fn spawn_deny_child(child_mode: &str, child_test_name: &str) -> std::process::Output {
    let exe = std::env::current_exe().expect("cannot get current exe path");
    Command::new(&exe)
        .env("DENY_SORRY", "1")
        .env("DENY_SORRY_GATE_CHILD", child_mode)
        .arg("--exact")
        .arg(child_test_name)
        .arg("--test-threads=1")
        .arg("--nocapture")
        .output()
        .expect("failed to exec child process")
}

/// Prove DENY_SORRY enforcement: `create_sorry_term` panics when the flag is on.
#[test]
fn deny_sorry_enforcement_blocks_sorry_creation() {
    let output = spawn_deny_child("create_sorry", "deny_sorry_child_create_sorry");

    assert!(
        !output.status.success(),
        "Child should fail when DENY_SORRY=1 blocks sorry creation.\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("DENY_SORRY mode enabled"),
        "Panic message should contain 'DENY_SORRY mode enabled', got stderr:\n{}",
        stderr,
    );
}

/// Prove C009 routes through the canonical sorry gate under DENY_SORRY=1.
#[test]
fn deny_sorry_c009_init_blocks_canonical_sorry_creation() {
    let output = spawn_deny_child("c009_init", "deny_sorry_child_c009_init");

    assert!(
        !output.status.success(),
        "C009 init should fail when DENY_SORRY=1 blocks canonical sorry \
         placeholder creation.\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("DENY_SORRY mode enabled"),
        "Panic message should contain 'DENY_SORRY mode enabled', got stderr:\n{}",
        stderr,
    );
}

/// Prove C008 init is sorry-FREE: since the 2026-06-12 R-weak unlock, C008's
/// base/step are constructive Theorems (no `create_sorry_term` call anywhere in
/// the C008 init path), so initialization SUCCEEDS even under DENY_SORRY=1. This
/// is a ratchet: if a future change reintroduces a sorry placeholder into C008
/// init, this child process will panic and the test will fail.
#[test]
fn deny_sorry_c008_init_is_sorry_free() {
    let output = spawn_deny_child("c008_init", "deny_sorry_child_c008_init");

    assert!(
        output.status.success(),
        "C008 init should succeed under DENY_SORRY=1 — base/step are now \
         constructive sorry-free Theorems (2026-06-12 unlock). A failure means a \
         sorry placeholder regressed back into the C008 init path.\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

/// Prove clean paths pass: type-checking without sorry succeeds under DENY_SORRY=1.
#[test]
fn deny_sorry_clean_path_passes() {
    let output = spawn_deny_child("clean_path", "deny_sorry_child_clean_path");

    assert!(
        output.status.success(),
        "clean type-checking path should pass under DENY_SORRY=1.\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

/// Prove the flag itself is wired: `deny_sorry_enabled()` returns true in child.
#[test]
fn deny_sorry_flag_is_wired() {
    let output = spawn_deny_child("flag_check", "deny_sorry_child_flag_check");

    assert!(
        output.status.success(),
        "Flag check should pass under DENY_SORRY=1.\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

/// Baseline: verify `deny_sorry_enabled()` is OFF in the parent (no env var set).
#[test]
fn deny_sorry_not_enabled_in_parent() {
    // The parent process should NOT have DENY_SORRY set (unless the user
    // explicitly ran with it, but that's outside the gate's scope).
    if std::env::var("DENY_SORRY").is_ok() {
        // If DENY_SORRY is set in the parent, skip this baseline check —
        // the user is running the whole suite under deny mode.
        return;
    }
    assert!(
        !deny_sorry_enabled(),
        "deny_sorry_enabled() should be false in the parent (normal mode)"
    );
}
