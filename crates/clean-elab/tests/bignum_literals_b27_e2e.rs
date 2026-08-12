// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end value pins for **B27 — bignum numeric literals `>= 2^64`**
//! (`docs/plans/GAP_SWEEP_2026-07-09.md`, literals/p16,p17).
//!
//! Lean 4 `Nat` literals are arbitrary-precision. Before B27 the lexer folded
//! literals into a `u64`, so anything at or above `18446744073709551616`
//! (`2^64`) was rejected as a `NumericOverflow` lex error in every base. The
//! accumulator is now the kernel `BigNat`, so these literals PARSE, elaborate,
//! and kernel-check with their EXACT value.
//!
//! Each pin drives the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass here matches the observable `clean check` verdict, and every `rfl`
//! is a genuine kernel def-eq on the arbitrary-precision value — a truncated or
//! wrong value would be a LOUD `rfl` failure, never a silent accept.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top of
/// the default prelude, short-circuiting on the first failure.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

fn assert_empty_closure(env: &Environment, name: &str) {
    let closure: Vec<String> = env
        .axiom_deps(&Name::from_string(name))
        .map(|deps| deps.iter().map(ToString::to_string).collect())
        .unwrap_or_else(|| panic!("{name} should be registered with a computable value"));
    assert!(
        closure.is_empty(),
        "{name} must have an EMPTY domain-axiom closure (no sorryAx), got {closure:?}"
    );
}

fn expect_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => panic!("{what} must be REJECTED (fail-closed), but it fully elaborated"),
        Err(e) => e,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// A `>= 2^64` literal parses, elaborates, and registers with a computable value.
// ═══════════════════════════════════════════════════════════════════════════

/// `def big : Nat := 2^64` — the boundary literal in def position registers with
/// no domain axioms (it is a genuine kernel `Nat`, not a `sorryAx` stand-in).
#[test]
fn b27_two_pow_64_def_registers() {
    let env = elaborate_module("def big : Nat := 18446744073709551616")
        .expect("`def big : Nat := 2^64` must elaborate and register");
    assert_empty_closure(&env, "big");
}

/// A 100-digit decimal literal registers exactly.
#[test]
fn b27_hundred_digit_decimal_def_registers() {
    let src = format!("def huge : Nat := 1{}", "0".repeat(99));
    let env = elaborate_module(&src).expect("a 100-digit decimal literal must register");
    assert_empty_closure(&env, "huge");
}

// ═══════════════════════════════════════════════════════════════════════════
// Value pins: the exact `Nat` value certifies by `rfl`.
// ═══════════════════════════════════════════════════════════════════════════

/// The identity pin: a `2^64` literal is `rfl`-equal to itself — it flows to the
/// kernel intact and is accepted inside an `@Eq Nat`.
#[test]
fn b27_two_pow_64_identity_pin() {
    elaborate_module("theorem t : (18446744073709551616 : Nat) = 18446744073709551616 := rfl")
        .expect("`(2^64 : Nat) = 2^64 := rfl` must certify");
}

/// Cross-base equality: `0x1_0000_0000_0000_0000` (hex) and the decimal `2^64`
/// fold to the SAME kernel `BigNat`, so `rfl` certifies. Different source
/// spellings, one exact value — the strongest "value is exact" evidence.
#[test]
fn b27_hex_decimal_cross_base_pin() {
    elaborate_module("theorem t : (0x10000000000000000 : Nat) = 18446744073709551616 := rfl")
        .expect("`0x10000000000000000 = 18446744073709551616 := rfl` must certify");
}

/// Binary and octal spellings of `2^64` also fold to the same value.
#[test]
fn b27_binary_octal_cross_base_pins() {
    let binary = format!("0b1{}", "0".repeat(64));
    elaborate_module(&format!(
        "theorem tb : ({binary} : Nat) = 18446744073709551616 := rfl"
    ))
    .expect("binary `2^64` cross-base pin must certify");

    elaborate_module("theorem to : (0o2000000000000000000000 : Nat) = 18446744073709551616 := rfl")
        .expect("octal `2^64` cross-base pin must certify");
}

/// `0xFFFFFFFFFFFFFFFF + 1 = 2^64` — the boundary crossing via `Nat.add`: a
/// u64-max literal plus one reduces to the multi-limb `2^64` in the kernel.
#[test]
fn b27_u64_max_plus_one_reduces_to_two_pow_64() {
    elaborate_module("theorem t : (0xFFFFFFFFFFFFFFFF + 1 : Nat) = 18446744073709551616 := rfl")
        .expect("`0xFFFFFFFFFFFFFFFF + 1 = 2^64 := rfl` must certify (Nat.add crosses u64)");
}

/// A FALSE big-literal pin is a LOUD `rfl` failure — the arbitrary-precision
/// value is compared honestly, never laundered into a silent accept or sorryAx.
#[test]
fn b27_false_big_pin_is_loud_reject() {
    let err = expect_rejected(
        "theorem bad : (18446744073709551616 : Nat) = 18446744073709551617 := rfl",
        "`2^64 = 2^64 + 1 := rfl` (distinct big Nats)",
    );
    assert!(
        !err.to_lowercase().contains("sorryax"),
        "a false big-literal pin must not be laundered into sorryAx: {err}"
    );
}
