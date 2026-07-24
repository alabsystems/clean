// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B20 — numeric literal fidelity: Float/OfScientific
//! + USize** (`docs/plans/GAP_SWEEP_2026-07-09.md`, literals/p09,p10,p17).
//!
//! Three fidelity guarantees, each a former GAP_SWEEP finding:
//!
//! * **p09 (SILENT-WRONG → fixed).** A decimal/scientific literal is TYPED as
//!   `Float` in EVERY position (def body, ascription, `Eq`/prop, argument) — it
//!   never silently collapses to `Nat`. The root cause was the `Float`-returning
//!   native reducers returning a bare `Nat` bit-pattern (type `Nat`), so a
//!   reduced `(1.5 : Float)` sat in an `@Eq Float _ _` as a `Nat` — "expected
//!   Float, got Nat". Reducers now return `Float.mk <bits>` (type `Float`), so a
//!   `Float` equality is honest: identical values certify by `rfl`, DISTINCT
//!   values are a LOUD `rfl` failure (never a silently-accepted wrong pin).
//! * **A `Float` literal where `Nat` is expected is a LOUD type error** (and
//!   vice-versa) — the mismatch is caught, not laundered.
//! * **p17.** `(n : USize)` lowers to `USize.ofNat n`, now a genuine
//!   kernel-checked prelude def (`def u : USize := 42` accepts instead of
//!   `Unknown constant: USize.ofNat`). Value pins on `USize` are an HONEST loud
//!   gap: the width `System.Platform.numBits` is opaque (matching Lean), so
//!   `(USize.ofNat n).toNat = n` does NOT reduce — never silently accepted.
//! * **UInt8 (incl. mod-256 wrap) stays exact** — the fixed-width lane is
//!   unchanged and still value-certifies.
//!
//! Lean ground truth: `Init/Data/OfScientific.lean`, `Init/Data/Float.lean`
//! (`Float` opaque + `OfScientific` instance), `Init/Data/UInt/Basic.lean`.
//!
//! These drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches the observable `clean check` verdict.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top of
/// the default prelude, short-circuiting on the first failure. `Err` carries the
/// first failure's rendered message.
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

/// Transitive domain-axiom closure of a registered declaration (empty = no
/// `sorryAx`, no domain axioms — foundational axioms are not reported here).
fn axiom_closure(env: &Environment, name: &str) -> Option<Vec<String>> {
    env.axiom_deps(&Name::from_string(name))
        .map(|deps| deps.iter().map(std::string::ToString::to_string).collect())
}

fn assert_empty_closure(env: &Environment, name: &str) {
    let closure = axiom_closure(env, name)
        .unwrap_or_else(|| panic!("{name} should be registered with a computable value"));
    assert!(
        closure.is_empty(),
        "{name} must have an EMPTY domain-axiom closure (no sorryAx), got {closure:?}"
    );
}

/// Assert `source` fails loud; return the rendered failure text.
fn expect_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => panic!("{what} must be REJECTED (fail-closed), but it fully elaborated"),
        Err(e) => e,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// p09 — a decimal literal is a Float, NEVER a silently-collapsed Nat.
// ═══════════════════════════════════════════════════════════════════════════

/// `def f : Float := 3.14` accepts and carries no domain axioms — the def-body
/// boundary already worked, but the value must remain a genuine `Float`.
#[test]
fn b20_float_literal_in_def_is_float() {
    let env = elaborate_module("def f : Float := 3.14")
        .expect("`(3.14 : Float)` in def position must accept as Float");
    assert_empty_closure(&env, "f");
}

/// THE silent-wrong fix: a decimal literal in an `Eq`/prop position pins the
/// `Float` value by `rfl`. Before the reducer fix this reduced to a bare `Nat`
/// and the kernel rejected the `Eq` with "expected Float, got Nat".
#[test]
fn b20_float_equality_pin_certifies_value() {
    let env = elaborate_module("def a : Float := 2.5\ntheorem a_pin : a = 2.5 := rfl")
        .expect("a Float value pin `a = 2.5 := rfl` must certify");
    assert_empty_closure(&env, "a_pin");
}

/// Fully-ascribed both sides: `(1.5 : Float) = (1.5 : Float) := rfl`. Identical
/// `OfScientific` triples reduce to identical `Float.mk <bits>` — honest accept.
#[test]
fn b20_ascribed_float_equality_certifies() {
    elaborate_module("theorem t : (1.5 : Float) = (1.5 : Float) := rfl")
        .expect("`(1.5 : Float) = (1.5 : Float) := rfl` must certify (identical Float)");
}

/// Honest disequality: two DISTINCT Float literals are NOT `rfl`-equal — a LOUD
/// failure, never a silent accept (and never the previous OOM on the collapsed
/// giant-`Nat` comparison).
#[test]
fn b20_distinct_float_pin_is_loud_reject() {
    let err = expect_rejected(
        "theorem bad : (3.14 : Float) = (3.99 : Float) := rfl",
        "`(3.14 : Float) = (3.99 : Float) := rfl` (distinct Floats)",
    );
    assert!(
        !err.to_lowercase().contains("sorryax"),
        "a false Float pin must not be laundered into sorryAx: {err}"
    );
}

/// The SW1 witness: two distinct `Float` DEFS, then `a = b := rfl`. Must reject
/// loud (distinct bit patterns), never silently certify a false Float equality.
#[test]
fn b20_distinct_float_defs_not_rfl_equal() {
    expect_rejected(
        "def a : Float := 3.14\ndef b : Float := 3.99\ntheorem bad : a = b := rfl",
        "`3.14 = 3.99` across two Float defs",
    );
}

/// A `Float` literal where `Nat` is expected is a LOUD type error — the Float is
/// not silently coerced/collapsed into the `Nat` position.
#[test]
fn b20_float_where_nat_expected_is_loud() {
    let err = expect_rejected("def bad : Nat := 3.14", "`(3.14)` where `Nat` expected");
    let low = err.to_lowercase();
    assert!(
        low.contains("mismatch") || low.contains("float") || low.contains("expected"),
        "Float-vs-Nat must be a loud typed mismatch, got: {err}"
    );
    assert!(
        !low.contains("sorryax"),
        "the mismatch must not inject sorryAx: {err}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (n : Float) via Float.ofNat — a Nat literal ascribed to Float is a Float.
// ═══════════════════════════════════════════════════════════════════════════

/// `def w : Float := 3` lowers through `Float.ofNat 3` (Lean's `instOfNatFloat`)
/// — a genuine `Float`, not a raw `Nat`.
#[test]
fn b20_nat_literal_ascribed_to_float_is_float() {
    let env = elaborate_module("def w : Float := 3")
        .expect("`(3 : Float)` must elaborate as Float via Float.ofNat");
    assert_empty_closure(&env, "w");
}

/// Right-reason reject: `(3.14 : Float) = (3 : Float)` — BOTH sides are Floats
/// now (RHS via `Float.ofNat`), and they differ, so `rfl` fails on a genuine
/// Float disequality (not on a bogus Float-vs-Nat type mismatch).
#[test]
fn b20_float_vs_nat_literal_float_reject_is_distinct_value() {
    expect_rejected(
        "theorem bad : (3.14 : Float) = (3 : Float) := rfl",
        "`(3.14 : Float) = (3 : Float) := rfl`",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// p10 — scientific literals typed + valued correctly.
// ═══════════════════════════════════════════════════════════════════════════

/// `def f2 : Float := 1.5e3` and `def f2b : Float := 2e-2` accept as Floats.
#[test]
fn b20_scientific_literal_typed_correctly() {
    let env = elaborate_module("def f2 : Float := 1.5e3\ndef f2b : Float := 2e-2")
        .expect("scientific Float literals must accept");
    assert_empty_closure(&env, "f2");
    assert_empty_closure(&env, "f2b");
}

/// Scientific values COMPUTE honestly: `1.5e3` and `1500.0` denote the SAME f64
/// (different `OfScientific` triples, identical `Float.mk <bits>`), so the pin
/// certifies — a genuinely-verified stored scientific value (p10).
#[test]
fn b20_scientific_value_computes() {
    elaborate_module("theorem t : (1.5e3 : Float) = (1500.0 : Float) := rfl")
        .expect("`1.5e3 = 1500.0` must certify (same f64 value)");
}

// ═══════════════════════════════════════════════════════════════════════════
// p17 — USize.ofNat registered; value pins are an HONEST loud gap.
// ═══════════════════════════════════════════════════════════════════════════

/// `def u3 : USize := 42` accepts — `USize.ofNat` is now a kernel-checked
/// prelude def (was `Unknown constant: USize.ofNat`).
#[test]
fn b20_usize_ofnat_literal_accepts() {
    elaborate_module("def u3 : USize := 42")
        .expect("`def u3 : USize := 42` must accept (USize.ofNat registered)");
}

/// `USize.ofNat` applied directly type-checks at `USize`.
#[test]
fn b20_usize_ofnat_applied_type_checks() {
    elaborate_module("def u : USize := USize.ofNat 7")
        .expect("`USize.ofNat 7 : USize` must type-check");
}

/// A `USize` value pin does NOT reduce — `System.Platform.numBits` is opaque
/// (matching Lean's kernel), so `(USize.ofNat 42).toNat = 42 := rfl` is an
/// HONEST loud gap, NOT a silently-accepted wrong value.
#[test]
fn b20_usize_value_pin_is_honest_loud_gap() {
    expect_rejected(
        "theorem u_pin : (USize.ofNat 42).toNat = 42 := rfl",
        "`(USize.ofNat 42).toNat = 42 := rfl` (opaque width — honest gap)",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// UInt8 fixed-width lane stays exact (control — must not regress).
// ═══════════════════════════════════════════════════════════════════════════

/// `def u1 : UInt8 := 255` with `u1.toNat = 255 := rfl` — the concrete-width
/// lane still value-certifies exactly.
#[test]
fn b20_uint8_literal_value_pin_exact() {
    elaborate_module("def u1 : UInt8 := 255\ntheorem u1_val : u1.toNat = 255 := rfl")
        .expect("UInt8 literal value pin must certify exactly");
}

/// `(256 : UInt8) = 0 := rfl` — mod-256 wrap is exact and `rfl`-certified.
#[test]
fn b20_uint8_mod256_wrap_exact() {
    elaborate_module("theorem u2_wrap : (256 : UInt8) = 0 := rfl")
        .expect("UInt8 mod-256 wrap `(256 : UInt8) = 0 := rfl` must certify");
}
