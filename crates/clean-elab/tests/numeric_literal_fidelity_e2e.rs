// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B20 — numeric literal fidelity: Float/OfScientific
//! + USize** (`docs/plans/GAP_SWEEP_2026-07-09.md`, literals/p09,p10,p17).
//!
//! Fidelity guarantees, each a former GAP_SWEEP finding:
//!
//! * **p09 (SILENT-WRONG → fixed).** A decimal/scientific literal is TYPED as
//!   `Float` in EVERY position (def body, ascription, `Eq`/prop, argument) — it
//!   never silently collapses to `Nat`. The root cause was the `Float`-returning
//!   native reducers returning a bare `Nat` bit-pattern (type `Nat`), so a
//!   reduced `(1.5 : Float)` sat in an `@Eq Float _ _` as a `Nat` — "expected
//!   Float, got Nat". Those reducers no longer fire over the prelude's `Float`
//!   heads at all: `Float.ofScientific` / `Float.ofNat` are `opaque` there, as
//!   `Float.ofScientific` is `opaque` in Lean, and the kernel folds a head only
//!   when it is a canonical definition (`env/native_fold_authority.rs`).
//! * **p10 — a `Float` literal's kernel meaning is its `OfScientific` TRIPLE,
//!   exactly as in Lean.** Lean's kernel computes no `Float`, so `rfl` decides a
//!   `Float` literal equality by the triple `(mantissa, expSign, decExp)`:
//!   one triple spelled two ways (`1.5e3`, `15e2`) certifies, and two distinct
//!   triples are a LOUD `rfl` failure even when they denote the same f64
//!   (`1.5e3` vs `1500.0`) — never a silently-accepted pin Lean rejects.
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
        .map(|deps| deps.iter().map(ToString::to_string).collect())
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
/// `Float` value by `rfl` — `a` δ-unfolds to the same `OfScientific` triple as
/// the right-hand side (pinned Lean accepts it the same way). Before the
/// reducer fix this reduced to a bare `Nat` and the kernel rejected the `Eq`
/// with "expected Float, got Nat".
#[test]
fn b20_float_equality_pin_certifies_value() {
    let env = elaborate_module("def a : Float := 2.5\ntheorem a_pin : a = 2.5 := rfl")
        .expect("a Float value pin `a = 2.5 := rfl` must certify");
    assert_empty_closure(&env, "a_pin");
}

/// Fully-ascribed both sides: `(1.5 : Float) = (1.5 : Float) := rfl`. Identical
/// `OfScientific` triples are the same term — honest accept, as in pinned Lean.
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
/// now (RHS via `Float.ofNat`), so `rfl` fails on two Float values (not on a
/// bogus Float-vs-Nat type mismatch); they are also distinct values.
#[test]
fn b20_float_vs_nat_literal_float_reject_is_distinct_value() {
    expect_rejected(
        "theorem bad : (3.14 : Float) = (3 : Float) := rfl",
        "`(3.14 : Float) = (3 : Float) := rfl`",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// p10 — scientific literals typed correctly; their kernel meaning is the
// `OfScientific` triple, never a computed f64 (Lean's kernel computes none).
// ═══════════════════════════════════════════════════════════════════════════

/// `def f2 : Float := 1.5e3` and `def f2b : Float := 2e-2` accept as Floats.
#[test]
fn b20_scientific_literal_typed_correctly() {
    let env = elaborate_module("def f2 : Float := 1.5e3\ndef f2b : Float := 2e-2")
        .expect("scientific Float literals must accept");
    assert_empty_closure(&env, "f2");
    assert_empty_closure(&env, "f2b");
}

/// RE-DECIDED 2026-09-28. This was `b20_scientific_value_computes`, asserting
/// that `(1.5e3 : Float) = (1500.0 : Float) := rfl` CERTIFIES because the
/// `Float.ofScientific` native reducer folded both triples to one f64. Pinned
/// Lean REJECTS it: `Float.ofScientific` is `protected opaque` in v4.30.0-rc2
/// and in v4.8.0, so its kernel computes no `Float` and `(15, false, 2)` and
/// `(15000, true, 1)` are distinct terms (v4.30.0-rc2, verbatim):
///
/// ```text
/// error: Type mismatch
///   rfl
/// has type
///   ?m.7 = ?m.7
/// but is expected to have type
///   15e2 = 1500.0
/// ```
///
/// Clean refuses it for the same reason: the prelude's `Float.ofScientific` is
/// an `opaque` placeholder, and a native fold fires only over a canonical
/// definition (`env/native_fold_authority.rs`), so accepting it again would be
/// a Clean superset of Lean. The fold was not even Lean's VALUE: its
/// `m * 10^±e` rounds twice, giving `0.3` the bits of `3 * 0.1`
/// (`0x3fd3333333333334`), where Lean's `(0.3 : Float).toBits` is
/// `4599075939470750515` (`0x3fd3333333333333`).
///
/// `1500.0 = 1500.00` is the sharper witness: one decimal value, two triples
/// (`(15000, true, 1)`, `(150000, true, 2)`), and both pinned toolchains reject
/// it too.
#[test]
fn b20_scientific_same_value_distinct_triple_is_loud_reject() {
    for (source, lhs, rhs) in [
        (
            "theorem t : (1.5e3 : Float) = (1500.0 : Float) := rfl",
            "15 Bool.false 2",
            "15000 Bool.true 1",
        ),
        (
            "theorem t : (1500.0 : Float) = (1500.00 : Float) := rfl",
            "15000 Bool.true 1",
            "150000 Bool.true 2",
        ),
    ] {
        let err = expect_rejected(source, source);
        // The right reason: the kernel met BOTH triples and could not equate
        // them — not a parse or elaboration failure before the equation.
        assert!(
            err.contains(lhs) && err.contains(rhs),
            "`{source}` must be refused as two distinct `OfScientific` triples \
             ({lhs} vs {rhs}), got: {err}"
        );
        assert!(
            !err.to_lowercase().contains("sorryax"),
            "a refused Float pin must not be laundered into sorryAx: {err}"
        );
    }
}

/// Control for the refusal above, and the part of p10 that is Lean's meaning:
/// the literal lowers to Lean's own triple, so ONE triple spelled two ways
/// certifies by `rfl`. Pinned Lean (v4.30.0-rc2 and v4.8.0) accepts both —
/// v4.30.0-rc2's `#check` prints `1.5e3` as `15e2` and `0.02` as `2e-2`:
/// `1.5e3` and `15e2` are both `(15, false, 2)`, and `2e-2` and `0.02` are both
/// `(2, true, 2)`.
#[test]
fn b20_scientific_same_triple_distinct_spelling_certifies() {
    let env = elaborate_module(
        "theorem t1 : (1.5e3 : Float) = (15e2 : Float) := rfl\n\
         theorem t2 : (2e-2 : Float) = (0.02 : Float) := rfl",
    )
    .expect("one `OfScientific` triple spelled two ways must certify by `rfl`, as in Lean");
    assert_empty_closure(&env, "t1");
    assert_empty_closure(&env, "t2");
}

/// Adversarial review of the re-decision above (2026-09-28): the triple must be
/// Lean's own, so an EXPLICIT `-` exponent sign survives a zero exponent. Lean's
/// `decodeScientificLitVal?` (`Init/Meta/Defs.lean` in v4.30.0-rc2,
/// `Init/Meta.lean` in v4.8.0) returns `(val, true, exp + e)` whenever `-` was
/// written, so `1e-0` is `(1, true, 0)` and `1e0` is `(1, false, 0)` — two
/// terms. Both pinned toolchains print `(1e-0 : Float)` under `pp.all` as
/// `OfScientific.ofScientific … 1 Bool.true 0` and REJECT each pin below
/// (v4.30.0-rc2: "Type mismatch … `1. = 1e0`", "… `5. = 5e0`",
/// "… `20e-3 = 2e-2`"). Clean used to fold the sign into a net exponent, gave
/// `1e-0` the triple `(1, false, 0)`, and so ACCEPTED the first two — a pin
/// Lean rejects. The third guards against a lowering that normalizes digits.
#[test]
fn b20_scientific_explicit_negative_zero_exponent_keeps_its_sign() {
    for (source, lhs, rhs) in [
        (
            "theorem t : (1e-0 : Float) = (1e0 : Float) := rfl",
            "1 Bool.true 0",
            "1 Bool.false 0",
        ),
        (
            "theorem t : (5e-00 : Float) = (5e+0 : Float) := rfl",
            "5 Bool.true 0",
            "5 Bool.false 0",
        ),
        (
            "theorem t : (0.020 : Float) = (2e-2 : Float) := rfl",
            "20 Bool.true 3",
            "2 Bool.true 2",
        ),
    ] {
        let err = expect_rejected(source, source);
        assert!(
            err.contains(lhs) && err.contains(rhs),
            "`{source}` must be refused as two distinct `OfScientific` triples \
             ({lhs} vs {rhs}), got: {err}"
        );
        assert!(
            !err.to_lowercase().contains("sorryax"),
            "a refused Float pin must not be laundered into sorryAx: {err}"
        );
    }
}

/// Control for the sign rule above: every spelling pinned Lean (v4.30.0-rc2 and
/// v4.8.0) accepts by `rfl` still certifies. `1e0`/`1e+0` are both
/// `(1, false, 0)`; `1.0e-0`/`1.0` are both `(10, true, 1)` (the `-` sign with a
/// fraction digit); `1.25e1`/`12.5` are both `(125, true, 1)` (a positive
/// exponent smaller than the fraction length); `1.5e-3`/`0.0015` are both
/// `(15, true, 4)`.
#[test]
fn b20_scientific_lean_equal_spellings_certify() {
    let env = elaborate_module(
        "theorem c1 : (1e0 : Float) = (1e+0 : Float) := rfl\n\
         theorem c2 : (1.0e-0 : Float) = (1.0 : Float) := rfl\n\
         theorem c3 : (1.25e1 : Float) = (12.5 : Float) := rfl\n\
         theorem c4 : (1.5e-3 : Float) = (0.0015 : Float) := rfl",
    )
    .expect("spellings pinned Lean decodes to one triple must certify by `rfl`");
    for name in ["c1", "c2", "c3", "c4"] {
        assert_empty_closure(&env, name);
    }
}

/// Adversarial: no OTHER route certifies the pin the re-decision refuses. Pinned
/// Lean rejects every one (v4.30.0-rc2: `decide`/`native_decide` "failed to
/// synthesize", `simp` "made no progress", the `rfl` tactic "Tactic `rfl`
/// failed"; v4.8.0 the same four), so none may elaborate here either.
#[test]
fn b20_scientific_distinct_triple_pin_has_no_tactic_route() {
    for tactic in ["rfl", "decide", "native_decide", "simp"] {
        let source = format!("theorem t : (1.5e3 : Float) = (1500.0 : Float) := by {tactic}");
        let err = expect_rejected(&source, &source);
        assert!(
            !err.to_lowercase().contains("sorryax"),
            "`by {tactic}` must not launder the Float pin into sorryAx: {err}"
        );
    }
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
