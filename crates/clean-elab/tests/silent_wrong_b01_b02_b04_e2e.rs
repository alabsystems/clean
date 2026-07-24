// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for the three Tier-0 silent-wrong bricks of
//! `docs/plans/GAP_SWEEP_2026-07-09.md`:
//!
//! - **B01 — named constructor/function arguments bound positionally.**
//!   `Point.mk (y := 2) (x := 1)` silently elaborated as `Point.mk 2 1` and
//!   the kernel certified the SWAPPED fields (`p.x = 2 := rfl` passed 4/0).
//!   Lean ground truth: lean4 `src/Lean/Elab/App.lean` (`ElabAppArgs` — named
//!   args bind by binder name; positional args fill the remaining explicit
//!   binders in order; unknown/double-filled names are errors).
//!
//! - **B02 — `example` declarations silently skipped.** `clean check` on an
//!   example-only file reported "Checked 0 declarations / 0 passed" exit 0.
//!   Lean ground truth: lean4 `src/Lean/Elab/Declaration.lean` (`elabExample`
//!   elaborates + checks like an anonymous def, then discards).
//!
//! - **B04 — `toString (n : Nat)` returned `""`** so interpolation
//!   rfl-PROVED wrong strings (`s!"one {1 + 1} three" = "one  three"`).
//!   Lean ground truth: lean4 `Init/Data/Repr.lean` (`Nat.repr` /
//!   `Nat.toDigits(Core)` / `Nat.digitChar`).
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches the observable `clean check` verdict.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Drive the real file pipeline. Returns the elaboration results (one per
/// surface decl) or the first error.
fn elaborate_file(source: &str) -> Result<(Environment, Vec<ElabResult>), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut results = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        results.push(elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?);
    }
    Ok((env, results))
}

fn expect_pass(source: &str) -> (Environment, Vec<ElabResult>) {
    elaborate_file(source).unwrap_or_else(|e| panic!("file must fully check, got: {e}\n{source}"))
}

fn expect_fail(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("file must be REJECTED, but it fully checked:\n{source}"),
        Err(e) => e,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// B01 — named-argument binding (structures/p17_named_args_mk +
//        structures/sub_p17_swapped_witness)
// ═══════════════════════════════════════════════════════════════════════════

const POINT_PREFIX: &str = "structure Point where\n  x : Nat\n  y : Nat\n\n\
                            def p : Point := Point.mk (y := 2) (x := 1)\n";

/// Sweep row `structures/p17_named_args_mk`: the CORRECT values now pin.
#[test]
fn b01_named_ctor_args_bind_by_name() {
    let src = format!("{POINT_PREFIX}theorem p17a : p.x = 1 := rfl\ntheorem p17b : p.y = 2 := rfl");
    expect_pass(&src);
}

/// Sweep row `structures/sub_p17_swapped_witness`: the previously-certified
/// SWAPPED values (`p.x = 2`, `p.y = 1`) are now REJECTED.
#[test]
fn b01_swapped_witness_rejected() {
    let src = format!("{POINT_PREFIX}theorem w1 : p.x = 2 := rfl");
    expect_fail(&src);
    let src = format!("{POINT_PREFIX}theorem w2 : p.y = 1 := rfl");
    expect_fail(&src);
}

/// Unknown named argument is a LOUD typed error (never positional fallback).
#[test]
fn b01_unknown_named_arg_is_loud() {
    let err = expect_fail(
        "structure Point where\n  x : Nat\n  y : Nat\n\n\
         def p : Point := Point.mk (z := 2) (x := 1)",
    );
    assert!(
        err.contains("invalid named argument") && err.contains('z'),
        "unknown named arg must raise NamedArgBindingFailed, got: {err}"
    );
}

/// Double-filled binder is a LOUD typed error.
#[test]
fn b01_double_filled_named_arg_is_loud() {
    let err = expect_fail(
        "structure Point where\n  x : Nat\n  y : Nat\n\n\
         def p : Point := Point.mk (x := 2) (x := 1)",
    );
    assert!(
        err.contains("invalid named argument") && err.contains('x'),
        "double-filled named arg must raise NamedArgBindingFailed, got: {err}"
    );
}

/// Mixed named + positional on a plain `def`: the positional argument fills
/// the remaining EXPLICIT binder (`x`), never the implicit `{α}` slot
/// (lean4 `src/Lean/Elab/App.lean`, `ElabAppArgs`).
#[test]
fn b01_positional_fills_remaining_explicit_binder() {
    expect_pass(
        "def pick {α : Type} (x y : α) : α := x\n\
         def g : Nat := pick (y := 2) 1\n\
         theorem gp : g = 1 := rfl",
    );
}

/// Named args in source order ARE Lean order: `f 1 (x := 2)` binds the named
/// `x` first and the positional `1` to the next unfilled explicit binder.
#[test]
fn b01_named_arg_wins_over_textual_position() {
    expect_pass(
        "def sub2 (x y : Nat) : Nat := x\n\
         def h : Nat := sub2 1 (x := 2)\n\
         theorem hp : h = 2 := rfl",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// B02 — `example` declarations are checked and counted
// (universes/p04,p05,p08,p11,p17,p18,p35 example-skipping rows)
// ═══════════════════════════════════════════════════════════════════════════

/// Sweep row `universes/p35_example_simple`: a trivial example elaborates to
/// a countable `ElabResult::Example` leaf (kernel-checked, never registered).
#[test]
fn b02_example_is_checked_and_counted() {
    let (_env, results) = expect_pass("example : (1 : Nat) = 1 := rfl");
    assert_eq!(results.len(), 1);
    assert!(
        matches!(results[0], ElabResult::Example { .. }),
        "example must surface as a countable Example leaf, got: {:?}",
        results[0]
    );
    let mut leaves = Vec::new();
    results[0].leaf_decls(&mut leaves);
    assert_eq!(
        leaves.len(),
        1,
        "an example is exactly one checked declaration unit"
    );
}

/// Sweep rows `universes/p04`/`p05`: the level-defeq examples now genuinely
/// verify (they were vacuously green before).
#[test]
fn b02_universe_examples_verify() {
    expect_pass("example : Sort 0 = Prop := rfl");
    expect_pass("example : Type = Type 0 := rfl");
}

/// A FALSE example must fail the file (no vacuous success).
#[test]
fn b02_false_example_fails() {
    let err = expect_fail("example : (1 : Nat) = 2 := rfl");
    assert!(
        err.contains("example"),
        "failure must be attributed to the example, got: {err}"
    );
}

/// Examples are checked-then-DISCARDED (Lean `elabExample`): nothing is
/// registered into the environment.
#[test]
fn b02_example_registers_nothing() {
    let (env, _results) = expect_pass("example : (1 : Nat) = 1 := rfl");
    assert!(
        env.get_const(&Name::from_string("example")).is_none(),
        "`example` must not be registered as a constant"
    );
    assert!(
        env.get_const(&Name::from_string("_example")).is_none(),
        "no anonymous example constant may be registered"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// B04 — real Nat → String computation
// (literals/p04_string_interp + literals/p05_string_interp_nested)
// ═══════════════════════════════════════════════════════════════════════════

/// Value pins: `toString 0 = "0"` and `toString 42 = "42"` by rfl.
#[test]
fn b04_tostring_nat_value_pins() {
    expect_pass(
        "def t0 : String := toString (0 : Nat)\n\
         def t42 : String := toString (42 : Nat)\n\
         theorem t0_pin : t0 = \"0\" := rfl\n\
         theorem t42_pin : t42 = \"42\" := rfl",
    );
}

/// Sweep row `literals/p04_string_interp`: the interpolation pin proves.
#[test]
fn b04_string_interp_value_pin() {
    expect_pass(
        "def s4 : String := s!\"one {1 + 1} three\"\n\
         theorem s4_val : s4 = \"one 2 three\" := rfl",
    );
}

/// Sweep row `literals/p05_string_interp_nested`: nested s! interpolation.
#[test]
fn b04_nested_string_interp_value_pin() {
    expect_pass(
        "def s5 : String := s!\"a{s!\"b{2}\"}c\"\n\
         theorem s5_val : s5 = \"ab2c\" := rfl",
    );
}

/// The pre-B04 certified-wrong values are now REJECTED.
#[test]
fn b04_old_wrong_values_rejected() {
    expect_fail("theorem bad : toString (2 : Nat) = \"\" := rfl");
    expect_fail(
        "def s4 : String := s!\"one {1 + 1} three\"\n\
         theorem bad : s4 = \"one  three\" := rfl",
    );
}

/// The value pins PROVE with an EMPTY axiom closure (no sorry/axiom lane).
#[test]
fn b04_value_pins_have_empty_axiom_closure() {
    let (env, _results) = expect_pass(
        "def t42 : String := toString (42 : Nat)\n\
         theorem t42_pin : t42 = \"42\" := rfl",
    );
    let deps = env
        .axiom_deps(&Name::from_string("t42_pin"))
        .expect("t42_pin is registered");
    assert!(
        deps.is_empty(),
        "t42_pin must have an EMPTY axiom closure, got {deps:?}"
    );
}
