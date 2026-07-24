// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B07 — instance-projection defeq reduction
//! (do-notation value certification)** of
//! `docs/plans/GAP_SWEEP_2026-07-09.md`.
//!
//! Before B07, `Pure.pure`/`Bind.bind` were value-less, instance-less axiom
//! stubs and the prelude had NO monad instances, so no do-block value was
//! rfl-certifiable (11 SILENT_WRONG_SUSPECT rows: do_notation p01–p07, p09,
//! p10, p17, p18) while raw `Option.bind` reduced fine (control probe).
//!
//! B07 fix (zero kernel tc/ changes):
//! - real `Pure`/`Bind` class structures + real-bodied `Option`/`List`
//!   instances (`clean-kernel::env::data_monad_insts`);
//! - the elaborator materialization pass
//!   (`clean-elab::infer::elab_monad_materialize`) rewrites stub applications
//!   over instance-resolvable concrete monads into instance-projected form,
//!   which the kernel reduces via ORDINARY delta + proj-of-mk iota + beta +
//!   `Option.rec` iota — the same reduction sequence Lean's kernel
//!   (`src/kernel/type_checker.cpp`) performs on Lean's own elaboration of
//!   these programs;
//! - strict lean4-core gate: `do` over `List` is REJECTED (Lean core has no
//!   List monad instance — GAP_SWEEP §5 OVER_ACCEPT-01).
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches the observable `clean check` verdict.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

/// Drive the real file pipeline against a caller-supplied environment.
fn elaborate_file_in(
    mut env: Environment,
    source: &str,
) -> Result<(Environment, Vec<ElabResult>), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut results = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        results.push(elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?);
    }
    Ok((env, results))
}

fn elaborate_file(source: &str) -> Result<(Environment, Vec<ElabResult>), String> {
    elaborate_file_in(Environment::with_prelude(), source)
}

fn expect_pass(source: &str) {
    elaborate_file(source).unwrap_or_else(|e| panic!("file must fully check, got: {e}\n{source}"));
}

fn expect_fail(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("file must be REJECTED, but it fully checked:\n{source}"),
        Err(e) => e,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// The 11 flipped SILENT_WRONG_SUSPECT value pins (do_notation family, §4.1)
// ═══════════════════════════════════════════════════════════════════════════

/// do_notation/p01_bind_ascii — `<-` bind + terminal `pure`.
#[test]
fn b07_p01_bind_ascii_value_certified() {
    expect_pass(
        "def f1 : Option Nat := do\n  let x <- some 3\n  pure (x + 1)\n\n\
         theorem f1_pin : f1 = some 4 := rfl",
    );
}

/// do_notation/p02_bind_unicode — `←` bind.
#[test]
fn b07_p02_bind_unicode_value_certified() {
    expect_pass(
        "def f2 : Option Nat := do\n  let x ← some 3\n  pure (x + 1)\n\n\
         theorem f2_pin : f2 = some 4 := rfl",
    );
}

/// do_notation/p03_return_keyword — terminal `return`.
#[test]
fn b07_p03_return_value_certified() {
    expect_pass(
        "def f3 : Option Nat := do\n  let x ← some 10\n  return x + 2\n\n\
         theorem f3_pin : f3 = some 12 := rfl",
    );
}

/// do_notation/p04_none_shortcircuit — `Option.bind none f ≡ none`.
#[test]
fn b07_p04_none_shortcircuit_value_certified() {
    expect_pass(
        "def f4 : Option Nat := do\n  let x ← (none : Option Nat)\n  pure (x + 1)\n\n\
         theorem f4_pin : f4 = none := rfl",
    );
}

/// do_notation/p05_discard_bind — `let _ ← e`.
#[test]
fn b07_p05_discard_bind_value_certified() {
    expect_pass(
        "def f5 : Option Nat := do\n  let _ ← some 1\n  pure 2\n\n\
         theorem f5_pin : f5 = some 2 := rfl",
    );
}

/// do_notation/p06_seq_unit_stmt — plain statement sequencing.
#[test]
fn b07_p06_seq_unit_stmt_value_certified() {
    expect_pass(
        "def f6 : Option Nat := do\n  some ()\n  some 3\n\n\
         theorem f6_pin : f6 = some 3 := rfl",
    );
}

/// do_notation/p07_if_else — if/else inside do.
#[test]
fn b07_p07_if_else_value_certified() {
    expect_pass(
        "def f7 : Option Nat := do\n  let x ← some 5\n  if x > 3 then\n    pure 1\n  \
         else\n    pure 0\n\n\
         theorem f7_pin : f7 = some 1 := rfl",
    );
}

/// do_notation/p09_nested_do — nested parenthesized do.
#[test]
fn b07_p09_nested_do_value_certified() {
    expect_pass(
        "def f9 : Option Nat := do\n  let x ← (do\n    let y ← some 2\n    pure (y + 1))\n  \
         pure (x * 2)\n\n\
         theorem f9_pin : f9 = some 6 := rfl",
    );
}

/// do_notation/p10_match_in_do — match inside do; BOTH pins.
#[test]
fn b07_p10_match_in_do_value_certified() {
    expect_pass(
        "def f10 (o : Option Nat) : Option Nat := do\n  let x ← o\n  match x with\n  \
         | 0 => pure 100\n  | n + 1 => pure n\n\n\
         theorem f10_pin1 : f10 (some 5) = some 4 := rfl\n\
         theorem f10_pin2 : f10 (some 0) = some 100 := rfl",
    );
}

/// do_notation/p17_pattern_bind — `let (a, b) ← e`.
#[test]
fn b07_p17_pattern_bind_value_certified() {
    expect_pass(
        "def f17 : Option Nat := do\n  let (a, b) ← some (3, 4)\n  pure (a + b)\n\n\
         theorem f17_pin : f17 = some 7 := rfl",
    );
}

/// do_notation/p18_pure_let — plain `let` interleaved with binds.
#[test]
fn b07_p18_pure_let_value_certified() {
    expect_pass(
        "def f18 : Option Nat := do\n  let x := 10\n  let y ← some 5\n  pure (x + y)\n\n\
         theorem f18_pin : f18 = some 15 := rfl",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// KERNEL-defeq acceptance pin from the brick brief + extra shapes
// ═══════════════════════════════════════════════════════════════════════════

/// The brick's acceptance pin verbatim: a do-block in TERM position inside a
/// theorem TYPE must be kernel-defeq to its ground value.
#[test]
fn b07_term_position_do_block_rfl_certifies() {
    expect_pass("theorem t : (do let x <- some 1; pure (x+1) : Option Nat) = some 2 := rfl");
}

/// Bind chains: three sequential arrow-binds.
#[test]
fn b07_let_arrow_chain_value_certified() {
    expect_pass(
        "def fc : Option Nat := do\n  let a ← some 1\n  let b ← some 2\n  let c ← some 3\n  \
         pure (a + b + c)\n\n\
         theorem fc_pin : fc = some 6 := rfl",
    );
}

/// A do-block captured under a lambda binder (closure over the argument):
/// the monad is still concrete, so materialization applies under the binder.
#[test]
fn b07_do_under_lambda_value_certified() {
    expect_pass(
        "def fl : Nat → Option Nat := fun n => do\n  let x ← some n\n  pure (x + 1)\n\n\
         theorem fl_pin : fl 4 = some 5 := rfl",
    );
}

/// An argument-less (empty-closure) do-block behind a unit abstraction.
#[test]
fn b07_do_thunk_value_certified() {
    expect_pass(
        "def ft : Unit → Option Nat := fun _ => do\n  let x ← some 2\n  pure (x * 3)\n\n\
         theorem ft_pin : ft () = some 6 := rfl",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// LOUD negatives — wrong values must be REJECTED (no over-acceptance)
// ═══════════════════════════════════════════════════════════════════════════

/// The materialized chain must not certify a WRONG ground value.
#[test]
fn b07_wrong_value_rejected() {
    let err = expect_fail(
        "def fw : Option Nat := do\n  let x <- some 3\n  pure (x + 1)\n\n\
         theorem fw_bad : fw = some 5 := rfl",
    );
    assert!(
        err.contains("mismatch") || err.contains("Kernel"),
        "wrong-value pin must die in the kernel, got: {err}"
    );
}

/// none/short-circuit direction must also not over-accept.
#[test]
fn b07_wrong_none_value_rejected() {
    expect_fail(
        "def fw2 : Option Nat := do\n  let x ← (none : Option Nat)\n  pure (x + 1)\n\n\
         theorem fw2_bad : fw2 = some 1 := rfl",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// List lane: builtin extension vs strict lean4-core rejection (p11)
// ═══════════════════════════════════════════════════════════════════════════

const LIST_DO: &str = "def g11 : List Nat := do\n  let x ← [1, 2]\n  let y ← [10, 20]\n  \
                       pure (x + y)\n\n\
                       theorem g11_pin : g11 = [11, 21, 12, 22] := rfl";

/// Builtin prelude (`clean check` default): the Clean-native List instances
/// are registered and the List do-block VALUE-certifies (left-to-right bind
/// order, matching Lean's `List` monad semantics from Mathlib).
#[test]
fn b07_p11_list_do_certifies_in_builtin_prelude() {
    let mut env = Environment::with_prelude();
    env.init_monad_list_insts()
        .expect("List monad instances must register");
    elaborate_file_in(env, LIST_DO)
        .unwrap_or_else(|e| panic!("builtin-prelude List do-block must certify, got: {e}"));
}

/// Strict lean4-core lane (`clean check --prelude lean4-core`): Lean 4 core
/// has NO `Monad List` instance (GAP_SWEEP §5 OVER_ACCEPT-01, verified
/// against v4.30.0-rc2 `Init/`), so the def itself must be REJECTED with a
/// failed-to-synthesize error.
#[test]
fn b07_p11_list_do_rejected_in_lean4_core_mode() {
    let mut env = Environment::with_prelude();
    env.set_lean4_core_strict_monads(true);
    let err = match elaborate_file_in(env, LIST_DO) {
        Ok(_) => panic!("lean4-core mode must reject do over List (no Monad List in core)"),
        Err(e) => e,
    };
    assert!(
        err.contains("failed to synthesize") && err.contains("List"),
        "expected failed-to-synthesize Monad List, got: {err}"
    );
}

/// Strict mode must NOT reject the monads Lean core DOES provide instances
/// for: Option (real instance) still certifies, and a stub-modeled core
/// monad (`Id`) still elaborates.
#[test]
fn b07_strict_mode_keeps_core_monads() {
    let mut env = Environment::with_prelude();
    env.set_lean4_core_strict_monads(true);
    elaborate_file_in(
        env,
        "def fo : Option Nat := do\n  let x ← some 1\n  pure (x + 1)\n\n\
         theorem fo_pin : fo = some 2 := rfl",
    )
    .unwrap_or_else(|e| panic!("strict mode must keep Option do-blocks certified, got: {e}"));

    let mut env = Environment::with_prelude();
    env.set_lean4_core_strict_monads(true);
    elaborate_file_in(
        env,
        "def fi : Id Nat := do\n  let x ← (pure 3 : Id Nat)\n  pure (x + 1)",
    )
    .unwrap_or_else(|e| panic!("strict mode must keep Id do-blocks elaborating, got: {e}"));
}

/// Control probe (unchanged from the sweep): raw `Option.bind` reduces.
#[test]
fn b07_control_raw_option_bind_still_reduces() {
    expect_pass(
        "def c1 : Option Nat := Option.bind (some 3) (fun x => some (x + 1))\n\
         theorem c1_pin : c1 = some 4 := rfl",
    );
}
