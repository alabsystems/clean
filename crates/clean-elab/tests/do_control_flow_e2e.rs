// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B08 — do-block mut/control-flow desugaring**
//! (`docs/plans/GAP_SWEEP_2026-07-09.md`).
//!
//! Before B08, the transformer-stack lane left `StateT.run`/`ExceptT.run`
//! initial states as unsolved metavariables, so every mutating / early-return
//! do-block failed kernel registration with "Declaration contains free
//! variables" (do_notation rows p08/p12/p13/p14/p15/p16), and straight-line
//! `let mut x := e; x := e'` additionally hit a `Discriminant(3) vs (4)`
//! unification shape error.
//!
//! B08 fix (elaborator-only; kernel untouched): the pure functional
//! state-threading lane (`clean-elab::infer::elab_do_mut`) desugars `mut`
//! reassignment to `let`-shadowing, `if`-without-`else` over one `mut` variable
//! to an `ite`-join, and tail-position early-`return` guards to
//! `ite _ (pure v) ⟦rest⟧`. The emitted terms are ordinary
//! `let`/`ite`/`Pure.pure`/`Bind.bind`, which the kernel both accepts AND
//! reduces — so each `theorem … := rfl` **value pin** below computes (mutation
//! accumulates, guards short-circuit).
//!
//! The forms outside B08's honest computable subset were descoped LOUD here.
//! **Brick B23** subsequently landed `for x in xs do <mut body>` (accumulate +
//! `break`/`continue`) in the same pure lane — the three former `for` LOUD
//! probes (p12/p14/p15) are now value-certified below, and the exhaustive
//! for-loop coverage lives in `do_loops_e2e.rs`. `while`/`repeat`, nested loops,
//! multi-variable joins, and non-tail early return REMAIN descoped LOUD: a typed
//! `Unsupported` error, asserted to NEVER surface as "free variables" / a kernel
//! reject.
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches the observable `clean check` verdict (given the
//! B07 monad-instance materialization that makes Option do-values reduce).

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

fn elaborate_file(source: &str) -> Result<Vec<ElabResult>, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut results = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        results.push(elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?);
    }
    Ok(results)
}

/// A supported shape must FULLY check — def registers AND every `rfl` value
/// pin kernel-checks (so the computed value is certified correct).
fn expect_pass(source: &str) {
    elaborate_file(source)
        .unwrap_or_else(|e| panic!("file must fully check (value-certified), got: {e}\n{source}"));
}

/// A descoped shape must be rejected LOUD — with a typed, human error, NEVER
/// "free variables" or a raw kernel reject.
fn expect_loud_reject(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("descoped shape must be REJECTED, but it fully checked:\n{source}"),
        Err(e) => {
            let lower = e.to_lowercase();
            assert!(
                !lower.contains("free variable"),
                "descoped shape must not leak unbound fvars ('free variables'); got: {e}\n{source}"
            );
            assert!(
                !lower.contains("contains free"),
                "descoped shape must not leak unbound fvars; got: {e}\n{source}"
            );
            assert!(
                !lower.contains("9223372036854775808"),
                "descoped shape must not leak the sentinel join-point fvar; got: {e}\n{source}"
            );
            e
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// SUPPORTED shapes — value-certified (mutation accumulates / guards fire).
// ═══════════════════════════════════════════════════════════════════════════

/// (a) do_notation/p13 — straight-line `let mut x := e; x := e'`.
/// The distinct `Discriminant(3) vs (4)` bug: reassignment desugars to
/// `let`-shadowing, so `x` accumulates `1 → 11`.
#[test]
fn b08_p13_mut_reassign_value_certified() {
    expect_pass(
        "def f13 : Option Nat := do\n  let mut x := 1\n  x := x + 10\n  pure x\n\n\
         theorem f13_pin : f13 = some 11 := rfl",
    );
}

/// Two straight-line reassignments chain correctly (`0 → 5 → 8`).
#[test]
fn b08_mut_reassign_chain_value_certified() {
    expect_pass(
        "def g : Option Nat := do\n  let mut x := 0\n  x := x + 5\n  x := x + 3\n  pure x\n\n\
         theorem g_pin : g = some 8 := rfl",
    );
}

/// A reassignment that reads another local (`let`-bound) value.
#[test]
fn b08_mut_reassign_reads_local_value_certified() {
    expect_pass(
        "def h : Option Nat := do\n  let mut x := 2\n  let y := 10\n  x := x + y\n  pure x\n\n\
         theorem h_pin : h = some 12 := rfl",
    );
}

/// (b) do_notation/p08 — `if`-without-`else` over `mut`, single variable.
/// Condition true → `r := 5` taken; false → `r` unchanged. The if desugars to
/// `let r := ite _ c inst 5 r`.
#[test]
fn b08_p08_if_no_else_mut_true_value_certified() {
    expect_pass(
        "def f8 : Option Nat := do\n  let mut r := 0\n  if true then\n    r := 5\n  pure r\n\n\
         theorem f8_pin : f8 = some 5 := rfl",
    );
}

/// The `false` arm of a no-else mut-if keeps the pre-if value.
#[test]
fn b08_if_no_else_mut_false_value_certified() {
    expect_pass(
        "def f8b : Option Nat := do\n  let mut r := 7\n  if false then\n    r := 5\n  pure r\n\n\
         theorem f8b_pin : f8b = some 7 := rfl",
    );
}

/// A no-else mut-if whose condition genuinely computes (`3 < 5`).
#[test]
fn b08_if_no_else_mut_computed_cond_value_certified() {
    expect_pass(
        "def f8c : Option Nat := do\n  let mut r := 1\n  if 3 < 5 then\n    r := r + 100\n  pure r\n\n\
         theorem f8c_pin : f8c = some 101 := rfl",
    );
}

/// An `if`-with-`else` single-variable mut join.
#[test]
fn b08_if_else_mut_join_value_certified() {
    expect_pass(
        "def f8d : Option Nat := do\n  let mut r := 0\n  if false then\n    r := 5\n  else\n    r := 9\n  pure r\n\n\
         theorem f8d_pin : f8d = some 9 := rfl",
    );
}

/// (c) do_notation/p16 — tail-position early-`return` guard, both branches.
#[test]
fn b08_p16_early_return_guard_taken_value_certified() {
    expect_pass(
        "def f16 (n : Nat) : Option Nat := do\n  if n == 0 then\n    return 42\n  pure n\n\n\
         theorem f16_pin0 : f16 0 = some 42 := rfl",
    );
}

#[test]
fn b08_p16_early_return_guard_fallthrough_value_certified() {
    expect_pass(
        "def f16 (n : Nat) : Option Nat := do\n  if n == 0 then\n    return 42\n  pure n\n\n\
         theorem f16_pin1 : f16 1 = some 1 := rfl",
    );
}

/// Early-return guard combined with a monadic bind in the continuation.
#[test]
fn b08_early_return_guard_then_bind_value_certified() {
    expect_pass(
        "def k (n : Nat) : Option Nat := do\n  if n == 0 then\n    return 100\n  let y ← some 7\n  pure (n + y)\n\n\
         theorem k_pin : k 3 = some 10 := rfl",
    );
}

/// Mutation flowing THROUGH a monadic bind (bind continuation still threads the
/// shadowed mut var).
#[test]
fn b08_mut_through_bind_value_certified() {
    expect_pass(
        "def m : Option Nat := do\n  let mut x := 1\n  let y ← some 4\n  x := x + y\n  pure x\n\n\
         theorem m_pin : m = some 5 := rfl",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// B23 — `for` over mut now VALUE-CERTIFIED (was B08 LOUD). Full coverage in
// `do_loops_e2e.rs`; these three pin the exact GAP_SWEEP probes that flipped.
// ═══════════════════════════════════════════════════════════════════════════

/// (d) do_notation/p12 — `for..in` accumulating into a mut var. `0+1+2+3 = 6`.
#[test]
fn b23_p12_for_in_mut_sum_value_certified() {
    expect_pass(
        "def f12 : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3] do\n    s := s + x\n  pure s\n\n\
         theorem f12_pin : f12 = some 6 := rfl",
    );
}

/// do_notation/p14 — `for` + `break` (→ ForInStep.done). Stop before 3: `1+2 = 3`.
#[test]
fn b23_p14_for_break_value_certified() {
    expect_pass(
        "def f14 : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3, 4] do\n    if x == 3 then\n      break\n    s := s + x\n  pure s\n\n\
         theorem f14_pin : f14 = some 3 := rfl",
    );
}

/// do_notation/p15 — `for` + `continue` (→ ForInStep.yield). Odds `1+3+5 = 9`.
#[test]
fn b23_p15_for_continue_value_certified() {
    expect_pass(
        "def f15 : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3, 4, 5] do\n    if x % 2 == 0 then\n      continue\n    s := s + x\n  pure s\n\n\
         theorem f15_pin : f15 = some 9 := rfl",
    );
}

/// do_notation/p19 — reassignment of an immutable (non-`mut`) binding. Lean
/// rejects; clean now rejects LOUD (was "free variables").
#[test]
fn b08_p19_reassign_immutable_loud_reject() {
    let e = expect_loud_reject("def f19 : Option Nat := do\n  let x ← some 1\n  x := 2\n  pure x");
    assert!(
        e.to_lowercase().contains("immutable") || e.to_lowercase().contains("mut"),
        "expected an immutable-reassignment descope, got: {e}"
    );
}

/// A bare `break` outside any loop is descoped LOUD (not free variables).
#[test]
fn b08_bare_break_loud_reject() {
    expect_loud_reject("def bb : Option Nat := do\n  break\n  pure 0");
}
