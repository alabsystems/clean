// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B23 — do-block imperative control flow: `for`
//! loops over mutable state** (`docs/plans/GAP_SWEEP_2026-07-09.md`, the B08
//! successor for the for/break/continue cases).
//!
//! B08 (`elab_do_mut`) landed the PURE state-threading lane for straight-line
//! `mut` reassignment, `if`-joins over one `mut` var, and tail early-`return`,
//! and DESCOPED `for`/`while`/`break`/`continue` LOUD. B23 extends the pure
//! lane to `for x in xs do <mut body>`: the loop lowers to the inlined
//! `List.forIn` recursion (`elab_do_pure_for` → `build_list_forin_fold`, the
//! kernel-registered `List.forIn` body of `data_for_in.rs`) with the mutable
//! accumulator threaded as the `ForIn` accumulator `β`. `break`/`continue`
//! lower to `ForInStep.done`/`.yield`.
//!
//! The emitted terms are ordinary `List.rec`/`ForInStep.rec`/`Bind.bind`/
//! `Pure.pure` applications; the B07 materialization pass rewrites the
//! `Bind.bind`/`Pure.pure` over `Option`/`Id` into computing instance-projected
//! form, so each `theorem … := rfl` **value pin** below COMPUTES (the loop runs,
//! mutation accumulates, break/continue short-circuit).
//!
//! Everything outside the honest computable fragment (`while`, `repeat`, nested
//! loops, multiple accumulators, early `return` inside a loop, non-`List`
//! collections, `break`/`continue` outside a loop) is descoped LOUD: a typed
//! `Unsupported` error, asserted here to NEVER surface as "free variables" or a
//! raw kernel reject.
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`).

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

/// A supported shape must FULLY check — the def registers AND every `rfl` value
/// pin kernel-checks (so the computed loop value is certified correct).
fn expect_pass(source: &str) {
    elaborate_file(source).unwrap_or_else(|e| {
        panic!("for-loop shape must fully check (value-certified), got: {e}\n{source}")
    });
}

/// A descoped shape must be rejected LOUD — a typed, human error, NEVER "free
/// variables" or a raw kernel reject.
fn expect_loud_reject(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("descoped shape must be REJECTED, but it fully checked:\n{source}"),
        Err(e) => {
            let lower = e.to_lowercase();
            assert!(
                !lower.contains("free variable") && !lower.contains("contains free"),
                "descoped shape must not leak unbound fvars ('free variables'); got: {e}\n{source}"
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
// (a) ForIn accumulate — the most common shape. Value-certified.
// ═══════════════════════════════════════════════════════════════════════════

/// do_notation/p12 — `for x in xs do s := s + x` accumulating into a `mut`.
/// `0 + 1 + 2 + 3 = 6`.
#[test]
fn b23_p12_for_in_mut_sum_value_certified() {
    expect_pass(
        "def f12 : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3] do\n    s := s + x\n  pure s\n\n\
         theorem f12_pin : f12 = some 6 := rfl",
    );
}

/// Accumulate over a longer list, distinct arithmetic (`2*x`): 2+4+6+8 = 20.
#[test]
fn b23_for_in_scaled_sum_value_certified() {
    expect_pass(
        "def g : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3, 4] do\n    s := s + x * 2\n  pure s\n\n\
         theorem g_pin : g = some 20 := rfl",
    );
}

/// A plain `let` inside the loop body threads correctly: y = x*10, sum = 60.
#[test]
fn b23_for_in_body_let_value_certified() {
    expect_pass(
        "def h : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3] do\n    let y := x * 10\n    s := s + y\n  pure s\n\n\
         theorem h_pin : h = some 60 := rfl",
    );
}

/// The loop body reads an OUTER `let`-bound local (`base`): (1+10)+(2+10) = 23.
#[test]
fn b23_for_in_reads_outer_local_value_certified() {
    expect_pass(
        "def k : Option Nat := do\n  let mut s := 0\n  let base := 10\n  for x in [1, 2] do\n    s := s + x + base\n  pure s\n\n\
         theorem k_pin : k = some 23 := rfl",
    );
}

/// An empty list leaves the accumulator at its initial value.
#[test]
fn b23_for_in_empty_list_value_certified() {
    expect_pass(
        "def e : Option Nat := do\n  let mut s := 5\n  for x in ([] : List Nat) do\n    s := s + x\n  pure s\n\n\
         theorem e_pin : e = some 5 := rfl",
    );
}

/// An `if`-join inside the loop body (both branches reassign): x even → +x,
/// x odd → +1.  x=1:+1(1) x=2:+2(3) x=3:+1(4) x=4:+4(8).
#[test]
fn b23_for_in_body_if_join_value_certified() {
    expect_pass(
        "def j : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3, 4] do\n    if x % 2 == 0 then\n      s := s + x\n    else\n      s := s + 1\n  pure s\n\n\
         theorem j_pin : j = some 8 := rfl",
    );
}

/// Accumulate in the `Id` monad (B22 Id-monad reduction): 1+2+3+4+5 = 15.
#[test]
fn b23_for_in_id_monad_value_certified() {
    expect_pass(
        "def fid : Id Nat := do\n  let mut s := 0\n  for x in [1, 2, 3, 4, 5] do\n    s := s + x\n  pure s\n\n\
         theorem fid_pin : fid = 15 := rfl",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (b) break / continue → ForInStep.done / .yield. Value-certified.
// ═══════════════════════════════════════════════════════════════════════════

/// do_notation/p14 — `for` + `break`. Stop before adding 3: 1+2 = 3.
#[test]
fn b23_p14_for_break_value_certified() {
    expect_pass(
        "def f14 : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3, 4] do\n    if x == 3 then\n      break\n    s := s + x\n  pure s\n\n\
         theorem f14_pin : f14 = some 3 := rfl",
    );
}

/// do_notation/p15 — `for` + `continue`. Sum of odds 1+3+5 = 9.
#[test]
fn b23_p15_for_continue_value_certified() {
    expect_pass(
        "def f15 : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3, 4, 5] do\n    if x % 2 == 0 then\n      continue\n    s := s + x\n  pure s\n\n\
         theorem f15_pin : f15 = some 9 := rfl",
    );
}

/// `break` in an `else` position also fires: add while x < 3, else stop.
/// x=1:+1(1) x=2:+2(3) x=3: break. Result 3.
#[test]
fn b23_for_break_else_value_certified() {
    expect_pass(
        "def fb : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3, 4] do\n    if x < 3 then\n      s := s + x\n    else\n      break\n  pure s\n\n\
         theorem fb_pin : fb = some 3 := rfl",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// DESCOPED shapes — LOUD typed rejects, never "free variables".
// ═══════════════════════════════════════════════════════════════════════════

/// `while` over mutable state — not modeled by the pure lane. LOUD.
#[test]
fn b23_while_loop_loud_reject() {
    let e = expect_loud_reject(
        "def w : Option Nat := do\n  let mut s := 0\n  while s < 3 do\n    s := s + 1\n  pure s",
    );
    assert!(
        e.to_lowercase().contains("while") || e.to_lowercase().contains("unsupported"),
        "expected a typed while descope, got: {e}"
    );
}

/// Nested `for` loops — the inner loop in the body is not lowered. LOUD.
#[test]
fn b23_nested_for_loud_reject() {
    expect_loud_reject(
        "def nf : Option Nat := do\n  let mut s := 0\n  for x in [1, 2] do\n    for y in [3, 4] do\n      s := s + y\n  pure s",
    );
}

/// A loop body mutating TWO accumulators — only one is supported. LOUD.
#[test]
fn b23_multi_accumulator_loud_reject() {
    let e = expect_loud_reject(
        "def ma : Option Nat := do\n  let mut a := 0\n  let mut b := 0\n  for x in [1, 2] do\n    a := a + x\n    b := b + 1\n  pure (a + b)",
    );
    assert!(
        e.to_lowercase().contains("accumulator") || e.to_lowercase().contains("unsupported"),
        "expected a typed multi-accumulator descope, got: {e}"
    );
}

/// A non-tail `return` inside the loop body needs the Option-tunneling
/// accumulator — descoped LOUD (B23 lands accumulate + break/continue).
#[test]
fn b23_return_in_for_body_loud_reject() {
    let e = expect_loud_reject(
        "def rr (n : Nat) : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3] do\n    if x == n then\n      return 99\n    s := s + x\n  pure s",
    );
    assert!(
        e.to_lowercase().contains("return") || e.to_lowercase().contains("unsupported"),
        "expected a typed early-return descope, got: {e}"
    );
}

/// Reassigning a NON-`mut` binding inside the loop — Lean rejects; clean rejects
/// LOUD (never "free variables").
#[test]
fn b23_for_reassign_immutable_loud_reject() {
    let e = expect_loud_reject(
        "def im : Option Nat := do\n  let s := 0\n  for x in [1, 2] do\n    s := s + x\n  pure s",
    );
    assert!(
        e.to_lowercase().contains("immutable") || e.to_lowercase().contains("mut"),
        "expected an immutable-reassignment descope, got: {e}"
    );
}
