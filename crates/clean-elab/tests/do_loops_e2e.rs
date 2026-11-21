// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B23 — do-block imperative control flow: `for`
//! loops over mutable state** (`docs/plans/GAP_SWEEP_2026-07-09.md`, the B08
//! successor for the for/break/continue cases).
//!
//! A loop uses the selected `ForIn` dictionary. Its accumulator carries the
//! mutable state, and each step returns `ForInStep.done` or `ForInStep.yield`.
//! The tests check the resulting values by definitional equality, including
//! early exits, nested accumulators, and a user-defined iterator.
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

const FOR_TUPLE_ACTIONS: &str = r#"
def tupleLoopAction (n : Nat) : Option Unit :=
  if n = 0 then none else some ()

def tupleActionLoop (xs : List (Nat × Nat)) : Option Nat := do
  let left := 7
  let mut count := 0
  for (left, right) in xs do
    tupleLoopAction left
    count := 10 * count + left * right
  pure (count + left)
"#;

#[test]
fn mutable_for_tuple_binds_and_sequences_actions() {
    expect_pass(&format!(
        "{FOR_TUPLE_ACTIONS}\n\
         theorem orderPin : tupleActionLoop [(2, 3), (4, 5)] = some 87 := rfl\n\
         theorem discardedError : tupleActionLoop [(2, 3), (0, 5)] = none := rfl\n\
         theorem zeroSteps : tupleActionLoop [] = some 7 := rfl"
    ));
    expect_loud_reject(&format!(
        "{FOR_TUPLE_ACTIONS}\n theorem wrongOrder : tupleActionLoop [(4, 5), (2, 3)] = some 87 := rfl"
    ));
}

#[test]
fn mutable_for_tuple_refuses_refutable_subpattern() {
    expect_loud_reject(
        r#"
def partialLoop (xs : List (Option Nat × Nat)) : Option Nat := do
  let mut count := 0
  for (some left, right) in xs do
    count := count + left * right
  pure count
"#,
    );
}

#[test]
fn mutable_for_tuple_refuses_to_shadow_the_accumulator() {
    expect_loud_reject(
        r#"
def shadowingLoop (xs : List (Nat × Nat)) : Option Nat := do
  let mut total := 7
  for (total, amount) in xs do
    total := total + amount
  pure total
"#,
    );
}

#[test]
fn mutable_for_tuple_ignores_mutable_declarations_after_the_loop() {
    expect_pass(
        r#"
def becomesMutableLater (xs : List (Nat × Nat)) : Option Nat := do
  let total := 7
  let mut sum := 0
  for (total, amount) in xs do
    sum := sum + total * amount
  let mut total := total
  total := total + 1
  pure (sum + total)
theorem laterPin : becomesMutableLater [(2, 3)] = some 14 := rfl
"#,
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

/// Nested `for` loops. Was a LOUD-REJECT guard; the capability landed and the
/// guard was never retired, so it failed as "descoped shape must be REJECTED,
/// but it fully checked".
///
/// Inverted rather than deleted, and certified by VALUE, not by "it
/// elaborated": the inner loop contributes 3+4 = 7 per outer iteration over a
/// two-element list, so the answer must be 14. A lowering that ran the inner
/// loop once, or hoisted it, would still elaborate and would still be wrong.
#[test]
fn b23_nested_for_value_certified() {
    expect_pass(
        "def nf : Option Nat := do\n  let mut s := 0\n  for x in [1, 2] do\n    for y in [3, 4] do\n      s := s + y\n  pure s\n\n\
         theorem nf_pin : nf = some 14 := rfl",
    );
}

/// A loop body mutating TWO accumulators. Was a LOUD-REJECT guard; the
/// capability landed and the guard was never retired.
///
/// Certified by value with the two accumulators DISTINGUISHED: `a` sums the
/// elements (1+2 = 3) while `b` counts iterations (2), so the answer is 5. If
/// both threaded the same state, or one were dropped, the sum would not be 5.
#[test]
fn b23_multi_accumulator_value_certified() {
    expect_pass(
        "def ma : Option Nat := do\n  let mut a := 0\n  let mut b := 0\n  for x in [1, 2] do\n    a := a + x\n    b := b + 1\n  pure (a + b)\n\n\
         theorem ma_pin : ma = some 5 := rfl",
    );
}

/// A non-tail `return` inside the loop body. Was a LOUD-REJECT guard.
/// Previously needed the Option-tunneling
/// accumulator — descoped LOUD (B23 lands accumulate + break/continue).
#[test]
fn b23_return_in_for_body_value_certified() {
    // Certified by value at THREE points, because "it elaborated" would not
    // distinguish a broken early return: it fires mid-loop (rr 2 = 99), it
    // does NOT fire when nothing matches and the accumulation completes
    // (rr 9 = 1+2+3 = 6), and it fires on the FIRST element before any
    // accumulation (rr 1 = 99).
    expect_pass(
        "def rr (n : Nat) : Option Nat := do\n  let mut s := 0\n  for x in [1, 2, 3] do\n    if x == n then\n      return 99\n    s := s + x\n  pure s\n\n\
         theorem rr_mid : rr 2 = some 99 := rfl\n\n\
         theorem rr_none : rr 9 = some 6 := rfl\n\n\
         theorem rr_first : rr 1 = some 99 := rfl",
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

#[test]
fn mutable_for_matches_constructors_in_kernel_order() {
    let definition = r#"
def sumPairs (xs : List (Option (Nat × Nat))) : Option Nat := do
  let mut total := 1
  for x in xs do
    match x with
    | some (a, b) => total := total + a * b
    | none => break
  pure total
"#;
    expect_pass(&format!(
        "{definition}\ntheorem sumPin : sumPairs [some (2, 3), none, some (7, 8)] = some 7 := rfl"
    ));
    expect_loud_reject(&format!(
        "{definition}\ntheorem wrong : sumPairs [some (2, 3), none, some (7, 8)] = some 63 := rfl"
    ));
    expect_loud_reject(&definition.replace("    | none => break\n", ""));
}

#[test]
fn a_higher_priority_for_in_instance_controls_a_mutable_loop() {
    let source = r#"
local instance (priority := 20000) skipAll : ForIn Id (List Nat) Nat where
  forIn _ initial _ := initial

def selectedCount (xs : List Nat) : Nat := Id.run do
  let mut n := 0
  for x in xs do
    n := n + x
  return n
"#;
    expect_pass(&format!(
        "{source}\ntheorem yes : selectedCount [1, 2, 3] = 0 := rfl"
    ));
    expect_loud_reject(&format!(
        "{source}\ntheorem no : selectedCount [1, 2, 3] = 6 := rfl"
    ));
}
