// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the `(by tac : T)` inline-proof idiom — a `by` tactic
//! block ascribed to a type, e.g. `(by exact h : p)`, `(by simp : P)`.
//!
//! A successful `Ok(ElabResult)` means the assembled proof term was accepted
//! by the trusted kernel via `add_decl`, not merely elaborated: the ascribed
//! `by`-block's proof term must type-check at the correct universe (previously
//! it either degraded to a synthetic `sorry` — the block's tactics were lost —
//! or assembled a mis-universed identity-lambda wrapper the kernel rejected
//! with `Sort(Succ Zero)` vs `Sort(Zero)`).
//!
//! Root cause: the parser's tactic-block reader did not treat the trailing
//! ascription `:` as a block terminator, so `by exact h : p` (inside parens)
//! mis-consumed the `:` as a new tactic, failed, and degraded the whole block
//! to a synthetic sorry; and even once parsed, the macro-expansion roundtrip
//! collapsed the nested `ByTactic` into an empty block. Both are fixed.
//!
//! Cross-checked against real Lean 4: all POSITIVE cases here are accepted by
//! `lean` (empty output, exit 0); the NEGATIVE case is rejected with a type
//! mismatch (`h : p` cannot prove `q`).

use super::*;

/// Tooth 1. An ascribed `by`-block as the whole theorem body:
/// `(by exact h : p)` proves `p` and must kernel-check.
#[test]
fn test_by_ascription_prop_body_kernel_checks() {
    let src = "theorem t (p : Prop) (h : p) : p := (by exact h : p)";
    elab_decl_with_prelude(src).expect("(by exact h : p) as theorem body should kernel-check");
}

/// Tooth 2. An ascribed `by`-block bound by a term-level `let`:
/// `let h2 := (by exact h : p); h2`. Previously this assembled a mis-universed
/// wrapper (`Sort(Succ Zero)` vs `Sort(Zero)`) the kernel rejected.
#[test]
fn test_by_ascription_in_term_let_kernel_checks() {
    let src = "theorem t (p : Prop) (h : p) : p := let h2 := (by exact h : p); h2";
    elab_decl_with_prelude(src).expect("let h2 := (by exact h : p); h2 should kernel-check");
}

/// Tooth 3. An ascribed `by`-block proving a compound `Prop` (an equality):
/// `(by exact h : a = b)`.
#[test]
fn test_by_ascription_compound_prop_kernel_checks() {
    let src = "theorem t (a b : Nat) (h : a = b) : a = b := (by exact h : a = b)";
    elab_decl_with_prelude(src)
        .expect("(by exact h : a = b) proving a compound Prop should kernel-check");
}

/// Tooth 4 (data ascription). A `by`-block ascribed to a DATA type used as an
/// operator argument: `(by exact 5 : Nat) + 1`. Confirms the fix also covers
/// non-`Prop` ascriptions in an application-argument position.
#[test]
fn test_by_ascription_data_as_operator_arg_kernel_checks() {
    let src = "def f : Nat := (by exact 5 : Nat) + 1";
    elab_decl_with_prelude(src)
        .expect("(by exact 5 : Nat) + 1 (data ascription arg) should kernel-check");
}

/// NEGATIVE. `(by exact h : q)` with `h : p` and `p ≠ q` cannot prove `q`.
/// The kernel-checked `exact` must reject the type mismatch — ERROR, no panic,
/// no over-accept. Real Lean 4 rejects this identically.
#[test]
fn test_by_ascription_wrong_prop_errors() {
    let src = "theorem t (p q : Prop) (h : p) : q := (by exact h : q)";
    let result = elab_decl_with_prelude(src);
    assert!(
        result.is_err(),
        "(by exact h : q) with h : p must error (type mismatch), got {result:?}"
    );
}

/// CONTROL. A NON-`by` ascription of a term to a Prop still works: `(h : p)`.
#[test]
fn test_plain_ascription_to_prop_still_kernel_checks() {
    let src = "theorem t (p : Prop) (h : p) : p := (h : p)";
    elab_decl_with_prelude(src).expect("plain (h : p) ascription should kernel-check");
}

/// CONTROL. A bare `by`-block as the theorem body still works:
/// `by exact h`.
#[test]
fn test_bare_by_block_body_still_kernel_checks() {
    let src = "theorem t (p : Prop) (h : p) : p := by exact h";
    elab_decl_with_prelude(src).expect("bare `by exact h` body should kernel-check");
}
