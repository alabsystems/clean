// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! The prelude lemmas restated to pinned Lean v4.30.0-rc2's EXACT statements
//! (2026-09-30; `data/prelude_collision_ratchet.json`), checked at the
//! surface a user writes.
//!
//! Before the restatement these lemmas took every argument explicitly, in the
//! prelude's own order, and were stated over the bare `Nat.le` / `Nat.mod` /
//! `Nat.min`. So a Lean-style call (`Nat.lt_trans h1 h2`,
//! `Nat.mod_eq_of_lt h`, `UInt8.le_iff_toNat_le.mp h`) failed to elaborate.
//! (The old explicit call, `Nat.lt_trans a b c h1 h2`, was ACCEPTED where
//! Lean refuses it, by a separate elaborator class, (73), closed by commit
//! 8c866b7fe; see `EXPLICIT_AT_IMPLICIT`.) Measured on the base binary: 12 of the first 20 POSITIVE
//! declarations below failed. The `Nat.toUInt8` / `Nat.shiftRight` rows pin
//! that an `@& Nat` (mdata) binder domain still applies and computes.
//!
//! Every declaration here was run through the pinned Lean binary
//! (`~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`, no
//! imports beyond the implicit `Init`): each POSITIVE one is accepted, and
//! each NEGATIVE and EXPLICIT_AT_IMPLICIT one is rejected. The negatives are
//! the controls the widening needs -- a fix that only grows what elaborates is
//! invisible to a success ratchet -- and Clean refuses them too. The
//! explicit-at-implicit calls were a separate, pre-existing elaborator class
//! that Clean accepted until it closed; see `EXPLICIT_AT_IMPLICIT`.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top
/// of the default prelude. Err carries the first failure.
fn elaborate_module(source: &str) -> Result<(), String> {
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
            return Err(failures.join("\n"));
        }
    }
    Ok(())
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

/// Lean-style uses pinned Lean accepts: implicit arguments left implicit,
/// class notation in the goals, and `rw` matching the notation.
const POSITIVE: &[(&str, &str)] = &[
    (
        "Nat.lt_trans",
        "theorem p (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := Nat.lt_trans h1 h2",
    ),
    (
        "Nat.lt_of_lt_of_le",
        "theorem p (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := Nat.lt_of_lt_of_le h1 h2",
    ),
    (
        "Nat.mod_eq_of_lt",
        "theorem p (a b : Nat) (h : a < b) : a % b = a := Nat.mod_eq_of_lt h",
    ),
    (
        "Nat.le_mul_of_pos_right",
        "theorem p (m n : Nat) (h : 0 < m) : n ≤ n * m := Nat.le_mul_of_pos_right n h",
    ),
    (
        "Nat.lt_of_mul_lt_mul_left",
        "theorem p (a b c : Nat) (h : a * b < a * c) : b < c := Nat.lt_of_mul_lt_mul_left h",
    ),
    (
        "Nat.min_eq_left",
        "theorem p (a b : Nat) (h : a ≤ b) : min a b = a := Nat.min_eq_left h",
    ),
    (
        "Nat.min_eq_right",
        "theorem p (a b : Nat) (h : b ≤ a) : min a b = b := Nat.min_eq_right h",
    ),
    (
        "Nat.min_def",
        "theorem p (n m : Nat) : min n m = if n ≤ m then n else m := Nat.min_def",
    ),
    (
        "Nat.div_le_self",
        "theorem p (n k : Nat) : n / k ≤ n := Nat.div_le_self n k",
    ),
    (
        "Nat.le_add_left",
        "theorem p (n m : Nat) : n ≤ m + n := Nat.le_add_left n m",
    ),
    (
        "Nat.ge_of_not_lt",
        "theorem p (n m : Nat) (h : ¬ n < m) : n ≥ m := Nat.ge_of_not_lt h",
    ),
    (
        "Nat.le_of_not_lt",
        "theorem p (a b : Nat) (h : ¬ a < b) : b ≤ a := Nat.le_of_not_lt h",
    ),
    (
        "UInt8.le_iff_toNat_le",
        "theorem p (a b : UInt8) (h : a ≤ b) : a.toNat ≤ b.toNat := UInt8.le_iff_toNat_le.mp h",
    ),
    (
        "UInt64.lt_iff_toNat_lt",
        "theorem p (a b : UInt64) (h : a < b) : a.toNat < b.toNat := UInt64.lt_iff_toNat_lt.mp h",
    ),
    (
        "UInt8.toNat_lt",
        "theorem p (x : UInt8) : x.toNat < 2 ^ 8 := UInt8.toNat_lt x",
    ),
    (
        "UInt32.toNat_div",
        "theorem p (a b : UInt32) : (a / b).toNat = a.toNat / b.toNat := UInt32.toNat_div a b",
    ),
    (
        "UInt16.toNat_ofNat",
        "theorem p (n : Nat) : (UInt16.ofNat n).toNat = n % 2 ^ 16 := @UInt16.toNat_ofNat n",
    ),
    (
        "decide_eq_decide",
        "theorem p (p q : Prop) [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q := \
         decide_eq_decide.mpr h",
    ),
    (
        "Nat.toUInt8 (borrowed `@& Nat` domain)",
        "theorem p : (Nat.toUInt8 300).toNat = 44 := rfl",
    ),
    (
        "Nat.shiftRight (borrowed `@& Nat` domains)",
        "theorem p : Nat.shiftRight 1024 5 = 32 := rfl",
    ),
    (
        "UInt64.toNat_ofNat at Nat.toUInt64",
        "theorem p (n : Nat) : (Nat.toUInt64 n).toNat = n % 2 ^ 64 := UInt64.toNat_ofNat",
    ),
    (
        "rw [Nat.mod_eq_of_lt h]",
        "theorem p (a b : Nat) (h : a < b) : a % b + 0 = a + 0 := by rw [Nat.mod_eq_of_lt h]",
    ),
    (
        "rw [Nat.min_eq_left h]",
        "theorem p (a b : Nat) (h : a ≤ b) : min a b + 0 = a + 0 := by rw [Nat.min_eq_left h]",
    ),
];

/// MISUSES of the restated lemmas — a swapped hypothesis, the wrong
/// direction of an `Iff`, a goal the statement does not prove, a `rw` at a goal
/// without the pattern. Pinned Lean rejects each; so must Clean. These are the
/// controls for the widening above: a Lean-style use now elaborates, and a
/// wrong one still does not.
const NEGATIVE: &[(&str, &str)] = &[
    (
        "Nat.lt_trans, hypotheses swapped",
        "theorem n (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := Nat.lt_trans h2 h1",
    ),
    (
        "Nat.lt_of_lt_of_le, hypotheses swapped",
        "theorem n (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := \
         Nat.lt_of_lt_of_le h2 h1",
    ),
    (
        "Nat.mod_eq_of_lt at the flipped goal",
        "theorem n (a b : Nat) (h : a < b) : b % a = b := Nat.mod_eq_of_lt h",
    ),
    (
        "Nat.le_mul_of_pos_right, multiplier passed as `n`",
        "theorem n (m n : Nat) (h : 0 < m) : n ≤ n * m := Nat.le_mul_of_pos_right m h",
    ),
    (
        "Nat.le_mul_of_pos_right, the old prelude order",
        "theorem n (m n : Nat) (h : 0 < m) : n ≤ n * m := Nat.le_mul_of_pos_right n m h",
    ),
    (
        "Nat.lt_of_mul_lt_mul_left at the flipped goal",
        "theorem n (a b c : Nat) (h : a * b < a * c) : c < b := Nat.lt_of_mul_lt_mul_left h",
    ),
    (
        "Nat.lt_of_mul_lt_mul_left, the old prelude order",
        "theorem n (a b c : Nat) (h : a * b < a * c) : b < c := \
         Nat.lt_of_mul_lt_mul_left b c a h",
    ),
    (
        "Nat.min_eq_left at the other side",
        "theorem n (a b : Nat) (h : a ≤ b) : min a b = b := Nat.min_eq_left h",
    ),
    (
        "Nat.min_eq_right from the wrong hypothesis",
        "theorem n (a b : Nat) (h : a ≤ b) : min a b = b := Nat.min_eq_right h",
    ),
    (
        "Nat.min_def with the test flipped",
        "theorem n (n m : Nat) : min n m = if m ≤ n then n else m := Nat.min_def",
    ),
    (
        "Nat.div_le_self at the divisor",
        "theorem n (n k : Nat) : n / k ≤ k := Nat.div_le_self n k",
    ),
    (
        "Nat.le_add_left at the other summand",
        "theorem n (n m : Nat) : m ≤ m + n := Nat.le_add_left n m",
    ),
    (
        "Nat.ge_of_not_lt at the flipped goal",
        "theorem n (n m : Nat) (h : ¬ n < m) : m ≥ n := Nat.ge_of_not_lt h",
    ),
    (
        "Nat.le_of_not_lt at the flipped goal",
        "theorem n (a b : Nat) (h : ¬ a < b) : a ≤ b := Nat.le_of_not_lt h",
    ),
    (
        "UInt8.le_iff_toNat_le from the reversed hypothesis",
        "theorem n (a b : UInt8) (h : b ≤ a) : a.toNat ≤ b.toNat := \
         UInt8.le_iff_toNat_le.mp h",
    ),
    (
        "UInt64.lt_iff_toNat_lt from the reversed hypothesis",
        "theorem n (a b : UInt64) (h : b < a) : a.toNat < b.toNat := \
         UInt64.lt_iff_toNat_lt.mp h",
    ),
    (
        "UInt8.toNat_lt at a smaller bound",
        "theorem n (x : UInt8) : x.toNat < 2 ^ 7 := UInt8.toNat_lt x",
    ),
    (
        "UInt32.toNat_div with the quotient flipped",
        "theorem n (a b : UInt32) : (a / b).toNat = b.toNat / a.toNat := UInt32.toNat_div a b",
    ),
    (
        "UInt16.toNat_ofNat at the wrong width",
        "theorem n (n : Nat) : (UInt16.ofNat n).toNat = n % 2 ^ 8 := @UInt16.toNat_ofNat n",
    ),
    (
        "decide_eq_decide in the wrong direction",
        "theorem n (p q : Prop) [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q := \
         decide_eq_decide.mp h",
    ),
    (
        "Nat.toUInt8 does not drop the wrap",
        "theorem n : (Nat.toUInt8 300).toNat = 300 := rfl",
    ),
    (
        "rw [Nat.mod_eq_of_lt h] at a goal without `a % b`",
        "theorem n (a b : Nat) (h : a < b) : b % a = b := by rw [Nat.mod_eq_of_lt h]",
    ),
];

/// NEGATIVE controls for ledger class (73), CLOSED: every argument passed
/// explicitly to a lemma whose leading binders are implicit, the call shape
/// these lemmas had in the prelude before 2026-09-30. Pinned Lean v4.30.0-rc2
/// rejects each (rows 1-5 "Application type mismatch", rows 6-9 "Function
/// expected", re-run 2026-11-14). Clean accepted them until commit 8c866b7fe
/// removed `try_consume_leading_implicit_args`, which let an explicit argument
/// fill a leading implicit binder whenever an expected type was present (#796,
/// recursor motives); only `@` or a named argument positions an implicit now.
/// Recorded as a divergence until 2026-11-14 (the class's history is in
/// `docs/FRONTEND_CLASS_LEDGER.md`); asserted REJECTED from then on, so a
/// reintroduction of the consumption fails here.
const EXPLICIT_AT_IMPLICIT: &[(&str, &str)] = &[
    (
        "Nat.lt_trans",
        "theorem n (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := Nat.lt_trans a b c h1 h2",
    ),
    (
        "Nat.lt_of_lt_of_le",
        "theorem n (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := \
         Nat.lt_of_lt_of_le a b c h1 h2",
    ),
    (
        "Nat.mod_eq_of_lt",
        "theorem n (a b : Nat) (h : a < b) : a % b = a := Nat.mod_eq_of_lt a b h",
    ),
    (
        "Nat.min_eq_left",
        "theorem n (a b : Nat) (h : a ≤ b) : min a b = a := Nat.min_eq_left a b h",
    ),
    (
        "Nat.min_eq_right",
        "theorem n (a b : Nat) (h : b ≤ a) : min a b = b := Nat.min_eq_right a b h",
    ),
    (
        "Nat.min_def",
        "theorem n (n m : Nat) : min n m = if n ≤ m then n else m := Nat.min_def n m",
    ),
    (
        "UInt8.le_iff_toNat_le",
        "theorem n (a b : UInt8) (h : a ≤ b) : a.toNat ≤ b.toNat := \
         (UInt8.le_iff_toNat_le a b).mp h",
    ),
    (
        "UInt64.lt_iff_toNat_lt",
        "theorem n (a b : UInt64) (h : a < b) : a.toNat < b.toNat := \
         (UInt64.lt_iff_toNat_lt a b).mp h",
    ),
    (
        "UInt16.toNat_ofNat",
        "theorem n (n : Nat) : (UInt16.ofNat n).toNat = n % 2 ^ 16 := UInt16.toNat_ofNat n",
    ),
];

#[test]
fn test_lean_style_uses_of_restated_lemmas_elaborate() {
    let failures: Vec<String> = POSITIVE
        .iter()
        .filter_map(|(what, src)| elaborate_module(src).err().map(|e| format!("{what}: {e}")))
        .collect();
    assert!(
        failures.is_empty(),
        "pinned Lean accepts every one of these; Clean refused {} of {}:\n{}",
        failures.len(),
        POSITIVE.len(),
        failures.join("\n")
    );
}

#[test]
fn test_misuses_of_restated_lemmas_are_rejected() {
    let accepted: Vec<&str> = NEGATIVE
        .iter()
        .filter(|(_, src)| elaborate_module(src).is_ok())
        .map(|(what, _)| *what)
        .collect();
    assert!(
        accepted.is_empty(),
        "pinned Lean rejects every one of these; Clean accepted {} of {}: {accepted:?}",
        accepted.len(),
        NEGATIVE.len()
    );
}

#[test]
fn test_explicit_args_at_implicit_binders_are_rejected() {
    let mut accepted = Vec::new();
    for (what, src) in EXPLICIT_AT_IMPLICIT {
        match elaborate_module(src) {
            Ok(()) => accepted.push(*what),
            Err(e) => assert!(
                !e.to_lowercase().contains("sorry"),
                "{what}: the rejection must not be laundered into a sorry: {e}"
            ),
        }
    }
    assert!(
        accepted.is_empty(),
        "class (73) reopened: pinned Lean rejects every explicit-at-implicit call; \
         Clean accepted {} of {}: {accepted:?}",
        accepted.len(),
        EXPLICIT_AT_IMPLICIT.len()
    );
}
