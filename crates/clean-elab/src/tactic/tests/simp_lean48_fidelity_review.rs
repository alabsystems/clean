// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The lane-T review (r4t, 2026-10-09) against pinned Lean 4.8.0: each row is
//! a probe of `scratchpad/r4t-review/p/` or its neighbour, with the oracle's
//! verdict quoted. A negative row asserts the refusal AND its reason.
//!
//! * G48 — the exemption for names Lean generates is as wide as what Lean
//!   realizes, and a `protected` `Init` name is not reached from an atomic
//!   identifier through `open`.
//! * G49 — no `assumption` closer under `[*]`, and `simpa … using e` closes
//!   with `e` alone.
//! * `simp only` — Lean's empty simproc set plus `eq_self` (`simpOnlyBuiltins`).
//! * `rw … at h` — the trailing `with_reducible rfl`, and dependents keep the
//!   old hypothesis.
//! * G41 — numerals beyond `u64`, the named comparison simprocs, and the
//!   canonical `OfNat` instance.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext};

/// Elaborate `code` into one fresh prelude environment; the outcome of the
/// LAST declaration (every earlier one must succeed).
///
/// A `namespace … end` / `section … end` block is ONE declaration that
/// returns `Ok` with a failed leaf inside, so the leaves are read: a block
/// whose inner declaration fails is that failure (integ/r5 2026-10-16 — the
/// `namespace Nat … simp [pow_succ]` row of
/// `test_simp_protected_init_name_through_open_is_unknown` read the block's
/// `Ok` as an acceptance and never saw its subject).
fn elab_last(code: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    clean_olean::declare_environment_world(&mut env, "v4.8.0").expect("fixture source world");
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    assert!(!decls.is_empty(), "nothing parsed from:\n{code}");
    let mut last = Ok(());
    for (i, decl) in decls.iter().enumerate() {
        assert!(
            last.is_ok(),
            "declaration {} failed: {last:?}\n{code}",
            i - 1
        );
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        last = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .map_err(|e| e.to_string())
            .and_then(|result| first_failed_leaf(&result).map_or(Ok(()), Err));
    }
    last
}

/// The rendered error of the first failed leaf declaration of `result`.
fn first_failed_leaf(result: &crate::ElabResult) -> Option<String> {
    let mut leaves = Vec::new();
    result.leaf_decls(&mut leaves);
    leaves.into_iter().find_map(|leaf| match leaf {
        crate::ElabResult::Failed { error, .. } => Some(error.to_string()),
        _ => None,
    })
}

#[track_caller]
fn assert_ok(code: &str) {
    if let Err(e) = elab_last(code) {
        panic!("Lean 4.8.0 accepts; Clean refused: {e}\n--- source ---\n{code}");
    }
}

#[track_caller]
fn assert_err(code: &str, needles: &[&str]) {
    let err = match elab_last(code) {
        Err(e) => e,
        Ok(()) => panic!("Lean 4.8.0 refuses; Clean accepted\n--- source ---\n{code}"),
    };
    let lower = err.to_lowercase();
    for needle in needles {
        assert!(
            lower.contains(&needle.to_lowercase()),
            "refusal does not mention `{needle}`: {err}\n--- source ---\n{code}"
        );
    }
}

const DEFS: &str = "def f : Nat → Nat\n  | 0 => 1\n  | n+1 => n\n\
                    def r : Nat → Nat\n  | 0 => 0\n  | n+1 => r n + 1\n\
                    def fib : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n+2 => fib n + fib (n+1)\n\
                    def g (n : Nat) : Nat := n + 1\n\
                    inductive T where\n  | a : T\n  | b : Nat → T\n\
                    structure P where\n  h : True\n\
                    inductive I : Nat → Type where\n  | mk : (n : Nat) → I n\n\
                    inductive J : Nat → Type where\n  | mk : (n m : Nat) → J n\n";

fn with_defs(simp_arg: &str) -> String {
    format!("{DEFS}theorem gen : True := by simp [{simp_arg}]\n")
}

// ------------------------------------------------- G48: generated names ----

/// Names pinned Lean 4.8.0 does NOT realize ("unknown identifier" /
/// "unknown constant"): a non-recursive `f` has only `f.eq_1`; `fib` has three
/// equations, `r` two; `.injEq` needs a constructor with a data field the
/// result indices do not fix; a theorem has no equations.
#[test]
fn test_simp_generated_names_lean_does_not_realize_are_unknown() {
    for name in [
        "f.eq_7",
        "f.eq_2",
        "f.eq_0",
        "f.eq_01",
        "r.eq_3",
        "fib.eq_4",
        "g.eq_2",
        "g.injEq",
        "g.inj",
        "T.a.injEq",
        "P.mk.injEq",
        "I.mk.injEq",
        "Nat.add_zero.eq_def",
        "Nat.add_zero.inj",
        "Nat.add_zero.eq_1",
    ] {
        assert_err(&with_defs(name), &["unknown identifier", name]);
    }
}

/// Names Lean 4.8.0 realizes and Clean does not mint stay a skipped element,
/// never an unknown identifier (each accepted by the pinned oracle).
#[test]
fn test_simp_generated_names_lean_realizes_are_skipped() {
    for name in [
        "f.eq_1",
        "f.eq_def",
        "r.eq_1",
        "r.eq_2",
        "fib.eq_3",
        "g.eq_1",
        "g.eq_def",
        "T.b.injEq",
        "T.b.inj",
        "J.mk.injEq",
        "Except.ok.injEq",
        "Option.some.injEq",
    ] {
        assert_ok(&with_defs(name));
    }
}

// --------------------------------------------- G48: protected Init names ----

/// `pow_succ`, `max_def`, `zero_lt_one`, `div_self` are protected in `Nat`:
/// Lean 4.8.0 says "unknown identifier" under `open Nat` and inside
/// `namespace Nat`; the qualified `Nat.pow_succ` and the unprotected
/// `succ_le_succ` resolve.
#[test]
fn test_simp_protected_init_name_through_open_is_unknown() {
    for name in ["pow_succ", "max_def", "zero_lt_one", "div_self"] {
        assert_err(
            &format!("open Nat in\ntheorem pr (n : Nat) : n + 0 = n := by simp [{name}]\n"),
            &["unknown identifier", name],
        );
    }
    assert_err(
        "namespace Nat\ntheorem pr1 (n : Nat) : n + 0 = n := by simp [pow_succ]\nend Nat\n",
        &["unknown identifier", "pow_succ"],
    );
    assert_ok("open Nat in\ntheorem pr3 (n : Nat) : n + 0 = n := by simp [succ_le_succ]\n");
    assert_ok("open Nat in\ntheorem pr4 (n : Nat) : n + 0 = n := by simp [Nat.pow_succ]\n");
}

// ------------------------------------------------- G49: [*] and simpa ----

/// t1: under `[*]` the hypothesis is a rewrite rule, not an `assumption`
/// (Lean: "simp made no progress"); sa1/sa2 still close by the rule.
#[test]
fn test_simp_star_has_no_assumption_closer() {
    assert_err(
        "def myid (n : Nat) : Nat := n\n\
         theorem t1 (n : Nat) (h : myid n = 0) : n = 0 := by simp [*]\n",
        &["no progress"],
    );
    assert_ok("theorem sa1 (n : Nat) (h : n = 0) : n = 0 := by simp [*]\n");
    assert_ok("theorem sa2 (p : Prop) (h : p) : p := by simp [*]\n");
}

/// s1-s3: `simpa … using e` closes with `e` only (Lean: "type mismatch").
#[test]
fn test_simpa_using_closes_with_the_term_only() {
    for code in [
        "theorem s1 (P Q : Prop) (hq : Q) (hp : P) : P := by simpa using hq\n",
        "theorem s2 (n : Nat) (hq : n + 0 = 1) (hp : n = 0) : n = 0 := by simpa using hq\n",
        "theorem s3 (n : Nat) (hp : n = 0) : n + 0 = 0 := by simpa [Nat.add_zero] using (rfl : 1 = 1)\n",
    ] {
        assert_err(code, &["mismatch"]);
    }
    assert_ok("theorem sa3 (n : Nat) (h : n = 0) : n = 0 := by simpa\n");
    assert_ok("theorem sa4 (n : Nat) (h : n = 0) : n = 0 := by simpa using h\n");
    assert_ok("theorem sa5 (P Q : Prop) (hp : P) (hq : Q) : P ∧ True := by simpa using hp\n");
}

// ------------------------------------------------------- simp only ----

/// m9/m1: `simp only` carries `eq_self`; m7: `¬(n = n)` becomes `¬True` and
/// stays (Lean: "unsolved goals … h : ¬True ⊢ False").
#[test]
fn test_simp_only_carries_eq_self_at_a_hypothesis() {
    assert_ok(
        "theorem m9 (a : Nat) (P : Prop) (h : a = a ∧ P) : P := by simp only [true_and] at h; exact h\n",
    );
    assert_ok(
        "theorem m10 (a : Nat) (P : Prop) (h : P) : a = a ∧ P := by simp only [true_and]; exact h\n",
    );
    assert_err(
        "theorem m7 (n : Nat) (h : ¬ (n = n)) : False := by simp only [] at h\n",
        &["unsolved goals"],
    );
}

/// l4-l7: Lean's `simp only` runs no simproc it does not name, so literal
/// arithmetic is left alone ("simp made no progress").
#[test]
fn test_simp_only_runs_no_unnamed_simproc() {
    for code in [
        "theorem l4 (x : Nat) (h : x = 2 + 2) : x = 4 := by simp only [] at h; exact h\n",
        "theorem l5 (x : Nat) (h : x = 4) : x = 2 + 2 := by simp only []; exact h\n",
        "theorem l6 (x : Nat) (h : x = 2 + 2) : x = 4 := by simp only [Nat.add_zero] at h; exact h\n",
        "theorem l7 (x : Nat) (h : x = 2 * 3) : x = 6 := by simp only [] at h; exact h\n",
    ] {
        assert_err(code, &["no progress"]);
    }
}

/// g5 and kin, KNOWN FALSE ACCEPTANCE (ledger class (153), G83; integ/r5
/// 2026-10-16): pinned Lean 4.8.0 refuses each ("simp made no progress",
/// "unsolved goals"), Clean ACCEPTS. Not a simproc: `&&`/`||` lower to `and` /
/// `or`, which Clean's builtin prelude marks REDUCIBLE (aliases of the
/// recursor-defined `Bool.and` / `Bool.or`), while Lean 4.8.0 has them
/// semireducible (`getReducibilityStatus`; `Bool.and` is the reducible one
/// there). So `simpOnlyBuiltins`' `eq_self` and `rw`'s `with_reducible rfl`
/// see `true && false` as `false`. g5 was a row of
/// `test_simp_only_runs_no_unnamed_simproc`, failing in the merge suite for
/// this reason (origin/main accepts it too). Fails the day it closes; then
/// move g5 back there and assert these refusals.
#[test]
fn test_bool_and_or_reducible_in_prelude_known_false_acceptance() {
    for code in [
        "theorem g5 : (true && false) = false := by simp only []\n",
        "theorem g5b (b : Bool) (h : b = true) : (b && false) = false := by rw [h]\n",
        "theorem g5c : (true || false) = true := by simp only []\n",
    ] {
        assert!(
            elab_last(code).is_ok(),
            "class (153) closed? Lean refuses this; flip the pin\n{code}"
        );
    }
}

// --------------------------------------------------------- rw … at h ----

/// j1/i1/j3: `rw … at h` ends with `with_reducible rfl` on the main goal, so
/// a following `rfl` has no goal (Lean: "no goals to be solved").
#[test]
fn test_rw_at_hypothesis_closes_a_reflexive_main_goal() {
    assert_err(
        "theorem j1 (a b : Nat) (hab : a = b) (h : a = 5) : 3 = 3 := by\n  rw [hab] at h\n  rfl\n",
        &["no goals"],
    );
    assert_err(
        "theorem i1 (a : Nat) (h : a + 0 = 5) (b : Nat) (hab : a = b) : h = h := by\n  \
         rw [hab] at h\n  rfl\n",
        &["no goals"],
    );
    assert_ok("theorem j2 (a b : Nat) (hab : a = b) (h : a = 5) : 3 = 3 := by\n  rw [hab] at h\n");
}

/// u1/u4: dependents of the rewritten hypothesis keep the OLD one (Lean's
/// `assertAfter` + failed `clear`); Clean retargeted them and refused.
#[test]
fn test_rw_at_hypothesis_with_dependents_keeps_the_old_local() {
    assert_ok(
        "theorem u1 (a b : Nat) (hab : a = b) (h : a = 5) (hp : h = h) : b = 5 := by\n  \
         rw [hab] at h; exact h\n",
    );
    assert_ok(
        "theorem u4 (a b : Nat) (hab : a = b) (h : a = 5) (P : a = 5 → Prop) (hp : P h) :\n    \
         ∃ h' : a = 5, P h' := by\n  rw [hab] at h\n  exact ⟨_, hp⟩\n",
    );
}

/// G38's right-reason twin (k2): the placement after the case equation
/// succeeds and the refusal is `exact`'s, as in Lean ("type mismatch … h has
/// type 0 = 5"); k3 is its accepted neighbour.
#[test]
fn test_rw_at_after_cases_twin_is_refused_by_exact() {
    assert_err(
        "theorem negative (g : Nat → Nat) (x : Nat) (h : g x = 5) : False := by\n  \
         cases hg : g x with\n  | zero => rw [hg] at h; exact h\n  | succ n => rw [hg] at h; exact h\n",
        &["mismatch"],
    );
    assert_ok(
        "theorem positive (g : Nat → Nat) (x : Nat) (h : g x = 5) : ∃ n, g x = n + 1 := by\n  \
         cases hg : g x with\n  | zero => rw [hg] at h; exact absurd h (by decide)\n  \
         | succ n => exact ⟨n, rfl⟩\n",
    );
}

// ------------------------------------------------------------- G41 ----

/// d5e/e5 and kin: numerals at and above `2^64` (Lean accepts each).
#[test]
fn test_simp_decides_numeral_comparisons_beyond_u64() {
    for stmt in [
        "(18446744073709551616 : Nat) > 3",
        "¬ ((18446744073709551615 : Nat) < 4294967296)",
        "(18446744073709551615 : Nat) < 18446744073709551616",
        "¬ ((18446744073709551616 : Int) ≤ -3)",
    ] {
        assert_ok(&format!("theorem big : {stmt} := by simp\n"));
    }
    assert_err(
        "theorem big_false : (18446744073709551616 : Nat) < 3 := by simp\n",
        &["unsolved goals", "False"],
    );
}

/// d2/d3: a named comparison simproc runs under `simp only`, and only on its
/// own head (Lean: `(5 : Nat) > 3` by `simp only [Nat.reduceLT]` is "simp
/// made no progress"; `Nat.reduceLeDiff` stays refused by name).
#[test]
fn test_simp_only_runs_the_named_comparison_simprocs() {
    assert_ok("theorem d2 : (1024 : Nat) > 0 := by simp only [Nat.reduceGT]\n");
    assert_ok("theorem d3 : (3 : Int) < 5 := by simp only [Int.reduceLT]\n");
    assert_ok("theorem d4 : (-3 : Int) ≤ 5 := by simp only [Int.reduceLE]\n");
    assert_err(
        "theorem a1 : (5 : Nat) > 3 := by simp only [Nat.reduceLT]\n",
        &["no progress"],
    );
    assert_err(
        "theorem a12 : (3 : Int) < 5 := by simp only [Int.reduceGT]\n",
        &["no progress"],
    );
    assert_err(
        "theorem b3 : (3 : Nat) ≤ 5 := by simp only [Nat.reduceLeDiff]\n",
        &["Nat.reduceLeDiff", "not implemented"],
    );
}

/// q1: a numeral at a non-canonical `OfNat` instance is not read (Lean:
/// "unsolved goals h : True ⊢ False" — its simp misreads the numeral and the
/// goal stays open; Clean must not close it either).
#[test]
fn test_simp_does_not_read_a_numeral_at_a_noncanonical_instance() {
    let err = elab_last(
        "instance weird : OfNat Nat 5 := ⟨7⟩\n\
         theorem q1 (h : (5 : Nat) < 6) : False := by simp at h\n",
    )
    .expect_err("Lean 4.8.0 refuses: the goal stays open");
    // Lean's simp rewrites `h` to `True` and stops ("unsolved goals"); Clean
    // does not read the numeral at all ("no progress"). Either way the goal
    // is NOT closed from a misread literal.
    assert!(
        err.contains("unsolved goals") || err.contains("no progress"),
        "refused for the open goal, not some other reason: {err}"
    );
}

// ------------------------------------------------- G39: open divergence ----

/// g1, pinned OPEN: the prelude states `ite_eq_left_iff` with Lean
/// v4.30.0-rc2's binder order (`{α} {P} [Decidable P] {a b}`, decision R50:
/// `.olean` import is first-registered-wins), while Lean 4.8.0 has `{α} {a b
/// : α} {P} [Decidable P]`, so a 4.8 explicit application is refused. The day
/// the telescope follows the target Lean, this row flips.
#[test]
fn test_ite_eq_left_iff_explicit_lean48_application_is_an_open_divergence() {
    assert_err(
        "theorem g1 (p : Prop) [Decidable p] :\n    \
         ((if p then 1 else 2) = (1 : Nat)) ↔ (¬p → (2 : Nat) = 1) :=\n  \
         @ite_eq_left_iff Nat 1 2 p _\n",
        &["mismatch"],
    );
}
