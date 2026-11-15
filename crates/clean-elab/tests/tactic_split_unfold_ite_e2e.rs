// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for `unfold <def>` followed by `split` on the
//! `if-then-else` the unfolding exposes (Trust two-language battery row r11).
//!
//! ## The defect this guards (measured 2026-09-13)
//!
//! ```text
//! def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
//! theorem min2_le_left (a b : UInt64) : min2 a b <= a := by
//!   unfold min2
//!   split <;> omega
//! ```
//!
//! failed with `type check failed: Unbound variable index: 1 [raised under
//! tactic `<;>` > `split`]` — identically with `Nat`, with `split; omega; omega`
//! and with bullets. Two root causes, each fixed at its source:
//!
//! 1. `unfold` substituted the definition's VALUE without contracting it
//!    against the occurrence's arguments, leaving the goal
//!    `(fun a b => if a < b then a else b) a b ≤ a` — Lean's `deltaExpand`
//!    does `f.betaRev args` and prints `(if a < b then a else b) ≤ a`.
//! 2. `split`'s candidate finder walked into that lambda and returned an `ite`
//!    whose condition was `BVar(1) < BVar(0)`, then lifted it into a
//!    `Decidable.casesOn` spine OUTSIDE the binders; the kernel refused the
//!    term. Lean's `isCandidate?` requires the condition to have no loose
//!    bound variables.
//!
//! Every PASS gate drives the same pipeline as `clean check`: the theorem must
//! register (the kernel re-checks the assembled proof), the proof must
//! `infer_type` def-eq to the stated proposition, and the axiom closure must
//! be free of `sorryAx`. The negative gates pin that a FALSE twin and a
//! binder-scoped `if` are REFUSED with an honest tactic error — never with an
//! internal kernel type-check error, and never by registering a proof.

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Elaborate `source` (which must define `name` last as a tactic-proved
/// theorem) and assert it elaborates + kernel-checks, that the proof
/// `infer_type`s def-eq to its proposition, and that no `sorryAx` is in its
/// axiom closure.
fn assert_tactic_theorem(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, source)
        .unwrap_or_else(|e| panic!("`{name}` must elaborate and kernel-check: {e}"));

    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered after elaboration"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` theorem must carry a proof value"));

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    assert!(
        !deps.iter().any(|d| d.to_string().contains("sorry")),
        "`{name}` axiom closure must not contain sorry, found {deps:?}"
    );
}

/// Assert that `source` is REFUSED: elaboration fails, the failure is an
/// honest tactic verdict (never an internal kernel type-check error), and no
/// proof of `name` is registered.
fn assert_refused_honestly(name: &str, source: &str) -> String {
    let mut env = Environment::with_prelude();
    let err = match try_elaborate_into(&mut env, source) {
        Err(e) => e,
        Ok(()) => {
            let registered = env
                .get_const(&Name::from_string(name))
                .and_then(|info| info.value.clone());
            panic!(
                "`{name}` must be refused, but elaboration succeeded (proof registered: {})",
                registered.is_some()
            );
        }
    };
    for internal in ["Unbound variable", "type check failed", "UnknownFVar"] {
        assert!(
            !err.contains(internal),
            "`{name}` must be refused with an honest tactic error, not an internal one: {err}"
        );
    }
    assert!(
        env.get_const(&Name::from_string(name))
            .and_then(|info| info.value.clone())
            .is_none(),
        "`{name}` must not have a registered proof after a refusal"
    );
    err
}

const MIN2_NAT: &str = "def min2 (a : Nat) (b : Nat) : Nat := if a < b then a else b\n";
const MIN2_U64: &str = "def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b\n";

// ---------------------------------------------------------------------------
// PASS gates — the exact battery fixture, three tactic spellings, on `Nat`
// ---------------------------------------------------------------------------

#[test]
fn unfold_split_seq_focus_omega_nat() {
    assert_tactic_theorem(
        "min2_le_left",
        &format!(
            "{MIN2_NAT}theorem min2_le_left (a b : Nat) : min2 a b <= a := by\n  unfold min2\n  split <;> omega\n"
        ),
    );
}

#[test]
fn unfold_split_two_omega_nat() {
    assert_tactic_theorem(
        "min2_le_left",
        &format!(
            "{MIN2_NAT}theorem min2_le_left (a b : Nat) : min2 a b <= a := by\n  unfold min2\n  split\n  omega\n  omega\n"
        ),
    );
}

#[test]
fn unfold_split_bullets_omega_nat() {
    assert_tactic_theorem(
        "min2_le_left",
        &format!(
            "{MIN2_NAT}theorem min2_le_left (a b : Nat) : min2 a b <= a := by\n  unfold min2\n  split\n  · omega\n  · omega\n"
        ),
    );
}

/// The other true bound, same tactics: `min2 a b ≤ b`.
#[test]
fn unfold_split_seq_focus_omega_nat_right_bound() {
    assert_tactic_theorem(
        "min2_le_right",
        &format!(
            "{MIN2_NAT}theorem min2_le_right (a b : Nat) : min2 a b <= b := by\n  unfold min2\n  split <;> omega\n"
        ),
    );
}

/// `unfold … at hm` contracts the redex in the hypothesis too (same helper);
/// rewriting it back into the goal then splits and proves.
#[test]
fn unfold_at_hypothesis_then_rw_split_nat() {
    assert_tactic_theorem(
        "min2_le_left_of_hyp",
        &format!(
            "{MIN2_NAT}theorem min2_le_left_of_hyp (a b c : Nat) (hm : min2 a b = c) : c <= a := by\n  unfold min2 at hm\n  rw [← hm]\n  split <;> omega\n"
        ),
    );
}

/// `split`'s branch hypothesis must not SHADOW a user hypothesis named `h`
/// (Lean's is inaccessible, `h✝`, so it never can). Measured 2026-09-13: with
/// a clashing `h : min2 a b = c` in context, omega read the wrong `h` and
/// refused (`close_goal rejected arithmetic proof: type mismatch`); the same
/// proof with the hypothesis renamed `hm` went through.
#[test]
fn split_hypothesis_does_not_shadow_user_h_nat() {
    assert_tactic_theorem(
        "min2_le_left_with_h",
        &format!(
            "{MIN2_NAT}theorem min2_le_left_with_h (a b c : Nat) (h : min2 a b = c) : min2 a b <= a := by\n  unfold min2\n  split <;> omega\n"
        ),
    );
}

// ---------------------------------------------------------------------------
// `UInt64` — `split` succeeds AND `omega` now closes both branches
//
// These two were REFUSAL gates when this file was written (77ecd98dd,
// 2026-09-13 12:33). `add7ca7a8` landed 4h26m later the same afternoon —
// "tactic(omega/linarith): pure-order reconstruction over UInt carriers
// (W2 r11)" — and its own message names this file's exact fixture as now
// verifying end-to-end, axiom-free. It was purely additive (5 files, 455
// insertions, 0 deletions) and never revisited these two gates, so they have
// asserted a superseded disposition ever since.
//
// `omega` (`tactic/omega_tactic/mod.rs`) and `linarith`
// (`tactic/arith_linarith/mod.rs`) both consult
// `tactic/arith_uint_order.rs::try_prove_uint_order`, which reduces a
// PURE-ORDER goal over an allow-listed fixed-width unsigned carrier
// (`UInt8/16/32/64`, `USize`) to the matching `Nat` problem over opaque
// `<carrier>.toNat` atoms — sound because `UInt64.le` IS `Nat.le` on the
// order-preserving `.toNat` embedding. That discharges exactly the two goals
// `split` produces here: `a ≤ a` and `¬(a < b) ⊢ b ≤ a`.
//
// The fail-closed boundary is atom SHAPE, not goal truth: `is_pure_order_atom`
// admits only a bare FVar / literal / nullary const / `OfNat.ofNat`, so any
// atom carrying `+`, `-` or `*` is refused because `UInt` arithmetic wraps at
// 2^w. The FALSE twins below (`false_twin_is_refused_honestly_u64` and its
// `Nat` sibling) are the load-bearing negatives for that boundary and must
// stay refusal gates.
//
// So these two are converted to PASS gates rather than deleted: between them
// they hold the `<;>` combinator spelling and the explicit-bullet spelling
// under the registration + def-eq + axiom-closure helper, neither of which
// `lean4_corpus_tests.rs`'s positive twin covers.
// ---------------------------------------------------------------------------

/// The exact `UInt64` fixture with the `<;>` combinator. `split` produces the
/// two branch goals and `omega` closes both through the UInt pure-order lane.
#[test]
fn unfold_split_seq_focus_u64_verifies() {
    assert_tactic_theorem(
        "min2_le_left",
        &format!(
            "{MIN2_U64}theorem min2_le_left (a b : UInt64) : min2 a b <= a := by\n  unfold min2\n  split <;> omega\n"
        ),
    );
}

/// The same fixture with EXPLICIT BULLETS, which is what this test uniquely
/// covers: the `isTrue` branch `a ≤ a` closes by `Nat.le_refl` through kernel
/// defeq (`UInt64.le` unfolds to `Nat.le` on `toNat`), proving the split itself
/// is kernel-sound on `UInt64`, and the `¬(a < b) → b ≤ a` branch closes by
/// `omega` through the pure-order lane.
#[test]
fn unfold_split_u64_branches_are_ordinary_goals() {
    assert_tactic_theorem(
        "min2_le_left",
        &format!(
            "{MIN2_U64}theorem min2_le_left (a b : UInt64) : min2 a b <= a := by\n  unfold min2\n  split\n  · exact Nat.le_refl _\n  · omega\n"
        ),
    );
}

// ---------------------------------------------------------------------------
// FAIL gates — refusals must be honest
// ---------------------------------------------------------------------------

/// FALSE twin: `b ≤ min2 a b` fails when `a < b`. Same tactics; must be
/// refused by `omega` on the branch it cannot prove, never by an internal
/// error, and never registered.
#[test]
fn false_twin_is_refused_honestly_nat() {
    let err = assert_refused_honestly(
        "min2_ge_right_false",
        &format!(
            "{MIN2_NAT}theorem min2_ge_right_false (a b : Nat) : b <= min2 a b := by\n  unfold min2\n  split <;> omega\n"
        ),
    );
    assert!(
        err.contains("omega"),
        "the false twin must be refused by omega: {err}"
    );
}

/// FALSE twin on `UInt64`, same shape.
#[test]
fn false_twin_is_refused_honestly_u64() {
    assert_refused_honestly(
        "min2_ge_right_false",
        &format!(
            "{MIN2_U64}theorem min2_ge_right_false (a b : UInt64) : b <= min2 a b := by\n  unfold min2\n  split <;> omega\n"
        ),
    );
}

/// The `split` half of the fix on its own: a goal whose only `if` sits under
/// a `∀` and mentions the bound variable is REFUSED with the fix named — Lean
/// refuses it too ("Could not split an `if` or `match` expression in the
/// goal"). Before the guard this was the same "Unbound variable index"
/// internal error.
#[test]
fn split_refuses_binder_scoped_ite_with_named_fix() {
    let err = assert_refused_honestly(
        "under_binder",
        "theorem under_binder (b : Nat) : ∀ x : Nat, (if x < b then x else b) <= b := by\n  split <;> omega\n",
    );
    assert!(
        err.contains("under a binder") && err.contains("intro"),
        "the refusal must name the cause and a fix: {err}"
    );
}

/// ... and the same goal proves after `intro x`, the first option the
/// refusal names.
#[test]
fn split_proves_binder_scoped_ite_after_intro() {
    assert_tactic_theorem(
        "under_binder_intro",
        "theorem under_binder_intro (b : Nat) : ∀ x : Nat, (if x < b then x else b) <= b := by\n  intro x\n  split <;> omega\n",
    );
}
