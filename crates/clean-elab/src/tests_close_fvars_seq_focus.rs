// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression: `constructor <;> intro h <;> exact h` on an `Iff` goal must not
//! panic in `close_fvars`.
//!
//! `constructor` on `p ↔ p` produces two PARALLEL sibling goals (the `mp`/`mpr`
//! arms of `Iff.intro`). The `<;>` (`SeqFocus`) combinator then runs `intro h`
//! on each. Before the fix, the two sibling `intro`s allocated *distinct,
//! monotonically-growing* tactic FVar ids (1 and 2), but each arm's `λ h => h`
//! lambda is only at binder depth 1. `close_fvars` converts a tactic FVar `n`
//! to a BVar only when `(n - base) < depth`, so the second arm's FVar (id 2 at
//! depth 1) was never converted — tripping the `debug_assert!` in
//! `close_fvars.rs` (panic in debug; "contains free variables" in release).
//!
//! The fix resets `next_fvar` to a shared base before each parallel sibling
//! branch in the `<;>` / `all_goals` / `any_goals` combinators, so every arm's
//! `intro` allocates the same FVar id and the id↔depth correspondence holds.
//! The assembled proof is still kernel-rechecked by `add_decl`.

use crate::tactic::builtins::builtin_tactic_patterns;
use crate::{elaborate_decl_and_register_with_warning, preprocess_decl_with_context, FileContext};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file_with_tactics;

/// Parse + elaborate `code`, asserting every declaration registers cleanly.
///
/// Mirrors the `clean check` pipeline exactly (cmd_core.rs `check_file_body`):
/// `parse_file_with_tactics(content, &builtin_tactic_patterns())` →
/// `preprocess_decl_with_context` → `elaborate_decl_and_register_with_warning`.
/// The tactic patterns matter: they drive how the indentation-sensitive parser
/// groups a `·` bullet's body (`· intro h; exact h`) into a `FocusBlock`.
/// Without them the bullet mis-parses as a bare term, exercising a different
/// (non-bullet) path than `clean check` — so the harness must use them. The
/// final proof term is kernel-rechecked by `add_decl`.
fn elaborate_ok(code: &str, label: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let patterns = builtin_tactic_patterns();
    let decls = parse_file_with_tactics(code, &patterns)
        .unwrap_or_else(|e| panic!("{label}: parse failed: {e:?}"));
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        // `RegisteredElabResult` is not `Debug`; drop it to the underlying
        // `ElabError` so a failure prints a useful diagnostic.
        let result = elaborate_decl_and_register_with_warning(&mut env, &processed).map(|_| ());
        assert!(
            result.is_ok(),
            "{label}: decl {i} should elaborate and kernel-recheck, got: {result:?}"
        );
    }
    env
}

/// Parse + elaborate `code`, asserting the (single) declaration is REJECTED.
/// Crucially this must be a graceful `Err`, never a panic. Mirrors the
/// `clean check` pipeline (see [`elaborate_ok`]).
fn elaborate_err(code: &str, label: &str) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let patterns = builtin_tactic_patterns();
    let decls = parse_file_with_tactics(code, &patterns)
        .unwrap_or_else(|e| panic!("{label}: parse failed: {e:?}"));
    let mut saw_err = false;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        if elaborate_decl_and_register_with_warning(&mut env, &processed).is_err() {
            saw_err = true;
        }
    }
    assert!(
        saw_err,
        "{label}: an unprovable goal must be rejected (graceful Err), not accepted"
    );
}

#[test]
fn test_iff_constructor_seq_intro_seq_exact_no_panic() {
    // The exact panic repro. Must close (and kernel-recheck), no panic.
    let env = elaborate_ok(
        "theorem t (p : Prop) : p ↔ p := by constructor <;> intro h <;> exact h\n",
        "iff constructor <;> intro h <;> exact h",
    );
    assert!(
        env.get_const(&Name::from_string("t")).is_some(),
        "theorem t should be registered after closing the Iff goal"
    );
}

#[test]
fn test_iff_constructor_seq_paren_intro_exact_no_panic() {
    // The `<;> (intro h; exact h)` grouping — same parallel-sibling path.
    let env = elaborate_ok(
        "theorem t2 (p : Prop) : p ↔ p := by constructor <;> (intro h; exact h)\n",
        "iff constructor <;> (intro h; exact h)",
    );
    assert!(
        env.get_const(&Name::from_string("t2")).is_some(),
        "theorem t2 should be registered"
    );
}

#[test]
fn test_nested_iff_constructor_seq_intro_exact_no_panic() {
    // A compound `Iff` between conjunctions: `constructor` still yields two
    // parallel arms, and `intro h <;> exact h` closes each. Exercises the same
    // parallel-sibling FVar reset with a richer arm body.
    let env = elaborate_ok(
        "theorem t3 (a b : Prop) : (a ∧ b) ↔ (a ∧ b) := by constructor <;> intro h <;> exact h\n",
        "compound iff constructor <;> intro h <;> exact h",
    );
    assert!(
        env.get_const(&Name::from_string("t3")).is_some(),
        "theorem t3 should be registered"
    );
}

#[test]
fn test_and_constructor_seq_assumption_still_works() {
    // Control: the And case (which never regressed) must still pass.
    let env = elaborate_ok(
        "theorem c (p q : Prop) (hp : p) (hq : q) : p ∧ q := by constructor <;> assumption\n",
        "and constructor <;> assumption",
    );
    assert!(
        env.get_const(&Name::from_string("c")).is_some(),
        "control theorem c should be registered"
    );
}

#[test]
fn test_iff_distinct_props_seq_intro_exact_errors_gracefully() {
    // Negative / no-over-accept: `p ↔ q` with distinct `p`, `q` is NOT provable
    // by `intro h; exact h` (each arm needs `q` from `p` or vice versa). The
    // post-fix path must REJECT this with a graceful error — never a panic, and
    // never silently accept an unsound proof.
    elaborate_err(
        "theorem bad (p q : Prop) : p ↔ q := by constructor <;> intro h <;> exact h\n",
        "iff distinct props (unprovable) must error",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// close_fvars ID-to-binder gap panic class — three import-free idioms that each
// crashed `clean check` at close_fvars.rs (the fvar-depth invariant) yet are
// accepted by real Lean 4. Each must now (a) NOT panic and (b) close + be
// kernel-rechecked by `add_decl`. Root causes, per trigger:
//   T1  nested `have := by`: the inner `by`-block's sub-proof was closed with a
//       `fvar_base` inherited from the parent (off by the +1 that
//       `clone_with_fresh_goal_target` adds to avoid id collisions), so the
//       sub-proof's first binder FVar had no matching binder at depth 1.
//   T2  `cases <non-fvar term> with`: the temporary motive sentinel FVar
//       permanently consumed an id, pushing each branch's field FVar one id too
//       high for the minor-premise binder depth.
//   T3  double `<;>` with a per-branch `intro`: `clone_with_goal` bumped an
//       empty-context goal's `next_fvar` to `0 + 1 = 1`, defeating the
//       per-branch reset so the `intro` FVar landed at id 1 while its lambda sat
//       at binder depth 1.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_nested_have_by_block_no_panic_and_closes() {
    // T1: a `have` whose `by` body contains another `have := by`.
    let env = elaborate_ok(
        "theorem tp : True := by\n  \
             have h2 : True := by\n    \
                 have h3 : True := by trivial\n    \
                 exact h3\n  \
             trivial\n",
        "nested have := by",
    );
    assert!(
        env.get_const(&Name::from_string("tp")).is_some(),
        "theorem tp (nested have := by) should be registered after kernel recheck"
    );
}

#[test]
fn test_cases_non_fvar_term_scrutinee_no_panic_and_closes() {
    // T2: `cases <term> with` where the scrutinee is a term (`Classical.em p`),
    // not a local hypothesis.
    let env = elaborate_ok(
        "theorem tcase (p : Prop) : p ∨ ¬p := by\n  \
             cases Classical.em p with\n  \
             | inl h => exact Or.inl h\n  \
             | inr h => exact Or.inr h\n",
        "cases Classical.em p with",
    );
    assert!(
        env.get_const(&Name::from_string("tcase")).is_some(),
        "theorem tcase (cases term with) should be registered after kernel recheck"
    );
}

#[test]
fn test_double_seq_focus_with_intro_no_panic_and_closes() {
    // T3: `constructor <;> intro h <;> trivial` — a double `<;>` with a
    // binder-introducing `intro` per branch and a non-`exact` closer.
    let env = elaborate_ok(
        "theorem tseq : (True → True) ∧ (True → True) := by \
             constructor <;> intro h <;> trivial\n",
        "constructor <;> intro h <;> trivial",
    );
    assert!(
        env.get_const(&Name::from_string("tseq")).is_some(),
        "theorem tseq (double <;> with intro) should be registered after kernel recheck"
    );
}

#[test]
fn test_double_seq_focus_with_intro_unprovable_errors_gracefully() {
    // Soundness control for T3: `h : True` has no `.elim` to close the arm, so
    // this is NOT provable. Must ERROR gracefully (never panic, never accept).
    elaborate_err(
        "theorem tseq_bad : (True → True) ∧ (True → True) := by \
             constructor <;> intro h <;> exact h.elim\n",
        "double <;> with unprovable arm must error",
    );
}

#[test]
fn test_cases_wrong_prop_scrutinee_errors_gracefully() {
    // Soundness control for T2: the scrutinee decides `q` but the goal is about
    // `p` (q ≠ p), so the arms do not close the goal. Must ERROR gracefully.
    elaborate_err(
        "theorem tcase_bad (p q : Prop) : p ∨ ¬p := by \
             cases Classical.em q with | inl h => exact Or.inl h | inr h => exact Or.inr h\n",
        "cases on wrong prop must error",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Consecutive `·` focus bullets that EACH `intro`. Each `·` bullet is its own
// `FocusBlock` in the enclosing tactic sequence and focuses goal 0 (a PARALLEL
// sibling of one `constructor`/`apply`/`refine`). Before the fix, the first
// bullet's `intro` left `next_fvar` advanced, so the second bullet's `intro`
// allocated an id one too high for its binder depth; `close_fvars` could not
// convert it and `closed_proof` fell through the fail-closed floor with
// `TacticFailed(ProofNotProduced)`. The fix resets `next_fvar` to a base
// derived purely from the focused goal's own context before each bullet body
// (mirroring the per-sibling reset in `all_goals`/`<;>`), so every sibling
// bullet's `intro` allocates the SAME id. The assembled term is still
// kernel-rechecked by `add_decl`. Real Lean 4 accepts all the positive cases.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_two_intro_bullets_after_constructor_closes() {
    // The primary repro: `constructor` + two `· intro h; exact h` bullets.
    let env = elaborate_ok(
        "theorem tbul (p q : Prop) : (p → p) ∧ (q → q) := by\n  \
             constructor\n  \
             · intro h; exact h\n  \
             · intro h; exact h\n",
        "constructor + two intro bullets",
    );
    assert!(
        env.get_const(&Name::from_string("tbul")).is_some(),
        "theorem tbul (two intro bullets) should be registered after kernel recheck"
    );
}

#[test]
fn test_two_intro_bullets_after_apply_and_intro_closes() {
    // Same bug via `apply And.intro` instead of `constructor`.
    let env = elaborate_ok(
        "theorem tbulap (p q : Prop) : (p → p) ∧ (q → q) := by\n  \
             apply And.intro\n  \
             · intro h; exact h\n  \
             · intro h; exact h\n",
        "apply And.intro + two intro bullets",
    );
    assert!(
        env.get_const(&Name::from_string("tbulap")).is_some(),
        "theorem tbulap (apply + two intro bullets) should be registered"
    );
}

#[test]
fn test_three_intro_bullets_after_refine_closes() {
    // Three FLAT sibling intro bullets via `refine ⟨?_, ?_, ?_⟩`.
    let env = elaborate_ok(
        "theorem tbul3 (p q r : Prop) : (p → p) ∧ (q → q) ∧ (r → r) := by\n  \
             refine ⟨?_, ?_, ?_⟩\n  \
             · intro h; exact h\n  \
             · intro h; exact h\n  \
             · intro h; exact h\n",
        "refine + three intro bullets",
    );
    assert!(
        env.get_const(&Name::from_string("tbul3")).is_some(),
        "theorem tbul3 (three intro bullets) should be registered after kernel recheck"
    );
}

#[test]
fn test_three_intro_bullets_via_refine_seq_focus_closes() {
    // The `<;>` form of ≥3 intro bullets — the sibling-reset path in `seq_focus`.
    let env = elaborate_ok(
        "theorem tbul3s (p q r : Prop) : (p → p) ∧ (q → q) ∧ (r → r) := by \
             refine ⟨?_, ?_, ?_⟩ <;> intro h <;> exact h\n",
        "refine ⟨?_,?_,?_⟩ <;> intro h <;> exact h",
    );
    assert!(
        env.get_const(&Name::from_string("tbul3s")).is_some(),
        "theorem tbul3s (refine <;> intro <;> exact) should be registered"
    );
}

#[test]
fn test_intro_bullet_then_non_intro_bullet_closes() {
    // Ordering control (intro-bullet FIRST, non-intro bullet SECOND).
    let env = elaborate_ok(
        "theorem tmix1 (p q : Prop) (hq : q) : (p → p) ∧ q := by\n  \
             constructor\n  \
             · intro h; exact h\n  \
             · exact hq\n",
        "intro-bullet then non-intro bullet",
    );
    assert!(
        env.get_const(&Name::from_string("tmix1")).is_some(),
        "theorem tmix1 (intro then non-intro bullet) should be registered"
    );
}

#[test]
fn test_non_intro_bullet_then_intro_bullet_closes() {
    // Ordering control (non-intro bullet FIRST, intro-bullet SECOND).
    let env = elaborate_ok(
        "theorem tmix2 (p q : Prop) (hq : q) : q ∧ (p → p) := by\n  \
             constructor\n  \
             · exact hq\n  \
             · intro h; exact h\n",
        "non-intro bullet then intro-bullet",
    );
    assert!(
        env.get_const(&Name::from_string("tmix2")).is_some(),
        "theorem tmix2 (non-intro then intro bullet) should be registered"
    );
}

#[test]
fn test_single_intro_bullet_still_closes() {
    // Control: a single intro-bullet on its own must still close.
    let env = elaborate_ok(
        "theorem tsingle (p : Prop) : (p → p) := by\n  \
             · intro h; exact h\n",
        "single intro bullet",
    );
    assert!(
        env.get_const(&Name::from_string("tsingle")).is_some(),
        "theorem tsingle (single intro bullet) should be registered"
    );
}

#[test]
fn test_two_intro_bullets_second_goal_unprovable_errors_gracefully() {
    // Negative / no-over-accept: the 2nd goal is `q` but only `hp : p` is in
    // scope, so `exact hp` cannot close it. Must ERROR gracefully — never panic,
    // never accept. Real Lean 4 rejects this with a type mismatch.
    elaborate_err(
        "theorem tbad (p q : Prop) (hp : p) : (p → p) ∧ q := by\n  \
             constructor\n  \
             · intro h; exact h\n  \
             · exact hp\n",
        "two intro bullets, 2nd goal unprovable, must error",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// `;`-SEQUENCED `intro` on PARALLEL sibling goals (no `·` bullet, no `<;>`).
// `constructor`/`refine ⟨…⟩`/`apply And.intro` on an `Iff`/`And` of arrows makes
// two (or more) sibling goals at the SAME binder depth. A single flat `;`
// sequence then `intro`s into each in turn. Before the fix, `intro` allocated
// its hypothesis FVar from the MONOTONIC global `next_fvar`: the FIRST sibling's
// `intro` correctly got id `fvar_base`, but after it (plus its `exact`) advanced
// the counter, the SECOND sibling's `intro` — at the same binder depth — got a
// too-high id that `close_fvars` could not convert, so `closed_proof` fell
// through its fail-closed floor with `TacticFailed(ProofNotProduced)`. Unlike
// the `·`-bullet / `<;>` paths there is no per-sibling loop here to reset
// `next_fvar`. The fix makes `intro` allocate from the CURRENT GOAL's own
// tactic-binder base (`goal_fvar_base`) instead of the global counter, which is
// depth-correct for every sibling (each fresh sibling → base `fvar_base`) AND
// for single-goal multi-`intro`. Real Lean 4 accepts all the positive cases;
// each assembled term is still kernel-rechecked by `add_decl`. (#2533 follow-up.)
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_iff_constructor_flat_seq_two_intros_closes() {
    // Tooth 1: `constructor; intro h; exact h; intro h; exact h` on `p ↔ p`.
    let env = elaborate_ok(
        "theorem tsq1 (p : Prop) : p ↔ p := by \
             constructor; intro h; exact h; intro h; exact h\n",
        "constructor; intro h; exact h; intro h; exact h",
    );
    assert!(
        env.get_const(&Name::from_string("tsq1")).is_some(),
        "theorem tsq1 (flat ; sequenced intros after constructor) should register"
    );
}

#[test]
fn test_refine_flat_seq_two_intros_closes() {
    // Tooth 2: `refine ⟨?_, ?_⟩; intro h; exact h; intro h; exact h`.
    let env = elaborate_ok(
        "theorem tsq2 (p : Prop) : (p → p) ∧ (p → p) := by \
             refine ⟨?_, ?_⟩; intro h; exact h; intro h; exact h\n",
        "refine ⟨?_, ?_⟩; intro h; exact h; intro h; exact h",
    );
    assert!(
        env.get_const(&Name::from_string("tsq2")).is_some(),
        "theorem tsq2 (flat ; sequenced intros after refine) should register"
    );
}

#[test]
fn test_apply_and_intro_flat_seq_two_intros_closes() {
    // Tooth 3: `apply And.intro; intro h; exact h; intro h; exact h`.
    let env = elaborate_ok(
        "theorem tsq3 (p : Prop) : (p → p) ∧ (p → p) := by \
             apply And.intro; intro h; exact h; intro h; exact h\n",
        "apply And.intro; intro h; exact h; intro h; exact h",
    );
    assert!(
        env.get_const(&Name::from_string("tsq3")).is_some(),
        "theorem tsq3 (flat ; sequenced intros after apply And.intro) should register"
    );
}

#[test]
fn test_refine_three_siblings_flat_seq_three_intros_closes() {
    // Tooth 4: THREE siblings, three `;`-sequenced intros.
    let env = elaborate_ok(
        "theorem tsq4 (p : Prop) : (p → p) ∧ (p → p) ∧ (p → p) := by \
             refine ⟨?_, ?_, ?_⟩; intro h; exact h; intro h; exact h; intro h; exact h\n",
        "refine ⟨?_, ?_, ?_⟩ + three ; sequenced intros",
    );
    assert!(
        env.get_const(&Name::from_string("tsq4")).is_some(),
        "theorem tsq4 (three siblings, three ; sequenced intros) should register"
    );
}

#[test]
fn test_single_goal_flat_seq_multi_intro_still_closes() {
    // Unregressed: single-goal multi-`intro` via `;` — `intro a; intro b` must
    // still allocate `base` then `base + 1` and close.
    let env = elaborate_ok(
        "theorem tsqm (p q : Prop) : p → q → p := by intro a; intro b; exact a\n",
        "single-goal intro a; intro b; exact a",
    );
    assert!(
        env.get_const(&Name::from_string("tsqm")).is_some(),
        "theorem tsqm (single-goal ; sequenced multi-intro) should register"
    );
}

#[test]
fn test_flat_seq_sibling_second_goal_unprovable_errors_gracefully() {
    // Negative / no-over-accept: after `constructor` on `(p→p) ∧ q`, the 2nd
    // sibling goal is `q` but only `hp : p` is in scope, so `exact hp` cannot
    // close it. Must ERROR gracefully — never panic, never accept. Real Lean 4
    // rejects this with a type mismatch.
    elaborate_err(
        "theorem tsqbad (p q : Prop) (hp : p) : (p → p) ∧ q := by \
             constructor; intro h; exact h; exact hp\n",
        "flat ; sequenced siblings, 2nd goal unprovable, must error",
    );
}
