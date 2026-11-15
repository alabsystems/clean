// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! grind's preprocessing: re-normalizing what a bridge produced, never
//! re-splitting a condition the branch already decided, and normalizing the
//! HYPOTHESES rather than the target alone.
//!
//! Three measured defects, all in `grind_preprocess_with`:
//!
//! - simp ran ONCE, BEFORE the bridges, so a goal a bridge REPLACED went to
//!   the closer fan unnormalized. `xor_true`'s recorded face is the bridge
//!   output with `True ∧ ¬p` and `¬True` still standing, and handing that same
//!   goal to grind directly closes it.
//! - `try_split_ite` scanned the target for a condition with no memory of what
//!   the branch had already decided, so a `dite` the branch simp could not
//!   collapse was split on again at the next depth — nine identical
//!   `h_grind.N : P` hypotheses and `grind/max-depth` where one honest
//!   `no progress` belongs (`dite_ne_left_iff`, `Mathlib/Logic/Basic.lean`).
//! - a nested split handed its branch only the INNERMOST case hypothesis, so
//!   a goal belonging to an enclosing split was preprocessed with the wrong
//!   fact and the `ite` that fact had decided stayed standing.
//! - `simp` reads `goal.target` and nothing else, so a decided `ite` sitting
//!   in a HYPOTHESIS was never collapsed (`Function.Injective.ite`), and
//!   `try_split_ite` never even saw a condition that only a hypothesis carried
//!   (`Function.Injective.dite`, a bare `fun x₁ x₂ h => by grind`).

use crate::elaborate_decl_and_register_with_warning;
use crate::tactic::builtins::builtin_tactic_patterns;
use clean_kernel::Environment;
use clean_parser::parse_file_with_tactics;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file_with_tactics(src, &builtin_tactic_patterns())
        .unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

/// An UNPROVABLE `dite` goal must fail ONCE, not nine times on the same
/// condition.
///
/// `dif_pos`/`dif_neg` live in `Init.Core`, not the built-in prelude, so
/// `try_simp_dite` declines the collapse here exactly as the ill-typed
/// dependent rewrite declines it under a real import — either way the branch
/// simp leaves the `dite` standing and the old code re-split it to
/// `grind/max-depth`. The goal is false, so the only question the test asks is
/// HOW grind gives up.
#[test]
fn test_grind_does_not_re_split_a_condition_the_branch_already_decided() {
    let mut env = Environment::with_prelude();
    let src =
        "theorem diteLoop (P : Prop) [Decidable P] (f : P → Nat) (g : ¬P → Nat) (b : Nat) :\n\
               \x20   dite P f g = b := by\n\
               \x20 grind\n";
    let err = elab(&mut env, src).expect("an unprovable dite goal must not close");
    assert!(
        !err.contains("max-depth"),
        "grind re-split one condition to max depth instead of reporting no progress: {err}"
    );
}

/// The control the guard must not break, end to end: DISTINCT conditions
/// still nest. The goal needs BOTH splits — the outer `P` and, inside each
/// branch, the inner `Q`.
///
/// The guard's own contract — that a DECIDED condition is skipped and the
/// next one taken — is pinned exactly in
/// `grind_tests::test_split_candidate_skips_a_decided_condition_and_takes_the_next`,
/// which needs no proof state and cannot be closed by some other closer.
#[test]
fn test_grind_still_nests_splits_on_distinct_conditions() {
    let mut env = Environment::with_prelude();
    let src = "theorem twoConditions (P Q : Prop) [Decidable P] [Decidable Q] (a : Nat) :\n\
               \x20   (if P then (if Q then a else a) else a) = a := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("nested splits on DISTINCT conditions must still work: {e}");
    }
}

/// A NESTED branch keeps every case hypothesis, not only the innermost.
///
/// A split handed its branch `std::slice::from_ref(&case_name)` — one name —
/// so the second split's branch lost the FIRST split's fact, and the outer
/// `ite` that fact decided was no longer collapsible. Measured face: at depth
/// three the context held `h_grind.0 : P → False` and `h_grind.2 : Q`, the
/// inner `if Q` had collapsed and the outer `if P` had not. Lean asserts every
/// hypothesis into one E-graph, where nothing goes out of scope.
#[test]
fn test_grind_keeps_every_case_hypothesis_in_a_nested_branch() {
    let mut env = Environment::with_prelude();
    let src = "theorem nestedCases (P Q : Prop) [Decidable P] [Decidable Q]\n\
               \x20   (f : Nat → Nat) (a b : Nat) :\n\
               \x20   f (if P then (if Q then a else b) else b)\n\
               \x20     = (if P then (if Q then f a else f b) else f b) := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a nested branch must keep the enclosing split's fact: {e}");
    }
}

/// A decided `ite` in a HYPOTHESIS is collapsed. `hp : ¬P` and
/// `h : (if P then a else b) = a` give `b = a` — with the hypothesis
/// untouched, grind saw a context that already contained everything needed and
/// reported no progress.
#[test]
fn test_grind_normalizes_an_ite_sitting_in_a_hypothesis() {
    let mut env = Environment::with_prelude();
    let src = "theorem hypIte (P : Prop) [Decidable P] (a b : Nat)\n\
               \x20   (h : (if P then a else b) = a) (hp : ¬P) : b = a := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("grind must normalize a hypothesis's decided ite: {e}");
    }
}

/// A condition that ONLY a hypothesis carries is still split on — the
/// load-bearing half for `Function.Injective.dite`, which is a bare
/// `fun x₁ x₂ h => by grind` with no case hypothesis at all.
///
/// The target here holds no `ite`, so the old target-only scan found nothing
/// to split and no closer could decide the condition. Split on `P`, each
/// branch's hypothesis normalizes to `a = c` or `b = c`, and the `Q` fact for
/// that side closes the goal.
#[test]
fn test_grind_splits_on_a_condition_only_a_hypothesis_carries() {
    let mut env = Environment::with_prelude();
    let src = "axiom Qpred : Nat → Prop\n\
               theorem hypOnlyCondition (P : Prop) [Decidable P] (a b c : Nat)\n\
               \x20   (h : (if P then a else b) = c) (qa : Qpred a) (qb : Qpred b) :\n\
               \x20   Qpred c := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("grind must reach a condition carried only by a hypothesis: {e}");
    }
}

/// SOUNDNESS PIN, and it guards every widening in this package. On a NESTED
/// `ite` goal grind has been measured to report SUCCESS and hand back an
/// ill-typed proof term, caught only by the final elaborator recheck — and the
/// same shape "closes" a statement that is FALSE. Widening what reaches
/// `try_split_ite` makes that defect more reachable, not less, so the refusal
/// is pinned here rather than left to the recheck alone being noticed.
///
/// `(if P then a else (if Q then b else c)) = (if Q then b else (if P then a
/// else c))` fails at `P = Q = True` with `a ≠ b`. Whatever grind does
/// internally, the declaration must NOT be accepted.
#[test]
fn test_grind_never_accepts_a_false_nested_ite_statement() {
    let mut env = Environment::with_prelude();
    let src = "theorem falseNestedIte (P Q : Prop) [Decidable P] [Decidable Q] (a b c : Nat) :\n\
               \x20   (if P then a else (if Q then b else c))\n\
               \x20     = (if Q then b else (if P then a else c)) := by\n\
               \x20 grind\n";
    let err = elab(&mut env, src)
        .expect("a FALSE statement must never be accepted, whatever grind reports internally");
    assert!(
        !err.is_empty(),
        "the refusal must carry a diagnostic: {err}"
    );
}

/// REGRESSION. A condition an ORDINARY hypothesis decides must still be split
/// on. The re-split guard first read the WHOLE local context, so `hP : P`
/// refused the split on `P` outright — and nothing collapsed the `ite`
/// instead, because only the splitter's own `h_grind.*` case hypotheses are
/// handed to the preprocessing `simp` as rewrite rules. Measured face before
/// the scope fix: `hP : #F0 ⊢ Eq Nat (ite Nat #F0 …) #F2`, untouched.
///
/// Pinned Lean v4.30.0-rc2 closes both of these. Splitting stays bounded: the
/// positive branch gets `h_grind.N : P`, which IS a case hypothesis, so a
/// second split on the same condition is still refused, and the negative
/// branch closes by contradiction against `hP`.
#[test]
fn test_grind_splits_on_a_condition_an_ordinary_hypothesis_decides() {
    let mut env = Environment::with_prelude();
    let src = "theorem decidedByContext (P : Prop) [Decidable P] (a b : Nat) (hP : P) :\n\
               \x20   (if P then a else b) = a := by\n\
               \x20 grind\n\
               theorem decidedByContextNeg (P : Prop) [Decidable P] (a b : Nat) (hP : ¬P) :\n\
               \x20   (if P then a else b) = b := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("an ordinary hypothesis must not block the split: {e}");
    }
}

/// The same scope fix with a SECOND `ite` sitting in a hypothesis, so the
/// candidate list really has more than one entry and the target's condition is
/// still taken first.
#[test]
fn test_grind_takes_the_target_condition_first_when_a_hypothesis_carries_another() {
    let mut env = Environment::with_prelude();
    let src = "theorem twoIfs (P Q : Prop) [Decidable P] [Decidable Q] (a b c : Nat)\n\
               \x20   (h : (if P then a else b) = c) (hq : Q) : (if Q then c else a) = c := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("the target's condition must still be split on first: {e}");
    }
}

/// A hypothesis carrying a `∀`-bound `ite` does not derail the split of a
/// GROUND one beside it.
///
/// Scanning hypotheses for conditions is what made a binder-bound condition
/// reachable at all: `hbind`'s `R n` lives under its `∀ n`, so the expression
/// the scan yields carries a loose bound variable and is not a term in this
/// goal's context (measured with `CLEAN_GRIND_TRACE` on the one-hypothesis
/// version of this shape: `n=1`, `App(FVar(0), BVar(0))`). The candidate
/// filter drops exactly those; this row checks that dropping them still leaves
/// `h`'s ground `P` to split on, end to end.
///
/// Pinned Lean v4.30.0-rc2 closes this file (unused-variable warnings only).
#[test]
fn test_grind_still_splits_a_ground_condition_beside_a_binder_bound_one() {
    let mut env = Environment::with_prelude();
    let src = "axiom Qq : Nat → Prop\n\
               theorem binderCondFirst (R : Nat → Prop) [inst : ∀ n, Decidable (R n)]\n\
               \x20   (P : Prop) [Decidable P] (g k : Nat → Nat) (a b c : Nat)\n\
               \x20   (hbind : ∀ n, (if R n then g n else k n) = g n)\n\
               \x20   (h : (if P then a else b) = c) (qa : Qq a) (qb : Qq b) : Qq c := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a binder-bound candidate must not cost the ground split: {e}");
    }
}
