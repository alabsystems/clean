// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exit criterion of plan item `tactics-decide-lean-faithful`
//! (`docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md`): the registered `decide`
//! and `native_decide` follow Lean's procedure (`Lean/Elab/Tactic/Decide.lean`).
//!
//! Every verdict and message below was measured on the pinned Lean,
//! `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`, on
//! 2026-10-17 (v4.8.0 gave the same verdicts; its free-variable message reads
//! "expected type must not contain free or meta variables"):
//!
//! ```text
//! example (x : Nat) (h : x < 3) : x < 5 := by decide
//!   error: Expected type must not contain free variables
//!     x < 5
//!   Hint: Use the `+revert` option to automatically clean up and revert free variables
//! example (x : Nat) (h : x < 3) : x < 5 := by native_decide      -- the same error
//! example : ∃ n : Nat, n = 2 := ⟨_, by decide⟩
//!   error: Expected type must not contain metavariables
//!     ?m.7 = 2
//! @[irreducible] def five := 5
//! example : five = 5 := by decide
//!   error: Tactic `decide` failed for proposition
//!     five = 5
//!   because its `Decidable` instance
//!     instDecidableEqNat five 5
//!   did not reduce to `isTrue` or `isFalse`.
//! theorem five_nd : five = 5 := by native_decide                  -- accepted
//! example : (some five) = some 5 := by decide
//!   error: Tactic `decide` failed for proposition … reduction got stuck at
//!     the `Decidable` instance  match h : five.beq 5 with …
//! def o : Option (Option Int) := some (some (5 : Nat))
//! example : (o = some (some 5)) := by decide                      -- accepted
//! example (x : Nat) : 2 + 2 = 4 := by decide                      -- accepted
//! def six := 6
//! theorem six_eq : six = 6 := by decide                           -- accepted
//! theorem f225 : 2 + 2 = 5 := by decide
//!   error: Tactic `decide` proved that the proposition
//!     2 + 2 = 5
//!   is false
//! theorem f225n : 2 + 2 = 5 := by native_decide
//!   error: Tactic `native_decide` evaluated that the proposition
//!     2 + 2 = 5
//!   is false
//! theorem t224 : 2 + 2 = 4 := by decide
//! set_option pp.all true in #print t224
//!   @of_decide_eq_true (2 + 2 = 4) (instDecidableEqNat (2 + 2) 4)
//!     (@id.{0} (@Eq.{1} Bool (@Decidable.decide (2 + 2 = 4) …) Bool.true)
//!       (@Eq.refl.{1} Bool Bool.true))
//! ```
//!
//! Each test below was RED at the base of this change (origin/main
//! 482b8ab21), where the registered `decide` was the `eval_decide` ladder with
//! its SMT fallback; the controls inside them are Lean's acceptances and hold
//! on both sides.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, ExprKind, Name};
use clean_parser::parse_file;

/// A failure recorded inside a block result (`ElabResult::Failed`, possibly
/// nested in `Multiple`), which registers nothing.
fn inner_failure(result: &ElabResult) -> Option<String> {
    match result {
        ElabResult::Failed { error, .. } => Some(error.to_string()),
        ElabResult::Multiple(results) => results.iter().find_map(inner_failure),
        _ => None,
    }
}

/// Elaborate every declaration of `source` against a fresh prelude; the
/// environment on success, the first error's message otherwise.
fn elaborate_file(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .map_err(|e| e.to_string())?;
        if let Some(failure) = inner_failure(&result) {
            return Err(failure);
        }
    }
    Ok(env)
}

#[track_caller]
fn expect_accepted(source: &str) -> Environment {
    elaborate_file(source)
        .unwrap_or_else(|e| panic!("pinned Lean accepts this; Clean refused it: {e}\n{source}"))
}

#[track_caller]
fn expect_refused(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("pinned Lean refuses this; Clean accepted it:\n{source}"),
        Err(message) => message,
    }
}

#[track_caller]
fn assert_mentions(message: &str, needle: &str, source: &str) {
    assert!(
        message.contains(needle),
        "expected Lean's message `{needle}` for\n{source}\ngot: {message}"
    );
}

const FREE_VARIABLES: &str = "Expected type must not contain free variables";
const REVERT_HINT: &str = "Use the `+revert` option to automatically clean up and revert";

/// (1) A hypothesis-carrying goal is refused before anything is evaluated,
/// with Lean's message, although `h` makes it true.
#[test]
fn test_decide_free_variable_goal_refused_with_leans_message() {
    let source = "theorem t (x : Nat) (h : x < 3) : x < 5 := by decide\n";
    let message = expect_refused(source);
    assert_mentions(&message, FREE_VARIABLES, source);
    assert_mentions(&message, REVERT_HINT, source);

    let source = "theorem t (b : Bool) : b = b := by decide\n";
    assert_mentions(&expect_refused(source), FREE_VARIABLES, source);

    // Control: a variable in the context but not in the goal is no obstacle.
    expect_accepted("theorem t (x : Nat) : 2 + 2 = 4 := by decide\n");
}

/// (1) `native_decide` shares Lean's preprocessing and its message.
#[test]
fn test_native_decide_free_variable_goal_refused_with_leans_message() {
    let source = "theorem t (x : Nat) (h : x < 3) : x < 5 := by native_decide\n";
    let message = expect_refused(source);
    assert_mentions(&message, FREE_VARIABLES, source);
    assert_mentions(&message, REVERT_HINT, source);

    // Control: the closed goal of the routing test still closes.
    expect_accepted("theorem t : ¬((3 : Nat) = 4) := by native_decide\n");
}

/// (1) A goal that still mentions a metavariable when `decide` runs is
/// refused, as Lean refuses `⟨_, by decide⟩`.
#[test]
fn test_decide_metavariable_goal_refused_with_leans_message() {
    let source = "theorem t : ∃ n : Nat, n = 2 := ⟨_, by decide⟩\n";
    assert_mentions(
        &expect_refused(source),
        "Expected type must not contain metavariables",
        source,
    );
}

/// (2) `decide` reduces at default transparency, so an `@[irreducible]` head
/// stays folded and the instance is stuck. `native_decide` evaluates through
/// it, as pinned Lean's compiled evaluation does.
#[test]
fn test_decide_irreducible_head_refused_at_default_transparency() {
    let irreducible = "@[irreducible] def five : Nat := 5\n";
    let source = format!("{irreducible}theorem t : five = 5 := by decide\n");
    let message = expect_refused(&source);
    assert_mentions(&message, "Tactic `decide` failed for proposition", &source);
    assert_mentions(&message, "did not reduce to `isTrue` or `isFalse`", &source);

    // Inside a derived `DecidableEq` (pinned Lean: `some five = some 5` is
    // stuck in `Option.instDecidableEq`, "did not reduce to `isTrue` or
    // `isFalse`"). Clean's built-in prelude has no `Option` instance; its
    // stand-in reduces both sides to constructor values, `five` stays folded,
    // and the stand-in is stuck as Lean's instance is.
    let source = format!("{irreducible}theorem t : (some five) = some 5 := by decide\n");
    assert_mentions(
        &expect_refused(&source),
        "did not reduce to `isTrue` or `isFalse`",
        &source,
    );

    // Controls: a semireducible head unfolds, and the stand-in accepts what
    // `Option.instDecidableEq` decides in pinned Lean.
    expect_accepted("def six : Nat := 6\ntheorem t : six = 6 := by decide\n");
    expect_accepted(
        "def o : Option (Option Int) := some (some (5 : Nat))\n\
         theorem t : (o = some (some 5)) := by decide\n",
    );

    // KNOWN GAP, pinned so it fails loudly the day it closes: pinned Lean
    // ACCEPTS `five = 5 := by native_decide` (compiled code ignores
    // reducibility and the result is asserted by an auxiliary axiom). Clean's
    // `native_decide` adds no axiom (DECISIONS R109), so its proof needs
    // `five` unfolded, which the elaboration boundary's default-transparency
    // re-check (B14) refuses. When this starts passing, assert Lean's verdict.
    let source = format!("{irreducible}theorem t : five = 5 := by native_decide\n");
    let message = expect_refused(&source);
    // The boundary re-check (`verify_tactic_proof`) is the refusal; any other
    // error means the cause moved and this pin no longer describes it.
    assert_mentions(&message, "Proof type mismatch", &source);
}

/// The application spine of `expr` after stripping metadata: head and args.
fn spine(expr: &Expr) -> (Expr, Vec<Expr>) {
    let expr = expr.strip_mdata();
    let args = expr.get_app_args().into_iter().cloned().collect();
    (expr.get_app_fn().clone(), args)
}

fn is_const(expr: &Expr, name: &str) -> bool {
    matches!(expr.strip_mdata().kind(), ExprKind::Const(n, _) if n == &Name::from_string(name))
}

/// (3) The proof is Lean's `of_decide_eq_true (Eq.refl true)` behind the
/// expected-type hint, so the kernel recomputes the decision.
#[test]
fn test_decide_proof_is_of_decide_eq_true_of_eq_refl() {
    let env = expect_accepted("theorem t224 : 2 + 2 = 4 := by decide\n");
    let value = env
        .get_const(&Name::from_string("t224"))
        .and_then(|info| info.value.clone())
        .expect("t224 is registered with a proof term");
    let (head, args) = spine(&value);
    assert!(
        is_const(&head, "of_decide_eq_true") && args.len() == 3,
        "the proof must be `@of_decide_eq_true p s h`, got {value}"
    );
    let (hint, hint_args) = spine(&args[2]);
    assert!(
        is_const(&hint, "id") && hint_args.len() == 2,
        "the third argument must be the expected-type hint `@id (decide p = true) _`, got {}",
        args[2]
    );
    let (refl, refl_args) = spine(&hint_args[1]);
    assert!(
        is_const(&refl, "Eq.refl")
            && refl_args.len() == 2
            && is_const(&refl_args[0], "Bool")
            && is_const(&refl_args[1], "Bool.true"),
        "the hinted proof must be `@Eq.refl Bool Bool.true`, got {}",
        hint_args[1]
    );
}

/// Lean's refusals of a false closed goal, for both tactics.
#[test]
fn test_false_goal_refused_with_leans_messages() {
    let source = "theorem f : 2 + 2 = 5 := by decide\n";
    let message = expect_refused(source);
    assert_mentions(
        &message,
        "Tactic `decide` proved that the proposition\n  ",
        source,
    );
    assert_mentions(&message, "\nis false", source);

    let source = "theorem f : 2 + 2 = 5 := by native_decide\n";
    let message = expect_refused(source);
    assert_mentions(
        &message,
        "Tactic `native_decide` evaluated that the proposition\n  ",
        source,
    );
    assert_mentions(&message, "\nis false", source);
}
