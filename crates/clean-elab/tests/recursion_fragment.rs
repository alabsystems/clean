// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural recursion: which parameter it descends on, and whether the
//! recursor it lowers to computes the whole definition. Every value below was
//! evaluated by Lean 4.8.0 (`reports/2026-09-26-recursion-fragment/probes/`).
//!
//! * LOST DEFINITIONS. The decreasing parameter was chosen by spelling
//!   (`detect::find_decreasing_arg`: the first position where every call
//!   passes a variable spelled unlike the parameter). `match c, b with | a+1,
//!   b+1 => b + f 4 c a | _, _ => 109` passes `c` at `b`'s position, so `b`
//!   was chosen, no call passes a child of `b`, and the definition was
//!   refused as recursion outside the fragment although Lean 4.8.0 recurses on
//!   `c`. Base 3f45fb7c6 accepted it only because `c` happened to be the
//!   first column; the same definition with the columns swapped was refused
//!   there too. The equation normalizer had the same blind spot: once `none`
//!   became a real constructor test (b09d8c775), the first structural column
//!   was the non-recursive `Option` one. The position is now read off the
//!   rows (`structural::classify_descent`).
//! * CONTEXT AROUND THE RECURSOR. The recursor is placed at the `match` on the
//!   decreasing argument, so an induction hypothesis is the value of that
//!   match, not of the definition. `1 + match n with | 0 => 0 | m+1 => f m`
//!   proved `f 2 = 1` (Lean: 3) on base, e3f696689 and db37ea99b alike, and a
//!   case split on a parameter the call changes was skipped at every level
//!   (`c 1 2 = 201`, Lean: 105). The context is now moved into the match's
//!   arms (`structural::hoist_recursive_match`), so these compute Lean's
//!   value; a context that rewrite cannot move is refused (`recursion_site`).
//! * FIXED CONTEXTS. A `let` or case split that depends only on parameters
//!   every recursive call passes back unchanged is the same at every level,
//!   and stays admitted — including a `let` the match reads, which the S1
//!   check used to refuse.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn register(env: &mut Environment, source: &str) -> Result<(), String> {
    fn failures(result: &ElabResult) -> Result<(), String> {
        match result {
            ElabResult::Multiple(results) => {
                for result in results {
                    failures(result)?;
                }
                Ok(())
            }
            ElabResult::Failed { name, error, .. } => Err(format!("{name}: {error}")),
            _ => Ok(()),
        }
    }
    let mut context = FileContext::new();
    for decl in parse_file(source).map_err(|error| format!("parse error: {error}"))? {
        let processed = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register(env, &processed)
            .map_err(|error| format!("elaborate/kernel-check error: {error}"))?;
        failures(&result)?;
    }
    Ok(())
}

/// `call = expected` must register axiom-free; `call = wrong` must be refused.
fn computation(env: &mut Environment, tag: &str, call: &str, expected: u64, wrong: u64) {
    assert_ne!(
        expected, wrong,
        "{tag}: a check needs a genuinely wrong value"
    );
    let good = format!("correct_{tag}");
    register(env, &format!("theorem {good} : {call} = {expected} := rfl"))
        .unwrap_or_else(|error| panic!("{call} = {expected} must hold: {error}"));
    let deps = env
        .axiom_deps(&Name::from_string(&good))
        .expect("registered theorem");
    assert!(
        deps.is_empty(),
        "{call}: computation depends on axioms: {deps:?}"
    );
    let bad = format!("incorrect_{tag}");
    let error = register(env, &format!("theorem {bad} : {call} = {wrong} := rfl"))
        .expect_err(&format!("FALSE theorem accepted: {call} = {wrong}"));
    assert!(
        !error.contains("parse error"),
        "negative must parse: {error}"
    );
    assert!(
        env.get_const(&Name::from_string(&bad)).is_none(),
        "false theorem registered: {call} = {wrong}"
    );
}

fn admitted(source: &str, cases: &[(&str, u64, u64)]) {
    let mut env = Environment::with_prelude();
    register(&mut env, source).unwrap_or_else(|error| panic!("must elaborate:\n{source}\n{error}"));
    for (id, (call, expected, wrong)) in cases.iter().enumerate() {
        computation(&mut env, &format!("c{id}"), call, *expected, *wrong);
    }
}

/// The definition must be refused with `needle` in the error, register
/// nothing, and leave no way to state the false value.
fn refused(name: &str, source: &str, needle: &str, false_claim: &str) {
    let mut env = Environment::with_prelude();
    let error = register(&mut env, source).expect_err(&format!("must be refused:\n{source}"));
    assert!(
        error.contains(needle),
        "{name}: refused for the wrong reason (want `{needle}`): {error}"
    );
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "{name} was registered although refused"
    );
    assert!(
        register(&mut env, &format!("theorem bad : {false_claim} := rfl")).is_err(),
        "{false_claim} accepted"
    );
}

#[test]
fn recursion_on_a_column_the_spelling_heuristic_did_not_pick() {
    // `c` at `b`'s position is spelled unlike `b`; the recursion is on `c`.
    admitted(
        "def f (a : Nat) (b : Nat) (c : Nat) : Nat :=\n  match c, b with\n  | a+1, b+1 => b + f 4 c a\n  | _, _ => 109",
        &[("f 3 2 2", 111, 109), ("f 1 2 4", 116, 115)],
    );
    // The same definition with the columns swapped: base 3f45fb7c6 refused it.
    admitted(
        "def f (a : Nat) (b : Nat) (c : Nat) : Nat :=\n  match b, c with\n  | b+1, a+1 => b + f 4 c a\n  | _, _ => 109",
        &[("f 3 2 2", 111, 109), ("f 1 2 4", 116, 115)],
    );
    admitted(
        "def f (a : Nat) (b : Nat) (c : Nat) : Nat :=\n  match b, c, a with\n  | x+1, g, 0 => x + f b x c\n  | _, _, _ => 101",
        &[("f 0 3 1", 103, 104), ("f 1 3 1", 101, 103)],
    );
}

#[test]
fn a_constructor_test_on_a_non_recursive_column_is_not_the_recursion() {
    // `none` is a constructor test on `c : Option Nat`; the recursion is on
    // `b`, which every call passes the predecessor of.
    admitted(
        "def k (a : Nat) (b : Nat) (c : Option Nat) : Nat :=\n  match c, b with\n  | none, z+1 => a + k z z (some 2)\n  | _, _ => 105",
        &[("k 1 4 none", 106, 112), ("k 1 4 (some 0)", 105, 106), ("k 0 0 none", 105, 106)],
    );
    // Equation form: the list column recurses, the `Option` column does not.
    admitted(
        "def q (c : Nat) : Option Nat → List Nat → Nat\n  | _, 3 :: z => c + q c none z\n  | none, [] => 7\n  | _, _ => 105",
        &[("q 1 (some 0) [3, 3]", 9, 10), ("q 1 none [3]", 8, 9), ("q 1 none [4]", 105, 7)],
    );
}

#[test]
fn an_explicit_structural_parameter_is_the_outermost_dispatch() {
    // Clean-only `termination_by structural b`: the rotation used to follow
    // the spelling heuristic, left `b` inside the case split on `c`, and the
    // recursion kept `c = none` at every level (`k 1 4 none = 112`). The value
    // is Lean 4.8.0's for the same definition without the clause.
    admitted(
        "def k (a : Nat) (b : Nat) (c : Option Nat) : Nat :=\n  match c, b with\n  | none, z+1 => a + k z z (some 2)\n  | _, _ => 105\ntermination_by structural b",
        &[("k 1 4 none", 106, 112)],
    );
}

#[test]
fn a_context_around_the_recursive_match_computes_leans_value() {
    // Each proved the false value on base, e3f696689 and db37ea99b; the
    // context is now moved into the match's arms (`hoist_recursive_match`).
    admitted(
        "def f (n : Nat) : Nat :=\n  1 + match n with\n  | 0 => 0\n  | Nat.succ m => f m",
        &[("f 2", 3, 1), ("f 0", 1, 0)],
    );
    admitted(
        "def g (k n : Nat) : Nat :=\n  let z := k + 1\n  z + match n with\n  | 0 => 0\n  | Nat.succ m => g k m",
        &[("g 1 2", 6, 2), ("g 0 0", 1, 0)],
    );
    admitted(
        "def h (n : Nat) : Nat :=\n  (fun t => t * 2) (match n with\n  | 0 => 1\n  | Nat.succ m => h m)",
        &[("h 2", 8, 2), ("h 0", 2, 1)],
    );
    admitted(
        "def l (xs : List Nat) : Nat :=\n  2 * match xs with\n  | [] => 1\n  | _ :: t => l t",
        &[("l [1, 2]", 8, 2), ("l []", 2, 1)],
    );
}

#[test]
fn a_case_split_on_a_changing_parameter_around_the_recursive_match_computes_leans_value() {
    // The recursion skipped the case split on `a`, which the call changes to
    // `0`, at every level below the first (`c 1 2 = 201` was provable).
    admitted(
        "def c (a b : Nat) : Nat :=\n  match a with\n  | 0 => 5\n  | Nat.succ _ => match b with\n    | 0 => 1\n    | Nat.succ y => c 0 y + 100",
        &[("c 1 2", 105, 201), ("c 0 2", 5, 1)],
    );
    admitted(
        "def d (a b : Nat) : Nat :=\n  if a = 0 then 5 else\n    match b with\n    | 0 => 1\n    | Nat.succ y => d 0 y + 100",
        &[("d 1 2", 105, 201), ("d 3 0", 1, 5)],
    );
}

#[test]
fn a_context_that_is_definitionally_the_identity_is_admitted() {
    // `Id.run (pure x)` is `x`: the kernel shows it, so the recursor IS the
    // definition although the rewrite cannot reach inside the `do` block.
    admitted(
        "def fe (n : Nat) : Nat := Id.run (do pure (match n with | 0 => 0 | m+1 => fe m + 1))",
        &[("fe 3", 3, 4), ("fe 0", 0, 1)],
    );
}

#[test]
fn a_context_the_rewrite_cannot_move_is_refused_by_the_site_check() {
    // Inside a `do` block the match is out of the rewrite's reach; db37ea99b
    // proved `fd 2 = 1` (Lean 4.8.0: 3). The recursion-site check refuses it.
    refused(
        "fd",
        "def fd (n : Nat) : Nat := Id.run (do pure (1 + match n with | 0 => 0 | m+1 => fd m))",
        "not the value of the whole definition",
        "fd 2 = 1",
    );
}

#[test]
fn contexts_that_every_recursive_call_leaves_unchanged_are_admitted() {
    // A `let` the match reads, over a parameter every call passes unchanged.
    admitted(
        "def g (k n : Nat) : Nat :=\n  let z := k + 1\n  match n with\n  | 0 => z\n  | Nat.succ m => g k m + z",
        &[("g 1 3", 8, 9), ("g 0 0", 1, 2)],
    );
    // A case split on such a parameter.
    admitted(
        "def g (k n : Nat) : Nat :=\n  if k = 0 then 7 else\n  match n with\n  | 0 => 1\n  | Nat.succ m => g k m + 2",
        &[("g 1 3", 7, 9), ("g 0 3", 7, 1)],
    );
    // `cond` (a beta-redex over `Bool.rec`) on such a parameter.
    admitted(
        "def g (k : Bool) (n : Nat) : Nat :=\n  cond k (match n with\n  | 0 => 1\n  | Nat.succ m => g k m * 2) 0",
        &[("g true 3", 8, 2), ("g false 3", 0, 8)],
    );
}
