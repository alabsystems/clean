// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A `by` block in an ARGUMENT slot must run its script whatever the
//! application's HEAD looks like.
//!
//! `surface_to_syntax` maps a tactic block to an empty opaque node
//! (`macro_integration/to_syntax.rs`), so every expression that reaches
//! `expand_macros` comes back with its scripts deleted. The elaborator
//! compensates with bypasses that route straight to `elab_app`, but the
//! argument-side bypass was keyed on the HEAD being an `Ident`/`Proj`. So
//! `@f (by …)`, `(f a) (by …)`, `f a <| by …` and `f.{u} (by …)` all fell
//! through to the roundtrip and ran ZERO tactics, reported as `unsolved
//! goals` on a correctly instantiated goal — the Mathlib rows
//! `Logic/Unique.lean` `Option` / `heq_const_of_unique` and
//! `Order/Basic.lean` `associative_of_commutative_of_le` /
//! `le_of_forall_gt_imp_ge_of_dense`. Ground-truthed on the pinned
//! v4.30.0-rc2 `lean` binary, which accepts every fixture below: Lean has no
//! lossy roundtrip — a `by` block becomes a synthetic metavariable whose
//! script `synthesizeSyntheticMVars` runs later, independently of the head.
//!
//! The guard beside the fix is the other half: a dropped script and a failed
//! script used to produce identical diagnostics (`by sorry`, `by skip` and
//! `by unknown_tactic_xyz` all read `unsolved goals` in the broken shape), so
//! `elab_by_tactic` now refuses an empty script outright.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

/// Opaque propositions and two functions over them: enough to put a `by`
/// block in an argument slot under every head shape without a single import.
const BASE: &str = "axiom P : Prop\n\
                    axiom Q : Prop\n\
                    axiom g1 : P → Q\n\
                    axiom f2 : P → P → Q\n";

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

#[test]
fn test_by_block_argument_runs_under_an_explicit_at_head() {
    let mut env = Environment::with_prelude();
    let src = format!("{BASE}theorem atHead (h : P) : Q := @g1 (by exact h)\n");
    if let Some(e) = elab(&mut env, &src) {
        panic!("`@g1 (by exact h)` must run its tactic script: {e}");
    }
}

#[test]
fn test_by_block_argument_runs_under_a_parenthesised_application_head() {
    let mut env = Environment::with_prelude();
    let src = format!("{BASE}theorem parenHead (h : P) (k : P) : Q := (f2 h) (by exact k)\n");
    if let Some(e) = elab(&mut env, &src) {
        panic!("`(f2 h) (by exact k)` must run its tactic script: {e}");
    }
}

#[test]
fn test_by_block_argument_runs_under_an_application_head() {
    let mut env = Environment::with_prelude();
    // `f2 h <| by exact k` desugars to `App(App(f2, [h]), [by exact k])`:
    // the head is itself an application and carries no block of its own.
    let src = format!("{BASE}theorem appHead (h : P) (k : P) : Q := f2 h <| by exact k\n");
    if let Some(e) = elab(&mut env, &src) {
        panic!("`f2 h <| by exact k` must run its tactic script: {e}");
    }
}

#[test]
fn test_anonymous_hypothesis_argument_runs_under_an_explicit_at_head() {
    let mut env = Environment::with_prelude();
    // `‹_›` is `(by assumption : _)` — the same path, and the shape the
    // `Logic/Unique.lean` `Option` row is written in.
    let src = format!("{BASE}theorem atAnon (h : P) : Q := @g1 ‹_›\n");
    if let Some(e) = elab(&mut env, &src) {
        panic!("`@g1 ‹_›` must run `assumption`: {e}");
    }
}

#[test]
fn test_by_block_argument_still_runs_under_an_identifier_head() {
    let mut env = Environment::with_prelude();
    // The controls that were already green: they must stay byte-for-byte green.
    let src = format!(
        "{BASE}theorem identHead (h : P) : Q := g1 (by exact h)\n\
         theorem identAnon (h : P) : Q := g1 ‹_›\n\
         theorem twoBlocks (h : P) (k : P) : Q := f2 (by exact h) (by exact k)\n\
         theorem pipeIdent (h : P) : Q := g1 <| by exact h\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("the identifier-head controls must stay green: {e}");
    }
}

#[test]
fn test_dropped_tactic_script_is_refused_rather_than_reported_as_unsolved() {
    // The fail-closed half. A script that RAN and failed must still name its
    // own failure; only a script that was never offered is an invariant
    // violation. `by unknownTacticXyz` under a widened head is the proof that
    // the script reached the tactic engine at all.
    let mut env = Environment::with_prelude();
    let src = format!("{BASE}theorem ranAndFailed (h : P) : Q := @g1 (by unknownTacticXyz)\n");
    let err = elab(&mut env, &src).expect("an unknown tactic must fail the declaration");
    assert!(
        !err.contains("empty tactic script"),
        "the script must reach the tactic engine, not be dropped: {err}"
    );
    assert!(
        err.contains("unknownTacticXyz") || err.to_lowercase().contains("unknown tactic"),
        "the failure must name the tactic that ran, not `unsolved goals`: {err}"
    );
}

/// The head shape the module doc names but no test reached: `f.{u} (by …)`
/// parses as `App(UniverseInst(Ident f, levels), args)`, and `@f.{u} (by …)`
/// as `App(UniverseInst(Explicit(Ident f), levels), args)`.
#[test]
fn test_by_block_argument_runs_under_a_universe_instance_head() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{BASE}axiom app2.{{u}} : {{α : Sort u}} → α → P → Q\n\
         theorem uHead (h : P) (n : Nat) : Q := app2.{{1}} n (by exact h)\n\
         theorem uAtHead (h : P) (n : Nat) : Q := @app2.{{1}} Nat n (by exact h)\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("a `by` block under a universe-instance head must run: {e}");
    }
}
