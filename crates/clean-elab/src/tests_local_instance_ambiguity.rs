// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! With TWO local instances of one class in scope, an instance goal whose
//! carrier is still a metavariable must be POSTPONED, not answered from the
//! most recently pushed binder.
//!
//! Lean's `SynthInstance` (`Lean/Meta/SynthInstance.lean:874-894`) runs under
//! `withNewMCtxDepth` with `isDefEqStuckEx := true`: the goal's metavariables
//! belong to the outer depth and no candidate — local or global — may assign
//! them, so the match is stuck, `trySynthInstance` returns `.undef`, and the
//! instance metavariable is postponed
//! (`Lean/Elab/Term/TermElabM.lean:1195-1237`) until
//! `Lean/Elab/App.lean:496-502` has unified the application's type with the
//! expected type.
//!
//! Clean's local loop ran most-recent-first and committed the first match,
//! assigning the goal's own carrier metavariable on the way. In
//! `Mathlib/Order/Basic.lean` every failing statement carries two order
//! instances (`[Preorder α] [Preorder β]`, `[LinearOrder α] [LinearOrder β]`)
//! and `le_rfl`'s `[Preorder ?α]` took the wrong one — "Type mismatch: …
//! fvar mismatch: fvar#3 vs fvar#2" (`le_imp_le_iff_lt_imp_lt`,
//! `lt_iff_lt_of_le_iff_le'`, `lt_iff_lt_of_le_iff_le`,
//! `Prod.mk_le_mk_iff_right`).
//!
//! The refusal is keyed on AMBIGUITY — two locals grounding the goal
//! DIFFERENTLY — and not on "the match assigned a metavariable", because a
//! single matching local is the laundering repair the unguarded loop exists
//! for (`instance.rs`'s `resolve_instance` header).
//!
//! Both fixtures below are accepted by the pinned `lean` v4.30.0-rc2.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

/// `Preorder` / `le_rfl` / `and_iff_right`, prelude-only.
const PRE_PRELUDE: &str = "class Pre (α : Type) where\n\
    \x20 le : α → α → Prop\n\
    \x20 le_refl : ∀ a : α, le a a\n\
    def ple {α : Type} [Pre α] (a b : α) : Prop := Pre.le a b\n\
    theorem le_rfl' {α : Type} [Pre α] {a : α} : ple a a := Pre.le_refl a\n\
    axiom and_iff_right' {a b : Prop} (ha : a) : (a ∧ b) ↔ b\n";

/// The row: two `Pre` binders in scope, and `le_rfl'`'s carrier is fixed only
/// by the expected type the enclosing application has not met yet.
#[test]
fn test_two_local_instances_postpone_an_open_carrier_goal() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{PRE_PRELUDE}theorem twoInstances {{α β : Type}} [Pre α] [Pre β] (a : α) (b b' : β) :\n\
         \x20   (ple a a ∧ ple b b') ↔ ple b b' := and_iff_right' le_rfl'\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!(
            "an open-carrier goal must be postponed, not answered from the most recent local: {e}"
        );
    }
}

/// The control that passed all along: ONE local of the class is evidence, not
/// a choice, so it must still match directly — the laundering repair.
#[test]
fn test_one_local_instance_still_answers_an_open_carrier_goal() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{PRE_PRELUDE}theorem oneInstance {{α : Type}} [Pre α] (a a' : α) :\n\
         \x20   (ple a a ∧ ple a a') ↔ ple a a' := and_iff_right' le_rfl'\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("a single local instance must still answer an open-carrier goal: {e}");
    }
}

/// A GROUND goal is not a choice even with two locals of the class in scope:
/// the first match still wins, with no second scan and no postponement.
#[test]
fn test_ground_goal_still_matches_the_most_recent_local() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{PRE_PRELUDE}theorem groundGoal {{α β : Type}} [Pre α] [Pre β] (a : α) (b : β) :\n\
         \x20   ple b b := le_rfl'\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("a ground goal must still resolve from the locals: {e}");
    }
}
