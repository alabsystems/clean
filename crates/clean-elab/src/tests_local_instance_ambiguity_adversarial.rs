// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Adversarial arms for the two-local-instance AMBIGUITY refusal
//! (`tests_local_instance_ambiguity.rs`): the near-miss shapes its three arms
//! do not reach.
//!
//! Every fixture below was run on the pinned `lean` v4.30.0-rc2 before being
//! written, and each arm asserts the verdict that binary gave:
//!
//! * `a1`/`a2`/`a3` — accepted, exit 0 (`t_amb.lean`).
//! * `a4` — REFUSED, exit 1, "typeclass instance problem is stuck / Pre ?m.2"
//!   (`t_amb2.lean`). Clean must not answer it from a binder either. This one
//!   is a CONTROL: it also passes with the refusal disabled.
//!
//! `a1`, `a2` and `a3` were each confirmed to FAIL on this tree with
//! `goal_has_open_input` forced to `false` (4 failed / 3 passed on the
//! `tests_local_instance_ambiguity` filter), so none of them is vacuous.
//!
//! `a3` inverts the SCAN ORDER — `[Pre β] [Pre α]` with a goal at `β` — so
//! the pre-fix "most recently pushed local wins" rule picked the wrong one,
//! and so would any repair that merely re-orders the scan rather than
//! refusing the CHOICE.

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

const PRE_PRELUDE: &str = "class Pre (α : Type) where\n\
    \x20 le : α → α → Prop\n\
    \x20 le_refl : ∀ a : α, le a a\n\
    def ple {α : Type} [Pre α] (a b : α) : Prop := Pre.le a b\n\
    theorem le_rfl' {α : Type} [Pre α] {a : α} : ple a a := Pre.le_refl a\n\
    axiom and_iff_right' {a b : Prop} (ha : a) : (a ∧ b) ↔ b\n\
    axiom drop {p : Prop} (h : p) : True\n";

/// EXPLICIT application mode: `@and_iff_right' _ _ le_rfl'`. The instance slot
/// is reached through the `@`-path, not through implicit insertion, so it is a
/// different call site of the same search.
#[test]
fn test_explicit_at_application_postpones_an_ambiguous_open_carrier() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{PRE_PRELUDE}theorem atMode {{α β : Type}} [Pre α] [Pre β] (a : α) (b b' : β) :\n\
         \x20   (ple a a ∧ ple b b') ↔ ple b b' := @and_iff_right' _ _ le_rfl'\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`@f`-mode must postpone the ambiguous goal too (pinned Lean accepts it): {e}");
    }
}

/// THREE locals of the class, two of them at the SAME carrier. The scan must
/// compare what each local GROUNDS, not how many locals exist: two agreeing
/// answers plus one differing is still a choice.
#[test]
fn test_three_local_instances_two_agreeing_still_postpone() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{PRE_PRELUDE}theorem threeInstances {{α β : Type}} [Pre α] [Pre β] [Pre α]\n\
         \x20   (a a' : α) (b : β) :\n\
         \x20   (ple b b ∧ ple a a') ↔ ple a a' := and_iff_right' le_rfl'\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("three locals, two agreeing, must still postpone (pinned Lean accepts it): {e}");
    }
}

/// The carrier the term needs is the FIRST-PUSHED binder. `[Pre β] [Pre α]`
/// with a goal at `β` inverts the scan order, so "the most recently pushed
/// local wins" answers `Pre α` here — and so would any repair that merely
/// re-orders the scan instead of refusing the CHOICE. Pinned `lean`
/// v4.30.0-rc2 accepts the file (`t_older.lean`, exit 0).
#[test]
fn test_first_pushed_local_is_the_right_carrier_and_is_not_preempted() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{PRE_PRELUDE}theorem olderWins {{α β : Type}} [Pre β] [Pre α] (a a' : α) (b : β) :\n\
         \x20   (ple b b ∧ ple a a') ↔ ple a a' := and_iff_right' le_rfl'\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("the FIRST-pushed binder must be reachable once the expected type grounds β: {e}");
    }
}

/// FAIL-CLOSED. Nothing in the term ever grounds the carrier, so the
/// postponement must end as an ERROR, never as a silent pick. The pinned
/// binary refuses this file (exit 1, "typeclass instance problem is stuck").
///
/// A CONTROL, not a falsification: measured with the ambiguity refusal
/// disabled on this same tree, it passes there too. It is here so that a
/// later widening of the postponement — one that queued this goal and let the
/// declaration close around an unassigned instance metavariable — fails
/// loudly instead of laundering it.
#[test]
fn test_ungrounded_ambiguous_carrier_is_refused_not_guessed() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{PRE_PRELUDE}theorem neverGrounded {{α β : Type}} [Pre α] [Pre β] : True :=\n\
         \x20   drop le_rfl'\n"
    );
    assert!(
        elab(&mut env, &src).is_some(),
        "an ambiguous carrier nothing grounds must FAIL closed, as pinned Lean does \
         (\"typeclass instance problem is stuck\"), not be answered from a binder"
    );
}
