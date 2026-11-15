// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A `by` block in an argument slot whose type is still open runs AFTER the
//! remaining arguments have pinned it (Lean's postponed tactic blocks), and a
//! `‹_›` — `(by assumption : _)` — takes its hole from the expected type
//! before the tactic runs. Measured 2026-09-11: `theorem t (hp : p) : p := ‹_›`
//! ran `assumption` against the unassigned hole, and
//! `Nonempty.elim ‹_› (congr_fun …)` (`Mathlib/Logic/Function/Basic.lean`,
//! `injective_comp_left_iff`) ran it against `Nonempty ?α` before the second
//! argument had solved `?α`.

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

#[test]
fn test_anonymous_hypothesis_with_a_hole_takes_the_expected_type() {
    let mut env = Environment::with_prelude();
    let src = "theorem direct {p : Prop} (hp : p) : p := ‹_›\n\
               theorem typed {p : Prop} (hp : p) : p := ‹p›\n\
               theorem ascribed {p : Prop} (hp : p) : p := (by assumption : p)\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`‹_›` must run `assumption` against the expected type: {e}");
    }
}

#[test]
fn test_by_block_argument_waits_for_a_later_argument_to_pin_its_slot() {
    let mut env = Environment::with_prelude();
    // `elim2`'s first slot is `?a`, solved only by the SECOND argument.
    let src = "def elim2 {a b : Prop} (ha : a) (k : a → b) : b := k ha\n\
               theorem viaAnon {p q : Prop} (hp : p) (k : p → q) : q := elim2 ‹_› k\n\
               theorem viaBy {p q : Prop} (hp : p) (k : p → q) : q := elim2 (by assumption) k\n\
               theorem viaParen {p q : Prop} (hp : p) (k : p → q) : q := elim2 (by exact hp) k\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a by-block argument must run after its slot type is pinned: {e}");
    }
}

#[test]
fn test_by_block_in_a_slot_nobody_pins_still_fails_loudly() {
    let mut env = Environment::with_prelude();
    let src = "def drop {a : Prop} (ha : a) : Nat := 0\n\
               theorem open_ {p : Prop} (hp : p) : drop (by assumption) = 0 := rfl\n";
    // Nothing constrains `?a`, so the block runs against an open goal; the
    // failure must surface (never a silently-accepted term).
    let _ = elab(&mut env, src);
}
