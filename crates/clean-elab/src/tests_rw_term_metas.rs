// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `rw [e]` with a TERM whose elaboration leaves implicit arguments open
//! (`addc fun n => q x n : q x (?a + ?b) ↔ q x (?b + ?a)`) solves them by
//! unifying the rewritten side against the goal (Lean's `kabstract`), at the
//! goal and at a hypothesis. Measured 2026-09-11: the term path searched for
//! the pattern with the metavariables as rigid locals and reported no match
//! (`exists_update_iff`, `Involutive.leftInverse_iff` in
//! `Mathlib/Logic/Function/Basic.lean`).

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

const ADDC: &str = "theorem addc {a b : Nat} (p : Nat → Prop) : p (a + b) ↔ p (b + a) := by\n\
                    \x20 rw [Nat.add_comm]\n";

#[test]
fn test_rw_term_solves_its_open_implicits_against_the_goal() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{ADDC}theorem atGoal (q : Nat → Nat → Prop) (x y : Nat) (h : q x (y + x)) : q x (x + y) := by\n\
         \x20 rw [addc fun n => q x n]\n\
         \x20 exact h\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`rw [addc fun n => q x n]` must solve `?a ?b` against the goal: {e}");
    }
}

#[test]
fn test_rw_term_solves_its_open_implicits_against_a_hypothesis() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{ADDC}theorem atHyp (q : Nat → Nat → Prop) (x y : Nat) (h : q x (x + y)) : q x (y + x) := by\n\
         \x20 rw [addc fun n => q x n] at h\n\
         \x20 exact h\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`rw [addc …] at h` must solve `?a ?b` against the hypothesis: {e}");
    }
}

#[test]
fn test_rw_term_with_no_matching_subterm_still_reports_no_match() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{ADDC}theorem noMatch (q : Nat → Nat → Prop) (x : Nat) (h : q x x) : q x x := by\n\
         \x20 rw [addc fun n => q x n]\n\
         \x20 exact h\n"
    );
    let err = elab(&mut env, &src).expect("nothing in `q x x` is a sum: rw must fail");
    assert!(
        err.contains("did not match") || err.contains("RewriteNoMatch"),
        "the failure must be the rewrite's no-match, got: {err}"
    );
}
