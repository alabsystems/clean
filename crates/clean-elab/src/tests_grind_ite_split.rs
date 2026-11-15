// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `grind` splits on the CONDITION of an `ite`/`dite` (argument 1 of the
//! five-argument spine, Lean's `e.getArg! 1`) and each branch rewrites with
//! its case hypothesis. It used to read argument 0 — the result type — so
//! `by_cases` refused and grind never split (`apply_ite_left` and its
//! siblings in `Mathlib/Logic/Basic.lean`, measured 2026-09-12). Fixtures
//! ground-truthed on the pinned v4.30.0-rc2 binary.

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
fn test_grind_splits_an_ite_on_its_condition() {
    let mut env = Environment::with_prelude();
    let src = "theorem sameBranches (P : Prop) [Decidable P] (a : Nat) : (if P then a else a) = a := by grind\n\
               theorem pushInto (P : Prop) [Decidable P] (f : Nat → Nat → Nat) (x y z : Nat) :\n\
               \x20   f (if P then x else y) z = if P then f x z else f y z := by grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("grind must split on the ite condition: {e}");
    }
}
