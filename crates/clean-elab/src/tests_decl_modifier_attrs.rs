// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An attribute written before a declaration modifier reaches the
//! declaration: `@[simp] private theorem` registers a simp lemma, as in Lean
//! (whose `declModifiers` put attributes before visibility). Measured
//! 2026-09-12: the parser dropped every attribute in front of `private`,
//! `protected`, `noncomputable`, `unsafe`, `partial`, `local`, `scoped`.

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
fn test_simp_attribute_before_a_visibility_modifier_registers_the_lemma() {
    let mut env = Environment::with_prelude();
    let src = "def myf (n : Nat) : Nat := n\n\
               @[simp] private theorem myf_eq (n : Nat) : myf n = n := rfl\n\
               theorem useIt : myf 3 = 3 := by simp\n\
               def myg (n : Nat) : Nat := n\n\
               @[simp] protected theorem myg_eq (n : Nat) : myg n = n := rfl\n\
               theorem useIt2 : myg 3 = 3 := by simp\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`@[simp]` before `private`/`protected` must register the lemma: {e}");
    }
}
