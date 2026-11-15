// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Command grammar alternatives: an `instance` given by equations (Lean's
//! `declValEqns`, `Lean/Parser/Command.lean:169-184,200-202`) and
//! `attribute [...] names in <command>` (`Lean/Parser/Command.lean:825-826`).
//!
//! Every fixture elaborates as written on the pinned v4.30.0-rc2 `lean`
//! binary (2026-09-12).

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

fn accepts(src: &str, what: &str) {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, src) {
        panic!("{what}: {e}");
    }
}

/// `decidableEqPFun` (Mathlib `Logic/Function/Basic.lean:165`): an instance
/// whose value is an equation over two positions of a dependent codomain.
#[test]
fn test_instance_given_by_equations() {
    accepts(
        "instance natDecEq' : DecidableEq Nat\n\
         \x20 | a, b => Nat.decEq a b\n",
        "an `instance` must accept `| a, b => …` equations",
    );
}

/// `attribute [local simp] foo in theorem …` (Mathlib `Logic/Unique.lean:240`).
#[test]
fn test_attribute_in_scopes_to_the_next_command() {
    accepts(
        "theorem foo_eq (n : Nat) : n + 0 = n := rfl\n\
         attribute [local simp] foo_eq in\n\
         theorem bar (n : Nat) : n + 0 = n := by simp only [foo_eq]\n\
         theorem after_bar (n : Nat) : n + 0 = n := bar n\n",
        "`attribute … in <command>` must elaborate the command",
    );
}
