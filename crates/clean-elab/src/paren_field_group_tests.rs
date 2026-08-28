// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end coverage for parenthesized field binder groups in `where`
//! blocks — `structure P where (x : Nat) (y : Nat)` and the `class` twin.
//!
//! The parser-level pins live in clean-parser
//! (`syntax_boundary_regressions.rs`); these prove the parsed fields
//! ELABORATE: the structure registers, the projections exist, and a consumer
//! definition kernel-checks against them. Before the parser fix the groups
//! silently fell out of the `where` block (zero-field structure + junk raw
//! decl), so a consumer of `P3.x` failed with an unknown constant.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn elaborate_all(env: &mut Environment, code: &str, label: &str) {
    let decls = parse_file(code).unwrap_or_else(|e| panic!("{label}: parse failed: {e:?}"));
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(env, decl);
        assert!(
            result.is_ok(),
            "{label}: decl {i} should elaborate, got: {result:?}"
        );
    }
}

#[test]
fn test_structure_paren_field_groups_elaborate_and_project() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "structure P3 where (x : Nat) (y : Nat)\n\
         def sum3 (p : P3) : Nat := Nat.add (P3.x p) (P3.y p)",
        "paren field groups",
    );
    for c in ["P3.x", "P3.y", "sum3"] {
        assert!(
            env.get_const(&Name::from_string(c)).is_some(),
            "{c} must be registered"
        );
    }
}

#[test]
fn test_structure_multi_name_group_expands_per_name() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "structure V2 where\n  (x y : Nat)\n\
         def swap2 (v : V2) : V2 := V2.mk (V2.y v) (V2.x v)",
        "multi-name group",
    );
    assert!(
        env.get_const(&Name::from_string("swap2")).is_some(),
        "swap2 must kernel-check against both projections"
    );
}

#[test]
fn test_class_paren_field_group_elaborates() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "class Pointed (a : Type) where (pt : a)\n\
         instance : Pointed Nat where pt := 0\n\
         def origin : Nat := Pointed.pt Nat",
        "class paren group",
    );
    assert!(
        env.get_const(&Name::from_string("origin")).is_some(),
        "instance method through a paren-group field must resolve"
    );
}
