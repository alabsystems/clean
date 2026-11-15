// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The same source files are measured with pinned native Lean 4.30.0-rc2.
//! `revert` sorts locals by declaration order and includes forward dependencies.

use clean_elab::tactic::builtins::builtin_tactic_patterns;
use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};
use clean_parser::parse_file_with_tactics;

fn check_case(source: &str, name: &str, accepts: bool) {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let declarations = parse_file_with_tactics(source, &builtin_tactic_patterns())
        .expect("paired source must parse");
    let result = declarations.iter().try_for_each(|declaration| {
        let declaration = preprocess_decl_with_context(declaration, &mut context);
        elaborate_decl_and_register(&mut env, &declaration).map(|_| ())
    });
    let name = Name::from_string(name);
    if !accepts {
        assert!(result.is_err(), "negative source must be rejected");
        assert!(
            env.get_const(&name).is_none(),
            "rejected theorem must not register"
        );
        return;
    }
    result.expect("native-accepted source must elaborate and kernel-check");
    let info = env.get_const(&name).expect("theorem must register");
    let proof = info.value.as_ref().expect("theorem must have a proof");
    let checker = TypeChecker::new(&env);
    let inferred = checker.infer_type(proof).expect("proof must infer");
    assert!(checker.is_def_eq(&inferred, &info.type_));
    assert!(env
        .axiom_deps(&name)
        .expect("axiom closure must exist")
        .is_empty());
}

#[test]
fn revert_forward_ok() {
    check_case(
        include_str!("fixtures/revert_order/forward_ok.lean"),
        "revert_forward_ok",
        true,
    );
}

#[test]
fn revert_forward_bad() {
    check_case(
        include_str!("fixtures/revert_order/forward_bad.lean"),
        "revert_forward_bad",
        false,
    );
}

#[test]
fn revert_reverse_ok() {
    check_case(
        include_str!("fixtures/revert_order/reverse_ok.lean"),
        "revert_reverse_ok",
        true,
    );
}

#[test]
fn revert_reverse_bad() {
    check_case(
        include_str!("fixtures/revert_order/reverse_bad.lean"),
        "revert_reverse_bad",
        false,
    );
}

#[test]
fn revert_single_ok() {
    check_case(
        include_str!("fixtures/revert_order/single_ok.lean"),
        "revert_single_ok",
        true,
    );
}

#[test]
fn revert_single_bad() {
    check_case(
        include_str!("fixtures/revert_order/single_bad.lean"),
        "revert_single_bad",
        false,
    );
}

#[test]
fn revert_explicit_dep() {
    check_case(
        include_str!("fixtures/revert_order/explicit_dep.lean"),
        "revert_explicit_dep",
        true,
    );
}

#[test]
fn revert_explicit_dep_bad() {
    check_case(
        include_str!("fixtures/revert_order/explicit_dep_bad.lean"),
        "revert_explicit_dep_bad",
        false,
    );
}

#[test]
fn revert_implicit_dep() {
    check_case(
        include_str!("fixtures/revert_order/implicit_dep.lean"),
        "revert_implicit_dep",
        true,
    );
}

#[test]
fn revert_implicit_dep_bad() {
    check_case(
        include_str!("fixtures/revert_order/implicit_dep_bad.lean"),
        "revert_implicit_dep_bad",
        false,
    );
}

#[test]
fn revert_transitive_dep() {
    check_case(
        include_str!("fixtures/revert_order/transitive_dep.lean"),
        "revert_transitive_dep",
        true,
    );
}

#[test]
fn revert_transitive_dep_bad() {
    check_case(
        include_str!("fixtures/revert_order/transitive_dep_bad.lean"),
        "revert_transitive_dep_bad",
        false,
    );
}

#[test]
fn revert_shadow_ok() {
    check_case(
        include_str!("fixtures/revert_order/shadow_ok.lean"),
        "revert_shadow_ok",
        true,
    );
}

#[test]
fn revert_shadow_bad() {
    check_case(
        include_str!("fixtures/revert_order/shadow_bad.lean"),
        "revert_shadow_bad",
        false,
    );
}

#[test]
fn intro_shadow_ok() {
    check_case(
        include_str!("fixtures/revert_order/intro_shadow_ok.lean"),
        "intro_shadow_ok",
        true,
    );
}

#[test]
fn intro_shadow_bad() {
    check_case(
        include_str!("fixtures/revert_order/intro_shadow_bad.lean"),
        "intro_shadow_bad",
        false,
    );
}
