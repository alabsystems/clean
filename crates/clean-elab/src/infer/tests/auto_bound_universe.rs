// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An undeclared universe NAME auto-binds only under Lean's rule
//! (`Lean/Elab/Level.lean` `elabLevel`): `autoImplicit` must be on and the
//! name must pass `isValidAutoBoundLevelName`. Otherwise it is
//! `unknown universe level`.
//!
//! Ground truth is Lean v4.30.0-rc2 on `tests/elab_fail/autoBoundImplicits2`,
//! whose `g2` (`set_option autoImplicit false in … {α : Type u}`) and `g3`
//! (`{α : Type β}` under `relaxedAutoImplicit false`) Lean rejects and Clean
//! used to accept, while `g4`/`g5`/`g6` and the declared-universe controls
//! below stay accepted.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

/// Elaborate every command of `src` in order, returning one result per
/// command (options and `universe` commands included).
fn run(src: &str) -> Vec<Result<(), ElabError>> {
    let decls = parse_file(src).expect("fixture must parse");
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    decls
        .iter()
        .map(|decl| {
            let decl = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &decl, &mut file_ctx).map(|_| ())
        })
        .collect()
}

fn expect_unknown_universe(result: &Result<(), ElabError>, name: &str) {
    match result {
        Err(ElabError::UnknownUniverseLevel { name: got }) => assert_eq!(got, name),
        other => panic!("expected unknown universe level `{name}`, got {other:?}"),
    }
}

fn expect_all_ok(results: &[Result<(), ElabError>]) {
    for (i, r) in results.iter().enumerate() {
        assert!(r.is_ok(), "command {i} must elaborate: {r:?}");
    }
}

#[test]
fn test_auto_bound_universe_autoimplicit_false_refuses_undeclared_name() {
    let results = run("set_option autoImplicit false in\n\
         def g2 {α : Type u} (a : α) : α := a\n");
    expect_unknown_universe(results.last().expect("one declaration"), "u");
}

#[test]
fn test_auto_bound_universe_autoimplicit_false_accepts_declared_names() {
    // Over-refusal control: a declared universe is never auto-bound.
    let results = run("set_option autoImplicit false\n\
         universe u\n\
         def d1 {α : Type u} (a : α) : α := a\n\
         def d2.{v} {α : Type v} (a : α) : α := a\n");
    expect_all_ok(&results);
}

#[test]
fn section_variable_levels_are_rigid_and_end_with_their_scope() {
    use crate::test_support::file_verdicts::{run_named_file_messages, verdict_of};

    let results = run_named_file_messages(
        "set_option autoImplicit false\n\
        universe u\n\
        section Scoped\n\
        universe v\n\
        variable {A : Type (max u v)}\n\
        theorem selfEq (x : A) : x = x := rfl\n\
        end Scoped\n\
        variable {B : Type u}\n\
        variable {Escaped : Type v}\n",
        "ScopedLevels",
    );
    assert!(verdict_of(&results, "selfEq").is_ok());
    let errors: Vec<_> = results
        .iter()
        .filter_map(|(_, row)| row.as_ref().err())
        .collect();
    assert_eq!(errors, ["unknown universe level `v`"]);
}

#[test]
fn test_auto_bound_universe_strict_names_refuse_greek_and_long() {
    let results = run("set_option relaxedAutoImplicit false\n\
         def g3 {α : Type β} (a : α) : α := a\n\
         def g3b {α : Type uv} (a : α) : α := a\n");
    expect_unknown_universe(&results[1], "β");
    expect_unknown_universe(&results[2], "uv");
}

#[test]
fn test_auto_bound_universe_strict_names_accept_lowercase_with_suffix() {
    let results = run("set_option relaxedAutoImplicit false\n\
         def g4 {α : Type v} (a : α) : α := a\n\
         def g5 {α : Type (v+1)} (a : α) : α := a\n\
         def g7 {α : Type u_1'} (a : α) : α := a\n\
         def g8 {α : Type w₁} (a : α) : α := a\n\
         def g6 {α : Type u} (a : α) :=\n  let β : Type u := α\n  let x : β := a\n  x\n");
    expect_all_ok(&results);
}

#[test]
fn test_auto_bound_universe_relaxed_default_accepts_greek_name() {
    // `relaxedAutoImplicit` defaults to true, where Lean auto-binds `β`.
    let results = run("def r {α : Type β} (a : α) : α := a\n");
    expect_all_ok(&results);
}
