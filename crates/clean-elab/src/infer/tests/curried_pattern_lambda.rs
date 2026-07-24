// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused curried pattern-lambda regressions for #796.

use super::*;

#[test]
fn test_def_curried_pattern_lambda_on_type_params_elaborates() {
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab("def chooseSecond {α β : Type} : α → β → β\n  | _, b => b")
        .expect("curried chooseSecond declaration should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "curried multi-argument pattern lambda should elaborate against the expected Pi telescope, got {result:?}"
    );
}

#[test]
fn test_def_curried_indexed_inductive_pattern_lambda_elaborates() {
    let mut env = Environment::with_prelude();
    let imf_decl = parse_decl_for_elab(
        "inductive Imf {α : Type} {β : Type} (f : α → β) : β → Type\n| mk : (a : α) → Imf f (f a)",
    )
    .expect("Imf inductive declaration should parse");
    crate::elaborate_decl_and_register(&mut env, &imf_decl)
        .expect("Imf inductive declaration should elaborate");

    let decl =
        parse_decl_for_elab("def h {α β} {f : α → β} : {b : β} → Imf f b → α\n| _, Imf.mk a => a")
            .expect("curried dependent equation should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "curried indexed-inductive equation should elaborate, got {result:?}"
    );
}
