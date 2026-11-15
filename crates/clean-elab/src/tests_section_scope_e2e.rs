// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `variable`s of a section die at its `end` — including when the section
//! holds a `namespace … end` block, which used to leave a stray scope frame
//! behind and keep the section's variables alive past `end` (see the
//! nested-namespace note in the Section arm of `elaborate_decl_and_register`).
//! Driven through the same preprocess-then-elaborate loop `clean check` runs,
//! since the leak lives in the interplay of the two.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

/// `(name, Ok | Err(rendering))` per leaf declaration, in file order.
fn run(src: &str) -> Vec<(String, Result<(), String>)> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut verdicts = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    match leaf {
                        ElabResult::Failed { name, error, .. } => {
                            verdicts.push((name.to_string(), Err(format!("{error:?}"))));
                        }
                        ElabResult::Theorem { name, .. } | ElabResult::Definition { name, .. } => {
                            verdicts.push((name.to_string(), Ok(())));
                        }
                        _ => {}
                    }
                }
            }
            Err(e) => verdicts.push((
                crate::preprocess_ext::decl_name(decl)
                    .map_or_else(|| "<decl>".to_string(), ToString::to_string),
                Err(format!("{e:?}")),
            )),
        }
    }
    verdicts
}

fn verdict_of<'a>(
    verdicts: &'a [(String, Result<(), String>)],
    name: &str,
) -> &'a Result<(), String> {
    &verdicts
        .iter()
        .find(|(n, _)| n == name)
        .unwrap_or_else(|| panic!("`{name}` must have a verdict; got {verdicts:?}"))
        .1
}

#[test]
fn test_section_variable_dies_at_end_when_the_section_holds_a_namespace_block() {
    // Lean: `unknown identifier 'n'` at `f`. The `namespace A … end A` block
    // inside the section is what used to keep `n` alive.
    let src = "section S\nvariable (n : Nat)\ndef g : Nat := n\nnamespace A\ndef h : Nat := 1\nend A\nend S\ndef f : Nat := n\n";
    let v = run(src);
    assert!(
        verdict_of(&v, "g").is_ok(),
        "inside the section `n` is in scope: {v:?}"
    );
    assert!(
        verdict_of(&v, "A.h").is_ok(),
        "the namespace block elaborates: {v:?}"
    );
    let f = verdict_of(&v, "f");
    assert!(
        f.as_ref()
            .is_err_and(|e| e.contains("UnknownIdent") && e.contains("\"n\"")),
        "`n` must be out of scope after `end S` even with a namespace block inside: {f:?}"
    );
}

#[test]
fn test_section_variable_dies_at_end_with_a_dotted_namespace_block_and_no_decls() {
    let src = "section S\nvariable (n : Nat)\nnamespace Mathlib.Tactic.GCongr\nend Mathlib.Tactic.GCongr\nend S\ndef f : Nat := n\n";
    let v = run(src);
    let f = verdict_of(&v, "f");
    assert!(
        f.as_ref().is_err_and(|e| e.contains("UnknownIdent")),
        "`n` must be out of scope after `end S`: {f:?}"
    );
}

#[test]
fn test_namespace_block_inside_section_still_sees_the_section_variable() {
    // The other direction: the section's `variable` IS visible inside the
    // nested namespace block (Lean scopes are nested, not disjoint).
    let src = "section S\nvariable (n : Nat)\nnamespace A\ndef h : Nat := n\nend A\nend S\n";
    let v = run(src);
    assert!(
        verdict_of(&v, "A.h").is_ok(),
        "`n` is in scope inside the nested namespace: {v:?}"
    );
}

#[test]
fn test_section_inside_namespace_control_is_unchanged() {
    let src = "namespace A\nsection S\nvariable (n : Nat)\nend S\ndef f : Nat := n\nend A\n";
    let v = run(src);
    let f = verdict_of(&v, "A.f");
    assert!(
        f.as_ref().is_err_and(|e| e.contains("UnknownIdent")),
        "the section-inside-namespace shape never leaked and must not now: {f:?}"
    );
}
