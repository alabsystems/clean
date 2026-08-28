// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `include` / `omit` semantics: which section variables a declaration gets.
//!
//! Lean includes a section `variable` in a declaration only when the
//! declaration MENTIONS it. `include x` overrides that for the rest of the
//! scope; `omit x` cancels the override. The parser-level fixtures live in
//! `clean_parser::include_omit_tests`; these pin what the commands MEAN.
//!
//! NOTE FOR ANYONE EXTENDING THIS. `crate::section_scope::SectionScope` also
//! models include/omit, but it is NOT the live path — nothing outside its own
//! tests constructs one — and its model is the older "auto-include everything,
//! `omit` excludes" one rather than Lean's current mention-based inclusion.
//! The live path is `used_section_binders` + `FileContext::apply_include`,
//! which is what these tests exercise.

use crate::{preprocess_decl_with_context, FileContext};
use clean_parser::{parse_file, SurfaceDecl};

/// Preprocess every declaration in `code` against one file context and return
/// the binder names each value declaration ends up carrying.
fn binder_names(code: &str) -> Vec<(String, Vec<String>)> {
    let decls = parse_file(code).expect("parses");
    let mut fc = FileContext::new();
    let mut out = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut fc);
        if let SurfaceDecl::Theorem { name, binders, .. } = &processed {
            out.push((
                name.clone(),
                binders.iter().map(|b| b.name.clone()).collect(),
            ));
        }
    }
    out
}

fn binders_of(code: &str, theorem: &str) -> Vec<String> {
    binder_names(code)
        .into_iter()
        .find(|(n, _)| n == theorem)
        .unwrap_or_else(|| panic!("no theorem `{theorem}`"))
        .1
}

/// Baseline, unchanged by this work: a section variable the declaration never
/// mentions is NOT prepended.
#[test]
fn test_unmentioned_section_variable_is_not_included_by_default() {
    let code = "variable {α : Type} (h : α)\ntheorem t : True := trivial\n";
    assert_eq!(binders_of(code, "t"), Vec::<String>::new());
}

/// `include h` forces `h` in even though `t` never mentions it — the whole
/// point of the command, and the shape Mathlib's `Function.Involutive` block
/// relies on. `α` comes with it because `h : α`; inclusion is closed under
/// type dependencies exactly as mention-based inclusion is.
#[test]
fn test_include_forces_an_unmentioned_variable_in() {
    let code = "variable {α : Type} (h : α)\ninclude h\ntheorem t : True := trivial\n";
    assert_eq!(
        binders_of(code, "t"),
        vec!["α".to_string(), "h".to_string()]
    );
}

/// Inclusion closes over type dependencies: `h : Foo f` drags `f`, and
/// `f : α → α` drags `α`, exactly as a MENTIONED variable would.
#[test]
fn test_include_closes_over_type_dependencies() {
    let code =
        "variable {α : Type} {f : α → α} (h : Foo f)\ninclude h\ntheorem t : True := trivial\n";
    assert_eq!(
        binders_of(code, "t"),
        vec!["α".to_string(), "f".to_string(), "h".to_string()],
        "including `h` must also bring in what `h`'s type needs"
    );
}

/// `omit` cancels a preceding `include`.
///
/// THE POSITION IS THE MEASUREMENT, not a stylistic choice. The obvious shape
/// for this test — `include h`, a theorem, `omit h`, a second theorem — CANNOT
/// be written, because a term-mode proof eats the `omit` line as two
/// application arguments before the command dispatcher ever sees it
/// (`clean_parser::include_omit_tests::
/// test_omit_after_a_term_mode_proof_is_absorbed_by_the_proof` pins that, with
/// the measured `App(Ident("trivial"), [Ident("omit"), Ident("h")])`). So the
/// cancellation is exercised in the position that DOES reach the dispatcher:
/// back to back with the `include` it cancels.
#[test]
fn test_omit_cancels_a_preceding_include() {
    let code = "variable {α : Type} (h : α)\n\
                include h\n\
                omit h\n\
                theorem after : True := trivial\n";
    assert_eq!(
        binders_of(code, "after"),
        Vec::<String>::new(),
        "`omit h` cancels the `include h` above it, so `after` — which never \
         mentions `h` — carries nothing"
    );
}

/// Without the `omit`, the same file gives `after` both binders. This is the
/// control for the test above: it is what makes the empty result there a
/// cancellation rather than an inclusion that never happened.
#[test]
fn test_control_without_omit_the_include_still_reaches_the_declaration() {
    let code = "variable {α : Type} (h : α)\n\
                include h\n\
                theorem after : True := trivial\n";
    assert_eq!(
        binders_of(code, "after"),
        vec!["α".to_string(), "h".to_string()]
    );
}

/// A declaration's OWN binder of the same name still shadows the section
/// variable — `include` does not override shadowing.
#[test]
fn test_own_binder_shadows_an_included_variable() {
    let code = "variable {α : Type} (h : α)\ninclude h\ntheorem t (h : True) : True := h\n";
    assert_eq!(
        binders_of(code, "t"),
        vec!["h".to_string()],
        "exactly one `h`: the declaration's own. `α` does not come either — it \
         was only ever reachable THROUGH the shadowed `h`"
    );
}

/// `include` is scoped like `variable`: a `section` boundary restores the
/// enclosing inclusion set, so an `include` cannot leak past its `end`.
///
/// Driven through `FileContext` directly rather than through a parsed
/// `section … end`, because the parser NESTS a section's declarations inside
/// the `Section` node and `preprocess_decl_with_context` does not walk into
/// them — the section drivers do. This asserts the scoping rule itself.
#[test]
fn test_include_dies_with_its_section() {
    let mut fc = FileContext::new();
    fc.enter_section();
    fc.include_variables(&["h".to_string()]);
    assert_eq!(fc.included_variables(), ["h".to_string()]);
    fc.exit_section();
    assert!(
        fc.included_variables().is_empty(),
        "an `include` must not outlive its section"
    );
}

/// Nested sections restore the OUTER inclusion set, not an empty one.
#[test]
fn test_nested_section_restores_the_outer_include_set() {
    let mut fc = FileContext::new();
    fc.enter_section();
    fc.include_variables(&["outer".to_string()]);
    fc.enter_section();
    fc.include_variables(&["inner".to_string()]);
    assert_eq!(
        fc.included_variables(),
        ["outer".to_string(), "inner".to_string()]
    );
    fc.exit_section();
    assert_eq!(fc.included_variables(), ["outer".to_string()]);
}

/// `include a b` includes both.
#[test]
fn test_include_several_names() {
    let code = "variable (a : Nat) (b : Nat)\ninclude a b\ntheorem t : True := trivial\n";
    assert_eq!(
        binders_of(code, "t"),
        vec!["a".to_string(), "b".to_string()]
    );
}

/// LANE FAILOPEN end-to-end: the Mathlib `Involutive` shape. Before the fix
/// the `variable` line absorbed `include h` as two untyped binders, the second
/// of which shadowed the real `(h : Involutive f)`; `injective` then
/// elaborated against an untyped meta and failed. Here `h` must arrive with
/// its real type.
#[test]
fn test_involutive_shape_keeps_the_typed_h() {
    let code = "variable {α : Sort u} {f : α → α} (h : Involutive f)\n\
                \n\
                include h\n\
                \n\
                theorem injective : Injective f := h.leftInverse.injective\n";
    let decls = parse_file(code).expect("parses");
    let mut fc = FileContext::new();
    for decl in &decls {
        // The rewritten declaration is not what is under test here — the
        // side effect on `fc`'s section-variable table is.
        let _ = preprocess_decl_with_context(decl, &mut fc);
    }
    let h = fc
        .current_variables()
        .iter()
        .filter(|b| b.name == "h")
        .collect::<Vec<_>>();
    assert_eq!(h.len(), 1, "exactly one section variable named `h`");
    assert!(
        h[0].ty.is_some(),
        "`h` must keep its type; an untyped `h` here is the fail-open"
    );
    assert!(
        fc.current_variables().iter().all(|b| b.name != "include"),
        "`include` must never become a section variable: {:?}",
        fc.current_variables()
            .iter()
            .map(|b| &b.name)
            .collect::<Vec<_>>()
    );
}
