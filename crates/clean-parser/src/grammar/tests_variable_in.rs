//! `variable … in <command>`, and `include … in` / `omit … in` beside it --
//! Lean's generic `cmd₁ in cmd₂`, which expands to `section cmd₁ cmd₂ end`:
//! the command's effect lasts for the one command after it. Breadth class
//! (68) in docs/FRONTEND_CLASS_LEDGER.md: before this none of the three
//! consumed `in`, so the `in` became a raw declaration and the command after it
//! was parsed without the scoping.
//!
//! Ground truth, pinned Lean v4.30.0-rc2: `variable (n : Nat) in def f : Nat
//! := n + 1` gives `f : Nat → Nat`; a later `def g : Nat := n` is `Unknown
//! identifier n`. Under `variable (n : Nat)`, `include n in theorem t : True`
//! gives `t : ∀ (n : Nat), True` and the next theorem stays `True`; after
//! `include n`, `omit n in` drops `n` from the next theorem only.

use super::*;

fn file(source: &str) -> Vec<SurfaceDecl> {
    Parser::parse_file(source).expect("file parses")
}

#[test]
fn test_variable_in_wraps_the_one_command_in_an_anonymous_section() {
    let decls = file("variable (n : Nat) in\ndef f : Nat := n + 1\ndef g : Nat := 0\n");
    assert_eq!(
        decls.len(),
        2,
        "the section and the following `def g`, got {decls:?}"
    );
    let SurfaceDecl::Section {
        name: None,
        decls: inner,
        ..
    } = &decls[0]
    else {
        panic!("expected an anonymous section, got {:?}", decls[0]);
    };
    assert!(
        matches!(
            inner.as_slice(),
            [SurfaceDecl::Variable { .. }, SurfaceDecl::Def { .. }]
        ),
        "the section must hold exactly the variable and the one command, got {inner:?}"
    );
    assert!(
        matches!(decls[1], SurfaceDecl::Def { .. }),
        "the command after the scoped one is outside the section, got {:?}",
        decls[1]
    );
    assert!(
        !decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::RawDecl { .. })),
        "no recovery placeholder, got {decls:?}"
    );
}

#[test]
fn test_variable_in_takes_a_theorem_and_implicit_binders() {
    let decls = file("variable {α : Type} (a : α) in\ntheorem t : a = a := rfl\n");
    let SurfaceDecl::Section { decls: inner, .. } = &decls[0] else {
        panic!("expected a section, got {:?}", decls[0]);
    };
    let [SurfaceDecl::Variable { binders, .. }, SurfaceDecl::Theorem { .. }] = inner.as_slice()
    else {
        panic!("expected variable then theorem, got {inner:?}");
    };
    assert_eq!(
        binders.len(),
        2,
        "both binders belong to the variable, got {binders:?}"
    );
}

#[test]
fn test_plain_variable_is_unchanged() {
    let decls = file("variable (n : Nat)\ndef f : Nat := n\n");
    assert!(
        matches!(
            decls.as_slice(),
            [SurfaceDecl::Variable { .. }, SurfaceDecl::Def { .. }]
        ),
        "a `variable` with no `in` stays a top-level command, got {decls:?}"
    );
}

#[test]
fn test_include_in_wraps_the_one_command_in_an_anonymous_section() {
    let decls = file("variable (n : Nat)\ninclude n in\ntheorem t : True := trivial\n");
    let [SurfaceDecl::Variable { .. }, SurfaceDecl::Section {
        name: None,
        decls: inner,
        ..
    }] = decls.as_slice()
    else {
        panic!("expected the variable, then an anonymous section, got {decls:?}");
    };
    assert!(
        matches!(
            inner.as_slice(),
            [SurfaceDecl::IncludeVars { .. }, SurfaceDecl::Theorem { .. }]
        ),
        "the section must hold exactly the include and the one command, got {inner:?}"
    );
}

#[test]
fn test_omit_in_wraps_the_one_command_in_an_anonymous_section() {
    let decls = file("variable (n : Nat)\ninclude n\nomit n in\ntheorem t : True := trivial\n");
    let [SurfaceDecl::Variable { .. }, SurfaceDecl::IncludeVars { .. }, SurfaceDecl::Section { decls: inner, .. }] =
        decls.as_slice()
    else {
        panic!("expected variable, include, then a section, got {decls:?}");
    };
    assert!(
        matches!(
            inner.as_slice(),
            [SurfaceDecl::OmitVars { .. }, SurfaceDecl::Theorem { .. }]
        ),
        "the section must hold exactly the omit and the one command, got {inner:?}"
    );
}
