// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module-system parser brick — end-to-end parse tests.
//!
//! Lean 4's module system (`src/Lean/Parser/Module.lean`, `Command.lean`) lets a
//! file begin with a `module` header, tag imports with visibility
//! (`public import` / `private import` / `import all` / `meta import`), and wrap
//! declarations in `public section` / `@[expose] public section` or prefix them
//! with `public` / `private` / `protected`. These modifiers govern
//! export/module semantics only — they are **transparent to type-checking**, so
//! for `clean check` (parse → elaborate → kernel-verify) each construct is
//! accepted and the underlying import / section / declaration is processed
//! exactly as its bare form.
//!
//! Before this brick, Clean's lexer did not know `public` / `module`; it lexed
//! them as identifiers, so `public import X`, a leading `module`, and
//! `public section` all fell into declaration-error recovery (`RawDecl`
//! placeholders). These tests pin that the module system now parses to the
//! right trees, with visibility recorded and otherwise transparent.

use clean_parser::{parse_file, SurfaceDecl, Visibility};

/// Non-recovery decls only (drops `RawDecl` recovery placeholders).
fn real_decls(src: &str) -> Vec<SurfaceDecl> {
    parse_file(src)
        .expect("file parses")
        .into_iter()
        .filter(|d| !matches!(d, SurfaceDecl::RawDecl { .. }))
        .collect()
}

/// Assert the file parses with NO recovery placeholders at the top level.
fn assert_no_raw(src: &str) -> Vec<SurfaceDecl> {
    let decls = parse_file(src).expect("file parses");
    let raw = decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::RawDecl { .. }))
        .count();
    assert_eq!(
        raw, 0,
        "expected no RawDecl recovery placeholders, got {raw} in {decls:#?}"
    );
    decls
}

// --------------------------------------------------------------------------
// Imports: visibility / meta / all are transparent — resolve as bare `import`.
// --------------------------------------------------------------------------

#[test]
fn test_public_import_parses_as_import() {
    let decls = assert_no_raw("public import Mathlib.Logic.Basic");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Import { paths, .. } => {
            assert_eq!(
                paths,
                &vec![vec![
                    "Mathlib".to_string(),
                    "Logic".to_string(),
                    "Basic".to_string()
                ]]
            );
        }
        other => panic!("expected Import, got {other:?}"),
    }
}

#[test]
fn test_private_import_parses_as_import() {
    let decls = assert_no_raw("private import Batteries.Logic");
    match &decls[0] {
        SurfaceDecl::Import { paths, .. } => {
            assert_eq!(
                paths,
                &vec![vec!["Batteries".to_string(), "Logic".to_string()]]
            );
        }
        other => panic!("expected Import, got {other:?}"),
    }
}

#[test]
fn test_import_all_parses_as_import_dropping_all_keyword() {
    // `import all X` — the `all` requests private decls too; transparent to
    // checking, so the resolved path is exactly `X` (the `all` marker is dropped).
    let decls = assert_no_raw("import all Mathlib.Tactic.Basic");
    match &decls[0] {
        SurfaceDecl::Import { paths, .. } => {
            assert_eq!(
                paths,
                &vec![vec![
                    "Mathlib".to_string(),
                    "Tactic".to_string(),
                    "Basic".to_string()
                ]]
            );
        }
        other => panic!("expected Import, got {other:?}"),
    }
}

#[test]
fn test_meta_import_parses_as_import() {
    let decls = assert_no_raw("meta import Lean.Elab.Command");
    match &decls[0] {
        SurfaceDecl::Import { paths, .. } => {
            assert_eq!(
                paths,
                &vec![vec![
                    "Lean".to_string(),
                    "Elab".to_string(),
                    "Command".to_string()
                ]]
            );
        }
        other => panic!("expected Import, got {other:?}"),
    }
}

#[test]
fn test_bare_import_still_parses() {
    // Regression guard: the plain form is unaffected.
    let decls = assert_no_raw("import Mathlib.Init");
    assert!(matches!(&decls[0], SurfaceDecl::Import { .. }));
}

#[test]
fn test_public_import_public_module_name_not_swallowed() {
    // A module literally named starting with `all` must not have its head
    // segment eaten: `import allFoo.Bar` is a single module path, since `all`
    // is only the modifier when a *separate* identifier follows it. Here there
    // is no space, so `allFoo` is one identifier.
    let decls = assert_no_raw("import allFoo.Bar");
    match &decls[0] {
        SurfaceDecl::Import { paths, .. } => {
            assert_eq!(paths, &vec![vec!["allFoo".to_string(), "Bar".to_string()]]);
        }
        other => panic!("expected Import, got {other:?}"),
    }
}

// --------------------------------------------------------------------------
// Leading `module` header: a no-op for checking (contributes no decl node).
// --------------------------------------------------------------------------

#[test]
fn test_leading_module_is_noop() {
    // `module` header followed by an import: only the import survives.
    let decls = assert_no_raw("module\nimport Mathlib.Init");
    assert_eq!(
        decls.len(),
        1,
        "module header should contribute no node: {decls:#?}"
    );
    assert!(matches!(&decls[0], SurfaceDecl::Import { .. }));
}

#[test]
fn test_module_then_public_import() {
    let decls = assert_no_raw("module\npublic import Mathlib.Init");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Import { .. }));
}

// --------------------------------------------------------------------------
// `public section` / `@[expose] public section`: ordinary section wrapper.
// --------------------------------------------------------------------------

#[test]
fn test_public_section_parses_as_section() {
    let decls = assert_no_raw("public section\ntheorem t : True := trivial\nend");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Section { decls, .. } => {
            assert_eq!(decls.len(), 1);
            assert!(matches!(&decls[0], SurfaceDecl::Theorem { .. }));
        }
        other => panic!("expected Section, got {other:?}"),
    }
}

#[test]
fn test_expose_public_section_parses_as_section() {
    let decls = assert_no_raw("@[expose] public section\ntheorem t : True := trivial\nend");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Section { decls, .. } => {
            assert_eq!(decls.len(), 1);
            assert!(matches!(&decls[0], SurfaceDecl::Theorem { .. }));
        }
        other => panic!("expected Section, got {other:?}"),
    }
}

// --------------------------------------------------------------------------
// `public` / `private` / `protected` declaration modifiers: decl parses
// normally, visibility recorded.
// --------------------------------------------------------------------------

#[test]
fn test_public_def_records_public_visibility() {
    let decls = real_decls("public def foo : Nat := 1");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, modifiers, ..
        } => {
            assert_eq!(name, "foo");
            assert_eq!(modifiers.visibility, Visibility::Public);
        }
        other => panic!("expected Def, got {other:?}"),
    }
}

#[test]
fn test_private_theorem_records_private_visibility() {
    let decls = real_decls("private theorem bar : True := trivial");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Theorem {
            name, modifiers, ..
        } => {
            assert_eq!(name, "bar");
            assert_eq!(modifiers.visibility, Visibility::Private);
        }
        other => panic!("expected Theorem, got {other:?}"),
    }
}

#[test]
fn test_protected_def_records_protected_visibility() {
    let decls = real_decls("protected def baz : Nat := 0");
    match &decls[0] {
        SurfaceDecl::Def { modifiers, .. } => {
            assert_eq!(modifiers.visibility, Visibility::Protected);
        }
        other => panic!("expected Def, got {other:?}"),
    }
}

#[test]
fn test_public_keyword_before_def_composes_with_other_modifiers() {
    // `public noncomputable def` — visibility + computability both recorded.
    let decls = real_decls("public noncomputable def q : Nat := 0");
    match &decls[0] {
        SurfaceDecl::Def { modifiers, .. } => {
            assert_eq!(modifiers.visibility, Visibility::Public);
            assert!(modifiers.is_noncomputable);
        }
        other => panic!("expected Def, got {other:?}"),
    }
}

// --------------------------------------------------------------------------
// Real-Mathlib-header snippet: the exact shape of Mathlib/Logic/Basic.lean's
// preamble parses to its declarations with zero recovery placeholders in the
// module-system header.
// --------------------------------------------------------------------------

#[test]
fn test_real_mathlib_header_snippet_parses() {
    let src = "\
module

public import Mathlib.Tactic.AdaptationNote
public import Batteries.Logic
public import Batteries.Util.LibraryNote

import Mathlib.Tactic.Attr.Register

@[expose] public section

theorem not_not_intro {a : Prop} (ha : a) : ¬¬a := fun h => h ha
";
    let decls = parse_file(src).expect("header snippet parses");

    // Four imports (three public, one bare), then a section wrapping the body.
    let imports = decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::Import { .. }))
        .count();
    assert_eq!(imports, 4, "expected 4 imports, got {decls:#?}");

    let section = decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::Section { decls, .. } => Some(decls),
            _ => None,
        })
        .expect("a `public section` wrapping the body");
    assert!(
        section
            .iter()
            .any(|d| matches!(d, SurfaceDecl::Theorem { .. })),
        "section should contain the theorem: {section:#?}"
    );

    // The module-system header must produce NO recovery placeholders.
    let raw = decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::RawDecl { .. }))
        .count();
    assert_eq!(
        raw, 0,
        "module-system header must not error-recover: {decls:#?}"
    );
}
