// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end parse pins for the **secondary Mathlib-source parser gaps** — the
//! syntax wall that follows the module-system brick when parsing real Mathlib
//! v4.30.0-rc2 source (measured on `Mathlib/Logic/Basic.lean`, per-declaration
//! isolated parse):
//!
//! - **P2 `Sort*`** — the `Sort` analogue of `Type*`; parses to
//!   [`UniverseExpr::SortStar`] (elaboration parity with `Type*` is pinned in
//!   `clean-elab/tests/universe_enforcement_e2e.rs`).
//! - **P3 `open scoped X in <term>`** — term-level namespace opening.
//! - **P5 `alias`** — Batteries/Mathlib alias command, desugared to `def`s.
//! - **P6 `library_note «title»`** — Mathlib doc no-op command, and guillemet
//!   `«…»` identifiers lexing as a single identifier.
//!
//! Each probe asserts the resulting surface tree, plus verbatim
//! `Mathlib/Logic/Basic.lean` snippets that must parse without falling back to a
//! `RawDecl` recovery placeholder.

use clean_parser::{parse_expr, parse_file, SurfaceDecl, SurfaceExpr, UniverseExpr};

/// Parse a source string expected to yield exactly one declaration.
fn parse_one(src: &str) -> SurfaceDecl {
    let mut decls =
        parse_file(src).unwrap_or_else(|e| panic!("parse_file failed on `{src}`: {e:?}"));
    assert_eq!(
        decls.len(),
        1,
        "expected exactly one declaration from `{src}`, got {decls:?}"
    );
    decls.pop().expect("length checked above")
}

/// Assert a source string parses with no `RawDecl` error-recovery placeholder
/// anywhere in the declaration stream.
fn assert_no_raw(src: &str) {
    let decls =
        parse_file(src).unwrap_or_else(|e| panic!("parse_file failed on:\n{src}\nerror: {e:?}"));
    assert!(!decls.is_empty(), "no declarations parsed from:\n{src}");
    for d in &decls {
        assert!(
            !matches!(d, SurfaceDecl::RawDecl { .. }),
            "unexpected RawDecl recovery in:\n{src}\n(decl: {d:?})"
        );
    }
}

// ── P2 · Sort* ───────────────────────────────────────────────────────────────

#[test]
fn test_sort_star_parses_to_sort_star_universe() {
    let expr = parse_expr("Sort*").expect("`Sort*` should parse");
    assert!(
        matches!(expr, SurfaceExpr::Universe(_, UniverseExpr::SortStar)),
        "expected SortStar universe, got {expr:?}"
    );
}

#[test]
fn test_sort_star_and_bare_sort_and_type_star_are_distinct() {
    // Bare `Sort` and `Sort u` are unaffected; `Type*` still parses to
    // TypeImplicit; only `Sort*` is the new SortStar.
    assert!(matches!(
        parse_expr("Sort").expect("`Sort`"),
        SurfaceExpr::Universe(_, UniverseExpr::SortImplicit)
    ));
    assert!(matches!(
        parse_expr("Sort u").expect("`Sort u`"),
        SurfaceExpr::Universe(_, UniverseExpr::Sort(_))
    ));
    assert!(matches!(
        parse_expr("Type*").expect("`Type*`"),
        SurfaceExpr::Universe(_, UniverseExpr::TypeImplicit)
    ));
    assert!(matches!(
        parse_expr("Sort*").expect("`Sort*`"),
        SurfaceExpr::Universe(_, UniverseExpr::SortStar)
    ));
}

#[test]
fn test_sort_star_in_binder_position() {
    // The `variable {α : Sort*}` pattern from Mathlib/Logic/Basic.lean.
    assert_no_raw("variable {\u{3b1} : Sort*}");
    assert_no_raw("abbrev hidden {\u{3b1} : Sort*} {a : \u{3b1}} := a");
}

// ── P3 · open scoped X in <term> ─────────────────────────────────────────────

#[test]
fn test_open_scoped_in_term_parses() {
    // Term-level `open scoped X in <term>` must parse to a real `OpenIn` node
    // that PRESERVES the opened namespace path and the `scoped` flag — not the
    // old lossy `App(Ident("open"), [body])` wrapper that discarded them.
    let expr = parse_expr("open scoped Classical in Decidable.byContradiction")
        .expect("`open scoped X in <term>` should parse");
    match expr {
        SurfaceExpr::OpenIn {
            paths,
            scoped,
            body,
            ..
        } => {
            assert!(scoped, "`open scoped` must set the scoped flag");
            assert_eq!(paths.len(), 1, "one opened namespace");
            assert_eq!(
                paths[0].path,
                vec!["Classical".to_string()],
                "the `Classical` namespace path must be preserved, not discarded"
            );
            // The sub-term is `Decidable.byContradiction`.
            assert!(
                !matches!(&*body, SurfaceExpr::Ident(_, n) if n == "open"),
                "body must be the real sub-term, not an `open` marker"
            );
        }
        other => panic!("expected OpenIn node, got {other:?}"),
    }
}

#[test]
fn test_open_plain_in_term_still_parses() {
    // The non-`scoped` term form must keep working and preserve its namespace.
    let expr = parse_expr("open Nat in succ zero").expect("`open X in <term>` should parse");
    match expr {
        SurfaceExpr::OpenIn {
            paths,
            scoped,
            body,
            ..
        } => {
            assert!(!scoped, "plain `open` is not scoped");
            assert_eq!(paths[0].path, vec!["Nat".to_string()]);
            // `succ zero` — an application of the opened `succ`.
            assert!(
                matches!(&*body, SurfaceExpr::App(_, _, _)),
                "body should be the `succ zero` application, got {body:?}"
            );
        }
        other => panic!("expected OpenIn node, got {other:?}"),
    }
}

#[test]
fn test_open_scoped_multiple_in_term_parses() {
    let expr = parse_expr("open scoped Classical Real in foo")
        .expect("multiple `open scoped` should parse");
    match expr {
        SurfaceExpr::OpenIn { paths, scoped, .. } => {
            assert!(scoped);
            assert_eq!(paths.len(), 2, "both namespaces preserved");
            assert_eq!(paths[0].path, vec!["Classical".to_string()]);
            assert_eq!(paths[1].path, vec!["Real".to_string()]);
        }
        other => panic!("expected OpenIn node, got {other:?}"),
    }
}

// ── P5 · alias ───────────────────────────────────────────────────────────────

#[test]
fn test_alias_plain_desugars_to_def() {
    match parse_one("alias Iff.imp := imp_congr") {
        SurfaceDecl::Def { name, val, .. } => {
            assert_eq!(name, "Iff.imp");
            assert!(
                matches!(&*val, SurfaceExpr::Ident(_, t) if t == "imp_congr"),
                "alias value should be the target identifier, got {val:?}"
            );
        }
        other => panic!("expected Def from plain alias, got {other:?}"),
    }
}

#[test]
fn test_alias_reverse_arrow_desugars_to_def() {
    // The historical `alias newName ← target` reverse form.
    match parse_one("alias foo \u{2190} bar") {
        SurfaceDecl::Def { name, val, .. } => {
            assert_eq!(name, "foo");
            assert!(matches!(&*val, SurfaceExpr::Ident(_, t) if t == "bar"));
        }
        other => panic!("expected Def from reverse alias, got {other:?}"),
    }
}

#[test]
fn test_alias_iff_destructure_forward_only_desugars_to_def() {
    // `alias ⟨fwd, _⟩ := iffThm` — only the forward direction is named.
    match parse_one("alias \u{27e8}And.rotate, _\u{27e9} := and_rotate") {
        SurfaceDecl::Def { name, val, .. } => {
            assert_eq!(name, "And.rotate");
            match &*val {
                SurfaceExpr::App(_, head, args) => {
                    assert!(
                        matches!(&**head, SurfaceExpr::Ident(_, n) if n == "Iff.mp"),
                        "forward direction should be `Iff.mp target`, got {head:?}"
                    );
                    assert_eq!(args.len(), 1);
                }
                other => panic!("expected `Iff.mp and_rotate`, got {other:?}"),
            }
        }
        other => panic!("expected Def from forward-only iff alias, got {other:?}"),
    }
}

#[test]
fn test_alias_iff_destructure_both_directions_desugars_to_mutual() {
    // Both directions named → a mutual block of two `def`s (fwd = Iff.mp,
    // bwd = Iff.mpr).
    match parse_one("alias \u{27e8}mpName, mprName\u{27e9} := someIff") {
        SurfaceDecl::Mutual { decls, .. } => {
            assert_eq!(decls.len(), 2, "two named directions → two defs");
            assert!(decls.iter().all(|d| matches!(d, SurfaceDecl::Def { .. })));
        }
        other => panic!("expected Mutual from two-direction iff alias, got {other:?}"),
    }
}

#[test]
fn test_alias_with_attribute_parses() {
    // Leading attributes carry through: `@[deprecated …] alias …`.
    assert_no_raw(
        "@[deprecated (since := \"2026-01-30\")] alias and_or_imp := Classical.and_or_imp",
    );
}

// ── P6 · library_note + guillemet identifiers ────────────────────────────────

#[test]
fn test_library_note_guillemet_title_is_noop() {
    match parse_one("library_note \u{ab}fact non-instances\u{bb}") {
        SurfaceDecl::LibraryNote { title, .. } => assert_eq!(title, "fact non-instances"),
        other => panic!("expected LibraryNote no-op, got {other:?}"),
    }
}

#[test]
fn test_library_note_string_title_parses() {
    match parse_one("library_note \"some title\"") {
        SurfaceDecl::LibraryNote { title, .. } => assert_eq!(title, "some title"),
        other => panic!("expected LibraryNote no-op, got {other:?}"),
    }
}

#[test]
fn test_guillemet_identifier_lexes_as_single_ident() {
    let expr = parse_expr("\u{ab}foo bar\u{bb}").expect("guillemet identifier should parse");
    assert!(
        matches!(&expr, SurfaceExpr::Ident(_, n) if n == "foo bar"),
        "guillemet `«foo bar»` should be a single identifier, got {expr:?}"
    );
}

// ── Real Mathlib/Logic/Basic.lean snippet pins (v4.30.0-rc2, verbatim) ───────

#[test]
fn test_real_mathlib_snippets_parse_without_recovery() {
    assert_no_raw("abbrev hidden {\u{3b1} : Sort*} {a : \u{3b1}} := a");
    assert_no_raw("variable {\u{3b1} : Sort*}");
    assert_no_raw("alias Iff.imp := imp_congr");
    assert_no_raw("alias by_contra := by_contradiction");
    assert_no_raw("alias \u{27e8}And.rotate, _\u{27e9} := and_rotate");
    assert_no_raw("@[nolint defLemma] alias Iff.eq := propext");
    assert_no_raw(
        "theorem of_not_imp : \u{ac}(a \u{2192} b) \u{2192} a := \
         open scoped Classical in Decidable.of_not_imp",
    );
    assert_no_raw("library_note \u{ab}decidable arguments\u{bb}");
}

/// Mathlib `initialize_simps_projections S (proj → name …)` sets up the
/// `@[simps]` projection-name table — a no-op for kernel checking. A drop-in
/// must SKIP it (consume its `name (…)` arguments) rather than wall the file
/// with a parser-recovery `RawDecl`. It parses to a `LibraryNote` Skipped
/// marker and the following declaration parses cleanly. (The `?` trace form and
/// the no-parenthesis form are also accepted.)
#[test]
fn initialize_simps_projections_is_a_skipped_noop() {
    for src in [
        "initialize_simps_projections Foo (val \u{2192} coe)\ndef after : Nat := 5\n",
        "initialize_simps_projections? Bar\ndef after2 : Nat := 5\n",
    ] {
        let decls =
            parse_file(src).unwrap_or_else(|e| panic!("must parse (skipped no-op):\n{src}\n{e:?}"));
        assert!(
            matches!(decls[0], SurfaceDecl::LibraryNote { .. }),
            "the command must become a Skipped LibraryNote no-op, got {:?}",
            decls[0]
        );
        assert!(
            !decls
                .iter()
                .any(|d| matches!(d, SurfaceDecl::RawDecl { .. })),
            "no parser-recovery RawDecl expected from:\n{src}"
        );
    }
}
