// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An apostrophe inside an operator symbol is part of the symbol, not the
//! opening of a character literal.
//!
//! Lean tokenizes from a token table by maximal munch, so `⁻¹'`
//! (`Set.preimage`, `infixl:80`, `Mathlib/Data/Set/Operations.lean:127`) is one
//! token. Clean lexes the whole file before any notation is registered, so the
//! trailing prime used to open a character literal that ran to the end of the
//! LINE — swallowing the operator's right operand and collapsing the whole
//! declaration into error recovery. Measured radius in mathlib4
//! (43ad0e9d2e14): `⁻¹'` appears in **786 files / 4,084 lines**.
//!
//! Its sibling ` '' ` (`Set.image`, same file, `infixl:80`, 912 files) already
//! worked, but only coincidentally: `''` lexes to the same single
//! `Error(InvalidChar)` token in the declaration and at the use site, so the
//! sequences matched by value. That coincidence is preserved deliberately, and
//! pinned here, because the fix is narrow by design.

use clean_parser::{parse_file, Projection, SurfaceArg, SurfaceDecl, SurfaceExpr};

fn def_value<'a>(decls: &'a [SurfaceDecl], name: &str) -> &'a SurfaceExpr {
    for d in decls {
        match d {
            SurfaceDecl::Def { name: n, val, .. } if n == name => return val,
            SurfaceDecl::RawDecl { content, .. } if content.contains(name) => {
                panic!("`def {name}` fell into error recovery as RawDecl: {content:?}")
            }
            _ => {}
        }
    }
    panic!("no `def {name}` in {decls:#?}");
}

fn render(e: &SurfaceExpr) -> String {
    match e {
        SurfaceExpr::Ident(_, s) => s.clone(),
        // A dotted expansion head (`Set.preimage`) parses as a projection on
        // `Set`; print it back as the dotted name so the notations here can be
        // spelled exactly as Mathlib spells them.
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            format!("{}.{field}", render(base))
        }
        SurfaceExpr::Paren(_, inner) => render(inner),
        SurfaceExpr::App(_, f, args) => {
            let mut parts = vec![render(f)];
            parts.extend(args.iter().map(|a: &SurfaceArg| render(&a.expr)));
            format!("({})", parts.join(" "))
        }
        other => format!("{other:?}"),
    }
}

#[test]
fn test_set_preimage_operator_parses_with_both_operands() {
    // The headline reproduction: today this printed
    // `1 ok, 1 RawDecl-recovered … lexer error: unterminated character literal`.
    let code = "infixl:80 \" ⁻¹' \" => Set.preimage\ndef x (f s : Type) : Type := f ⁻¹' s\n";
    let decls = parse_file(code).expect("file with `⁻¹'` notation should parse");
    assert_eq!(render(def_value(&decls, "x")), "(Set.preimage f s)");
}

#[test]
fn test_set_image_operator_still_parses() {
    // Regression control: ` '' ` worked before this brick and must keep working.
    let code = "infixl:80 \" '' \" => Set.image\ndef y (f s : Type) : Type := f '' s\n";
    let decls = parse_file(code).expect("file with `''` notation should parse");
    assert_eq!(render(def_value(&decls, "y")), "(Set.image f s)");
}

#[test]
fn test_both_set_operators_coexist_in_one_file() {
    let code = "infixl:80 \" ⁻¹' \" => Set.preimage\n\
                infixl:80 \" '' \" => Set.image\n\
                def z (f s t : Type) : Type := f ⁻¹' s\n\
                def w (f s t : Type) : Type := f '' t\n";
    let decls = parse_file(code).expect("both notations should coexist");
    assert_eq!(render(def_value(&decls, "z")), "(Set.preimage f s)");
    assert_eq!(render(def_value(&decls, "w")), "(Set.image f t)");
}

#[test]
fn test_builtin_postfix_inverse_survives_the_longer_symbol() {
    // `⁻¹` is the PREFIX of `⁻¹'`. Registering the longer operator must not
    // cost the builtin `postfix:max "⁻¹" => Inv.inv`, and the longer one must
    // win where it actually matches (maximal munch, as in Lean's token table).
    let code = "infixl:80 \" ⁻¹' \" => Set.preimage\n\
                def a (g : Type) : Type := g⁻¹\n\
                def b (f s : Type) : Type := f ⁻¹' s\n";
    let decls = parse_file(code).expect("parse");
    assert_eq!(render(def_value(&decls, "a")), "(Inv.inv g)");
    assert_eq!(render(def_value(&decls, "b")), "(Set.preimage f s)");

    // …and with no notation registered at all, `⁻¹` is unchanged.
    let plain = parse_file("def a (g : Type) : Type := g⁻¹\n").expect("parse");
    assert_eq!(render(def_value(&plain, "a")), "(Inv.inv g)");
}

#[test]
fn test_ordinary_character_literals_are_untouched() {
    // The fix must not reach any ordinary literal. Escapes included, since the
    // whole escape table lives behind the same entry point.
    for (src, shown) in [
        ("'a'", "'a'"),
        (r"'\n'", r"'\n'"),
        (r"'\t'", r"'\t'"),
        (r"'\\'", r"'\\'"),
        (r"'\''", r"'\''"),
        (r"'\x41'", r"'\x41'"),
        (r"'\u{41}'", r"'\u{41}'"),
    ] {
        let code = format!("def c := {src}\n");
        let decls =
            parse_file(&code).unwrap_or_else(|e| panic!("`{shown}` should still parse: {e}"));
        assert!(
            matches!(
                def_value(&decls, "c"),
                SurfaceExpr::Lit(_, clean_parser::SurfaceLit::Char(_))
            ),
            "`{shown}` must stay a character literal: {:?}",
            def_value(&decls, "c"),
        );
    }
}

#[test]
fn test_char_literal_after_an_anonymous_constructor_bracket() {
    // `⟨` is non-ASCII but is a BRACKET, so the prime after it still opens a
    // literal — the narrowing that keeps `⟨'a', h⟩` working.
    let decls = parse_file("def c := ⟨'a', h⟩\n").expect("anonymous constructor should parse");
    assert!(
        !decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::RawDecl { .. })),
        "`⟨'a', h⟩` must not fall into error recovery: {decls:#?}",
    );
}

#[test]
fn test_a_malformed_char_literal_still_does_not_swallow_the_next_declaration() {
    // The single-line bound on character literals is what keeps one bad literal
    // from eating the rest of the file; opening the symbol case must not relax
    // it. `'ab` is unterminated, and `def after` must still be seen.
    let code = "def bad := 'ab\ndef after := 1\n";
    let decls = parse_file(code).expect("file parser should recover");
    assert!(
        decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::Def { name, .. } if name == "after")),
        "the declaration after a malformed literal must survive: {decls:#?}",
    );
}
