// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The modifier-prefix model (plan item `formats-module-spelling-refusals`).
//! Its agreement with pinned Lean is tested row by row in
//! `crates/clean-parser/tests/module_system_b_e2e_support/verdict_tables.rs`;
//! these pin the model's own rules and the parser's world gate.

use super::*;
use crate::{ParseError, SurfaceDecl};

#[test]
fn test_render_expected_uses_leans_list_shape() {
    assert_eq!(render_expected(&["section"]), "'section'");
    assert_eq!(render_expected(&["a", "b"]), "'a' or 'b'");
    assert_eq!(render_expected(&["a", "b", "c"]), "'a', 'b' or 'c'");
}

#[test]
fn test_section_header_takes_only_its_own_order() {
    let take = |words: &[Word]| lean_verdict(words, GuardedCommand::Section, false).is_none();
    let expose = Word::Attributes { expose_only: true };
    assert!(take(&[Word::Public]));
    assert!(take(&[Word::Noncomputable]));
    assert!(take(&[Word::Meta]));
    assert!(take(&[
        expose,
        Word::Public,
        Word::Noncomputable,
        Word::Meta
    ]));
    // Out of order, a modifier `sectionHeader` lacks, or another attribute.
    assert!(!take(&[Word::Noncomputable, Word::Public]));
    assert!(!take(&[Word::Meta, Word::Noncomputable]));
    assert!(!take(&[Word::Private]));
    assert!(!take(&[Word::Protected]));
    assert!(!take(&[Word::Attributes { expose_only: false }]));
    assert!(!take(&[expose, expose]));
}

#[test]
fn test_no_prefix_is_taken_by_import() {
    for words in [
        &[Word::Public][..],
        &[Word::Meta],
        &[Word::Public, Word::Meta],
        &[Word::Private],
        &[Word::AttrKind],
    ] {
        assert!(
            lean_verdict(words, GuardedCommand::Import, true).is_some(),
            "{words:?}"
        );
    }
}

#[test]
fn test_variable_visibility_is_world_gated() {
    for words in [&[Word::Public][..], &[Word::Private]] {
        assert!(lean_verdict(words, GuardedCommand::Variable, false).is_some());
        assert_eq!(lean_verdict(words, GuardedCommand::Variable, true), None);
    }
    // lean4#15518's `optional visibility` takes one visibility, nothing else.
    for words in [
        &[Word::Protected][..],
        &[Word::Public, Word::Noncomputable],
        &[Word::Attributes { expose_only: false }, Word::Public],
    ] {
        assert!(lean_verdict(words, GuardedCommand::Variable, true).is_some());
    }
}

#[test]
fn test_refusal_stops_at_the_first_word_no_reader_takes() {
    // `noncomputable private`: `declModifiers` filled its visibility slot's
    // successor, `sectionHeader` has no `private`.
    let refusal = lean_verdict(
        &[Word::Noncomputable, Word::Private],
        GuardedCommand::Import,
        false,
    )
    .expect("refused");
    assert_eq!(refusal.at, 1);
    assert!(refusal.expected.contains(&"section"));
    assert!(refusal.expected.contains(&"def"));
    // `private scoped`: only `instance`'s `attrKind` survives.
    let refusal = lean_verdict(
        &[Word::Private, Word::AttrKind],
        GuardedCommand::Section,
        false,
    )
    .expect("refused");
    assert_eq!(
        refusal,
        Refusal {
            at: 2,
            expected: vec!["instance"]
        }
    );
}

/// A declaration doc comment opens `declModifiers` and the other parsers that
/// start with one; `sectionHeader` and `grind_pattern` take none.
#[test]
fn test_doc_comment_is_a_first_slot_section_header_lacks() {
    let refusal =
        lean_verdict(&[Word::DocComment], GuardedCommand::Section, false).expect("refused");
    assert_eq!(refusal.at, 1);
    assert_eq!(refusal.expected.len(), 49, "{:?}", refusal.expected);
    assert_eq!(refusal.expected.first(), Some(&"#guard_msgs"));
    assert!(refusal.expected.contains(&"add_decl_doc"));
    assert!(!refusal.expected.contains(&"section"));
    assert!(!refusal.expected.contains(&"grind_pattern"));
    // After the doc comment, `scoped` keeps `instance`, the attribute-taking
    // commands and the `simproc` family, and loses `grind_pattern`.
    let refusal = lean_verdict(
        &[Word::DocComment, Word::AttrKind],
        GuardedCommand::Import,
        false,
    )
    .expect("refused");
    assert!(refusal.expected.contains(&"instance"));
    assert!(refusal.expected.contains(&"simproc"));
    assert!(!refusal.expected.contains(&"grind_pattern"));
    // Without one, `scoped` still reaches `grind_pattern`.
    let refusal = lean_verdict(&[Word::AttrKind], GuardedCommand::Import, false).expect("refused");
    assert!(refusal.expected.contains(&"grind_pattern"));
    // The doc comment is a first word only, and `sectionHeader` never takes it.
    assert!(lean_verdict(
        &[Word::Public, Word::DocComment],
        GuardedCommand::Section,
        false
    )
    .is_some_and(|refusal| refusal.at == 1));
    assert!(lean_verdict(
        &[Word::DocComment, Word::Public],
        GuardedCommand::Section,
        false
    )
    .is_some());
    // No reader takes an identifier where the command keyword belongs.
    assert!(lean_verdict(&[Word::DocComment], GuardedCommand::Identifier, true).is_some());
}

/// The parser reads a doc comment ending right before the command as the
/// prefix's first word, through a plain comment (whitespace to Lean), and
/// reports Lean's position at the doc comment's end, a multi-line one
/// included (v4.30.0-rc2, measured 2026-10-26: `3:6` and `2:8`).
#[test]
fn test_doc_comment_prefix_is_reported_at_the_doc_comments_end() {
    for (src, position) in [
        ("def y : Nat := 1\n/-- a\n  b -/\nsection\nend\n", "3:6"),
        ("def y : Nat := 1\n/-- a -/ /- c -/ section\nend\n", "2:8"),
    ] {
        let message = Parser::new(src)
            .file()
            .expect_err("Lean refuses a doc comment before `section`")
            .to_string();
        assert!(
            message.starts_with(&format!(
                "{position}: error: unexpected token 'section'; expected '#guard_msgs', "
            )),
            "{src}: {message}"
        );
    }
    // A module doc is a command of its own, so it is no prefix word: Lean
    // accepts this file.
    let decls = Parser::new("def y : Nat := 1\n/-! m -/\nsection\nend\n")
        .file()
        .expect("Lean accepts a module doc before `section`");
    assert!(
        matches!(
            decls.as_slice(),
            [SurfaceDecl::Def { .. }, SurfaceDecl::Section { .. }]
        ),
        "{decls:?}"
    );
}

fn parse_at(world: &'static str, src: &str) -> Result<Vec<SurfaceDecl>, ParseError> {
    Parser::new(src).at_lean_world(world).file()
}

/// The open side of the world gate: from v4.36.0-rc1 `public variable` and
/// `private variable` parse as the bare command, whose modifier lean4#15518
/// gives no effect. The test helper models the unregistered rc1 boundary;
/// production defaults to Oracle and selects qualified rc2 only through the
/// closed LeanWorld decision (`crate::parse_world`).
#[test]
fn test_variable_visibility_parses_from_v4_36_0_rc1() {
    for src in [
        "public variable (n : Nat)\ndef x : Nat := n\n",
        "private variable (n : Nat)\ndef x : Nat := n\n",
    ] {
        let decls = parse_at("v4.36.0-rc1", src).expect("v4.36.0-rc1 takes the modifier");
        assert!(
            matches!(
                decls.as_slice(),
                [SurfaceDecl::Variable { .. }, SurfaceDecl::Def { .. }]
            ),
            "{src}: {decls:?}"
        );
        let err = parse_at("v4.35.0", src).expect_err("v4.35.0 refuses the modifier");
        assert!(
            matches!(&err, ParseError::ModuleSyntaxRefused { message, .. }
                if message.starts_with("unexpected token 'variable'; expected ")),
            "{src}: {err}"
        );
    }
    // `protected variable` stays refused at every world.
    let err = parse_at("v4.36.0-rc1", "protected variable (n : Nat)\n")
        .expect_err("`variable` takes a visibility only");
    assert!(
        matches!(err, ParseError::ModuleSyntaxRefused { .. }),
        "{err}"
    );
}

/// The parser's default world is the Oracle, which refuses the modifier.
#[test]
fn test_default_parse_is_at_the_oracle_and_refuses_variable_visibility() {
    // Pinned Lean reports different expected lists: only public includes section.
    for (src, expected) in [
        (
            "public variable (n : Nat)\n",
            "1:6: error: unexpected token 'variable'; expected 'abbrev', 'axiom', \
             'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', \
             'initialize', 'instance', 'opaque', 'section', 'structure', 'syntax' or 'theorem'",
        ),
        (
            "private variable (n : Nat)\n",
            "1:7: error: unexpected token 'variable'; expected 'abbrev', 'axiom', \
             'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', \
             'initialize', 'instance', 'opaque', 'structure', 'syntax' or 'theorem'",
        ),
    ] {
        let err = Parser::new(src)
            .file()
            .expect_err("the Oracle refuses variable visibility");
        assert_eq!(err.to_string(), expected, "{src}");
    }
}
