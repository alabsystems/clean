// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which spellings are NAMES, for the identifier properties in
//! `grammar::tests` (`prop_ident_parses`, `prop_lambda_parses`,
//! `prop_forall_parses`), and the pins that keep that answer honest.
//!
//! The properties draw names from a regex and must skip every spelling that
//! is not a name. They used to skip hand-copied keyword lists. When the parser
//! adopted Lean 4.8.0's token table (`crate::lean_keywords`) and made every
//! identifier-shaped token in it a keyword, the lists did not follow, and
//! `prop_lambda_parses` / `prop_forall_parses` drew `at`.
//!
//! The filter is LEAN's answer, not the lexer's. A spelling is a name when
//! Lean 4.8.0's token table does not hold it and Clean has not reserved it
//! beyond Lean ([`CLEAN_ONLY_RESERVED`], each one pinned as a divergence). A
//! filter derived from the lexer would test the parser against itself: a word
//! the lexer wrongly reserves would leave the properties' domain with no test
//! failing. [`test_parser_reserves_exactly_lean_keywords_and_the_pinned_divergences`]
//! checks that the lexer and this filter agree.

use proptest::prelude::*;

use crate::grammar::Parser;
use crate::lexer::{Lexer, TokenKind};
use crate::surface::SurfaceExpr;

/// Clean's keyword tokens whose spellings Lean 4.8.0 reads as ordinary
/// identifiers. Lean 4.8.0 is the version of the keyword table the parser
/// adopts. No Clean binder site accepts them
/// ([`test_clean_only_reserved_words_are_refused_as_binders`]).
///
/// Measured with `#check fun w => w` and `#check ∀ (w : Prop), w`:
/// Lean 4.8.0 accepts all seven. v4.30.0-rc2 accepts the first five and
/// reserves the last two (`unexpected token 'public'; expected '[', '{',
/// '|', '⦃' or term`). The first five are also exactly
/// [`TokenKind::is_core_lean_identifier_word`], which was measured against
/// v4.30.0-rc2.
///
/// `module` was the eighth until it stopped being a token: it lexes as an
/// identifier and only the file header reads it as a keyword
/// (`Parser::file`), as in Lean, whose header grammar has its own token
/// table.
const CLEAN_ONLY_RESERVED: [&str; 7] = [
    "rfl",
    "rec",
    "lemma",
    "codata",
    "codef",
    "coinductive",
    "public",
];

/// Whether `spelling` is a name: Lean 4.8.0's token table does not hold it,
/// and it is not one of the pinned Clean-only reservations.
fn is_name(spelling: &str) -> bool {
    !crate::lean_keywords::is_lean_keyword(spelling) && !CLEAN_ONLY_RESERVED.contains(&spelling)
}

/// Whether the PARSER reads `spelling` as a name. The lexer must scan all of
/// `spelling` as one unescaped `Ident` token. That rules out Clean's keyword
/// tokens (`fun`, `by`, `rfl`, …). The token must also not be marked as a
/// Lean 4.8.0 keyword (`Token::lean_keyword`).
fn parser_reads_as_name(spelling: &str) -> bool {
    matches!(Lexer::tokenize(spelling).as_slice(), [token, eof]
        if matches!(&token.kind, TokenKind::Ident(text) if text == spelling)
            && !token.lean_keyword
            && !token.ident_escaped
            && matches!(eof.kind, TokenKind::Eof))
}

/// Arbitrary identifiers of the regex `shape` that are names ([`is_name`]).
/// Rejected spellings are redrawn, so no case is spent on them.
pub(super) fn name_strategy(shape: &'static str) -> impl Strategy<Value = String> {
    shape.prop_filter("a keyword is not a name", |spelling| is_name(spelling))
}

/// Every spelling of the lexer's keyword match arms (`"fun" =>
/// TokenKind::Fun`), read from its source. This is only a candidate list for
/// the agreement check below, so a stray match adds a harmless extra
/// candidate. A missed arm would shrink the list, so the test asserts that the
/// scan still finds the arms it knows.
fn lexer_keyword_arm_spellings() -> Vec<&'static str> {
    const LEXER_SOURCE: &str = include_str!("../lexer.rs");
    LEXER_SOURCE
        .lines()
        .filter_map(|line| {
            let rest = line.trim_start().strip_prefix('"')?;
            let (word, tail) = rest.split_once('"')?;
            tail.trim_start()
                .starts_with("=> TokenKind::")
                .then_some(word)
        })
        .collect()
}

/// The parser reserves exactly Lean 4.8.0's keywords and the pinned
/// Clean-only words, and nothing else. This is what makes [`is_name`] the
/// parser's answer too, without asking the parser.
///
/// The candidates are every spelling in the Lean table, every keyword arm of
/// the lexer, the pinned words, and every spelling of the lambda shape with
/// at most three characters. A keyword the lexer gains without a Lean
/// counterpart fails here until it is either dropped or pinned in
/// [`CLEAN_ONLY_RESERVED`]. The keyword filter this replaces passed that
/// word silently, and that is how `public` and `coinductive` went unpinned.
#[test]
fn test_parser_reserves_exactly_lean_keywords_and_the_pinned_divergences() {
    let arms = lexer_keyword_arm_spellings();
    for known in ["fun", "forall", "Type", "rfl", "public", "coinductive"] {
        assert!(
            arms.contains(&known),
            "the lexer-source scan no longer finds the `{known}` arm: {arms:?}"
        );
    }

    let lowercase = 'a'..='z';
    let rest = || ('a'..='z').chain('0'..='9');
    let short = lowercase.flat_map(|a| {
        std::iter::once(a.to_string())
            .chain(rest().map(move |b| format!("{a}{b}")))
            .chain(rest().flat_map(move |b| rest().map(move |c| format!("{a}{b}{c}"))))
    });
    let candidates = crate::lean_keywords::all_lean_keywords()
        .chain(arms)
        .chain(CLEAN_ONLY_RESERVED)
        .map(String::from)
        .chain(short);

    let disagreements: Vec<String> = candidates
        .filter(|spelling| parser_reads_as_name(spelling) != is_name(spelling))
        .collect();
    assert!(
        disagreements.is_empty(),
        "the parser and Lean 4.8.0 + CLEAN_ONLY_RESERVED disagree on whether \
         these are names: {disagreements:?}"
    );
}

/// The name strategy drops every keyword and nothing else.
///
/// `at` is Lean's keyword, not Clean's invention. Lean 4.8.0 and v4.30.0-rc2
/// agree on all three: `fun at => at` is "unexpected token 'at'; expected
/// '[', '{', '|', '⦃' or term", `forall (at : Prop), at` is "unexpected token
/// 'at'; expected '_' or identifier", and `def at := 1` is "unexpected token
/// 'at'; expected identifier". So the TEST drew a non-name; the parser was
/// right.
#[test]
fn test_name_strategy_drops_every_keyword_and_keeps_every_name() {
    for keyword in crate::lean_keywords::all_lean_keywords() {
        assert!(
            !is_name(keyword),
            "`{keyword}` is a Lean 4.8.0 keyword, never a name"
        );
    }
    Parser::parse_expr("fun at => at").expect_err("Lean: unexpected token 'at'");
    Parser::parse_expr("forall (at : Prop), at").expect_err("Lean: unexpected token 'at'");

    // Keywords are densest among the spellings of at most two characters, so
    // check every spelling of the lambda/forall shape up to that length. Each
    // one the strategy keeps must parse as a binder in both properties'
    // shapes and as an identifier on its own. The ones it drops must be
    // exactly the two-letter keywords in Lean 4.8.0's table, so the
    // properties still range over arbitrary names.
    let heads = ('a'..='z').map(String::from);
    let tails = ('a'..='z').chain('0'..='9');
    let two = ('a'..='z').flat_map(|h| tails.clone().map(move |t| format!("{h}{t}")));
    let mut dropped = Vec::new();
    for name in heads.chain(two) {
        if !is_name(&name) {
            dropped.push(name);
            continue;
        }
        let lambda = Parser::parse_expr(&format!("fun {name} => {name}"));
        assert!(
            matches!(lambda, Ok(SurfaceExpr::Lambda(..))),
            "`fun {name} => {name}`: {lambda:?}"
        );
        let pi = Parser::parse_expr(&format!("forall ({name} : Prop), {name}"));
        assert!(
            matches!(pi, Ok(SurfaceExpr::Pi(..))),
            "`forall ({name} : Prop), {name}`: {pi:?}"
        );
        let ident = Parser::parse_expr(&name);
        assert!(
            matches!(&ident, Ok(SurfaceExpr::Ident(_, s)) if s.name() == crate::SurfaceName::component(&name, false).name()),
            "`{name}`: {ident:?}"
        );
    }
    assert_eq!(dropped, ["at", "by", "do", "if", "in"]);

    // Containing or extending a keyword does not make a keyword.
    for name in [
        "ats", "at1", "fora", "nomatch1", "rfl0", "inn", "publics", "x",
    ] {
        assert!(is_name(name), "`{name}` is a name");
        assert!(parser_reads_as_name(name), "`{name}` is a name");
    }
}

/// A DIVERGENCE the strategy inherits, pinned so that it fails loudly the day
/// it closes. Clean's lexer mints keyword tokens for the seven spellings in
/// [`CLEAN_ONLY_RESERVED`], and no binder site accepts them, so the strategy
/// drops them. Lean 4.8.0 accepts every one: `fun rec => rec : ?m → ?m`,
/// `∀ (rec : Prop), rec : Prop`, and the same for the other six.
/// v4.30.0-rc2 agrees for five and reserves `coinductive` and `public`. When a
/// binder site learns one of them, remove it from [`CLEAN_ONLY_RESERVED`];
/// the agreement test and this pin will both say so.
#[test]
fn test_clean_only_reserved_words_are_refused_as_binders() {
    for word in CLEAN_ONLY_RESERVED {
        let tokens = Lexer::tokenize(word);
        let [token, _eof] = tokens.as_slice() else {
            panic!("`{word}` no longer lexes as one token: {tokens:?}");
        };
        assert_eq!(
            token.kind.as_keyword_str(),
            Some(word),
            "`{word}` is no longer a Clean keyword token; re-derive this pin"
        );
        let reserved_by_lean_4_30 = matches!(word, "coinductive" | "public");
        assert_eq!(
            token.kind.is_core_lean_identifier_word(),
            !reserved_by_lean_4_30,
            "`{word}`: is_core_lean_identifier_word must match v4.30.0-rc2"
        );
        assert!(!is_name(word), "`{word}`");
        assert!(!parser_reads_as_name(word), "`{word}`");
        let lambda = Parser::parse_expr(&format!("fun {word} => {word}"))
            .expect_err("Lean 4.8.0 accepts this binder; Clean does not yet");
        assert!(
            format!("{lambda}").contains("expected at least one binder"),
            "{lambda}"
        );
        let pi = Parser::parse_expr(&format!("forall ({word} : Prop), {word}"))
            .expect_err("Lean 4.8.0 accepts this binder; Clean does not yet");
        assert!(
            format!("{pi}").contains("expected identifier in binder"),
            "{pi}"
        );
    }
}
