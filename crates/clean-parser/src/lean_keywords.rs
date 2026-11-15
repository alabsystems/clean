// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The identifier-shaped keywords of Lean 4.8.0.
//!
//! Lean's identifier scanner reads `nomatch` as an identifier and then asks
//! the token table: a token at least as long as the identifier wins
//! (`Lean.Parser.identFnAux`, `mkIdResult`), so every token spelled like an
//! identifier is a KEYWORD there, never a name. `fun (nomatch : Nat → Nat) =>
//! …`, `let nomatch := …` and `def nomatch := …` are syntax errors in Lean
//! ("expected identifier"). Clean's lexer knows only the keywords it has
//! syntax for; the rest (`nomatch`, `nofun`, `at`, `using`, `for`, …) were
//! ordinary identifiers, so such a binder was accepted and then CAPTURED the
//! keyword: with `nomatch` bound, `nomatch a + b` computed the user's
//! function where Lean has no such program (14 definitions of one battery,
//! measured 2026-09-26).
//!
//! The table is the token table of a Lean 4.8.0 file with no import line,
//! filtered by Lean's own `isIdFirst`/`isIdRest`, printed by
//! `crates/clean-elab/data/lean_core/DumpLeanCore.lean` through
//! `scripts/gen_lean_core_tables.sh` — never a hand list. Its digests and a
//! fresh dump are checked by `clean_elab`'s `lean_core_names` tests.
//!
//! A spelling is a keyword only as a WHOLE identifier: `Foo.nomatch`,
//! `nomatch.foo` and `x.nomatch` are single identifiers in Lean (longer than
//! the token), and a `«nomatch»` escape is always an identifier. The lexer
//! decides this once per token ([`crate::lexer::Token::lean_keyword`]).

use std::collections::HashSet;
use std::sync::OnceLock;

const KEYWORDS: &str = include_str!("../data/lean_core/keywords_v4.8.0.txt");

fn keywords() -> &'static HashSet<&'static str> {
    static TABLE: OnceLock<HashSet<&'static str>> = OnceLock::new();
    TABLE.get_or_init(|| {
        KEYWORDS
            .lines()
            .filter(|line| !line.starts_with('#'))
            .collect()
    })
}

/// Whether Lean 4.8.0 scans the whole identifier `text` as a keyword.
#[must_use]
pub(crate) fn is_lean_keyword(text: &str) -> bool {
    keywords().contains(text)
}

/// Every spelling of the table, for a test that must range over all of it
/// rather than over a copy that can drift from it.
#[cfg(test)]
pub(crate) fn all_lean_keywords() -> impl Iterator<Item = &'static str> {
    keywords().iter().copied()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_table_holds_the_measured_keywords_and_no_plain_names() {
        for keyword in [
            "nomatch",
            "nofun",
            "at",
            "using",
            "for",
            "fun",
            "StateRefT",
            "panic!",
        ] {
            assert!(is_lean_keyword(keyword), "{keyword}");
        }
        // Leading tactic atoms are non-reserved in Lean (the `tactic`
        // category's `leadingIdentBehavior`), and `rec`/`only` are
        // `nonReservedSymbol`s: all stay identifiers.
        for name in [
            "exact", "simp", "rfl", "rec", "only", "x", "nomatch'", "Nat",
        ] {
            assert!(!is_lean_keyword(name), "{name}");
        }
    }

    /// The lexer marks a keyword only as a WHOLE unescaped identifier.
    #[test]
    fn the_lexer_marks_whole_unescaped_keywords_only() {
        let marked = |src: &str| -> Vec<(String, bool)> {
            crate::lexer::Lexer::tokenize(src)
                .into_iter()
                .filter_map(|t| match t.kind {
                    crate::lexer::TokenKind::Ident(s) => Some((s, t.lean_keyword)),
                    _ => None,
                })
                .collect()
        };
        assert_eq!(
            marked("nomatch h"),
            vec![("nomatch".into(), true), ("h".into(), false)]
        );
        assert_eq!(marked("«nomatch»"), vec![("nomatch".into(), false)]);
        assert_eq!(
            marked("x.nomatch"),
            vec![("x".into(), false), ("nomatch".into(), false)]
        );
        assert_eq!(
            marked("nomatch.foo"),
            vec![("nomatch".into(), false), ("foo".into(), false)]
        );
        assert_eq!(marked(".at"), vec![("at".into(), false)]);
        assert_eq!(marked("nomatch.1"), vec![("nomatch".into(), true)]);
    }

    /// A keyword is refused wherever a name is bound or declared (Lean 4.8.0:
    /// "expected identifier"), and accepted where Lean reads an identifier
    /// without the token table (`«…»`, a dotted name, a field after `.`, an
    /// `inductive` constructor).
    #[test]
    fn the_parser_refuses_keyword_names_and_keeps_raw_identifiers() {
        // Parsed with no recovery event and no placeholder declaration.
        let parses = |src: &str| {
            crate::parse_file_with_diagnostics(src).is_ok_and(|report| {
                report.diagnostics.is_empty()
                    && !report
                        .decls
                        .iter()
                        .any(|d| matches!(d, crate::SurfaceDecl::RawDecl { .. }))
            })
        };
        for bad in [
            "def f (nomatch : Nat) : Nat := 1",
            "def f : Nat := (fun at => at) 1",
            "def f : Nat := let using := 1; using",
            "def nomatch : Nat := 1",
            "structure S where\n  for : Nat",
            "def f (a : Nat) : Nat := match a with\n  | nofun => 1",
        ] {
            assert!(!parses(bad), "must be refused: {bad}");
        }
        for good in [
            "def f («nomatch» : Nat) : Nat := «nomatch»",
            "def Foo.nomatch : Nat := 1",
            "def f (x : Foo) : Nat := x.nomatch",
            "inductive T where\n  | nomatch : T\n  | at : T",
            "def f (h : False) : Nat := nomatch h",
        ] {
            assert!(parses(good), "must parse: {good}");
        }
    }
}
