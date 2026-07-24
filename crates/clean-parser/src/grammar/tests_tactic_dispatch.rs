// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser tests for newly wired tactic dispatch entries (#1789).

use super::*;

fn by_tactics(input: &str) -> Vec<SurfaceTactic> {
    let e = Parser::parse_expr(input).expect("parse should succeed");
    match e {
        SurfaceExpr::ByTactic(_, t) => t,
        other => unreachable!("expected ByTactic, got {:?}", other),
    }
}

#[test]
fn test_parse_symm_tactic() {
    let t = by_tactics("by symm");
    assert!(matches!(&t[0], SurfaceTactic::Named { ref name, .. } if name == "symm"));
}

#[test]
fn test_parse_trans_tactic() {
    let t = by_tactics("by trans Type");
    assert!(
        matches!(&t[0], SurfaceTactic::Named { ref name, args, .. } if name == "trans" && args.len() == 1)
    );
}

#[test]
fn test_parse_use_tactic() {
    let t = by_tactics("by use Type");
    assert!(
        matches!(&t[0], SurfaceTactic::Named { ref name, args, .. } if name == "use" && args.len() == 1)
    );
}

#[test]
fn test_parse_admit_tactic() {
    let t = by_tactics("by admit");
    assert!(matches!(&t[0], SurfaceTactic::Named { ref name, .. } if name == "admit"));
}

#[test]
fn test_parse_rotate_left_tactic() {
    let t = by_tactics("by rotate_left 2");
    assert!(
        matches!(&t[0], SurfaceTactic::Named { ref name, args, .. } if name == "rotate_left" && args.len() == 1)
    );
}

// =========================================================================
// Named tactic dispatch tests (#1899)
//
// Verify that unknown tactic names produce SurfaceTactic::Named, and that
// pattern-aware parsing via _with_tactics APIs respects TacticArgPattern.
// =========================================================================

use crate::tactic_patterns::{TacticArgPattern, TacticPatterns};

/// Helper: parse with tactic patterns
fn by_tactics_with(input: &str, patterns: &TacticPatterns) -> Vec<SurfaceTactic> {
    let e = Parser::parse_expr_with_tactics(input, patterns).expect("parse should succeed");
    match e {
        SurfaceExpr::ByTactic(_, t) => t,
        other => unreachable!("expected ByTactic, got {:?}", other),
    }
}

#[test]
fn test_named_tactic_unknown_produces_named() {
    // An unknown tactic name with one ident argument falls through to the
    // generic Named path. (`rcases` previously stood in here, but it now has a
    // dedicated parse arm; see `test_rcases_no_with_defaults_to_wildcard`.)
    let t = by_tactics("by my_unknown_tac h");
    assert!(
        matches!(&t[0], SurfaceTactic::Named { name, args, .. }
            if name == "my_unknown_tac" && args.len() == 1),
        "expected Named 'my_unknown_tac' with 1 arg, got {:?}",
        t[0]
    );
}

#[test]
fn test_named_tactic_nullary_no_args() {
    let t = by_tactics("by itauto");
    assert!(
        matches!(&t[0], SurfaceTactic::Named { name, .. } if name == "itauto"),
        "expected Named 'itauto', got {:?}",
        t[0]
    );
}

#[test]
fn test_named_tactic_with_pattern_nullary() {
    let mut patterns = TacticPatterns::new();
    patterns.insert("my_tac".to_string(), TacticArgPattern::Nullary);
    // With Nullary pattern, parser should consume zero args even if identifiers follow
    let t = by_tactics_with("by my_tac", &patterns);
    assert!(
        matches!(&t[0], SurfaceTactic::Named { name, args, .. }
            if name == "my_tac" && args.is_empty()),
        "Nullary pattern should produce zero args, got {:?}",
        t[0]
    );
}

#[test]
fn test_named_tactic_with_pattern_term_arg() {
    let mut patterns = TacticPatterns::new();
    patterns.insert("my_exact".to_string(), TacticArgPattern::TermArg);
    let t = by_tactics_with("by my_exact Type", &patterns);
    assert!(
        matches!(&t[0], SurfaceTactic::Named { name, args, .. }
            if name == "my_exact" && args.len() == 1),
        "TermArg pattern should produce 1 arg, got {:?}",
        t[0]
    );
}

#[test]
fn test_named_tactic_without_pattern_generic_args() {
    // Without patterns, generic comma-separated parsing applies
    let t = by_tactics("by my_unknown_tac x, y");
    assert!(
        matches!(&t[0], SurfaceTactic::Named { name, args, .. }
            if name == "my_unknown_tac" && args.len() == 2),
        "Generic parsing should produce 2 comma-separated args, got {:?}",
        t[0]
    );
}

#[test]
fn test_named_tactic_with_pattern_ident_list() {
    let mut patterns = TacticPatterns::new();
    patterns.insert("my_intro".to_string(), TacticArgPattern::IdentList);
    let t = by_tactics_with("by my_intro a b c", &patterns);
    assert!(
        matches!(&t[0], SurfaceTactic::Named { name, args, .. }
            if name == "my_intro" && args.len() == 3),
        "IdentList pattern should produce 3 ident args, got {:?}",
        t[0]
    );
}

#[test]
fn test_named_tactic_with_pattern_two_terms_idents() {
    // The TwoTerms pattern parses `absurd h hn` as TWO separate term args,
    // NOT a single left-associative application `h hn`. This is the pattern
    // that wires the `absurd h hn` tactic.
    let mut patterns = TacticPatterns::new();
    patterns.insert("absurd".to_string(), TacticArgPattern::TwoTerms);
    let t = by_tactics_with("by absurd h hn", &patterns);
    assert!(
        matches!(&t[0], SurfaceTactic::Named { name, args, .. }
            if name == "absurd" && args.len() == 2),
        "TwoTerms pattern should produce 2 args, got {:?}",
        t[0]
    );
    if let SurfaceTactic::Named { args, .. } = &t[0] {
        assert!(
            matches!(&args[0], SurfaceExpr::Ident(_, n) if n == "h"),
            "first arg should be bare ident `h`, got {:?}",
            args[0]
        );
        assert!(
            matches!(&args[1], SurfaceExpr::Ident(_, n) if n == "hn"),
            "second arg should be bare ident `hn`, got {:?}",
            args[1]
        );
    }
}

#[test]
fn test_named_tactic_with_pattern_two_terms_parenthesized_apps() {
    // `absurd (f x) (g y)` must yield two parenthesized applications, NOT a
    // single chained application `f x (g y)`.
    let mut patterns = TacticPatterns::new();
    patterns.insert("absurd".to_string(), TacticArgPattern::TwoTerms);
    let t = by_tactics_with("by absurd (f x) (g y)", &patterns);
    assert!(
        matches!(&t[0], SurfaceTactic::Named { name, args, .. }
            if name == "absurd" && args.len() == 2),
        "TwoTerms pattern should produce 2 parenthesized args, got {:?}",
        t[0]
    );
}

#[test]
fn test_two_terms_without_pattern_collapses_to_single_app() {
    // Documents the bug this change fixes: without the TwoTerms pattern,
    // the generic expr-list parser folds `absurd h hn` into a SINGLE
    // application arg `App(h, hn)`, which is why `absurd` was unreachable.
    let t = by_tactics("by absurd h hn");
    assert!(
        matches!(&t[0], SurfaceTactic::Named { name, args, .. }
            if name == "absurd" && args.len() == 1),
        "without TwoTerms, generic parsing collapses to 1 App arg, got {:?}",
        t[0]
    );
}

#[test]
fn test_named_tactic_two_terms_only_one_term_degrades_not_silent_success() {
    // The TwoTerms pattern requires exactly two terms: when only one is given,
    // the tactic parser raises a ParseError. The `by` block recovers it into a
    // SyntheticSorry (graceful degradation) — it must NOT silently succeed as a
    // valid 1-arg `absurd` Named tactic (which could close a goal unsoundly).
    let mut patterns = TacticPatterns::new();
    patterns.insert("absurd".to_string(), TacticArgPattern::TwoTerms);
    let e = Parser::parse_expr_with_tactics("by absurd h", &patterns)
        .expect("by-block recovers errors");
    match e {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert!(
                !tactics.iter().any(|t| matches!(
                    t,
                    SurfaceTactic::Named { name, args, .. } if name == "absurd" && args.len() == 2
                )),
                "one-term `absurd` must not parse as a valid two-arg tactic, got {tactics:?}"
            );
        }
        SurfaceExpr::SyntheticSorry(_) => {
            // Recovered to a sorry node — the malformed tactic did not parse.
        }
        other => unreachable!("expected ByTactic or SyntheticSorry, got {other:?}"),
    }
}

#[test]
fn test_migrated_nullary_produces_named() {
    // `ring` was migrated from hardcoded Ring variant to Named dispatch in Phase 3B
    let t = by_tactics("by ring");
    assert!(
        matches!(&t[0], SurfaceTactic::Named { ref name, .. } if name == "ring"),
        "'ring' should produce Named variant after migration, got {:?}",
        t[0]
    );
}

#[test]
fn test_with_tactics_backwards_compatible() {
    // _with_tactics API with empty patterns should produce same result as regular parse
    let patterns = TacticPatterns::new();
    let t = by_tactics_with("by exact Type", &patterns);
    assert!(
        matches!(&t[0], SurfaceTactic::Named { ref name, .. } if name == "exact"),
        "'exact' should produce Named variant, got {:?}",
        t[0]
    );
}

#[test]
fn test_ident_list_stops_at_registered_tactic() {
    // `intro x rcases h` should parse as two tactics: `intro x` then `rcases h`.
    // `rcases` is in the pattern map, so try_eat_ident must reject it.
    let mut patterns = TacticPatterns::new();
    patterns.insert("rcases".to_string(), TacticArgPattern::ExprList);
    let t = by_tactics_with("by intro x rcases h", &patterns);
    assert_eq!(t.len(), 2, "should parse as 2 tactics, got {:?}", t);
    assert!(
        matches!(&t[0], SurfaceTactic::Named { name, args, .. } if name == "intro" && args.len() == 1),
        "first tactic should be `intro x`, got {:?}",
        t[0]
    );
    // `rcases` now has a dedicated parse arm producing `RCases`. With no
    // `with`-clause the pattern defaults to a single wildcard `_`.
    assert!(
        matches!(&t[1], SurfaceTactic::RCases { term, pattern, .. }
            if matches!(term.as_ref(), SurfaceExpr::Ident(_, n) if n == "h") && pattern == "_"),
        "second tactic should be `rcases h` (RCases, pattern `_`), got {:?}",
        t[1]
    );
}

#[test]
fn test_ident_list_without_pattern_consumes_all() {
    // Without patterns, `intro x rcases h` should parse `intro` with 3 ident args
    // because `rcases` is not in the keyword list or pattern map
    let t = by_tactics("by intro x rcases h");
    assert!(
        matches!(&t[0], SurfaceTactic::Named { name, args, .. } if name == "intro" && args.len() == 3),
        "without patterns, intro should consume all idents, got {:?}",
        t[0]
    );
}

// =========================================================================
// obtain surface-form parsing (#clean97-obtain)
//
// `obtain pat (: T)? := e` must parse to SurfaceTactic::Obtain so the `:=`
// separator and the anonymous-constructor pattern ⟨...⟩ are handled rather
// than falling to the generic comma-separated expr-list arg parser.
// =========================================================================

#[test]
fn test_obtain_tuple_pattern_parses_to_obtain_variant() {
    let t = by_tactics("by obtain ⟨hp, hq⟩ := h");
    assert_eq!(t.len(), 1, "expected a single tactic, got {:?}", t);
    match &t[0] {
        SurfaceTactic::Obtain {
            pattern, ty, term, ..
        } => {
            assert_eq!(pattern, "⟨hp, hq⟩", "pattern text round-trips");
            assert!(ty.is_none(), "no type ascription expected");
            assert!(
                matches!(term.as_ref(), SurfaceExpr::Ident(_, n) if n == "h"),
                "RHS term should be the hypothesis `h`, got {:?}",
                term
            );
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
}

#[test]
fn test_obtain_nested_pattern_parses() {
    let t = by_tactics("by obtain ⟨⟨a, b⟩, c⟩ := h");
    match &t[0] {
        SurfaceTactic::Obtain { pattern, .. } => {
            assert_eq!(pattern, "⟨⟨a, b⟩, c⟩", "nested pattern text round-trips");
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
}

#[test]
fn test_obtain_single_name_pattern_parses() {
    let t = by_tactics("by obtain h2 := h");
    match &t[0] {
        SurfaceTactic::Obtain { pattern, term, .. } => {
            assert_eq!(pattern, "h2");
            assert!(matches!(term.as_ref(), SurfaceExpr::Ident(_, n) if n == "h"));
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
}

#[test]
fn test_obtain_with_type_ascription_parses() {
    let t = by_tactics("by obtain ⟨x, hx⟩ : Foo := h");
    match &t[0] {
        SurfaceTactic::Obtain {
            pattern, ty, term, ..
        } => {
            assert_eq!(pattern, "⟨x, hx⟩");
            assert!(ty.is_some(), "type ascription `: Foo` should be captured");
            assert!(matches!(term.as_ref(), SurfaceExpr::Ident(_, n) if n == "h"));
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
}

#[test]
fn test_obtain_compound_rhs_term_parses() {
    // The RHS may be an arbitrary term, not just a hyp name.
    let t = by_tactics("by obtain ⟨a, b⟩ := And.intro hp hq");
    match &t[0] {
        SurfaceTactic::Obtain { pattern, term, .. } => {
            assert_eq!(pattern, "⟨a, b⟩");
            assert!(
                matches!(term.as_ref(), SurfaceExpr::App(..)),
                "RHS should parse as an application `And.intro hp hq`, got {:?}",
                term
            );
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
}

// =========================================================================
// rcases surface-form parsing — `rcases <term> with <pattern>`
//
// `rcases` destructures an EXISTING hypothesis. It must parse to
// SurfaceTactic::RCases so the `with`-clause and the anonymous-constructor
// pattern ⟨...⟩ are handled, reusing obtain's pattern reader. Without the
// dedicated arm the generic expr-list parser stopped at `with`, leaving it for
// the sequencer, which mis-parsed `with ⟨...⟩` and triggered decl recovery.
// =========================================================================

#[test]
fn test_rcases_with_tuple_pattern_parses_to_rcases_variant() {
    let t = by_tactics("by rcases h with ⟨hp, hq⟩");
    assert_eq!(t.len(), 1, "expected a single tactic, got {:?}", t);
    match &t[0] {
        SurfaceTactic::RCases { term, pattern, .. } => {
            assert_eq!(pattern, "⟨hp, hq⟩", "pattern text round-trips");
            assert!(
                matches!(term.as_ref(), SurfaceExpr::Ident(_, n) if n == "h"),
                "scrutinee should be the hypothesis `h`, got {:?}",
                term
            );
        }
        other => unreachable!("expected SurfaceTactic::RCases, got {:?}", other),
    }
}

#[test]
fn test_rcases_nested_pattern_parses() {
    let t = by_tactics("by rcases h with ⟨a, ⟨b, c⟩⟩");
    match &t[0] {
        SurfaceTactic::RCases { pattern, .. } => {
            assert_eq!(pattern, "⟨a, ⟨b, c⟩⟩", "nested pattern text round-trips");
        }
        other => unreachable!("expected SurfaceTactic::RCases, got {:?}", other),
    }
}

#[test]
fn test_rcases_single_name_pattern_parses() {
    let t = by_tactics("by rcases h with h2");
    match &t[0] {
        SurfaceTactic::RCases { pattern, term, .. } => {
            assert_eq!(pattern, "h2");
            assert!(matches!(term.as_ref(), SurfaceExpr::Ident(_, n) if n == "h"));
        }
        other => unreachable!("expected SurfaceTactic::RCases, got {:?}", other),
    }
}

#[test]
fn test_rcases_no_with_defaults_to_wildcard() {
    // `rcases h` with no `with`-clause defaults the pattern to a wildcard.
    let t = by_tactics("by rcases h");
    match &t[0] {
        SurfaceTactic::RCases { pattern, term, .. } => {
            assert_eq!(pattern, "_");
            assert!(matches!(term.as_ref(), SurfaceExpr::Ident(_, n) if n == "h"));
        }
        other => unreachable!("expected SurfaceTactic::RCases, got {:?}", other),
    }
}

#[test]
fn test_rcases_with_sequenced_continuation_parses_two_tactics() {
    // The `;`-sequenced continuation must be left for the sequencer: parsing
    // must stop cleanly at the pattern's closing `⟩`. This is the confirmed
    // repro that previously triggered decl-level recovery.
    let t = by_tactics("by rcases h with ⟨hp, hq⟩; exact hq");
    assert_eq!(
        t.len(),
        2,
        "expected `rcases ...` then `exact hq`, got {:?}",
        t
    );
    match &t[0] {
        SurfaceTactic::RCases { pattern, .. } => {
            assert_eq!(pattern, "⟨hp, hq⟩");
        }
        other => unreachable!("expected SurfaceTactic::RCases, got {:?}", other),
    }
}

#[test]
fn test_rcases_existential_pattern_parses() {
    let t = by_tactics("by rcases h with ⟨n, hn⟩");
    match &t[0] {
        SurfaceTactic::RCases { pattern, .. } => {
            assert_eq!(pattern, "⟨n, hn⟩");
        }
        other => unreachable!("expected SurfaceTactic::RCases, got {:?}", other),
    }
}

// =========================================================================
// `|` alternation (Or-pattern) parsing — `rcases`/`obtain`/`rintro`
//
// The top-level `pat₁ | pat₂` alternation must be captured into the pattern
// text so the elaborator's `RIntroPattern::parse` reads it as an `Or` and
// case-splits. Previously the leaf reader stopped at the first leaf, leaving the
// dangling `| ..` for declaration recovery (the `Pipe` raw-decl error).
// =========================================================================

#[test]
fn test_rcases_or_alternation_pattern_parses_to_pipe_text() {
    // `rcases h with hp | hq` captures the whole alternation as `hp | hq`.
    let t = by_tactics("by rcases h with hp | hq");
    assert_eq!(
        t.len(),
        1,
        "alternation must not spill into a second tactic, got {:?}",
        t
    );
    match &t[0] {
        SurfaceTactic::RCases { pattern, term, .. } => {
            assert_eq!(pattern, "hp | hq", "top-level `|` alternation round-trips");
            assert!(matches!(term.as_ref(), SurfaceExpr::Ident(_, n) if n == "h"));
        }
        other => unreachable!("expected SurfaceTactic::RCases, got {:?}", other),
    }
}

#[test]
fn test_rcases_three_way_alternation_pattern_parses() {
    let t = by_tactics("by rcases h with hp | hq | hr");
    assert_eq!(
        t.len(),
        1,
        "three-way alternation is one tactic, got {:?}",
        t
    );
    match &t[0] {
        SurfaceTactic::RCases { pattern, .. } => {
            assert_eq!(pattern, "hp | hq | hr", "3-way `|` alternation round-trips");
        }
        other => unreachable!("expected SurfaceTactic::RCases, got {:?}", other),
    }
}

#[test]
fn test_obtain_or_alternation_pattern_parses() {
    // `obtain hp | hq := h` captures the alternation as the pattern text.
    let t = by_tactics("by obtain hp | hq := h");
    match &t[0] {
        SurfaceTactic::Obtain { pattern, term, .. } => {
            assert_eq!(
                pattern, "hp | hq",
                "obtain top-level alternation round-trips"
            );
            assert!(matches!(term.as_ref(), SurfaceExpr::Ident(_, n) if n == "h"));
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
}

#[test]
fn test_obtain_nested_and_or_alternation_pattern_parses() {
    // A `|` alternation INSIDE an anonymous-constructor field: `⟨hp, hq | hr⟩`.
    let t = by_tactics("by obtain ⟨hp, hq | hr⟩ := h");
    match &t[0] {
        SurfaceTactic::Obtain { pattern, .. } => {
            assert_eq!(
                pattern, "⟨hp, hq | hr⟩",
                "nested field alternation round-trips inside ⟨⟩"
            );
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
}

#[test]
fn test_rintro_paren_or_alternation_pattern_parses() {
    // `rintro (hp | hq)`: the parens group the alternation; the captured pattern
    // text drops the parens, yielding `hp | hq`.
    let t = by_tactics("by rintro (hp | hq)");
    match &t[0] {
        SurfaceTactic::RIntro { patterns, .. } => {
            assert_eq!(
                patterns.len(),
                1,
                "one parenthesized pattern, got {:?}",
                patterns
            );
            assert_eq!(
                patterns[0], "hp | hq",
                "paren-grouped alternation round-trips"
            );
        }
        other => unreachable!("expected SurfaceTactic::RIntro, got {:?}", other),
    }
}

#[test]
fn test_rcases_alternation_then_sequenced_continuation_parses_separately() {
    // The same-line `|` alternation must be consumed, but a `;`-sequenced
    // continuation must remain a separate tactic — the alternation reader must
    // not swallow it, and the dangling `|` must not trigger decl recovery (the
    // `Pipe` raw-decl error this fix removes).
    let t = by_tactics("by rcases h with hp | hq; exact hp");
    assert_eq!(
        t.len(),
        2,
        "alternation tactic plus `exact hp` expected, got {:?}",
        t
    );
    match &t[0] {
        SurfaceTactic::RCases { pattern, .. } => {
            assert_eq!(pattern, "hp | hq");
        }
        other => unreachable!("expected SurfaceTactic::RCases first, got {:?}", other),
    }
}
