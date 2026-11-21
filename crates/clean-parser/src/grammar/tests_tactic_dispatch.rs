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
fn test_subst_contextual_names_keep_sibling_tactics() {
    let tactics =
        by_tactics("by\n  subst constructor left «first»\n  constructor\n  subst right; rfl");
    let [SurfaceTactic::Named { name, args, .. }, constructor, subst, reflexivity] =
        tactics.as_slice()
    else {
        panic!("expected four tactics: {tactics:?}");
    };
    assert_eq!(name, "subst");
    let [first, second, third] = args.as_slice() else {
        panic!("expected three arguments: {args:?}");
    };
    for (arg, text, escaped) in [
        (first, "constructor", false),
        (second, "left", false),
        (third, "first", true),
    ] {
        assert!(matches!(arg, SurfaceExpr::Ident(_, name)
            if *name == crate::SurfaceName::component(text, escaped)));
    }
    assert!(
        matches!(constructor, SurfaceTactic::Named { name, args, .. }
        if name == "constructor" && args.is_empty())
    );
    assert!(matches!(subst, SurfaceTactic::Named { name, args, .. }
        if name == "subst" && matches!(args.as_slice(), [SurfaceExpr::Ident(_, arg)]
            if *arg == crate::SurfaceName::component("right", false))));
    assert!(matches!(reflexivity, SurfaceTactic::Named { name, .. } if name == "rfl"));
}

#[test]
fn test_subst_argument_layout_uses_the_tactic_block_column() {
    let tactics = by_tactics("by\n  · skip; subst\n      right\n    constructor");
    let [SurfaceTactic::FocusBlock(_, body)] = tactics.as_slice() else {
        panic!("expected a bullet: {tactics:?}");
    };
    let [_, subst, constructor] = body.as_slice() else {
        panic!("expected three tactics inside the bullet: {body:?}");
    };
    assert!(matches!(subst, SurfaceTactic::Named { name, args, .. }
        if name == "subst" && matches!(args.as_slice(), [SurfaceExpr::Ident(_, arg)]
            if *arg == crate::SurfaceName::component("right", false))));
    assert!(matches!(constructor, SurfaceTactic::Named { name, .. } if name == "constructor"));
}

#[test]
fn test_subst_requires_an_identifier_before_the_next_tactic() {
    for source in ["subst\n  constructor", "subst nomatch"] {
        let file = format!("example : True := by\n  {source}");
        let report = Parser::parse_file_with_diagnostics(&file).expect("recover malformed subst");
        assert!(
            report.diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("expected at least one identifier in subst")),
            "{source}: {:?}",
            report.diagnostics
        );
    }
}

#[test]
fn test_have_underscore_preserves_proof_and_following_tactic() {
    for input in [
        "by\n  have _ := h.symm\n  exact h",
        "by\n  have _ : b = a := h.symm\n  exact h",
        "by\n  have _ : b = a := by\n    exact h.symm\n  exact h",
        "by\n  have _ := by\n    exact h.symm\n  exact h",
        "by\n  have _ : Nat → True\n    | _ => True.intro\n  exact h",
    ] {
        let tactics = by_tactics(input);
        assert_eq!(tactics.len(), 2, "{input}");
        let SurfaceTactic::Have(_, Some(name), _, proof) = &tactics[0] else {
            panic!("expected inaccessible have: {tactics:?}");
        };
        assert_eq!(name, &tactic::inaccessible_hypothesis());
        assert!(matches!(
            proof.as_ref(),
            SurfaceTactic::Term(..) | SurfaceTactic::Named { .. }
        ));
        assert!(matches!(&tactics[1], SurfaceTactic::Named { name, .. } if name == "exact"));
    }
}

#[test]
fn test_have_equations_leave_the_enclosing_case_pipe() {
    for continuation in ["    trivial\n", ""] {
        // The empty continuation tests a pipe immediately after the local
        // equation, without another tactic masking the arm-list boundary.
        let tactics = by_tactics(&format!(
            "by\n  cases b with\n  | false =>\n    have _ : Bool → Bool → True\n      | false, false | true, true => True.intro\n      | _, _ => True.intro\n{continuation}  | true =>\n    trivial",
        ));
        let SurfaceTactic::Cases(_, _, _, alts) = &tactics[0] else {
            panic!("expected cases: {tactics:?}");
        };
        assert_eq!(alts.len(), 2, "local equations must not consume a case");
    }
}

#[test]
fn test_grouped_declaration_equations_cannot_take_a_dedented_case_arrow() {
    let input = "example (b : Bool) : True := by\n  cases b with\n  | false =>\n    have _ : Bool → True\n      | false\n  | true =>\n        exact True.intro";
    let report = Parser::parse_file_with_diagnostics(input).expect("recover malformed proof");
    assert!(
        report.diagnostics.iter().any(|diagnostic| {
            diagnostic.message.contains("expected FatArrow, got Pipe")
                && diagnostic.recovery_start.line == 6
        }),
        "{:?}",
        report.diagnostics
    );
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
fn change_location_keeps_escaped_at_in_the_term() {
    let tactics = by_tactics("by\n  change P «at» at h k ⊢\n  exact h");
    let [SurfaceTactic::Named { name, args, .. }, SurfaceTactic::Named { name: next, .. }] =
        tactics.as_slice()
    else {
        panic!("expected change followed by exact: {tactics:?}");
    };
    assert_eq!(name, "change");
    assert_eq!(next, "exact");
    let [SurfaceExpr::App(_, _, term_args), SurfaceExpr::Ident(_, first), SurfaceExpr::Ident(_, second), SurfaceExpr::Ident(_, goal)] =
        args.as_slice()
    else {
        panic!("expected term plus three locations: {args:?}");
    };
    assert!(matches!(&term_args[..], [arg] if matches!(&arg.expr,
        SurfaceExpr::Ident(_, name) if name.to_string() == "at")));
    assert_eq!(first.to_string(), "h");
    assert_eq!(second.to_string(), "k");
    assert!(goal.same_syntax(&crate::SurfaceName::generated_path("⊢")));
}

#[test]
fn change_location_accepts_contextual_hypothesis_names() {
    let tactics = by_tactics("by\n  change P at right left\n  exact right");
    let [SurfaceTactic::Named { name, args, .. }, SurfaceTactic::Named { name: next, .. }] =
        tactics.as_slice()
    else {
        panic!("expected change followed by exact: {tactics:?}");
    };
    assert_eq!(name, "change");
    assert_eq!(next, "exact");
    let [_, SurfaceExpr::Ident(_, right), SurfaceExpr::Ident(_, left)] = args.as_slice() else {
        panic!("expected term and both hypothesis names: {args:?}");
    };
    assert_eq!(right.to_string(), "right");
    assert_eq!(left.to_string(), "left");
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
            matches!(&args[0], SurfaceExpr::Ident(_, n) if (n).name() == crate::SurfaceName::generated_path("h").name()),
            "first arg should be bare ident `h`, got {:?}",
            args[0]
        );
        assert!(
            matches!(&args[1], SurfaceExpr::Ident(_, n) if (n).name() == crate::SurfaceName::generated_path("hn").name()),
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
    // `with`-clause the pattern is Lean's empty tuple `⟨⟩`.
    assert!(
        matches!(&t[1], SurfaceTactic::RCases { targets, pattern, .. }
            if matches!(&targets[0].term, SurfaceExpr::Ident(_, n) if (n).name() == crate::SurfaceName::generated_path("h").name()) && pattern == "⟨⟩"),
        "second tactic should be `rcases h` (RCases, pattern `⟨⟩`), got {:?}",
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
                matches!(term.as_deref(), Some(SurfaceExpr::Ident(_, n)) if (n).name() == crate::SurfaceName::generated_path("h").name()),
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
            assert!(
                matches!(term.as_deref(), Some(SurfaceExpr::Ident(_, n)) if (n).name() == crate::SurfaceName::generated_path("h").name())
            );
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
}

// -------------------------------------------------------------------------
// Tactic-mode `let ⟨a, b⟩ := e` (2026-08-26)
//
// `parse_tactic_let` opened with `expect_ident("let")`, so `⟨` was rejected
// outright ("expected identifier in let, got LAngle") and the whole
// declaration fell into parser recovery, which then MISNAMED the failure
// after the preceding tactic. It now mirrors `parse_tactic_have`'s
// destructuring route into `obtain`'s pattern engine.
// -------------------------------------------------------------------------

#[test]
fn test_tactic_let_tuple_pattern_desugars_to_obtain() {
    let t = by_tactics("by let ⟨a, b⟩ := p");
    assert_eq!(t.len(), 1, "expected a single tactic, got {:?}", t);
    match &t[0] {
        SurfaceTactic::Obtain {
            pattern, ty, term, ..
        } => {
            assert_eq!(pattern, "⟨a, b⟩", "pattern text round-trips");
            assert!(ty.is_none(), "no type ascription expected");
            assert!(
                matches!(term.as_deref(), Some(SurfaceExpr::Ident(_, n)) if (n).name() == crate::SurfaceName::generated_path("p").name()),
                "RHS term should be `p`, got {:?}",
                term
            );
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
}

#[test]
fn test_tactic_let_nested_pattern_and_ascription_desugar_to_obtain() {
    match &by_tactics("by let ⟨⟨a, b⟩, c⟩ := h")[0] {
        SurfaceTactic::Obtain { pattern, .. } => {
            assert_eq!(pattern, "⟨⟨a, b⟩, c⟩", "nested pattern text round-trips");
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
    match &by_tactics("by let ⟨x, hx⟩ : Foo := h")[0] {
        SurfaceTactic::Obtain { pattern, ty, .. } => {
            assert_eq!(pattern, "⟨x, hx⟩");
            assert!(ty.is_some(), "type ascription `: Foo` should be captured");
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
}

/// Control: the NAMED `let` forms must be untouched by the destructuring
/// route — they still produce `SurfaceTactic::Let`, with and without the
/// `: T` ascription.
#[test]
fn test_named_tactic_let_still_parses_to_let() {
    match &by_tactics("by let x := p")[0] {
        SurfaceTactic::Let(_, name, ty, _) => {
            assert_eq!(
                (name).name(),
                crate::SurfaceName::generated_path("x").name()
            );
            assert!(ty.is_none());
        }
        other => unreachable!("expected SurfaceTactic::Let, got {:?}", other),
    }
    match &by_tactics("by let x : Nat := p")[0] {
        SurfaceTactic::Let(_, name, ty, _) => {
            assert_eq!(
                (name).name(),
                crate::SurfaceName::generated_path("x").name()
            );
            assert!(ty.is_some(), "`: Nat` should be captured");
        }
        other => unreachable!("expected SurfaceTactic::Let, got {:?}", other),
    }
}

#[test]
fn test_anonymous_tactic_let_keeps_both_bindings_and_continuation() {
    let source = "def t (h : Nat) : Nat := by\n  let _ := h\n  let _ : Nat := h\n  exact h";
    let decls = crate::parse_file_with_tactics_located(source, &TacticPatterns::new())
        .expect("both anonymous lets must parse without recovery");
    let [SurfaceDecl::Def { val, .. }] = decls.as_slice() else {
        panic!("expected one definition, got {decls:?}");
    };
    let SurfaceExpr::ByTactic(_, tactics) = val.as_ref() else {
        panic!("expected a tactic block, got {val:?}");
    };
    let [SurfaceTactic::Let(_, inferred, None, first), SurfaceTactic::Let(_, typed, Some(ty), second), continuation] =
        tactics.as_slice()
    else {
        panic!("expected two lets and their continuation, got {tactics:?}");
    };
    for name in [inferred, typed] {
        assert_eq!(name, &tactic::inaccessible_hypothesis());
    }
    for value in [first, second] {
        assert!(
            matches!(value.as_ref(), SurfaceExpr::Ident(_, name) if name.is_unescaped_component("h"))
        );
    }
    assert!(
        matches!(ty.as_ref(), SurfaceExpr::Ident(_, name) if name.is_unescaped_component("Nat"))
    );
    assert!(matches!(continuation, SurfaceTactic::Named { name, .. } if name == "exact"));
}

#[test]
fn test_anonymous_tactic_let_requires_a_value() {
    let source = "def t : Nat := by\n  let _ : Nat :=\n";
    assert!(crate::parse_file_with_tactics_located(source, &TacticPatterns::new()).is_err());
}

#[test]
fn tactic_let_i_keeps_named_anonymous_and_inaccessible_binders() {
    let tactics = by_tactics(
        "by\n  letI d : Decidable p := w\n  letI : Decidable q := by exact v\n  letI := w\n  letI _ := w\n  exact d",
    );
    let [SurfaceTactic::LetI(_, d, Some(ty), w), SurfaceTactic::LetI(_, typed, Some(_), proof), SurfaceTactic::LetI(_, inferred, None, _), SurfaceTactic::LetI(_, inaccessible, None, _), continuation] =
        tactics.as_slice()
    else {
        panic!("expected four local instance declarations and their continuation: {tactics:?}");
    };
    assert!(d.is_unescaped_component("d"));
    assert!(matches!(ty.as_ref(), SurfaceExpr::App(..)));
    assert!(matches!(w.as_ref(), SurfaceExpr::Ident(_, n) if n.is_unescaped_component("w")));
    assert!(matches!(proof.as_ref(), SurfaceExpr::ByTactic(_, t) if t.len() == 1));
    assert!(typed.is_unescaped_component("this"));
    assert!(inferred.is_unescaped_component("this"));
    assert_eq!(inaccessible, &super::tactic::inaccessible_hypothesis());
    assert!(matches!(continuation, SurfaceTactic::Named { name, .. } if name == "exact"));
}

#[test]
fn tactic_let_i_binder_telescope_scopes_the_result_and_value() {
    for (declaration, binder) in [
        ("letI f (x : Nat) : Nat := x", "f"),
        ("letI (x : Nat) : Nat := x", "this"),
    ] {
        let tactics = by_tactics(&format!("by\n  {declaration}\n  exact {binder}"));
        let [SurfaceTactic::LetI(_, name, Some(ty), val), _] = tactics.as_slice() else {
            panic!("expected local function and continuation: {tactics:?}");
        };
        assert!(name.is_unescaped_component(binder));
        assert!(matches!(ty.as_ref(), SurfaceExpr::Pi(_, bs, _) if bs.len() == 1));
        assert!(matches!(val.as_ref(), SurfaceExpr::Lambda(_, bs, _) if bs.len() == 1));
    }
}

#[test]
fn tactic_let_i_requires_a_value_and_refuses_patterns() {
    for decl in [
        "letI d : Nat",
        "letI (x, y) := (1, 2)",
        "letI f (x, y) := (1, 2)",
        "letI ⟨x, y⟩ := p",
        "letI (x) := p",
        "letI f[x] := p",
    ] {
        let source = format!("def t : Nat := by\n  {decl}\n  exact 1");
        assert!(
            crate::parse_file_with_tactics_located(&source, &TacticPatterns::new()).is_err(),
            "{source}"
        );
    }
}

#[test]
fn test_tactic_binding_types_keep_arguments_inside_record_fields() {
    let body = "  typed := by\n    have h : And True True := ⟨True.intro, True.intro⟩\n    let xs : List Nat := []\n    exact h.1";
    for source in [
        format!("def r : Record where\n{body}\n  tail := 1"),
        format!("def r : Record := {{\n{body},\n  tail := 1\n}}"),
    ] {
        let decls = crate::parse_file_with_tactics_located(&source, &TacticPatterns::new())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        let [SurfaceDecl::Def { val, .. }] = decls.as_slice() else {
            panic!("expected one definition, got {decls:?}");
        };
        let SurfaceExpr::StructLit { fields, .. } = val.as_ref() else {
            panic!("expected record fields, got {val:?}");
        };
        let [typed, tail] = fields.as_slice() else {
            panic!("expected both fields, got {fields:?}");
        };
        assert!(typed.name.is_unescaped_component("typed"));
        assert!(tail.name.is_unescaped_component("tail"));
        let SurfaceExpr::ByTactic(_, tactics) = &typed.val else {
            panic!("expected field tactics, got {:?}", typed.val);
        };
        let [SurfaceTactic::Have(_, _, Some(have_ty), _), SurfaceTactic::Let(_, _, Some(let_ty), _), continuation] =
            tactics.as_slice()
        else {
            panic!("expected have, let and their continuation, got {tactics:?}");
        };
        for (ty, constructor, count, last) in
            [(have_ty, "And", 2, "True"), (let_ty, "List", 1, "Nat")]
        {
            let SurfaceExpr::App(_, head, args) = ty.as_ref() else {
                panic!("expected applied type, got {ty:?}");
            };
            assert!(
                matches!(head.as_ref(), SurfaceExpr::Ident(_, name) if name.is_unescaped_component(constructor))
            );
            assert_eq!(args.len(), count);
            assert!(
                matches!(&args[count - 1].expr, SurfaceExpr::Ident(_, name) if name.is_unescaped_component(last))
            );
        }
        assert!(matches!(continuation, SurfaceTactic::Named { name, .. } if name == "exact"));
    }
}

#[test]
fn test_tactic_binding_type_in_field_still_needs_assignment() {
    for tactic in ["have h : And True True", "let xs : List Nat"] {
        let source = format!("def r : Record where\n  typed := by\n    {tactic}\n  tail := 1");
        assert!(
            crate::parse_file_with_tactics_located(&source, &TacticPatterns::new()).is_err(),
            "{source}"
        );
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
            assert!(
                matches!(term.as_deref(), Some(SurfaceExpr::Ident(_, n)) if (n).name() == crate::SurfaceName::generated_path("h").name())
            );
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
                matches!(term.as_deref(), Some(SurfaceExpr::App(..))),
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
        SurfaceTactic::RCases {
            targets, pattern, ..
        } => {
            assert_eq!(pattern, "⟨hp, hq⟩", "pattern text round-trips");
            assert!(
                matches!(&targets[0].term, SurfaceExpr::Ident(_, n) if (n).name() == crate::SurfaceName::generated_path("h").name()),
                "scrutinee should be the hypothesis `h`, got {:?}",
                targets
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
        SurfaceTactic::RCases {
            pattern, targets, ..
        } => {
            assert_eq!(pattern, "h2");
            assert!(
                matches!(&targets[0].term, SurfaceExpr::Ident(_, n) if (n).name() == crate::SurfaceName::generated_path("h").name())
            );
        }
        other => unreachable!("expected SurfaceTactic::RCases, got {:?}", other),
    }
}

#[test]
fn test_rcases_no_with_defaults_to_empty_tuple() {
    // `rcases h` with no `with`-clause takes Lean's `RCasesPatt.tuple tk []`
    // (`evalRCases`), which splits one level.
    let t = by_tactics("by rcases h");
    match &t[0] {
        SurfaceTactic::RCases {
            pattern, targets, ..
        } => {
            assert_eq!(pattern, "⟨⟩");
            assert!(
                matches!(&targets[0].term, SurfaceExpr::Ident(_, n) if (n).name() == crate::SurfaceName::generated_path("h").name())
            );
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
        SurfaceTactic::RCases {
            pattern, targets, ..
        } => {
            assert_eq!(pattern, "hp | hq", "top-level `|` alternation round-trips");
            assert!(
                matches!(&targets[0].term, SurfaceExpr::Ident(_, n) if (n).name() == crate::SurfaceName::generated_path("h").name())
            );
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
            assert!(
                matches!(term.as_deref(), Some(SurfaceExpr::Ident(_, n)) if (n).name() == crate::SurfaceName::generated_path("h").name())
            );
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

#[test]
fn intro_constructor_pattern_binds_into_later_template_tactics() {
    let tactics = by_tactics("by\n  intro z ⟨_, «case»⟩ w\n  exact «case»");
    let expanded = crate::instantiate_tactic_template(&tactics, &[], &[], true).unwrap();
    let [SurfaceTactic::Paren(_, steps), SurfaceTactic::Named { name, args, .. }] =
        expanded.as_slice()
    else {
        panic!("expected an intro followed by exact");
    };
    assert_eq!(name, "exact");
    let [SurfaceTactic::Named { name: first, .. }, SurfaceTactic::IntroPattern(_, SurfacePattern::Ctor(_, fields)), SurfaceTactic::Named { name: last, .. }] =
        steps.as_slice()
    else {
        panic!("expected an introduction on either side of the pattern");
    };
    assert_eq!((first.as_str(), last.as_str()), ("intro", "intro"));
    let [SurfacePattern::Wildcard, SurfacePattern::Var(bound)] = fields.as_slice() else {
        panic!("expected the two constructor fields");
    };
    let [SurfaceExpr::Ident(_, used)] = args.as_slice() else {
        panic!("expected exact to use the second field");
    };
    assert!(bound.same_syntax(used));
}
