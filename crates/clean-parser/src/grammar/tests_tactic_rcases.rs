// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser tests for the rcases pattern grammar (`Init/RCases.lean`): the
//! clear pattern `-`, the explicit pattern `@pat`, grouping of parenthesized
//! alternatives, and `rintro`'s binder groups and trailing type.

use super::*;

fn by_tactics(input: &str) -> Vec<SurfaceTactic> {
    let e = Parser::parse_expr(input).expect("parse should succeed");
    match e {
        SurfaceExpr::ByTactic(_, t) => t,
        other => unreachable!("expected ByTactic, got {:?}", other),
    }
}

fn rintro_patterns(tactic: &SurfaceTactic) -> (&[String], usize) {
    match tactic {
        SurfaceTactic::RIntro {
            patterns,
            pattern_types,
            ..
        } => (patterns, pattern_types.len()),
        other => unreachable!("expected SurfaceTactic::RIntro, got {:?}", other),
    }
}

fn rcases_pattern(tactic: &SurfaceTactic) -> (&str, usize) {
    match tactic {
        SurfaceTactic::RCases {
            pattern,
            pattern_types,
            ..
        } => (pattern, pattern_types.len()),
        other => unreachable!("expected SurfaceTactic::RCases, got {:?}", other),
    }
}

fn obtain_pattern(tactic: &SurfaceTactic) -> &str {
    match tactic {
        SurfaceTactic::Obtain { pattern, .. } => pattern,
        other => unreachable!("expected SurfaceTactic::Obtain, got {:?}", other),
    }
}

#[test]
fn test_rintro_clear_field_parses_trust_ir_basic_429() {
    // `TrustIr/Basic.lean:429`, which died "expected identifier in rcases
    // pattern, got Minus"; the next line's tactic stays a separate tactic.
    let t = by_tactics("by\n  rintro ⟨hlo, -⟩\n  omega");
    assert_eq!(t.len(), 2, "rintro then omega, got {t:?}");
    assert_eq!(rintro_patterns(&t[0]).0, ["⟨hlo, -⟩"]);
}

#[test]
fn test_rintro_top_level_clear_patterns_parse() {
    let t = by_tactics("by rintro - h -");
    assert_eq!(rintro_patterns(&t[0]).0, ["-", "h", "-"]);
}

#[test]
fn test_obtain_clear_patterns_parse() {
    let t = by_tactics("by obtain ⟨addr, -, -, h, -⟩ := e");
    assert_eq!(obtain_pattern(&t[0]), "⟨addr, -, -, h, -⟩");
    let t = by_tactics("by obtain - := h");
    assert_eq!(obtain_pattern(&t[0]), "-");
}

#[test]
fn test_rcases_clear_in_alternation_parses() {
    let t = by_tactics("by rcases h with ⟨a, -⟩ | -");
    assert_eq!(rcases_pattern(&t[0]).0, "⟨a, -⟩ | -");
}

#[test]
fn test_explicit_patterns_parse() {
    let t = by_tactics("by rcases h with @⟨a, b⟩");
    assert_eq!(rcases_pattern(&t[0]).0, "@⟨a, b⟩");
    let t = by_tactics("by rintro @⟨a, -⟩ @h");
    assert_eq!(rintro_patterns(&t[0]).0, ["@⟨a, -⟩", "@h"]);
    let t = by_tactics("by obtain @⟨a, b⟩ := h");
    assert_eq!(obtain_pattern(&t[0]), "@⟨a, b⟩");
    // A parenthesized operand keeps its parens: the `@` covers the group.
    let t = by_tactics("by rcases h with @(a | b) | c");
    assert_eq!(rcases_pattern(&t[0]).0, "@(a | b) | c");
}

#[test]
fn test_explicit_pattern_refuses_whitespace_after_at() {
    // `"@" noWs rcasesPat`: `@ ⟨a, b⟩` is not an explicit pattern.
    let parsed = Parser::parse_expr("by rcases h with @ ⟨a, b⟩");
    let accepted_as_explicit = matches!(
        &parsed,
        Ok(SurfaceExpr::ByTactic(_, t))
            if t.iter().any(|tac| matches!(tac, SurfaceTactic::RCases { pattern, .. } if pattern.starts_with('@')))
    );
    assert!(
        !accepted_as_explicit,
        "`@ ⟨a, b⟩` must not parse as an explicit pattern: {parsed:?}"
    );
}

#[test]
fn test_parenthesized_alternative_keeps_its_grouping() {
    // `(hp | hq) | hr` is a two-way alternation whose first arm splits again;
    // flattening it to `hp | hq | hr` would change which field each name binds.
    let t = by_tactics("by rcases h with (hp | hq) | hr");
    assert_eq!(rcases_pattern(&t[0]).0, "(hp | hq) | hr");
    // A typed alternative keeps its type on that alternative alone.
    let t = by_tactics("by rcases h with hr | (h : p)");
    assert_eq!(rcases_pattern(&t[0]), ("hr | (h : #0)", 1));
    // A lone parenthesized pattern still drops its parens.
    let t = by_tactics("by rintro (hp | hq)");
    assert_eq!(rintro_patterns(&t[0]).0, ["hp | hq"]);
}

#[test]
fn test_empty_tuple_pattern_parses() {
    let t = by_tactics("by rcases h with ⟨⟩");
    assert_eq!(rcases_pattern(&t[0]).0, "⟨⟩");
}

#[test]
fn test_rintro_binder_group_types_each_member() {
    // `rintroPat.binder`: `(x y : Nat)` introduces two hypotheses of type Nat.
    let t = by_tactics("by rintro (x y : Nat) ⟨a, b⟩");
    assert_eq!(
        rintro_patterns(&t[0]),
        (
            &[
                "x : #0".to_string(),
                "y : #0".to_string(),
                "⟨a, b⟩".to_string()
            ][..],
            1
        )
    );
    // A one-member group is the typed pattern itself.
    let t = by_tactics("by rintro (h : p)");
    assert_eq!(rintro_patterns(&t[0]), (&["h : #0".to_string()][..], 1));
    // Untyped group: its members are plain patterns.
    let t = by_tactics("by rintro (x -)");
    assert_eq!(
        rintro_patterns(&t[0]),
        (&["x".to_string(), "-".to_string()][..], 0)
    );
}

#[test]
fn test_rintro_trailing_type_types_untyped_patterns() {
    // `rintro (pat)+ (" : " term)?`: the trailing type covers every pattern
    // without one of its own; a group's own type wins.
    let t = by_tactics("by rintro x ⟨a, b⟩ : T");
    assert_eq!(
        rintro_patterns(&t[0]),
        (&["x : #0".to_string(), "⟨a, b⟩ : #0".to_string()][..], 1)
    );
    let t = by_tactics("by rintro (x : A) y : B");
    assert_eq!(
        rintro_patterns(&t[0]),
        (&["x : #0".to_string(), "y : #1".to_string()][..], 2)
    );
}

#[test]
fn test_obtain_accepts_every_pattern_start() {
    let t = by_tactics("by obtain (hp | hq) := h");
    assert_eq!(obtain_pattern(&t[0]), "hp | hq");
    let t = by_tactics("by obtain -|h := h");
    assert_eq!(obtain_pattern(&t[0]), "- | h");
}

#[test]
fn test_obtain_without_value_takes_a_type() {
    // `obtain pat (: T)? (:= e)?`: `obtain ⟨h1, h2⟩ : P ∧ Q` asserts `P ∧ Q`.
    let t = by_tactics("by\n  obtain ⟨h1, h2⟩ : P ∧ Q\n  · exact x\n  exact y");
    assert_eq!(t.len(), 3, "obtain, the bullet, exact: {t:?}");
    match &t[0] {
        SurfaceTactic::Obtain {
            pattern, ty, term, ..
        } => {
            assert_eq!(pattern, "⟨h1, h2⟩");
            assert!(ty.is_some(), "the asserted type is kept");
            assert!(term.is_none(), "no `:= e`, got {term:?}");
        }
        other => unreachable!("expected SurfaceTactic::Obtain, got {other:?}"),
    }
    // With neither a type nor a value there is nothing to destructure.
    let parsed = Parser::parse_expr("by obtain ⟨h1, h2⟩");
    let accepted = matches!(
        &parsed,
        Ok(SurfaceExpr::ByTactic(_, t)) if t.iter().any(|tac| matches!(tac, SurfaceTactic::Obtain { .. }))
    );
    assert!(!accepted, "`obtain pat` alone must not parse: {parsed:?}");
}

fn rcases_targets(tactic: &SurfaceTactic) -> Vec<(Option<String>, String)> {
    match tactic {
        SurfaceTactic::RCases { targets, .. } => targets
            .iter()
            .map(|target| {
                (
                    target
                        .eq_name
                        .as_ref()
                        .and_then(|name| name.source_spelling()),
                    format!("{:?}", target.term),
                )
            })
            .collect(),
        other => unreachable!("expected SurfaceTactic::RCases, got {:?}", other),
    }
}

#[test]
fn test_rcases_named_equation_target_parses_trust_ir_memory_safety_727() {
    // `TrustIr/Proofs/MemorySafety.lean:727`: `casesTarget := (ident " : ")?
    // term`. The `:` used to end the tactic, so the elaborator saw the
    // unknown identifier `hp` and the proof fell to parser recovery.
    let t = by_tactics(
        "by\n  rcases hp : s.lookupValue ptrId with _ | ptrVal\n  · simp only [hp] at hOk\n  exact x",
    );
    assert_eq!(t.len(), 3, "rcases, the bullet, exact: {t:?}");
    assert_eq!(rcases_pattern(&t[0]), ("_ | ptrVal", 0));
    let targets = rcases_targets(&t[0]);
    assert_eq!(targets.len(), 1, "{targets:?}");
    assert_eq!(targets[0].0.as_deref(), Some("hp"));
    assert!(targets[0].1.contains("lookupValue"), "{targets:?}");
}

#[test]
fn test_rcases_comma_separated_targets_parse_in_order() {
    // `casesTarget,*`: a bare target, then a named one; the tuple pattern is
    // kept whole (the elaborator distributes its components).
    let t = by_tactics("by rcases h1, e : f x with ⟨a, b⟩");
    assert_eq!(t.len(), 1, "{t:?}");
    assert_eq!(rcases_pattern(&t[0]), ("⟨a, b⟩", 0));
    let targets = rcases_targets(&t[0]);
    assert_eq!(targets.len(), 2, "{targets:?}");
    assert_eq!(targets[0].0, None);
    assert_eq!(targets[1].0.as_deref(), Some("e"));
    // A typed term target in parentheses is a term, not an equation name.
    let t = by_tactics("by rcases (h : p) with hp");
    assert_eq!(rcases_targets(&t[0])[0].0, None);
}
