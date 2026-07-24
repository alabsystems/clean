// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended notation elaboration.

use clean_kernel::{Expr, Name};

use super::notation_ext::*;
use super::notation_priority::{MixfixItem, MixfixPattern, NotationPriority};

// ============================================================================
// Helpers
// ============================================================================

fn mk_name(s: &str) -> Name {
    Name::from_string(s)
}

fn mk_entry(
    name: &str,
    pattern: MixfixPattern,
    kind: NotationKindExt,
    priority: u32,
) -> ExtNotationEntry {
    ExtNotationEntry::new(
        mk_name(name),
        pattern,
        Expr::const_str(name),
        NotationPriority::new(priority),
        kind,
    )
}

fn infix_pattern(token: &str) -> MixfixPattern {
    MixfixPattern::infix(token)
}

fn prefix_pattern(token: &str) -> MixfixPattern {
    MixfixPattern::prefix(token)
}

fn postfix_pattern(token: &str) -> MixfixPattern {
    MixfixPattern::postfix(token)
}

// ============================================================================
// NotationKindExt
// ============================================================================

#[test]
fn test_kind_ext_associativity_infix_left() {
    assert_eq!(
        NotationKindExt::InfixLeft.associativity(),
        super::notation_priority::Associativity::Left
    );
}

#[test]
fn test_kind_ext_associativity_infix_right() {
    assert_eq!(
        NotationKindExt::InfixRight.associativity(),
        super::notation_priority::Associativity::Right
    );
}

#[test]
fn test_kind_ext_associativity_prefix() {
    assert_eq!(
        NotationKindExt::Prefix.associativity(),
        super::notation_priority::Associativity::None
    );
}

#[test]
fn test_kind_ext_is_infix() {
    assert!(NotationKindExt::InfixLeft.is_infix());
    assert!(NotationKindExt::InfixRight.is_infix());
    assert!(NotationKindExt::InfixNone.is_infix());
    assert!(!NotationKindExt::Prefix.is_infix());
    assert!(!NotationKindExt::Postfix.is_infix());
    assert!(!NotationKindExt::Mixfix.is_infix());
}

// ============================================================================
// NotationExtConfig
// ============================================================================

#[test]
fn test_config_defaults() {
    let config = NotationExtConfig::default();
    assert_eq!(config.max_expansion_depth, 64);
    assert!(config.warn_deprecated);
    assert!(config.detect_conflicts);
}

// ============================================================================
// ExtNotationEntry — creation and builder methods
// ============================================================================

#[test]
fn test_entry_new_defaults() {
    let entry = mk_entry(
        "HAdd.hAdd",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    );
    assert_eq!(entry.name, mk_name("HAdd.hAdd"));
    assert_eq!(entry.priority, NotationPriority::new(65));
    assert_eq!(entry.kind, NotationKindExt::InfixLeft);
    assert!(entry.is_active());
    assert!(!entry.deprecated);
    assert!(entry.scope.is_none());
}

#[test]
fn test_entry_with_scope() {
    let entry = mk_entry("foo", prefix_pattern("!"), NotationKindExt::Prefix, 100)
        .with_scope(mk_name("MyNamespace"));
    assert_eq!(entry.scope, Some(mk_name("MyNamespace")));
}

#[test]
fn test_entry_with_deprecation() {
    let entry = mk_entry(
        "old_op",
        infix_pattern("+++"),
        NotationKindExt::InfixLeft,
        50,
    )
    .with_deprecation("use new_op instead");
    assert!(entry.deprecated);
    assert_eq!(entry.deprecation_msg.as_deref(), Some("use new_op instead"));
}

#[test]
fn test_entry_activate_deactivate() {
    let mut entry = mk_entry("foo", infix_pattern("+"), NotationKindExt::InfixLeft, 65);
    assert!(entry.is_active());
    entry.deactivate();
    assert!(!entry.is_active());
    entry.reactivate();
    assert!(entry.is_active());
}

// ============================================================================
// Mixfix patterns — prefix, postfix, infix, general
// ============================================================================

#[test]
fn test_prefix_pattern_shape() {
    let p = prefix_pattern("-");
    assert_eq!(p.arity(), 1);
    assert_eq!(p.leading_token(), Some("-"));
    assert!(!p.is_led());
}

#[test]
fn test_postfix_pattern_shape() {
    let p = postfix_pattern("?");
    assert_eq!(p.arity(), 1);
    assert!(p.is_led()); // starts with Arg
}

#[test]
fn test_infix_pattern_shape() {
    let p = infix_pattern("+");
    assert_eq!(p.arity(), 2);
    assert_eq!(p.leading_token(), Some("+"));
    assert!(p.is_led());
}

#[test]
fn test_mixfix_pattern_custom() {
    // if _ then _ else _
    let p = MixfixPattern::new(vec![
        MixfixItem::Token("if".to_owned()),
        MixfixItem::Arg(0),
        MixfixItem::Token("then".to_owned()),
        MixfixItem::Arg(1),
        MixfixItem::Token("else".to_owned()),
        MixfixItem::Arg(2),
    ]);
    assert_eq!(p.arity(), 3);
    assert_eq!(p.leading_token(), Some("if"));
    assert!(!p.is_led());
    assert_eq!(p.tokens(), vec!["if", "then", "else"]);
}

// ============================================================================
// Precedence and associativity
// ============================================================================

#[test]
fn test_precedence_higher_wins() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "add",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    reg.register(mk_entry(
        "custom_add",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        70,
    ));
    let resolved = reg.resolve("+").unwrap();
    assert_eq!(resolved.name, mk_name("custom_add"));
}

#[test]
fn test_precedence_resolve_all_ordering() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "low",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        10,
    ));
    reg.register(mk_entry(
        "high",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        90,
    ));
    reg.register(mk_entry(
        "mid",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        50,
    ));
    let all = reg.resolve_all("+");
    assert_eq!(all.len(), 3);
    assert_eq!(all[0].name, mk_name("high"));
    assert_eq!(all[1].name, mk_name("mid"));
    assert_eq!(all[2].name, mk_name("low"));
}

// ============================================================================
// Notation expansion
// ============================================================================

#[test]
fn test_expand_infix_notation() {
    let entry = mk_entry(
        "HAdd.hAdd",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    );
    let args = [Expr::const_str("a"), Expr::const_str("b")];
    let config = NotationExtConfig::default();
    let result = expand_notation(&entry, &args, &config).unwrap();
    assert!(result.warnings.is_empty());
    // expansion should be `HAdd.hAdd a b`
    assert!(!format!("{:?}", result.expr).is_empty());
}

#[test]
fn test_expand_arity_mismatch_returns_none() {
    let entry = mk_entry(
        "HAdd.hAdd",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    );
    let args = [Expr::const_str("a")]; // arity 2 needs 2 args
    let config = NotationExtConfig::default();
    assert!(expand_notation(&entry, &args, &config).is_none());
}

#[test]
fn test_expand_prefix_notation() {
    let entry = mk_entry("Neg.neg", prefix_pattern("-"), NotationKindExt::Prefix, 100);
    let args = [Expr::const_str("x")];
    let config = NotationExtConfig::default();
    let result = expand_notation(&entry, &args, &config).unwrap();
    assert!(result.warnings.is_empty());
}

// ============================================================================
// Scoped notation
// ============================================================================

#[test]
fn test_scoped_notation_invisible_when_namespace_closed() {
    let mut reg = ExtNotationRegistry::new();
    let entry = mk_entry("Ns.op", infix_pattern("@@"), NotationKindExt::InfixLeft, 50)
        .with_scope(mk_name("Ns"));
    reg.register(entry);
    assert!(reg.resolve("@@").is_none());
}

#[test]
fn test_scoped_notation_visible_when_namespace_open() {
    let mut reg = ExtNotationRegistry::new();
    let entry = mk_entry("Ns.op", infix_pattern("@@"), NotationKindExt::InfixLeft, 50)
        .with_scope(mk_name("Ns"));
    reg.register(entry);
    reg.open_namespace(mk_name("Ns"));
    assert!(reg.resolve("@@").is_some());
    assert_eq!(reg.resolve("@@").unwrap().name, mk_name("Ns.op"));
}

#[test]
fn test_scoped_notation_hidden_after_close() {
    let mut reg = ExtNotationRegistry::new();
    let entry = mk_entry("Ns.op", infix_pattern("@@"), NotationKindExt::InfixLeft, 50)
        .with_scope(mk_name("Ns"));
    reg.register(entry);
    reg.open_namespace(mk_name("Ns"));
    assert!(reg.resolve("@@").is_some());
    reg.close_namespace(&mk_name("Ns"));
    assert!(reg.resolve("@@").is_none());
}

#[test]
fn test_global_notation_always_visible() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "add",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    assert!(reg.resolve("+").is_some());
}

// ============================================================================
// Overloading and disambiguation
// ============================================================================

#[test]
fn test_overloaded_notations_resolve_all() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "Nat.add",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    reg.register(mk_entry(
        "Int.add",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    let all = reg.resolve_all("+");
    assert_eq!(all.len(), 2);
}

#[test]
fn test_overloaded_higher_priority_preferred() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "Nat.add",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    reg.register(mk_entry(
        "Float.add",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        70,
    ));
    let best = reg.resolve("+").unwrap();
    assert_eq!(best.name, mk_name("Float.add"));
}

// ============================================================================
// Dynamic registration
// ============================================================================

#[test]
fn test_dynamic_registration() {
    let mut reg = ExtNotationRegistry::new();
    assert!(!reg.has_notation(">>>"));
    let idx = reg.register(mk_entry(
        "pipe",
        infix_pattern(">>>"),
        NotationKindExt::InfixLeft,
        20,
    ));
    assert!(reg.has_notation(">>>"));
    assert_eq!(reg.get(idx).unwrap().name, mk_name("pipe"));
}

#[test]
fn test_dynamic_registration_increases_count() {
    let mut reg = ExtNotationRegistry::new();
    assert_eq!(reg.entry_count(), 0);
    reg.register(mk_entry(
        "a",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    reg.register(mk_entry(
        "b",
        prefix_pattern("!"),
        NotationKindExt::Prefix,
        100,
    ));
    assert_eq!(reg.entry_count(), 2);
}

#[test]
fn test_deactivate_hides_notation() {
    let mut reg = ExtNotationRegistry::new();
    let idx = reg.register(mk_entry(
        "op",
        infix_pattern("**"),
        NotationKindExt::InfixLeft,
        50,
    ));
    assert!(reg.has_notation("**"));
    reg.deactivate(idx);
    assert!(!reg.has_notation("**"));
}

#[test]
fn test_reactivate_restores_notation() {
    let mut reg = ExtNotationRegistry::new();
    let idx = reg.register(mk_entry(
        "op",
        infix_pattern("**"),
        NotationKindExt::InfixLeft,
        50,
    ));
    reg.deactivate(idx);
    assert!(!reg.has_notation("**"));
    reg.reactivate(idx);
    assert!(reg.has_notation("**"));
}

// ============================================================================
// Pretty-print integration
// ============================================================================

#[test]
fn test_pretty_fragments_infix() {
    let p = infix_pattern("+");
    let frags = pretty_fragments_from_pattern(&p);
    // Arg(0) Space Token(+) Space Arg(1)
    assert_eq!(frags.len(), 5);
    assert_eq!(frags[0], PrettyFragment::Arg(0));
    assert_eq!(frags[1], PrettyFragment::Space);
    assert_eq!(frags[2], PrettyFragment::Lit("+".to_owned()));
    assert_eq!(frags[3], PrettyFragment::Space);
    assert_eq!(frags[4], PrettyFragment::Arg(1));
}

#[test]
fn test_render_pretty_fragments() {
    let p = infix_pattern("+");
    let frags = pretty_fragments_from_pattern(&p);
    let rendered = render_pretty_fragments(&frags);
    assert_eq!(rendered, "_ + _");
}

#[test]
fn test_pretty_fragments_prefix() {
    let p = prefix_pattern("-");
    let frags = pretty_fragments_from_pattern(&p);
    let rendered = render_pretty_fragments(&frags);
    assert_eq!(rendered, "- _");
}

#[test]
fn test_registry_pretty_print() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "add",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    let frags = reg.pretty_print("+").unwrap();
    let rendered = render_pretty_fragments(&frags);
    assert_eq!(rendered, "_ + _");
}

// ============================================================================
// Conflict detection
// ============================================================================

#[test]
fn test_conflict_detection_associativity_mismatch() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "left_op",
        infix_pattern("^"),
        NotationKindExt::InfixLeft,
        50,
    ));
    reg.register(mk_entry(
        "right_op",
        infix_pattern("^"),
        NotationKindExt::InfixRight,
        50,
    ));
    let conflicts = reg.detect_conflicts();
    assert!(!conflicts.is_empty());
    assert!(conflicts
        .iter()
        .any(|c| c.reason == ConflictReason::AssociativityMismatch));
}

#[test]
fn test_conflict_detection_overlapping_pattern() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "op_a",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    reg.register(mk_entry(
        "op_b",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    let conflicts = reg.detect_conflicts();
    assert!(conflicts
        .iter()
        .any(|c| c.reason == ConflictReason::OverlappingPattern));
}

#[test]
fn test_no_conflict_when_different_tokens() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "add",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    reg.register(mk_entry(
        "mul",
        infix_pattern("*"),
        NotationKindExt::InfixLeft,
        70,
    ));
    let conflicts = reg.detect_conflicts();
    assert!(conflicts.is_empty());
}

#[test]
fn test_conflict_detection_disabled_in_config() {
    let config = NotationExtConfig {
        detect_conflicts: false,
        ..Default::default()
    };
    let mut reg = ExtNotationRegistry::with_config(config);
    reg.register(mk_entry(
        "left",
        infix_pattern("^"),
        NotationKindExt::InfixLeft,
        50,
    ));
    reg.register(mk_entry(
        "right",
        infix_pattern("^"),
        NotationKindExt::InfixRight,
        50,
    ));
    assert!(reg.detect_conflicts().is_empty());
}

#[test]
fn test_conflict_display() {
    let c = NotationConflict {
        token: "^".to_owned(),
        first: mk_name("left_op"),
        second: mk_name("right_op"),
        reason: ConflictReason::AssociativityMismatch,
    };
    let s = c.to_string();
    assert!(s.contains("^"));
    assert!(s.contains("left_op"));
    assert!(s.contains("right_op"));
}

// ============================================================================
// Deprecation warnings
// ============================================================================

#[test]
fn test_deprecated_notation_emits_warning() {
    let entry = mk_entry(
        "old_op",
        infix_pattern("+++"),
        NotationKindExt::InfixLeft,
        50,
    )
    .with_deprecation("use new_op instead");
    let args = [Expr::const_str("a"), Expr::const_str("b")];
    let config = NotationExtConfig::default();
    let result = expand_notation(&entry, &args, &config).unwrap();
    assert_eq!(result.warnings.len(), 1);
    assert!(result.warnings[0].message.contains("use new_op instead"));
}

#[test]
fn test_deprecation_warning_suppressed_by_config() {
    let entry = mk_entry(
        "old_op",
        infix_pattern("+++"),
        NotationKindExt::InfixLeft,
        50,
    )
    .with_deprecation("use new_op instead");
    let args = [Expr::const_str("a"), Expr::const_str("b")];
    let config = NotationExtConfig {
        warn_deprecated: false,
        ..Default::default()
    };
    let result = expand_notation(&entry, &args, &config).unwrap();
    assert!(result.warnings.is_empty());
}

#[test]
fn test_deprecate_by_index() {
    let mut reg = ExtNotationRegistry::new();
    let idx = reg.register(mk_entry(
        "op",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    assert!(!reg.get(idx).unwrap().deprecated);
    reg.deprecate(idx, "deprecated");
    assert!(reg.get(idx).unwrap().deprecated);
}

// ============================================================================
// Edge cases
// ============================================================================

#[test]
fn test_empty_registry_resolve_returns_none() {
    let reg = ExtNotationRegistry::new();
    assert!(reg.resolve("+").is_none());
    assert!(reg.resolve_all("+").is_empty());
}

#[test]
fn test_empty_pattern() {
    let p = MixfixPattern::new(vec![]);
    assert_eq!(p.arity(), 0);
    assert!(p.leading_token().is_none());
    assert!(!p.is_led());
}

#[test]
fn test_expand_zero_arity() {
    // A notation with no arguments (e.g., a keyword)
    let pattern = MixfixPattern::new(vec![MixfixItem::Token("true".to_owned())]);
    let entry = ExtNotationEntry::new(
        mk_name("Bool.true"),
        pattern,
        Expr::const_str("Bool.true"),
        NotationPriority::new(1024),
        NotationKindExt::Mixfix,
    );
    let config = NotationExtConfig::default();
    let result = expand_notation(&entry, &[], &config).unwrap();
    assert!(result.warnings.is_empty());
}

#[test]
fn test_visible_count_tracks_scope() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "global",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    let scoped = mk_entry("scoped", infix_pattern("-"), NotationKindExt::InfixLeft, 65)
        .with_scope(mk_name("Ns"));
    reg.register(scoped);
    // Only global is visible
    assert_eq!(reg.visible_count(), 1);
    reg.open_namespace(mk_name("Ns"));
    assert_eq!(reg.visible_count(), 2);
    reg.close_namespace(&mk_name("Ns"));
    assert_eq!(reg.visible_count(), 1);
}

#[test]
fn test_deactivated_not_in_conflicts() {
    let mut reg = ExtNotationRegistry::new();
    let idx = reg.register(mk_entry(
        "left",
        infix_pattern("^"),
        NotationKindExt::InfixLeft,
        50,
    ));
    reg.register(mk_entry(
        "right",
        infix_pattern("^"),
        NotationKindExt::InfixRight,
        50,
    ));
    // Conflict exists
    assert!(!reg.detect_conflicts().is_empty());
    // Deactivate one side
    reg.deactivate(idx);
    assert!(reg.detect_conflicts().is_empty());
}

#[test]
fn test_scoped_entries_excluded_from_conflicts_when_ns_closed() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "global",
        infix_pattern("^"),
        NotationKindExt::InfixLeft,
        50,
    ));
    let scoped = mk_entry(
        "scoped",
        infix_pattern("^"),
        NotationKindExt::InfixRight,
        50,
    )
    .with_scope(mk_name("Ns"));
    reg.register(scoped);
    // No conflict because scoped is not visible
    assert!(reg.detect_conflicts().is_empty());
    // Open namespace: now conflicts appear
    reg.open_namespace(mk_name("Ns"));
    assert!(!reg.detect_conflicts().is_empty());
}

#[test]
fn test_registry_expand_through_registry() {
    let mut reg = ExtNotationRegistry::new();
    reg.register(mk_entry(
        "add",
        infix_pattern("+"),
        NotationKindExt::InfixLeft,
        65,
    ));
    let args = [Expr::const_str("x"), Expr::const_str("y")];
    let result = reg.expand("+", &args);
    assert!(result.is_some());
}

#[test]
fn test_registry_expand_nonexistent_returns_none() {
    let reg = ExtNotationRegistry::new();
    let args = [Expr::const_str("x")];
    assert!(reg.expand("???", &args).is_none());
}
