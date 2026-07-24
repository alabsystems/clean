// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended notation scoping (`notation_scope_ext`).

use clean_kernel::name::Name;
use clean_kernel::Expr;

use crate::notation_scope_ext::{
    compare_precedence, filter_by_fixity, merge_notation_scopes, notation_conflicts,
    parse_precedence, NotationScopeEntry, NotationScopeKind, NotationScopeManager, PrecedenceLevel,
};

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

fn dummy_expr(s: &str) -> Expr {
    Expr::const_str(s)
}

fn mk_entry(
    pattern: &str,
    expansion_name: &str,
    priority: u32,
    kind: NotationScopeKind,
) -> NotationScopeEntry {
    NotationScopeEntry::new(pattern, dummy_expr(expansion_name), priority, kind)
}

fn mk_infix(
    pattern: &str,
    expansion_name: &str,
    priority: u32,
    kind: NotationScopeKind,
) -> NotationScopeEntry {
    NotationScopeEntry::new(pattern, dummy_expr(expansion_name), priority, kind)
        .with_fixity(false, true, false)
}

fn mk_prefix(
    pattern: &str,
    expansion_name: &str,
    priority: u32,
    kind: NotationScopeKind,
) -> NotationScopeEntry {
    NotationScopeEntry::new(pattern, dummy_expr(expansion_name), priority, kind)
        .with_fixity(true, false, false)
}

fn mk_postfix(
    pattern: &str,
    expansion_name: &str,
    priority: u32,
    kind: NotationScopeKind,
) -> NotationScopeEntry {
    NotationScopeEntry::new(pattern, dummy_expr(expansion_name), priority, kind)
        .with_fixity(false, false, true)
}

// ---------------------------------------------------------------------------
// PrecedenceLevel
// ---------------------------------------------------------------------------

#[test]
fn test_parse_precedence_max() {
    let p = parse_precedence("max").expect("should parse max");
    assert_eq!(p.value(), 1024);
    assert!(p.is_max());
}

#[test]
fn test_parse_precedence_lead() {
    let p = parse_precedence("lead").expect("should parse lead");
    assert_eq!(p.value(), 0);
    assert!(!p.is_max());
}

#[test]
fn test_parse_precedence_numeric() {
    let p = parse_precedence("65").expect("should parse 65");
    assert_eq!(p.value(), 65);
    assert!(!p.is_max());
}

#[test]
fn test_parse_precedence_1024_is_max() {
    let p = parse_precedence("1024").expect("should parse 1024");
    assert_eq!(p.value(), 1024);
    assert!(p.is_max());
}

#[test]
fn test_parse_precedence_exceeds_max() {
    let err = parse_precedence("1025");
    assert!(err.is_err());
}

#[test]
fn test_parse_precedence_invalid() {
    let err = parse_precedence("abc");
    assert!(err.is_err());
}

#[test]
fn test_parse_precedence_whitespace_trimmed() {
    let p = parse_precedence("  70  ").expect("should trim whitespace");
    assert_eq!(p.value(), 70);
}

#[test]
fn test_compare_precedence_basic() {
    let a = PrecedenceLevel::new(65);
    let b = PrecedenceLevel::new(70);
    assert_eq!(compare_precedence(&a, &b), std::cmp::Ordering::Less);
    assert_eq!(compare_precedence(&b, &a), std::cmp::Ordering::Greater);
    assert_eq!(compare_precedence(&a, &a), std::cmp::Ordering::Equal);
}

#[test]
fn test_compare_precedence_max_vs_numeric() {
    let max = PrecedenceLevel::MAX;
    let num = PrecedenceLevel::new(1023);
    assert_eq!(compare_precedence(&max, &num), std::cmp::Ordering::Greater);
}

#[test]
fn test_precedence_level_ord_trait() {
    let a = PrecedenceLevel::new(10);
    let b = PrecedenceLevel::new(20);
    assert!(a < b);
    assert!(b > a);
    assert_eq!(PrecedenceLevel::MAX, PrecedenceLevel::new(1024));
}

// ---------------------------------------------------------------------------
// NotationScopeKind
// ---------------------------------------------------------------------------

#[test]
fn test_scope_kind_display() {
    assert_eq!(format!("{}", NotationScopeKind::Global), "global");
    assert_eq!(format!("{}", NotationScopeKind::Local), "local");
    assert_eq!(format!("{}", NotationScopeKind::Protected), "protected");
    let ns = Name::from_string("Nat");
    assert_eq!(format!("{}", NotationScopeKind::Scoped(ns)), "scoped(Nat)");
}

#[test]
fn test_scope_kind_equality() {
    let a = NotationScopeKind::Scoped(Name::from_string("Nat"));
    let b = NotationScopeKind::Scoped(Name::from_string("Nat"));
    let c = NotationScopeKind::Scoped(Name::from_string("Int"));
    assert_eq!(a, b);
    assert_ne!(a, c);
    assert_ne!(NotationScopeKind::Global, NotationScopeKind::Local);
}

// ---------------------------------------------------------------------------
// NotationScopeEntry visibility
// ---------------------------------------------------------------------------

#[test]
fn test_entry_global_always_visible() {
    let entry = mk_entry("+", "HAdd.hAdd", 65, NotationScopeKind::Global);
    assert!(entry.is_visible(&[]));
    assert!(entry.is_visible(&[Name::from_string("Nat")]));
}

#[test]
fn test_entry_local_always_visible() {
    let entry = mk_entry("+", "local_add", 65, NotationScopeKind::Local);
    assert!(entry.is_visible(&[]));
}

#[test]
fn test_entry_protected_always_visible() {
    let entry = mk_entry("+", "protected_add", 65, NotationScopeKind::Protected);
    assert!(entry.is_visible(&[]));
}

#[test]
fn test_entry_scoped_visible_only_when_open() {
    let nat = Name::from_string("Nat");
    let entry = mk_entry("+", "Nat.add", 70, NotationScopeKind::Scoped(nat.clone()));
    assert!(!entry.is_visible(&[]));
    assert!(!entry.is_visible(&[Name::from_string("Int")]));
    assert!(entry.is_visible(&[nat]));
}

#[test]
fn test_entry_fixity_flags() {
    let entry = mk_entry("+", "add", 65, NotationScopeKind::Global).with_fixity(false, true, false);
    assert!(!entry.is_prefix);
    assert!(entry.is_infix);
    assert!(!entry.is_postfix);
}

// ---------------------------------------------------------------------------
// NotationScopeManager registration
// ---------------------------------------------------------------------------

#[test]
fn test_register_and_count() {
    let mut mgr = NotationScopeManager::new();
    mgr.register_notation(mk_entry("+", "HAdd.hAdd", 65, NotationScopeKind::Global))
        .expect("should register");
    mgr.register_notation(mk_entry("-", "HSub.hSub", 65, NotationScopeKind::Global))
        .expect("should register");
    assert_eq!(mgr.entry_count(), 2);
    assert_eq!(mgr.token_count(), 2);
}

#[test]
fn test_register_empty_pattern_rejected() {
    let mut mgr = NotationScopeManager::new();
    let entry = mk_entry("", "bad", 0, NotationScopeKind::Global);
    assert!(mgr.register_notation(entry).is_err());
}

#[test]
fn test_register_multiple_same_token() {
    let mut mgr = NotationScopeManager::new();
    mgr.register_notation(mk_entry("+", "HAdd.hAdd", 65, NotationScopeKind::Global))
        .expect("reg1");
    let nat = Name::from_string("Nat");
    mgr.register_notation(mk_entry("+", "Nat.add", 70, NotationScopeKind::Scoped(nat)))
        .expect("reg2");
    assert_eq!(mgr.entry_count(), 2);
    assert_eq!(mgr.token_count(), 1);
}

// ---------------------------------------------------------------------------
// resolve_notation
// ---------------------------------------------------------------------------

#[test]
fn test_resolve_global_notation() {
    let mut mgr = NotationScopeManager::new();
    mgr.register_notation(mk_entry("+", "HAdd.hAdd", 65, NotationScopeKind::Global))
        .expect("reg");
    let anon = Name::anon();
    let results = mgr.resolve_notation("+", &anon);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].pattern, "+");
}

#[test]
fn test_resolve_scoped_only_when_open() {
    let mut mgr = NotationScopeManager::new();
    let nat = Name::from_string("Nat");
    mgr.register_notation(mk_entry(
        "++",
        "Nat.append",
        65,
        NotationScopeKind::Scoped(nat.clone()),
    ))
    .expect("reg");

    // Not visible with different scope
    let int = Name::from_string("Int");
    assert!(mgr.resolve_notation("++", &int).is_empty());

    // Visible with Nat scope
    let results = mgr.resolve_notation("++", &nat);
    assert_eq!(results.len(), 1);
}

#[test]
fn test_resolve_priority_order() {
    let mut mgr = NotationScopeManager::new();
    mgr.register_notation(mk_entry("+", "low", 10, NotationScopeKind::Global))
        .expect("low");
    mgr.register_notation(mk_entry("+", "high", 90, NotationScopeKind::Global))
        .expect("high");
    mgr.register_notation(mk_entry("+", "mid", 50, NotationScopeKind::Global))
        .expect("mid");

    let anon = Name::anon();
    let results = mgr.resolve_notation("+", &anon);
    assert_eq!(results.len(), 3);
    assert_eq!(results[0].priority, 90);
    assert_eq!(results[1].priority, 50);
    assert_eq!(results[2].priority, 10);
}

#[test]
fn test_resolve_nonexistent_token() {
    let mgr = NotationScopeManager::new();
    let anon = Name::anon();
    assert!(mgr.resolve_notation("???", &anon).is_empty());
}

// ---------------------------------------------------------------------------
// active_notations
// ---------------------------------------------------------------------------

#[test]
fn test_active_notations_empty_scopes() {
    let mut mgr = NotationScopeManager::new();
    mgr.register_notation(mk_entry("+", "add", 65, NotationScopeKind::Global))
        .expect("g");
    let nat = Name::from_string("Nat");
    mgr.register_notation(mk_entry("-", "Nat.sub", 65, NotationScopeKind::Scoped(nat)))
        .expect("s");

    let active = mgr.active_notations(&[]);
    assert_eq!(active.len(), 1);
    assert_eq!(active[0].pattern, "+");
}

#[test]
fn test_active_notations_with_scope() {
    let mut mgr = NotationScopeManager::new();
    let nat = Name::from_string("Nat");
    mgr.register_notation(mk_entry("+", "add", 65, NotationScopeKind::Global))
        .expect("g");
    mgr.register_notation(mk_entry(
        "-",
        "Nat.sub",
        65,
        NotationScopeKind::Scoped(nat.clone()),
    ))
    .expect("s");

    let active = mgr.active_notations(&[nat]);
    assert_eq!(active.len(), 2);
}

// ---------------------------------------------------------------------------
// check_ambiguity
// ---------------------------------------------------------------------------

#[test]
fn test_no_ambiguity_different_priorities() {
    let mut mgr = NotationScopeManager::new();
    mgr.register_notation(mk_entry("+", "add1", 65, NotationScopeKind::Global))
        .expect("r1");
    mgr.register_notation(mk_entry("+", "add2", 70, NotationScopeKind::Global))
        .expect("r2");

    let anon = Name::anon();
    assert!(mgr.check_ambiguity("+", &anon).is_none());
}

#[test]
fn test_ambiguity_same_priority() {
    let mut mgr = NotationScopeManager::new();
    mgr.register_notation(mk_entry("+", "add_v1", 65, NotationScopeKind::Global))
        .expect("r1");
    mgr.register_notation(mk_entry("+", "add_v2", 65, NotationScopeKind::Global))
        .expect("r2");

    let anon = Name::anon();
    let amb = mgr.check_ambiguity("+", &anon);
    assert!(amb.is_some());
    assert_eq!(amb.unwrap().len(), 2);
}

#[test]
fn test_no_ambiguity_single_entry() {
    let mut mgr = NotationScopeManager::new();
    mgr.register_notation(mk_entry("+", "add", 65, NotationScopeKind::Global))
        .expect("r");
    let anon = Name::anon();
    assert!(mgr.check_ambiguity("+", &anon).is_none());
}

#[test]
fn test_no_ambiguity_no_entries() {
    let mgr = NotationScopeManager::new();
    let anon = Name::anon();
    assert!(mgr.check_ambiguity("+", &anon).is_none());
}

// ---------------------------------------------------------------------------
// notation_conflicts
// ---------------------------------------------------------------------------

#[test]
fn test_conflicts_same_pattern_same_priority_different_expansion() {
    let a = mk_entry("+", "add1", 65, NotationScopeKind::Global);
    let b = mk_entry("+", "add2", 65, NotationScopeKind::Global);
    assert!(notation_conflicts(&a, &b));
}

#[test]
fn test_no_conflict_different_patterns() {
    let a = mk_entry("+", "add", 65, NotationScopeKind::Global);
    let b = mk_entry("-", "sub", 65, NotationScopeKind::Global);
    assert!(!notation_conflicts(&a, &b));
}

#[test]
fn test_no_conflict_different_priorities() {
    let a = mk_entry("+", "add1", 65, NotationScopeKind::Global);
    let b = mk_entry("+", "add2", 70, NotationScopeKind::Global);
    assert!(!notation_conflicts(&a, &b));
}

#[test]
fn test_no_conflict_same_expansion() {
    let a = mk_entry("+", "add", 65, NotationScopeKind::Global);
    let b = mk_entry("+", "add", 65, NotationScopeKind::Local);
    assert!(!notation_conflicts(&a, &b));
}

// ---------------------------------------------------------------------------
// filter_by_fixity
// ---------------------------------------------------------------------------

#[test]
fn test_filter_by_fixity_infix_only() {
    let prefix = mk_prefix("-", "neg", 75, NotationScopeKind::Global);
    let infix = mk_infix("-", "sub", 65, NotationScopeKind::Global);
    let entries: Vec<&NotationScopeEntry> = vec![&prefix, &infix];
    let result = filter_by_fixity(&entries, false, true, false);
    assert_eq!(result.len(), 1);
    assert!(result[0].is_infix);
}

#[test]
fn test_filter_by_fixity_prefix_only() {
    let prefix = mk_prefix("!", "not", 75, NotationScopeKind::Global);
    let infix = mk_infix("+", "add", 65, NotationScopeKind::Global);
    let entries: Vec<&NotationScopeEntry> = vec![&prefix, &infix];
    let result = filter_by_fixity(&entries, true, false, false);
    assert_eq!(result.len(), 1);
    assert!(result[0].is_prefix);
}

#[test]
fn test_filter_by_fixity_postfix_only() {
    let postfix = mk_postfix("?", "Option.get", 100, NotationScopeKind::Global);
    let infix = mk_infix("+", "add", 65, NotationScopeKind::Global);
    let entries: Vec<&NotationScopeEntry> = vec![&postfix, &infix];
    let result = filter_by_fixity(&entries, false, false, true);
    assert_eq!(result.len(), 1);
    assert!(result[0].is_postfix);
}

#[test]
fn test_filter_by_fixity_multiple_flags() {
    let prefix = mk_prefix("-", "neg", 75, NotationScopeKind::Global);
    let infix = mk_infix("+", "add", 65, NotationScopeKind::Global);
    let postfix = mk_postfix("?", "opt", 100, NotationScopeKind::Global);
    let entries: Vec<&NotationScopeEntry> = vec![&prefix, &infix, &postfix];
    let result = filter_by_fixity(&entries, true, true, false);
    assert_eq!(result.len(), 2);
}

#[test]
fn test_filter_by_fixity_none_match() {
    let entry = mk_entry("+", "add", 65, NotationScopeKind::Global);
    let entries: Vec<&NotationScopeEntry> = vec![&entry];
    let result = filter_by_fixity(&entries, true, false, false);
    assert!(result.is_empty());
}

// ---------------------------------------------------------------------------
// merge_notation_scopes
// ---------------------------------------------------------------------------

#[test]
fn test_merge_empty_scopes() {
    let merged = merge_notation_scopes(&[]);
    assert_eq!(merged.entry_count(), 0);
}

#[test]
fn test_merge_single_scope() {
    let mut mgr = NotationScopeManager::new();
    mgr.register_notation(mk_entry("+", "add", 65, NotationScopeKind::Global))
        .expect("reg");
    let merged = merge_notation_scopes(&[&mgr]);
    assert_eq!(merged.entry_count(), 1);
}

#[test]
fn test_merge_two_scopes() {
    let mut mgr1 = NotationScopeManager::new();
    mgr1.register_notation(mk_entry("+", "add", 65, NotationScopeKind::Global))
        .expect("r1");
    let mut mgr2 = NotationScopeManager::new();
    mgr2.register_notation(mk_entry("-", "sub", 65, NotationScopeKind::Global))
        .expect("r2");
    let merged = merge_notation_scopes(&[&mgr1, &mgr2]);
    assert_eq!(merged.entry_count(), 2);
    assert_eq!(merged.token_count(), 2);
}

#[test]
fn test_merge_preserves_priority_order() {
    let mut mgr1 = NotationScopeManager::new();
    mgr1.register_notation(mk_entry("+", "low", 10, NotationScopeKind::Global))
        .expect("lo");
    let mut mgr2 = NotationScopeManager::new();
    mgr2.register_notation(mk_entry("+", "high", 90, NotationScopeKind::Global))
        .expect("hi");
    let merged = merge_notation_scopes(&[&mgr1, &mgr2]);

    let anon = Name::anon();
    let results = merged.resolve_notation("+", &anon);
    assert_eq!(results.len(), 2);
    assert_eq!(results[0].priority, 90);
    assert_eq!(results[1].priority, 10);
}

#[test]
fn test_merge_preserves_scoped_entries() {
    let mut mgr = NotationScopeManager::new();
    let nat = Name::from_string("Nat");
    mgr.register_notation(mk_entry(
        "+",
        "Nat.add",
        70,
        NotationScopeKind::Scoped(nat.clone()),
    ))
    .expect("reg");
    let merged = merge_notation_scopes(&[&mgr]);

    // Not visible without Nat
    let anon = Name::anon();
    assert!(merged.resolve_notation("+", &anon).is_empty());

    // Visible with Nat
    let results = merged.resolve_notation("+", &nat);
    assert_eq!(results.len(), 1);
}

// ---------------------------------------------------------------------------
// Integration / edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_scoped_entry_shadows_global_when_open() {
    let mut mgr = NotationScopeManager::new();
    let nat = Name::from_string("Nat");
    mgr.register_notation(mk_entry("+", "HAdd.hAdd", 65, NotationScopeKind::Global))
        .expect("global");
    mgr.register_notation(mk_entry(
        "+",
        "Nat.add",
        70,
        NotationScopeKind::Scoped(nat.clone()),
    ))
    .expect("scoped");

    // With Nat open: scoped (70) is first
    let results = mgr.resolve_notation("+", &nat);
    assert_eq!(results.len(), 2);
    assert_eq!(results[0].priority, 70);
    assert_eq!(results[1].priority, 65);
}

#[test]
fn test_default_manager_is_empty() {
    let mgr = NotationScopeManager::default();
    assert_eq!(mgr.entry_count(), 0);
    assert_eq!(mgr.token_count(), 0);
}

#[test]
fn test_precedence_level_zero() {
    let p = PrecedenceLevel::new(0);
    assert_eq!(p.value(), 0);
    assert!(!p.is_max());
}

#[test]
fn test_entry_with_all_fixity_flags() {
    let entry = mk_entry("|>", "pipe", 20, NotationScopeKind::Global).with_fixity(true, true, true);
    assert!(entry.is_prefix);
    assert!(entry.is_infix);
    assert!(entry.is_postfix);
}

#[test]
fn test_ambiguity_scoped_hidden_entries_excluded() {
    let mut mgr = NotationScopeManager::new();
    let nat = Name::from_string("Nat");
    let int = Name::from_string("Int");
    mgr.register_notation(mk_entry(
        "+",
        "Nat.add",
        65,
        NotationScopeKind::Scoped(nat.clone()),
    ))
    .expect("nat");
    mgr.register_notation(mk_entry(
        "+",
        "Int.add",
        65,
        NotationScopeKind::Scoped(int.clone()),
    ))
    .expect("int");

    // Only Nat open: no ambiguity (only one visible)
    assert!(mgr.check_ambiguity("+", &nat).is_none());

    // Both open via active_notations check
    let active = mgr.active_notations(&[nat, int]);
    assert_eq!(active.len(), 2);
}

#[test]
fn test_parse_precedence_zero() {
    let p = parse_precedence("0").expect("should parse 0");
    assert_eq!(p.value(), 0);
    assert!(!p.is_max());
}

#[test]
fn test_parse_precedence_boundary_1024() {
    let p = parse_precedence("1024").expect("should parse 1024");
    assert_eq!(p.value(), 1024);
    assert!(p.is_max());
}
