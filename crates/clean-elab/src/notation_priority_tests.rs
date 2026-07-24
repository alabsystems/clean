// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for notation priority, associativity, and mixfix elaboration.

use super::notation_priority::*;

// ============================================================================
// Associativity
// ============================================================================

#[test]
fn test_associativity_display() {
    assert_eq!(Associativity::Left.to_string(), "left");
    assert_eq!(Associativity::Right.to_string(), "right");
    assert_eq!(Associativity::None.to_string(), "none");
}

#[test]
fn test_associativity_equality() {
    assert_eq!(Associativity::Left, Associativity::Left);
    assert_ne!(Associativity::Left, Associativity::Right);
    assert_ne!(Associativity::Right, Associativity::None);
}

// ============================================================================
// NotationPriority
// ============================================================================

#[test]
fn test_priority_constants() {
    assert_eq!(NotationPriority::LEAD.value(), 0);
    assert_eq!(NotationPriority::DEFAULT.value(), 0);
    assert_eq!(NotationPriority::ADD.value(), 65);
    assert_eq!(NotationPriority::MUL.value(), 70);
    assert_eq!(NotationPriority::MAX.value(), 1024);
    assert_eq!(NotationPriority::APP.value(), 1024);
}

#[test]
fn test_priority_ordering() {
    assert!(NotationPriority::MUL.is_tighter_than(NotationPriority::ADD));
    assert!(NotationPriority::MAX.is_tighter_than(NotationPriority::MUL));
    assert!(!NotationPriority::ADD.is_tighter_than(NotationPriority::MUL));
    assert!(!NotationPriority::ADD.is_tighter_than(NotationPriority::ADD));
}

#[test]
fn test_priority_new_and_value() {
    let p = NotationPriority::new(42);
    assert_eq!(p.value(), 42);
}

#[test]
fn test_priority_display() {
    assert_eq!(NotationPriority::ADD.to_string(), "65");
    assert_eq!(NotationPriority::new(999).to_string(), "999");
}

#[test]
fn test_priority_derived_ord() {
    let mut priorities = [
        NotationPriority::MUL,
        NotationPriority::LEAD,
        NotationPriority::ADD,
        NotationPriority::MAX,
    ];
    priorities.sort();
    assert_eq!(priorities[0], NotationPriority::LEAD);
    assert_eq!(priorities[1], NotationPriority::ADD);
    assert_eq!(priorities[2], NotationPriority::MUL);
    assert_eq!(priorities[3], NotationPriority::MAX);
}

// ============================================================================
// MixfixPattern
// ============================================================================

#[test]
fn test_mixfix_infix_pattern() {
    let pat = MixfixPattern::infix("+");
    assert_eq!(pat.arity(), 2);
    assert_eq!(pat.leading_token(), Some("+"));
    assert!(pat.is_led());
    assert_eq!(pat.tokens(), vec!["+"]);
}

#[test]
fn test_mixfix_prefix_pattern() {
    let pat = MixfixPattern::prefix("-");
    assert_eq!(pat.arity(), 1);
    assert_eq!(pat.leading_token(), Some("-"));
    assert!(!pat.is_led());
}

#[test]
fn test_mixfix_postfix_pattern() {
    let pat = MixfixPattern::postfix("!");
    assert_eq!(pat.arity(), 1);
    assert_eq!(pat.leading_token(), Some("!"));
    assert!(pat.is_led());
}

#[test]
fn test_mixfix_general_pattern() {
    // if _ then _ else _
    let pat = MixfixPattern::new(vec![
        MixfixItem::Token("if".to_owned()),
        MixfixItem::Arg(0),
        MixfixItem::Token("then".to_owned()),
        MixfixItem::Arg(1),
        MixfixItem::Token("else".to_owned()),
        MixfixItem::Arg(2),
    ]);
    assert_eq!(pat.arity(), 3);
    assert_eq!(pat.leading_token(), Some("if"));
    assert!(!pat.is_led());
    assert_eq!(pat.tokens(), vec!["if", "then", "else"]);
}

#[test]
fn test_mixfix_angle_bracket_pattern() {
    // ⟨_, _⟩
    let pat = MixfixPattern::new(vec![
        MixfixItem::Token("\u{27E8}".to_owned()),
        MixfixItem::Arg(0),
        MixfixItem::Token(",".to_owned()),
        MixfixItem::Arg(1),
        MixfixItem::Token("\u{27E9}".to_owned()),
    ]);
    assert_eq!(pat.arity(), 2);
    assert_eq!(pat.leading_token(), Some("\u{27E8}"));
    assert!(!pat.is_led());
}

#[test]
fn test_mixfix_items_accessor() {
    let pat = MixfixPattern::prefix("!");
    assert_eq!(pat.items().len(), 2);
    assert!(matches!(&pat.items()[0], MixfixItem::Token(t) if t == "!"));
    assert!(matches!(&pat.items()[1], MixfixItem::Arg(0)));
}

// ============================================================================
// PriorityEntry
// ============================================================================

#[test]
fn test_entry_basic_construction() {
    let entry = PriorityEntry::new(
        "HAdd.hAdd",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    );
    assert_eq!(entry.name(), "HAdd.hAdd");
    assert_eq!(entry.priority(), NotationPriority::ADD);
    assert_eq!(entry.assoc(), Associativity::Left);
    assert!(entry.is_active());
}

#[test]
fn test_entry_with_namespace() {
    let entry = PriorityEntry::new(
        "Nat.add",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    )
    .with_namespace("Nat");
    assert_eq!(entry.name(), "Nat.add");
}

#[test]
fn test_entry_with_local() {
    let entry = PriorityEntry::new(
        "local_op",
        MixfixPattern::infix("@"),
        NotationPriority::new(50),
        Associativity::None,
    )
    .with_local();
    assert!(entry.is_active());
}

#[test]
fn test_entry_deactivate_reactivate() {
    let mut entry = PriorityEntry::new(
        "f",
        MixfixPattern::prefix("!"),
        NotationPriority::new(100),
        Associativity::None,
    );
    assert!(entry.is_active());
    entry.deactivate();
    assert!(!entry.is_active());
    entry.reactivate();
    assert!(entry.is_active());
}

// ============================================================================
// PriorityConflict
// ============================================================================

#[test]
fn test_conflict_display() {
    let c = PriorityConflict {
        token: "+".to_owned(),
        priority: NotationPriority::ADD,
        first: "HAdd.hAdd".to_owned(),
        second: "custom_add".to_owned(),
    };
    let s = c.to_string();
    assert!(s.contains("65"));
    assert!(s.contains("+"));
    assert!(s.contains("HAdd.hAdd"));
    assert!(s.contains("custom_add"));
}

// ============================================================================
// PriorityScopeStack
// ============================================================================

#[test]
fn test_scope_stack_empty() {
    let stack = PriorityScopeStack::new();
    assert!(stack.is_empty());
    assert_eq!(stack.depth(), 0);
    assert_eq!(stack.current_priority(), NotationPriority::DEFAULT);
}

#[test]
fn test_scope_stack_push_pop() {
    let mut stack = PriorityScopeStack::new();
    stack.push_scope(false);
    assert_eq!(stack.depth(), 1);
    assert!(!stack.is_empty());

    stack.push_scope(false);
    assert_eq!(stack.depth(), 2);

    let indices = stack.pop_scope();
    assert!(indices.is_some());
    assert_eq!(stack.depth(), 1);

    let indices = stack.pop_scope();
    assert!(indices.is_some());
    assert!(stack.is_empty());
}

#[test]
fn test_scope_stack_pop_empty_returns_none() {
    let mut stack = PriorityScopeStack::new();
    assert!(stack.pop_scope().is_none());
}

#[test]
fn test_scope_stack_priority_inheritance() {
    let mut stack = PriorityScopeStack::new();
    stack.set_root_priority(NotationPriority::new(50));
    assert_eq!(stack.current_priority(), NotationPriority::new(50));

    // Push scope that inherits parent priority
    stack.push_scope(true);
    assert_eq!(stack.current_priority(), NotationPriority::new(50));

    // Push scope without inheritance
    stack.push_scope(false);
    // Falls through to the inherited scope below
    assert_eq!(stack.current_priority(), NotationPriority::new(50));

    stack.pop_scope();
    stack.pop_scope();
    assert_eq!(stack.current_priority(), NotationPriority::new(50));
}

#[test]
fn test_scope_stack_track_entries() {
    let mut stack = PriorityScopeStack::new();
    stack.push_scope(false);
    stack.track_entry(0);
    stack.track_entry(1);

    let indices = stack.pop_scope().expect("should return indices");
    assert_eq!(indices, vec![0, 1]);
}

// ============================================================================
// PriorityResolver: basic registration and resolution
// ============================================================================

#[test]
fn test_resolver_empty() {
    let resolver = PriorityResolver::new();
    assert_eq!(resolver.entry_count(), 0);
    assert_eq!(resolver.active_count(), 0);
    assert!(resolver.resolve("+").is_none());
    assert!(resolver.resolve_all("+").is_empty());
    assert!(!resolver.has_active_notation("+"));
}

#[test]
fn test_resolver_default() {
    let resolver = PriorityResolver::default();
    assert_eq!(resolver.entry_count(), 0);
}

#[test]
fn test_resolver_register_and_resolve() {
    let mut resolver = PriorityResolver::new();
    resolver.register(PriorityEntry::new(
        "HAdd.hAdd",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));

    assert_eq!(resolver.entry_count(), 1);
    assert_eq!(resolver.active_count(), 1);
    assert!(resolver.has_active_notation("+"));

    let entry = resolver.resolve("+").expect("should resolve");
    assert_eq!(entry.name(), "HAdd.hAdd");
    assert_eq!(entry.priority(), NotationPriority::ADD);
    assert_eq!(entry.assoc(), Associativity::Left);
}

#[test]
fn test_resolver_highest_priority_wins() {
    let mut resolver = PriorityResolver::new();
    resolver.register(PriorityEntry::new(
        "low_add",
        MixfixPattern::infix("+"),
        NotationPriority::new(50),
        Associativity::Left,
    ));
    resolver.register(PriorityEntry::new(
        "high_add",
        MixfixPattern::infix("+"),
        NotationPriority::new(80),
        Associativity::Left,
    ));
    resolver.register(PriorityEntry::new(
        "mid_add",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));

    let best = resolver.resolve("+").expect("should resolve");
    assert_eq!(best.name(), "high_add");
}

#[test]
fn test_resolver_resolve_all_descending_order() {
    let mut resolver = PriorityResolver::new();
    resolver.register(PriorityEntry::new(
        "low",
        MixfixPattern::infix("+"),
        NotationPriority::new(10),
        Associativity::Left,
    ));
    resolver.register(PriorityEntry::new(
        "high",
        MixfixPattern::infix("+"),
        NotationPriority::new(90),
        Associativity::Left,
    ));
    resolver.register(PriorityEntry::new(
        "mid",
        MixfixPattern::infix("+"),
        NotationPriority::new(50),
        Associativity::Left,
    ));

    let all = resolver.resolve_all("+");
    assert_eq!(all.len(), 3);
    assert_eq!(all[0].name(), "high");
    assert_eq!(all[1].name(), "mid");
    assert_eq!(all[2].name(), "low");
}

// ============================================================================
// Conflict detection
// ============================================================================

#[test]
fn test_resolver_no_conflict_same_assoc() {
    let mut resolver = PriorityResolver::new();
    resolver.register(PriorityEntry::new(
        "a",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    resolver.register(PriorityEntry::new(
        "b",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    assert!(resolver.detect_conflicts().is_empty());
}

#[test]
fn test_resolver_conflict_different_assoc_same_priority() {
    let mut resolver = PriorityResolver::new();
    resolver.register(PriorityEntry::new(
        "left_add",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    resolver.register(PriorityEntry::new(
        "right_add",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Right,
    ));

    let conflicts = resolver.detect_conflicts();
    assert_eq!(conflicts.len(), 1);
    assert_eq!(conflicts[0].token, "+");
    assert_eq!(conflicts[0].priority, NotationPriority::ADD);
}

#[test]
fn test_resolver_no_conflict_different_priority() {
    let mut resolver = PriorityResolver::new();
    resolver.register(PriorityEntry::new(
        "left_add",
        MixfixPattern::infix("+"),
        NotationPriority::new(65),
        Associativity::Left,
    ));
    resolver.register(PriorityEntry::new(
        "right_add",
        MixfixPattern::infix("+"),
        NotationPriority::new(66),
        Associativity::Right,
    ));
    assert!(resolver.detect_conflicts().is_empty());
}

// ============================================================================
// Deactivation / reactivation
// ============================================================================

#[test]
fn test_resolver_deactivate_hides_entry() {
    let mut resolver = PriorityResolver::new();
    let idx = resolver.register(PriorityEntry::new(
        "f",
        MixfixPattern::prefix("!"),
        NotationPriority::new(100),
        Associativity::None,
    ));

    assert!(resolver.resolve("!").is_some());
    resolver.deactivate(idx);
    assert!(resolver.resolve("!").is_none());
    assert_eq!(resolver.active_count(), 0);
    assert_eq!(resolver.entry_count(), 1);
}

#[test]
fn test_resolver_reactivate_restores_entry() {
    let mut resolver = PriorityResolver::new();
    let idx = resolver.register(PriorityEntry::new(
        "f",
        MixfixPattern::prefix("!"),
        NotationPriority::new(100),
        Associativity::None,
    ));

    resolver.deactivate(idx);
    assert!(resolver.resolve("!").is_none());
    resolver.reactivate(idx);
    assert!(resolver.resolve("!").is_some());
}

// ============================================================================
// Scoped registration and pop
// ============================================================================

#[test]
fn test_resolver_scope_deactivates_on_pop() {
    let mut resolver = PriorityResolver::new();

    // Register in root scope
    resolver.register(PriorityEntry::new(
        "global_add",
        MixfixPattern::infix("+"),
        NotationPriority::new(65),
        Associativity::Left,
    ));

    // Enter scope and register a higher-priority override
    resolver.push_scope(false);
    resolver.register(PriorityEntry::new(
        "local_add",
        MixfixPattern::infix("+"),
        NotationPriority::new(80),
        Associativity::Left,
    ));

    assert_eq!(
        resolver.resolve("+").expect("should resolve").name(),
        "local_add"
    );
    assert_eq!(resolver.scope_depth(), 1);

    // Pop scope: local_add deactivated, global_add remains
    resolver.pop_scope();
    assert_eq!(resolver.scope_depth(), 0);
    assert_eq!(
        resolver.resolve("+").expect("should resolve").name(),
        "global_add"
    );
}

#[test]
fn test_resolver_nested_scopes() {
    let mut resolver = PriorityResolver::new();

    resolver.register(PriorityEntry::new(
        "base",
        MixfixPattern::infix("*"),
        NotationPriority::new(10),
        Associativity::Left,
    ));

    resolver.push_scope(false);
    resolver.register(PriorityEntry::new(
        "mid",
        MixfixPattern::infix("*"),
        NotationPriority::new(50),
        Associativity::Left,
    ));

    resolver.push_scope(false);
    resolver.register(PriorityEntry::new(
        "inner",
        MixfixPattern::infix("*"),
        NotationPriority::new(90),
        Associativity::Left,
    ));

    assert_eq!(resolver.resolve("*").expect("inner").name(), "inner");

    resolver.pop_scope();
    assert_eq!(resolver.resolve("*").expect("mid").name(), "mid");

    resolver.pop_scope();
    assert_eq!(resolver.resolve("*").expect("base").name(), "base");
}

#[test]
fn test_resolver_scope_priority_inheritance() {
    let mut resolver = PriorityResolver::new();
    assert_eq!(resolver.current_scope_priority(), NotationPriority::DEFAULT);

    resolver.push_scope(true);
    assert_eq!(resolver.current_scope_priority(), NotationPriority::DEFAULT);

    resolver.pop_scope();
}

// ============================================================================
// Mixed operator types
// ============================================================================

#[test]
fn test_resolver_multiple_tokens() {
    let mut resolver = PriorityResolver::new();
    resolver.register(PriorityEntry::new(
        "HAdd.hAdd",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    resolver.register(PriorityEntry::new(
        "HMul.hMul",
        MixfixPattern::infix("*"),
        NotationPriority::MUL,
        Associativity::Left,
    ));
    resolver.register(PriorityEntry::new(
        "Neg.neg",
        MixfixPattern::prefix("-"),
        NotationPriority::new(75),
        Associativity::None,
    ));
    resolver.register(PriorityEntry::new(
        "List.cons",
        MixfixPattern::infix("::"),
        NotationPriority::new(67),
        Associativity::Right,
    ));

    assert_eq!(resolver.entry_count(), 4);
    assert_eq!(resolver.resolve("+").expect("+").name(), "HAdd.hAdd");
    assert_eq!(resolver.resolve("*").expect("*").name(), "HMul.hMul");
    assert_eq!(
        resolver.resolve("-").expect("-").assoc(),
        Associativity::None
    );
    assert_eq!(
        resolver.resolve("::").expect("::").assoc(),
        Associativity::Right
    );
    assert!(resolver.resolve("?").is_none());
}

#[test]
fn test_resolver_deactivated_entry_excluded_from_conflicts() {
    let mut resolver = PriorityResolver::new();
    let idx = resolver.register(PriorityEntry::new(
        "left",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    resolver.register(PriorityEntry::new(
        "right",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Right,
    ));
    // Conflict exists
    assert_eq!(resolver.detect_conflicts().len(), 1);

    // Deactivate one side: no more conflict
    resolver.deactivate(idx);
    assert!(resolver.detect_conflicts().is_empty());
}

#[test]
fn test_resolver_deactivate_out_of_bounds_is_safe() {
    let mut resolver = PriorityResolver::new();
    // Should not panic
    resolver.deactivate(999);
    resolver.reactivate(999);
}
