// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for notation declaration storage and lookup.

use super::*;
use clean_parser::Span;

/// Helper: create a simple infix notation entry (e.g., `_ + _`).
fn make_infix_entry(token: &str, name: &str, priority: u32) -> NotationEntry {
    NotationEntry {
        name: name.to_owned(),
        pattern: NotationPattern {
            items: vec![
                NotationPatternItem::Placeholder,
                NotationPatternItem::Token(token.to_owned()),
                NotationPatternItem::Placeholder,
            ],
        },
        expansion: SurfaceExpr::Ident(Span::new(0, 0), name.to_owned()),
        priority,
        kind: NotationKind::Infixl,
    }
}

/// Helper: create a prefix notation entry (e.g., `! _`).
fn make_prefix_entry(token: &str, name: &str, priority: u32) -> NotationEntry {
    NotationEntry {
        name: name.to_owned(),
        pattern: NotationPattern {
            items: vec![
                NotationPatternItem::Token(token.to_owned()),
                NotationPatternItem::Placeholder,
            ],
        },
        expansion: SurfaceExpr::Ident(Span::new(0, 0), name.to_owned()),
        priority,
        kind: NotationKind::Prefix,
    }
}

/// Helper: create a mixfix notation entry (e.g., `⟨ _ , _ ⟩`).
fn make_mixfix_entry(tokens: &[&str], name: &str, priority: u32, arity: usize) -> NotationEntry {
    let mut items = Vec::new();
    // Interleave tokens and placeholders
    for (i, &tok) in tokens.iter().enumerate() {
        items.push(NotationPatternItem::Token(tok.to_owned()));
        if i < arity.min(tokens.len()) {
            items.push(NotationPatternItem::Placeholder);
        }
    }
    NotationEntry {
        name: name.to_owned(),
        pattern: NotationPattern { items },
        expansion: SurfaceExpr::Ident(Span::new(0, 0), name.to_owned()),
        priority,
        kind: NotationKind::Notation,
    }
}

#[test]
fn test_register_infix_and_lookup() {
    let mut registry = NotationRegistry::new();
    registry.register(make_infix_entry("+", "HAdd.hAdd", 65));

    let results = registry.lookup("+");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].name, "HAdd.hAdd");
    assert_eq!(results[0].priority, 65);
    assert_eq!(results[0].kind, NotationKind::Infixl);
}

#[test]
fn test_lookup_empty_returns_empty() {
    let registry = NotationRegistry::new();
    assert!(registry.lookup("+").is_empty());
    assert!(registry.lookup("").is_empty());
}

#[test]
fn test_priority_ordering() {
    let mut registry = NotationRegistry::new();
    // Register lower priority first
    registry.register(make_infix_entry("+", "Nat.add", 50));
    // Then higher priority
    registry.register(make_infix_entry("+", "HAdd.hAdd", 65));
    // Then middle priority
    registry.register(make_infix_entry("+", "Int.add", 60));

    let results = registry.lookup("+");
    assert_eq!(results.len(), 3);
    // Descending priority order
    assert_eq!(results[0].name, "HAdd.hAdd");
    assert_eq!(results[0].priority, 65);
    assert_eq!(results[1].name, "Int.add");
    assert_eq!(results[1].priority, 60);
    assert_eq!(results[2].name, "Nat.add");
    assert_eq!(results[2].priority, 50);
}

#[test]
fn test_prefix_notation() {
    let mut registry = NotationRegistry::new();
    registry.register(make_prefix_entry("!", "Not", 100));

    let results = registry.lookup("!");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].name, "Not");
    assert_eq!(results[0].kind, NotationKind::Prefix);
}

#[test]
fn test_postfix_notation() {
    let mut registry = NotationRegistry::new();
    registry.register(NotationEntry {
        name: "Decidable.decide".to_owned(),
        pattern: NotationPattern {
            items: vec![
                NotationPatternItem::Placeholder,
                NotationPatternItem::Token("?".to_owned()),
            ],
        },
        expansion: SurfaceExpr::Ident(Span::new(0, 0), "Decidable.decide".to_owned()),
        priority: 100,
        kind: NotationKind::Postfix,
    });

    let results = registry.lookup("?");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].name, "Decidable.decide");
}

#[test]
fn test_mixfix_notation_multiple_tokens() {
    let mut registry = NotationRegistry::new();
    registry.register(make_mixfix_entry(&["⟨", ",", "⟩"], "Prod.mk", 0, 2));

    let results = registry.lookup("⟨");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].name, "Prod.mk");
    assert_eq!(results[0].kind, NotationKind::Notation);
}

#[test]
fn test_pattern_leading_token() {
    let infix_pattern = NotationPattern {
        items: vec![
            NotationPatternItem::Placeholder,
            NotationPatternItem::Token("+".to_owned()),
            NotationPatternItem::Placeholder,
        ],
    };
    assert_eq!(infix_pattern.leading_token(), Some("+"));

    let prefix_pattern = NotationPattern {
        items: vec![
            NotationPatternItem::Token("!".to_owned()),
            NotationPatternItem::Placeholder,
        ],
    };
    assert_eq!(prefix_pattern.leading_token(), Some("!"));

    let empty_pattern = NotationPattern { items: vec![] };
    assert_eq!(empty_pattern.leading_token(), None);

    let placeholder_only = NotationPattern {
        items: vec![NotationPatternItem::Placeholder],
    };
    assert_eq!(placeholder_only.leading_token(), None);
}

#[test]
fn test_pattern_arity() {
    let infix = NotationPattern {
        items: vec![
            NotationPatternItem::Placeholder,
            NotationPatternItem::Token("+".to_owned()),
            NotationPatternItem::Placeholder,
        ],
    };
    assert_eq!(infix.arity(), 2);

    let prefix = NotationPattern {
        items: vec![
            NotationPatternItem::Token("!".to_owned()),
            NotationPatternItem::Placeholder,
        ],
    };
    assert_eq!(prefix.arity(), 1);

    let ternary = NotationPattern {
        items: vec![
            NotationPatternItem::Placeholder,
            NotationPatternItem::Token("?".to_owned()),
            NotationPatternItem::Placeholder,
            NotationPatternItem::Token(":".to_owned()),
            NotationPatternItem::Placeholder,
        ],
    };
    assert_eq!(ternary.arity(), 3);
}

#[test]
fn test_all_notations_iterator() {
    let mut registry = NotationRegistry::new();
    registry.register(make_infix_entry("+", "HAdd.hAdd", 65));
    registry.register(make_infix_entry("*", "HMul.hMul", 70));
    registry.register(make_prefix_entry("!", "Not", 100));

    let all: Vec<&NotationEntry> = registry.all_notations().collect();
    assert_eq!(all.len(), 3);

    let names: Vec<&str> = all.iter().map(|e| e.name.as_str()).collect();
    assert!(names.contains(&"HAdd.hAdd"));
    assert!(names.contains(&"HMul.hMul"));
    assert!(names.contains(&"Not"));
}

#[test]
fn test_token_count_and_entry_count() {
    let mut registry = NotationRegistry::new();
    assert_eq!(registry.token_count(), 0);
    assert_eq!(registry.entry_count(), 0);

    registry.register(make_infix_entry("+", "HAdd.hAdd", 65));
    assert_eq!(registry.token_count(), 1);
    assert_eq!(registry.entry_count(), 1);

    // Same token, different priority
    registry.register(make_infix_entry("+", "Nat.add", 50));
    assert_eq!(registry.token_count(), 1);
    assert_eq!(registry.entry_count(), 2);

    // Different token
    registry.register(make_infix_entry("*", "HMul.hMul", 70));
    assert_eq!(registry.token_count(), 2);
    assert_eq!(registry.entry_count(), 3);
}

#[test]
fn test_has_notation() {
    let mut registry = NotationRegistry::new();
    assert!(!registry.has_notation("+"));

    registry.register(make_infix_entry("+", "HAdd.hAdd", 65));
    assert!(registry.has_notation("+"));
    assert!(!registry.has_notation("*"));
}

#[test]
fn test_default_creates_empty() {
    let registry = NotationRegistry::default();
    assert_eq!(registry.token_count(), 0);
    assert_eq!(registry.entry_count(), 0);
}

#[test]
fn test_same_priority_preserves_insertion_order() {
    let mut registry = NotationRegistry::new();
    registry.register(make_infix_entry("+", "first", 65));
    registry.register(make_infix_entry("+", "second", 65));

    let results = registry.lookup("+");
    assert_eq!(results.len(), 2);
    // Same priority: second insert goes after first (stable ordering)
    assert_eq!(results[0].name, "first");
    assert_eq!(results[1].name, "second");
}
