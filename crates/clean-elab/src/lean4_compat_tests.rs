// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Lean 4 compatibility layer.

use crate::lean4_compat::{DeprecatedEntry, Lean4Compat};

// ---------------------------------------------------------------------------
// Construction
// ---------------------------------------------------------------------------

#[test]
fn test_new_populates_tactics() {
    let compat = Lean4Compat::new();
    assert!(
        compat.tactic_count() >= 13,
        "expected at least 13 tactic renames, got {}",
        compat.tactic_count()
    );
}

#[test]
fn test_new_populates_commands() {
    let compat = Lean4Compat::new();
    assert!(
        compat.command_count() >= 5,
        "expected at least 5 command renames, got {}",
        compat.command_count()
    );
}

#[test]
fn test_default_equals_new() {
    let a = Lean4Compat::new();
    let b = Lean4Compat::default();
    assert_eq!(a.tactic_count(), b.tactic_count());
    assert_eq!(a.command_count(), b.command_count());
    assert_eq!(a.all_deprecated().len(), b.all_deprecated().len());
}

// ---------------------------------------------------------------------------
// Tactic resolution
// ---------------------------------------------------------------------------

#[test]
fn test_resolve_tactic_library_search_to_exact_q() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_tactic("library_search"), Some("exact?"));
}

#[test]
fn test_resolve_tactic_suggest_to_exact_q() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_tactic("suggest"), Some("exact?"));
}

#[test]
fn test_resolve_tactic_squeeze_simp_to_simp_q() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_tactic("squeeze_simp"), Some("simp?"));
}

#[test]
fn test_resolve_tactic_aesop_family() {
    let compat = Lean4Compat::new();
    for old in &["tidy", "finish", "clarify", "safe"] {
        assert_eq!(
            compat.resolve_tactic(old),
            Some("aesop"),
            "{old} should resolve to aesop",
        );
    }
}

#[test]
fn test_resolve_tactic_decide_family() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_tactic("obviously"), Some("decide"));
    assert_eq!(compat.resolve_tactic("dec_trivial"), Some("decide"));
}

#[test]
fn test_resolve_tactic_ring_nf_to_ring() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_tactic("ring_nf"), Some("ring"));
}

#[test]
fn test_resolve_tactic_norm_num1_to_norm_num() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_tactic("norm_num1"), Some("norm_num"));
}

#[test]
fn test_resolve_tactic_tauto_to_omega() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_tactic("tauto"), Some("omega"));
}

#[test]
fn test_resolve_tactic_unknown_returns_none() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_tactic("nonexistent_tactic"), None);
}

#[test]
fn test_is_deprecated_tactic_true() {
    let compat = Lean4Compat::new();
    assert!(compat.is_deprecated_tactic("tidy"));
    assert!(compat.is_deprecated_tactic("library_search"));
}

#[test]
fn test_is_deprecated_tactic_false_for_current() {
    let compat = Lean4Compat::new();
    assert!(!compat.is_deprecated_tactic("aesop"));
    assert!(!compat.is_deprecated_tactic("exact?"));
    assert!(!compat.is_deprecated_tactic("simp"));
}

// ---------------------------------------------------------------------------
// Command resolution
// ---------------------------------------------------------------------------

#[test]
fn test_resolve_command_check() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_command("#check"), Some("check_expression"));
}

#[test]
fn test_resolve_command_eval() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_command("#eval"), Some("eval_expression"));
}

#[test]
fn test_resolve_command_print() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_command("#print"), Some("print_declaration"),);
}

#[test]
fn test_resolve_command_reduce_maps_to_eval() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_command("#reduce"), Some("eval_expression"));
}

#[test]
fn test_resolve_command_check_failure() {
    let compat = Lean4Compat::new();
    assert_eq!(
        compat.resolve_command("#check_failure"),
        Some("check_failure"),
    );
}

#[test]
fn test_resolve_command_unknown_returns_none() {
    let compat = Lean4Compat::new();
    assert_eq!(compat.resolve_command("#nonexistent"), None);
}

#[test]
fn test_is_deprecated_command() {
    let compat = Lean4Compat::new();
    assert!(compat.is_deprecated_command("#check"));
    assert!(!compat.is_deprecated_command("check_expression"));
}

// ---------------------------------------------------------------------------
// Deprecation metadata
// ---------------------------------------------------------------------------

#[test]
fn test_check_deprecated_returns_entry() {
    let compat = Lean4Compat::new();
    let entry = compat
        .check_deprecated("library_search")
        .expect("library_search should have a deprecation entry");
    assert_eq!(entry.old, "library_search");
    assert_eq!(entry.new, "exact?");
    assert!(!entry.message.is_empty());
}

#[test]
fn test_check_deprecated_returns_none_for_unknown() {
    let compat = Lean4Compat::new();
    assert!(compat.check_deprecated("nonexistent").is_none());
}

#[test]
fn test_all_deprecated_includes_syntax_entries() {
    let compat = Lean4Compat::new();
    let all = compat.all_deprecated();
    // Should include tactic renames + command renames + syntax-only entries
    let has_match_entry = all
        .iter()
        .any(|e| e.old == "match" || e.old.contains("match"));
    assert!(
        has_match_entry,
        "all_deprecated should include a match-related entry",
    );
}

#[test]
fn test_all_deprecated_includes_do_entries() {
    let compat = Lean4Compat::new();
    let all = compat.all_deprecated();
    let has_do_entry = all.iter().any(|e| e.old.contains("do"));
    assert!(
        has_do_entry,
        "all_deprecated should include a do-notation entry",
    );
}

#[test]
fn test_deprecated_entry_version_format() {
    let compat = Lean4Compat::new();
    for entry in compat.all_deprecated() {
        assert!(
            entry.since_version.contains('.'),
            "version '{}' for '{}' should be semver-like",
            entry.since_version,
            entry.old,
        );
    }
}

#[test]
fn test_no_empty_messages() {
    let compat = Lean4Compat::new();
    for entry in compat.all_deprecated() {
        assert!(
            !entry.message.is_empty(),
            "deprecation entry for '{}' has empty message",
            entry.old,
        );
    }
}

// ---------------------------------------------------------------------------
// DeprecatedEntry accessors
// ---------------------------------------------------------------------------

#[test]
fn test_deprecated_entry_new_constructor() {
    let entry = DeprecatedEntry::new("old_name", "new_name", "4.0.0", "migration hint");
    assert_eq!(entry.old_name(), "old_name");
    assert_eq!(entry.replacement(), "new_name");
    assert_eq!(entry.version(), "4.0.0");
    assert_eq!(entry.diagnostic_message(), "migration hint");
}

#[test]
fn test_deprecated_entry_matches() {
    let entry = DeprecatedEntry::new("tidy", "aesop", "4.0.0", "Use aesop");
    assert!(entry.matches("tidy"));
    assert!(!entry.matches("aesop"));
    assert!(!entry.matches("tid"));
}

#[test]
fn test_all_deprecated_count() {
    let compat = Lean4Compat::new();
    // 5 command + 13 tactic + 8 syntax = 26 entries
    // Use a lower bound to be resilient to future additions
    assert!(
        compat.all_deprecated().len() >= 20,
        "expected at least 20 deprecated entries, got {}",
        compat.all_deprecated().len(),
    );
}
