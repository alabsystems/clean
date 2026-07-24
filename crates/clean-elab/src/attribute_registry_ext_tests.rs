// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended attribute registry module.

use clean_kernel::Name;

use crate::attribute_registry::{AttributeKind, AttributeRegistry};
use crate::attribute_registry_ext::{
    allowed_decl_kinds, edit_distance, last_segment, namespace_scopes, normalize_for_match,
    AttributeConflict, AttributeScope, AttributeStats, DeclarationKind, DeprecatedMapping,
    ExtendedAttributeRegistry,
};

// ===========================================================================
// Helper
// ===========================================================================

fn mk_registry() -> AttributeRegistry {
    AttributeRegistry::new()
}

fn mk_ext(registry: &AttributeRegistry) -> ExtendedAttributeRegistry<'_> {
    ExtendedAttributeRegistry::new(registry)
}

// ===========================================================================
// DeclarationKind tests
// ===========================================================================

#[test]
fn test_declaration_kind_debug_format() {
    let kind = DeclarationKind::Theorem;
    let s = format!("{kind:?}");
    assert!(s.contains("Theorem"));
}

#[test]
fn test_declaration_kind_equality() {
    assert_eq!(DeclarationKind::Theorem, DeclarationKind::Theorem);
    assert_ne!(DeclarationKind::Theorem, DeclarationKind::Definition);
}

#[test]
fn test_declaration_kind_all_variants_distinct() {
    let variants = [
        DeclarationKind::Theorem,
        DeclarationKind::Definition,
        DeclarationKind::Inductive,
        DeclarationKind::Structure,
        DeclarationKind::Instance,
        DeclarationKind::Class,
        DeclarationKind::Axiom,
        DeclarationKind::Opaque,
    ];
    for (i, a) in variants.iter().enumerate() {
        for (j, b) in variants.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(a, b);
            }
        }
    }
}

// ===========================================================================
// Conflict detection tests
// ===========================================================================

#[test]
fn test_check_conflicts_no_conflict() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let conflicts = ext.check_conflicts(&["simp", "instance"]);
    assert!(conflicts.is_empty());
}

#[test]
fn test_check_conflicts_inline_noinline() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let conflicts = ext.check_conflicts(&["inline", "noinline"]);
    assert_eq!(conflicts.len(), 1);
    assert_eq!(conflicts[0].first_attr, "inline");
    assert_eq!(conflicts[0].second_attr, "noinline");
}

#[test]
fn test_check_conflicts_reducible_irreducible() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let conflicts = ext.check_conflicts(&["reducible", "irreducible"]);
    assert_eq!(conflicts.len(), 1);
    assert_eq!(conflicts[0].first_attr, "reducible");
    assert_eq!(conflicts[0].second_attr, "irreducible");
}

#[test]
fn test_check_conflicts_specialize_nospecialize() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let conflicts = ext.check_conflicts(&["specialize", "nospecialize"]);
    assert_eq!(conflicts.len(), 1);
}

#[test]
fn test_check_conflicts_always_inline_noinline() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let conflicts = ext.check_conflicts(&["always_inline", "noinline"]);
    assert_eq!(conflicts.len(), 1);
}

#[test]
fn test_check_conflicts_reducible_semireducible() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let conflicts = ext.check_conflicts(&["reducible", "semireducible"]);
    assert_eq!(conflicts.len(), 1);
}

#[test]
fn test_check_conflicts_semireducible_irreducible() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let conflicts = ext.check_conflicts(&["semireducible", "irreducible"]);
    assert_eq!(conflicts.len(), 1);
}

#[test]
fn test_check_conflicts_multiple_pairs() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let conflicts = ext.check_conflicts(&["inline", "noinline", "reducible", "irreducible"]);
    assert_eq!(conflicts.len(), 2);
}

#[test]
fn test_check_conflicts_empty_list() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let conflicts = ext.check_conflicts(&[]);
    assert!(conflicts.is_empty());
}

#[test]
fn test_check_conflicts_single_attr() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let conflicts = ext.check_conflicts(&["inline"]);
    assert!(conflicts.is_empty());
}

#[test]
fn test_check_conflicts_deprecated_spelling_normalizes() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    // "no_inline" is a deprecated spelling of "noinline"
    let conflicts = ext.check_conflicts(&["inline", "no_inline"]);
    assert_eq!(conflicts.len(), 1);
}

// ===========================================================================
// Validation tests
// ===========================================================================

#[test]
fn test_validate_simp_on_theorem_ok() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    ext.validate_for_decl_kind("simp", &DeclarationKind::Theorem)
        .expect("simp should be valid on theorems");
}

#[test]
fn test_validate_simp_on_definition_ok() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    ext.validate_for_decl_kind("simp", &DeclarationKind::Definition)
        .expect("simp should be valid on definitions");
}

#[test]
fn test_validate_simp_on_inductive_err() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let result = ext.validate_for_decl_kind("simp", &DeclarationKind::Inductive);
    assert!(result.is_err());
}

#[test]
fn test_validate_class_on_structure_ok() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    ext.validate_for_decl_kind("class", &DeclarationKind::Structure)
        .expect("class should be valid on structures");
}

#[test]
fn test_validate_class_on_inductive_ok() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    ext.validate_for_decl_kind("class", &DeclarationKind::Inductive)
        .expect("class should be valid on inductives");
}

#[test]
fn test_validate_class_on_theorem_err() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let result = ext.validate_for_decl_kind("class", &DeclarationKind::Theorem);
    assert!(result.is_err());
}

#[test]
fn test_validate_instance_on_instance_ok() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    ext.validate_for_decl_kind("instance", &DeclarationKind::Instance)
        .expect("instance attr valid on instance decl");
}

#[test]
fn test_validate_instance_on_structure_err() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let result = ext.validate_for_decl_kind("instance", &DeclarationKind::Structure);
    assert!(result.is_err());
}

#[test]
fn test_validate_inline_on_definition_ok() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    ext.validate_for_decl_kind("inline", &DeclarationKind::Definition)
        .expect("inline should be valid on definitions");
}

#[test]
fn test_validate_inline_on_theorem_err() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let result = ext.validate_for_decl_kind("inline", &DeclarationKind::Theorem);
    assert!(result.is_err());
}

#[test]
fn test_validate_unknown_attribute_err() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let result = ext.validate_for_decl_kind("nonexistent", &DeclarationKind::Theorem);
    assert!(result.is_err());
}

#[test]
fn test_validate_deprecated_spelling_resolves() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    // "implemented_by" is deprecated spelling of "implementedBy"
    ext.validate_for_decl_kind("implemented_by", &DeclarationKind::Definition)
        .expect("deprecated spelling should resolve");
}

#[test]
fn test_validate_user_defined_attr_on_any_kind() {
    let mut reg = mk_registry();
    reg.register("custom_attr", AttributeKind::UserDefined, "custom", None)
        .expect("registration should succeed");
    let ext = mk_ext(&reg);
    ext.validate_for_decl_kind("custom_attr", &DeclarationKind::Theorem)
        .expect("custom attr should be valid on any kind");
    ext.validate_for_decl_kind("custom_attr", &DeclarationKind::Inductive)
        .expect("custom attr should be valid on any kind");
}

// ===========================================================================
// Scoping tests
// ===========================================================================

#[test]
fn test_resolve_scoped_registered_attr_always_true() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let ns = Name::from_string("Mathlib.Tactic");
    assert!(ext.resolve_scoped("simp", &ns));
}

#[test]
fn test_resolve_scoped_unknown_attr_false() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let ns = Name::from_string("Mathlib.Tactic");
    assert!(!ext.resolve_scoped("nonexistent_attr", &ns));
}

#[test]
fn test_resolve_scoped_deprecated_attr_resolves() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let ns = Name::from_string("Foo");
    // "implemented_by" maps to "implementedBy" which is registered
    assert!(ext.resolve_scoped("implemented_by", &ns));
}

#[test]
fn test_resolve_scoped_namespaced_attr() {
    let mut reg = mk_registry();
    reg.register(
        "Foo.scoped_attr",
        AttributeKind::UserDefined,
        "scoped",
        None,
    )
    .expect("registration should succeed");
    let ext = mk_ext(&reg);
    assert!(ext.resolve_scoped("scoped_attr", &Name::from_string("Foo.Bar.Baz")));
    assert!(!ext.resolve_scoped("scoped_attr", &Name::from_string("Other")));
}

#[test]
fn test_namespace_scopes_simple() {
    let scopes = namespace_scopes(&Name::from_string("A.B.C"));
    assert_eq!(scopes.len(), 3);
    // Most specific first
    assert_eq!(scopes[0].namespace, Name::from_string("A.B.C"));
    assert!(!scopes[0].inherited);
    assert_eq!(scopes[1].namespace, Name::from_string("A.B"));
    assert!(scopes[1].inherited);
    assert_eq!(scopes[2].namespace, Name::from_string("A"));
    assert!(scopes[2].inherited);
}

#[test]
fn test_namespace_scopes_single_segment() {
    let scopes = namespace_scopes(&Name::from_string("Foo"));
    assert_eq!(scopes.len(), 1);
    assert!(!scopes[0].inherited);
}

// ===========================================================================
// Statistics tests
// ===========================================================================

#[test]
fn test_stats_initial_all_zero() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let stats = ext.get_stats();
    for &count in stats.usage_counts.values() {
        assert_eq!(count, 0);
    }
}

#[test]
fn test_record_usage_increments() {
    let reg = mk_registry();
    let mut ext = mk_ext(&reg);
    ext.record_usage("simp");
    ext.record_usage("simp");
    ext.record_usage("coe");
    let stats = ext.get_stats();
    assert_eq!(stats.usage_counts["simp"], 2);
    assert_eq!(stats.usage_counts["coe"], 1);
}

#[test]
fn test_popularity_ranking_order() {
    let reg = mk_registry();
    let mut ext = mk_ext(&reg);
    ext.record_usage("coe");
    ext.record_usage("simp");
    ext.record_usage("simp");
    ext.record_usage("simp");
    ext.record_usage("inline");
    ext.record_usage("inline");
    let stats = ext.get_stats();
    // First in ranking should be the most used
    assert_eq!(stats.popularity_rankings[0].0, "simp");
    assert_eq!(stats.popularity_rankings[0].1, 3);
}

#[test]
fn test_record_usage_deprecated_normalizes() {
    let reg = mk_registry();
    let mut ext = mk_ext(&reg);
    ext.record_usage("implemented_by");
    let stats = ext.get_stats();
    assert_eq!(stats.usage_counts.get("implementedBy"), Some(&1));
}

#[test]
fn test_get_unused_attributes() {
    let reg = mk_registry();
    let mut ext = mk_ext(&reg);
    ext.record_usage("simp");
    ext.record_usage("inline");
    let unused = ext.get_unused_attributes();
    assert!(!unused.contains(&"simp".to_owned()));
    assert!(!unused.contains(&"inline".to_owned()));
    assert!(unused.contains(&"coe".to_owned()));
    assert!(unused.contains(&"reducible".to_owned()));
}

#[test]
fn test_get_unused_all_unused_initially() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let unused = ext.get_unused_attributes();
    assert!(unused.len() >= 20);
}

#[test]
fn test_unused_is_sorted() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let unused = ext.get_unused_attributes();
    let mut sorted = unused.clone();
    sorted.sort();
    assert_eq!(unused, sorted);
}

// ===========================================================================
// Migration tests
// ===========================================================================

#[test]
fn test_migrate_implemented_by() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let mapping = ext.migrate_attribute("implemented_by");
    assert!(mapping.is_some());
    let m = mapping.unwrap();
    assert_eq!(m.old_name, "implemented_by");
    assert_eq!(m.new_name, "implementedBy");
}

#[test]
fn test_migrate_default_instance() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let mapping = ext.migrate_attribute("defaultInstance");
    assert!(mapping.is_some());
    assert_eq!(mapping.unwrap().new_name, "default_instance");
}

#[test]
fn test_migrate_always_inline() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let mapping = ext.migrate_attribute("alwaysInline");
    assert!(mapping.is_some());
    assert_eq!(mapping.unwrap().new_name, "always_inline");
}

#[test]
fn test_migrate_unknown_returns_none() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    assert!(ext.migrate_attribute("simp").is_none());
}

#[test]
fn test_suggest_replacement_deprecated() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let suggestion = ext.suggest_replacement("implemented_by");
    assert_eq!(suggestion, Some("implementedBy".to_owned()));
}

#[test]
fn test_suggest_replacement_not_deprecated() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    assert!(ext.suggest_replacement("simp").is_none());
}

#[test]
fn test_suggest_replacement_typo() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    // "implmentedBy" is close to "implementedBy" by edit distance
    let suggestion = ext.suggest_replacement("implmentedBy");
    assert_eq!(suggestion, Some("implementedBy".to_owned()));
}

// ===========================================================================
// Helper function tests
// ===========================================================================

#[test]
fn test_last_segment_dotted() {
    assert_eq!(last_segment("Foo.Bar.baz"), "baz");
}

#[test]
fn test_last_segment_no_dots() {
    assert_eq!(last_segment("simp"), "simp");
}

#[test]
fn test_normalize_for_match_strips_underscores() {
    assert_eq!(normalize_for_match("always_inline"), "alwaysinline");
}

#[test]
fn test_normalize_for_match_lowercases() {
    assert_eq!(normalize_for_match("implementedBy"), "implementedby");
}

#[test]
fn test_edit_distance_identical() {
    assert_eq!(edit_distance("simp", "simp"), 0);
}

#[test]
fn test_edit_distance_one_insertion() {
    assert_eq!(edit_distance("sim", "simp"), 1);
}

#[test]
fn test_edit_distance_one_deletion() {
    assert_eq!(edit_distance("simpp", "simp"), 1);
}

#[test]
fn test_edit_distance_one_substitution() {
    assert_eq!(edit_distance("siap", "simp"), 1);
}

#[test]
fn test_edit_distance_empty_strings() {
    assert_eq!(edit_distance("", ""), 0);
    assert_eq!(edit_distance("abc", ""), 3);
    assert_eq!(edit_distance("", "abc"), 3);
}

// ===========================================================================
// allowed_decl_kinds tests
// ===========================================================================

#[test]
fn test_allowed_decl_kinds_simp() {
    let kinds = allowed_decl_kinds("simp");
    assert!(kinds.is_some());
    let k = kinds.unwrap();
    assert!(k.contains(&DeclarationKind::Theorem));
    assert!(!k.contains(&DeclarationKind::Inductive));
}

#[test]
fn test_allowed_decl_kinds_class() {
    let kinds = allowed_decl_kinds("class");
    assert!(kinds.is_some());
    let k = kinds.unwrap();
    assert!(k.contains(&DeclarationKind::Class));
    assert!(k.contains(&DeclarationKind::Structure));
    assert!(k.contains(&DeclarationKind::Inductive));
}

#[test]
fn test_allowed_decl_kinds_unknown_returns_none() {
    assert!(allowed_decl_kinds("my_custom_attr").is_none());
}

// ===========================================================================
// Struct construction tests
// ===========================================================================

#[test]
fn test_attribute_conflict_struct() {
    let c = AttributeConflict {
        first_attr: "inline".to_owned(),
        second_attr: "noinline".to_owned(),
        reason: "test".to_owned(),
    };
    assert_eq!(c.first_attr, "inline");
    assert_eq!(c.second_attr, "noinline");
}

#[test]
fn test_attribute_scope_struct() {
    let s = AttributeScope {
        namespace: Name::from_string("Ns"),
        inherited: true,
    };
    assert!(s.inherited);
    assert_eq!(s.namespace, Name::from_string("Ns"));
}

#[test]
fn test_deprecated_mapping_struct() {
    let m = DeprecatedMapping {
        old_name: "old".to_owned(),
        new_name: "new".to_owned(),
        reason: "migrate".to_owned(),
    };
    assert_eq!(m.old_name, "old");
    assert_eq!(m.new_name, "new");
    assert_eq!(m.reason, "migrate");
}

#[test]
fn test_attribute_stats_default() {
    let stats = AttributeStats::default();
    assert!(stats.usage_counts.is_empty());
    assert!(stats.popularity_rankings.is_empty());
}

#[test]
fn test_extended_registry_debug() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    let s = format!("{ext:?}");
    assert!(s.contains("ExtendedAttributeRegistry"));
}

#[test]
fn test_normalize_attr_name_deprecated() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    assert_eq!(ext.normalize_attr_name("implemented_by"), "implementedBy");
}

#[test]
fn test_normalize_attr_name_registered() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    assert_eq!(ext.normalize_attr_name("simp"), "simp");
}

#[test]
fn test_find_decl_direct() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    assert!(ext.find_decl("simp").is_some());
}

#[test]
fn test_find_decl_deprecated() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    assert!(ext.find_decl("implemented_by").is_some());
}

#[test]
fn test_find_decl_unknown() {
    let reg = mk_registry();
    let ext = mk_ext(&reg);
    assert!(ext.find_decl("totally_unknown").is_none());
}
