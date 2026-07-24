// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended helpers for attribute registry lookup, validation, stats, and migration.

use std::collections::HashMap;

use clean_kernel::Name;

use crate::attribute_registry::{AttributeDecl, AttributeKind, AttributeRegistry, BUILTIN_ATTRS};
use crate::error::ElabError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum DeclarationKind {
    Theorem,
    Definition,
    Inductive,
    Structure,
    Instance,
    Class,
    Axiom,
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AttributeConflict {
    pub(crate) first_attr: String,
    pub(crate) second_attr: String,
    pub(crate) reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AttributeScope {
    pub(crate) namespace: Name,
    pub(crate) inherited: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct AttributeStats {
    pub(crate) usage_counts: HashMap<String, usize>,
    pub(crate) popularity_rankings: Vec<(String, usize)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeprecatedMapping {
    pub(crate) old_name: String,
    pub(crate) new_name: String,
    pub(crate) reason: String,
}

#[derive(Debug)]
pub(crate) struct ExtendedAttributeRegistry<'a> {
    pub(crate) registry: &'a AttributeRegistry,
    pub(crate) usage_counts: HashMap<String, usize>,
    pub(crate) deprecated_mappings: HashMap<String, DeprecatedMapping>,
}

const CONFLICT_RULES: &[(&str, &str, &str)] = &[
    (
        "inline",
        "noinline",
        "inlining directives point in opposite directions",
    ),
    (
        "always_inline",
        "noinline",
        "inlining directives point in opposite directions",
    ),
    (
        "reducible",
        "semireducible",
        "only one reducibility mode can be active at a time",
    ),
    (
        "reducible",
        "irreducible",
        "only one reducibility mode can be active at a time",
    ),
    (
        "semireducible",
        "irreducible",
        "only one reducibility mode can be active at a time",
    ),
    (
        "specialize",
        "nospecialize",
        "specialization directives point in opposite directions",
    ),
];

const DEPRECATED_ATTRS: &[(&str, &str, &str)] = &[
    (
        "implemented_by",
        "implementedBy",
        "snake_case spelling was replaced by Lean 5 canonical spelling",
    ),
    (
        "defaultInstance",
        "default_instance",
        "camelCase spelling was replaced by the canonical builtin name",
    ),
    (
        "alwaysInline",
        "always_inline",
        "camelCase spelling was replaced by the canonical builtin name",
    ),
    (
        "macroInline",
        "macro_inline",
        "camelCase spelling was replaced by the canonical builtin name",
    ),
    (
        "inlineIfReduce",
        "inline_if_reduce",
        "camelCase spelling was replaced by the canonical builtin name",
    ),
    (
        "no_inline",
        "noinline",
        "legacy spelling was replaced by the canonical builtin name",
    ),
];

impl<'a> ExtendedAttributeRegistry<'a> {
    #[must_use]
    pub(crate) fn new(registry: &'a AttributeRegistry) -> Self {
        let mut usage_counts = HashMap::with_capacity(BUILTIN_ATTRS.len());
        for &(name, _) in BUILTIN_ATTRS {
            usage_counts.entry(name.to_owned()).or_insert(0);
        }
        for decl in registry.all_attributes() {
            usage_counts.entry(decl.name.clone()).or_insert(0);
        }
        let deprecated_mappings = DEPRECATED_ATTRS
            .iter()
            .map(|&(old_name, new_name, reason)| {
                (
                    old_name.to_owned(),
                    DeprecatedMapping {
                        old_name: old_name.to_owned(),
                        new_name: new_name.to_owned(),
                        reason: reason.to_owned(),
                    },
                )
            })
            .collect();
        Self {
            registry,
            usage_counts,
            deprecated_mappings,
        }
    }

    #[must_use]
    pub(crate) fn check_conflicts(&self, attrs: &[&str]) -> Vec<AttributeConflict> {
        let normalized: Vec<String> = attrs
            .iter()
            .map(|attr| self.normalize_attr_name(attr))
            .collect();
        CONFLICT_RULES
            .iter()
            .filter(|(left, right, _)| {
                normalized.iter().any(|attr| attr == left)
                    && normalized.iter().any(|attr| attr == right)
            })
            .map(|(left, right, reason)| AttributeConflict {
                first_attr: (*left).to_owned(),
                second_attr: (*right).to_owned(),
                reason: (*reason).to_owned(),
            })
            .collect()
    }

    pub(crate) fn validate_for_decl_kind(
        &self,
        attr: &str,
        kind: &DeclarationKind,
    ) -> Result<(), ElabError> {
        let normalized = self.normalize_attr_name(attr);
        if self.find_decl(attr).is_none() && self.find_decl(&normalized).is_none() {
            let suggestion = self
                .suggest_replacement(attr)
                .map_or_else(String::new, |name| format!("; did you mean '{name}'?"));
            return Err(ElabError::UnknownIdent(format!(
                "attribute '{attr}'{suggestion}"
            )));
        }
        if let Some(allowed_kinds) = allowed_decl_kinds(&normalized) {
            if !allowed_kinds.contains(kind) {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "attribute '{normalized}' cannot be applied to {kind:?} declarations"
                    ),
                });
            }
        }
        Ok(())
    }

    #[must_use]
    pub(crate) fn resolve_scoped(&self, attr: &str, namespace: &Name) -> bool {
        if self.registry.is_registered(attr) {
            return true;
        }
        if let Some(mapping) = self.migrate_attribute(attr) {
            return self.registry.is_registered(&mapping.new_name);
        }
        if attr.contains('.') {
            return false;
        }
        self.resolve_scope(attr, namespace).is_some()
    }

    pub(crate) fn record_usage(&mut self, attr: &str) {
        let key = self.normalize_attr_name(attr);
        *self.usage_counts.entry(key).or_insert(0) += 1;
    }

    #[must_use]
    pub(crate) fn get_stats(&self) -> AttributeStats {
        let mut popularity_rankings: Vec<(String, usize)> = self
            .usage_counts
            .iter()
            .map(|(name, count)| (name.clone(), *count))
            .collect();
        popularity_rankings.sort_by(|(left_name, left_count), (right_name, right_count)| {
            right_count
                .cmp(left_count)
                .then_with(|| {
                    self.attr_kind_rank(left_name)
                        .cmp(&self.attr_kind_rank(right_name))
                })
                .then_with(|| left_name.cmp(right_name))
        });
        AttributeStats {
            usage_counts: self.usage_counts.clone(),
            popularity_rankings,
        }
    }

    #[must_use]
    pub(crate) fn get_unused_attributes(&self) -> Vec<String> {
        let mut unused: Vec<String> = self
            .registry
            .all_attributes()
            .filter_map(|decl| {
                let count = self.usage_counts.get(&decl.name).copied().unwrap_or(0);
                (count == 0).then(|| decl.name.clone())
            })
            .collect();
        unused.sort();
        unused
    }

    #[must_use]
    pub(crate) fn migrate_attribute(&self, old_name: &str) -> Option<&DeprecatedMapping> {
        self.deprecated_mappings.get(old_name)
    }

    #[must_use]
    pub(crate) fn suggest_replacement(&self, attr: &str) -> Option<String> {
        if self.registry.is_registered(attr) {
            return None;
        }
        if let Some(mapping) = self.migrate_attribute(attr) {
            return Some(mapping.new_name.clone());
        }
        let normalized = normalize_for_match(attr);
        let exact = self
            .sorted_decls()
            .into_iter()
            .find(|decl| normalize_for_match(&decl.name) == normalized)
            .map(|decl| decl.name.clone());
        if exact.is_some() {
            return exact;
        }
        self.sorted_decls()
            .into_iter()
            .map(|decl| {
                (
                    decl.name.clone(),
                    edit_distance(&normalized, &normalize_for_match(&decl.name)),
                )
            })
            .filter(|(_, distance)| *distance <= 3)
            .min_by(|(left_name, left_distance), (right_name, right_distance)| {
                left_distance
                    .cmp(right_distance)
                    .then_with(|| left_name.cmp(right_name))
            })
            .map(|(name, _)| name)
    }

    #[must_use]
    pub(crate) fn resolve_scope(&self, attr: &str, namespace: &Name) -> Option<AttributeScope> {
        for scope in namespace_scopes(namespace) {
            let candidate = format!("{}.{}", scope.namespace, attr);
            if self.registry.is_registered(&candidate) {
                return Some(scope);
            }
        }
        None
    }

    #[must_use]
    pub(crate) fn normalize_attr_name(&self, attr: &str) -> String {
        if let Some(mapping) = self.migrate_attribute(attr) {
            return mapping.new_name.clone();
        }
        if self.registry.is_registered(attr) {
            return attr.to_owned();
        }
        let base = last_segment(attr);
        if self.registry.is_registered(base) {
            return base.to_owned();
        }
        base.to_owned()
    }

    #[must_use]
    pub(crate) fn find_decl(&self, attr: &str) -> Option<&AttributeDecl> {
        self.registry
            .get(attr)
            .or_else(|| {
                self.migrate_attribute(attr)
                    .and_then(|mapping| self.registry.get(&mapping.new_name))
            })
            .or_else(|| self.registry.get(last_segment(attr)))
    }

    #[must_use]
    pub(crate) fn sorted_decls(&self) -> Vec<&AttributeDecl> {
        let mut decls: Vec<&AttributeDecl> = self.registry.all_attributes().collect();
        decls.sort_by(|left, right| {
            (matches!(left.kind, AttributeKind::UserDefined) as u8)
                .cmp(&(matches!(right.kind, AttributeKind::UserDefined) as u8))
                .then_with(|| left.name.cmp(&right.name))
        });
        decls
    }

    #[must_use]
    pub(crate) fn attr_kind_rank(&self, attr: &str) -> u8 {
        match self.find_decl(attr).map(|decl| decl.kind) {
            Some(AttributeKind::Builtin) => 0,
            Some(AttributeKind::UserDefined) => 1,
            None => 2,
        }
    }
}

#[must_use]
pub(crate) fn allowed_decl_kinds(attr: &str) -> Option<&'static [DeclarationKind]> {
    match attr {
        "simp" | "congr" | "ext" | "refl" | "symm" | "deprecated" => Some(&[
            DeclarationKind::Theorem,
            DeclarationKind::Definition,
            DeclarationKind::Axiom,
            DeclarationKind::Opaque,
        ]),
        "coe" | "match_pattern" => Some(&[
            DeclarationKind::Definition,
            DeclarationKind::Opaque,
            DeclarationKind::Inductive,
        ]),
        "inline" | "always_inline" | "macro_inline" | "inline_if_reduce" | "noinline"
        | "reducible" | "semireducible" | "irreducible" | "extern" | "export" | "implementedBy"
        | "specialize" | "nospecialize" | "unbox" | "init" => {
            Some(&[DeclarationKind::Definition, DeclarationKind::Opaque])
        }
        "instance" | "default_instance" => Some(&[
            DeclarationKind::Instance,
            DeclarationKind::Definition,
            DeclarationKind::Opaque,
        ]),
        "class" => Some(&[
            DeclarationKind::Class,
            DeclarationKind::Structure,
            DeclarationKind::Inductive,
        ]),
        _ => None,
    }
}

#[must_use]
pub(crate) fn namespace_scopes(namespace: &Name) -> Vec<AttributeScope> {
    if namespace.is_anon() {
        return Vec::new();
    }
    let rendered = namespace.to_string();
    let parts: Vec<&str> = rendered.split('.').collect();
    (1..=parts.len())
        .rev()
        .map(|len| AttributeScope {
            namespace: Name::from_string(&parts[..len].join(".")),
            inherited: len != parts.len(),
        })
        .collect()
}

#[must_use]
pub(crate) fn last_segment(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

#[must_use]
pub(crate) fn normalize_for_match(name: &str) -> String {
    name.chars()
        .filter(|ch| *ch != '_' && *ch != '-')
        .flat_map(char::to_lowercase)
        .collect()
}

#[must_use]
pub(crate) fn edit_distance(left: &str, right: &str) -> usize {
    if left == right {
        return 0;
    }
    if left.is_empty() {
        return right.chars().count();
    }
    if right.is_empty() {
        return left.chars().count();
    }
    let right_chars: Vec<char> = right.chars().collect();
    let mut prev: Vec<usize> = (0..=right_chars.len()).collect();
    let mut next = vec![0; right_chars.len() + 1];
    for (i, left_ch) in left.chars().enumerate() {
        next[0] = i + 1;
        for (j, right_ch) in right_chars.iter().enumerate() {
            let cost = usize::from(left_ch != *right_ch);
            let insert = next[j] + 1;
            let delete = prev[j + 1] + 1;
            let replace = prev[j] + cost;
            next[j + 1] = insert.min(delete).min(replace);
        }
        prev.clone_from(&next);
    }
    prev[right_chars.len()]
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::attribute_registry::AttributeKind;

    #[test]
    fn test_attribute_registry_ext_check_conflicts_detects_multiple_pairs() {
        let registry = AttributeRegistry::new();
        let ext = ExtendedAttributeRegistry::new(&registry);
        let conflicts = ext.check_conflicts(&["inline", "noinline", "reducible", "irreducible"]);
        assert_eq!(conflicts.len(), 2);
        assert!(conflicts.iter().any(|conflict| {
            conflict.first_attr == "inline" && conflict.second_attr == "noinline"
        }));
        assert!(conflicts.iter().any(|conflict| {
            conflict.first_attr == "reducible" && conflict.second_attr == "irreducible"
        }));
    }

    #[test]
    fn test_attribute_registry_ext_validate_for_decl_kind_rejects_invalid_class_target() {
        let registry = AttributeRegistry::new();
        let ext = ExtendedAttributeRegistry::new(&registry);
        let err = ext.validate_for_decl_kind("class", &DeclarationKind::Theorem);
        assert!(matches!(err, Err(ElabError::Unsupported { .. })));
    }

    #[test]
    fn test_attribute_registry_ext_resolve_scoped_inherits_parent_namespace() {
        let mut registry = AttributeRegistry::new();
        registry
            .register(
                "Foo.scoped_attr",
                AttributeKind::UserDefined,
                "scoped attribute",
                None,
            )
            .expect("registration should succeed");
        let ext = ExtendedAttributeRegistry::new(&registry);
        assert!(ext.resolve_scoped("scoped_attr", &Name::from_string("Foo.Bar.Baz")));
        assert!(!ext.resolve_scoped("missing_attr", &Name::from_string("Foo.Bar.Baz")));
    }

    #[test]
    fn test_attribute_registry_ext_record_usage_updates_stats_and_unused() {
        let registry = AttributeRegistry::new();
        let mut ext = ExtendedAttributeRegistry::new(&registry);
        ext.record_usage("simp");
        ext.record_usage("simp");
        ext.record_usage("implemented_by");
        let stats = ext.get_stats();
        assert_eq!(stats.usage_counts.get("simp"), Some(&2));
        assert_eq!(stats.usage_counts.get("implementedBy"), Some(&1));
        assert_eq!(
            stats.popularity_rankings.first(),
            Some(&("simp".to_owned(), 2))
        );
        assert!(ext
            .get_unused_attributes()
            .iter()
            .any(|attr| attr == "noinline"));
    }

    #[test]
    fn test_attribute_registry_ext_migrate_attribute_returns_mapping() {
        let registry = AttributeRegistry::new();
        let ext = ExtendedAttributeRegistry::new(&registry);
        let mapping = ext
            .migrate_attribute("implemented_by")
            .expect("mapping should exist");
        assert_eq!(mapping.new_name, "implementedBy");
        assert_eq!(
            ext.suggest_replacement("implmentedBy"),
            Some("implementedBy".to_owned())
        );
    }

    #[test]
    fn test_attribute_registry_ext_validate_for_decl_kind_accepts_registered_user_attribute() {
        let mut registry = AttributeRegistry::new();
        registry
            .register("custom_attr", AttributeKind::UserDefined, "custom", None)
            .expect("registration should succeed");
        let ext = ExtendedAttributeRegistry::new(&registry);
        assert!(ext
            .validate_for_decl_kind("custom_attr", &DeclarationKind::Theorem)
            .is_ok());
    }
}
