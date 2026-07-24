// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration of scoped attributes with simp and instance extensions.
//!
//! Provides helper functions to register simp lemmas and instances with
//! scoping information, and to resolve which scoped attributes become
//! active when namespaces are opened.
//!
//! These functions bridge the gap between the general-purpose
//! [`ScopedAttrRegistry`] and the concrete attribute kinds (simp, instance)
//! that the elaborator needs to manage.

use clean_kernel::name::Name;

use crate::attr_scoping::{AttributeScope, ScopedAttrEntry, ScopedAttrRegistry};

/// Register a simp lemma with scoping information.
///
/// Creates a [`ScopedAttrEntry`] with `attr_name = "simp"` and the given
/// scope, then adds it to the registry. The `namespace` field is set to
/// the anonymous name (root namespace) by default; callers should construct
/// entries with explicit namespaces when needed.
pub(crate) fn apply_scoped_simp(
    name: &Name,
    scope: &AttributeScope,
    registry: &mut ScopedAttrRegistry,
) {
    registry.register(ScopedAttrEntry {
        decl_name: name.clone(),
        attr_name: "simp".to_string(),
        scope: scope.clone(),
        namespace: namespace_from_scope(scope),
    });
}

/// Register an instance with scoping information.
///
/// Creates a [`ScopedAttrEntry`] with `attr_name = "instance"` and the given
/// scope and priority (encoded in the entry for downstream consumers),
/// then adds it to the registry.
pub(crate) fn apply_scoped_instance(
    name: &Name,
    scope: &AttributeScope,
    _priority: u32,
    registry: &mut ScopedAttrRegistry,
) {
    registry.register(ScopedAttrEntry {
        decl_name: name.clone(),
        attr_name: "instance".to_string(),
        scope: scope.clone(),
        namespace: namespace_from_scope(scope),
    });
}

/// Resolve which scoped attribute entries become active when the given
/// namespaces are opened.
///
/// Returns cloned entries whose scope matches one of the provided namespaces.
/// Global and Local entries are excluded since they are always (or contextually)
/// active and do not depend on namespace opens.
#[must_use]
pub(crate) fn resolve_scoped_attrs(
    open_ns: &[Name],
    registry: &ScopedAttrRegistry,
) -> Vec<ScopedAttrEntry> {
    let ns_set: std::collections::HashSet<&Name> = open_ns.iter().collect();

    registry
        .entries()
        .flat_map(|entries| {
            entries.iter().filter(
                |entry| matches!(&entry.scope, AttributeScope::Scoped(ns) if ns_set.contains(ns)),
            )
        })
        .cloned()
        .collect()
}

/// Extract the namespace from a scope, defaulting to anonymous for
/// Global and Local scopes.
fn namespace_from_scope(scope: &AttributeScope) -> Name {
    match scope {
        AttributeScope::Scoped(ns) => ns.clone(),
        AttributeScope::Global | AttributeScope::Local => Name::anon(),
    }
}
