// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers used across multiple parser submodules.

use crate::stmt::StorageClass;
use tree_sitter::Node;

/// Get the source text of a tree-sitter node.
pub(super) fn node_text(node: Node, source: &str) -> String {
    source[node.start_byte()..node.end_byte()].to_string()
}

/// Find an identifier of the given kind(s) in nested declarators.
///
/// Replaces the previous separate `find_identifier` and `find_field_identifier`
/// helpers with a single recursive walk parameterized by target node kinds.
///
/// Usage:
/// - `find_nested_identifier(node, source, &["identifier"])` for declarators
/// - `find_nested_identifier(node, source, &["field_identifier"])` for field declarators
pub(super) fn find_nested_identifier(
    node: Node,
    source: &str,
    target_kinds: &[&str],
) -> Option<String> {
    for i in 0..node.child_count() {
        if let Some(child) = node.child(i as u32) {
            if target_kinds.contains(&child.kind()) {
                return Some(node_text(child, source));
            }
            if let Some(found) = find_nested_identifier(child, source, target_kinds) {
                return Some(found);
            }
        }
    }
    None
}

/// Qualifiers (`const`, `volatile`, `restrict`) applied directly to a pointer.
///
/// In C a `type_qualifier` written *after* the `*` of a `pointer_declarator`
/// qualifies the pointer itself, e.g. `int * restrict p` declares a
/// restrict-qualified pointer to `int` (C99 6.7.3). tree-sitter-c surfaces such
/// qualifiers as direct `type_qualifier` children of the `pointer_declarator`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct PointerQualifiers {
    pub is_const: bool,
    pub is_volatile: bool,
    pub is_restrict: bool,
}

/// Collect the qualifiers applied to a `pointer_declarator` by scanning its
/// direct `type_qualifier` children (the qualifiers written after the `*`).
///
/// Recognizes the C99 keyword `restrict` and the common GNU spellings
/// `__restrict` / `__restrict__`, plus `const` and `volatile`.
pub(super) fn pointer_qualifiers(node: Node, source: &str) -> PointerQualifiers {
    let mut quals = PointerQualifiers::default();
    for i in 0..node.child_count() {
        if let Some(child) = node.child(i as u32) {
            if child.kind() == "type_qualifier" {
                match node_text(child, source).trim() {
                    "restrict" | "__restrict" | "__restrict__" => quals.is_restrict = true,
                    "const" => quals.is_const = true,
                    "volatile" => quals.is_volatile = true,
                    _ => {}
                }
            }
        }
    }
    quals
}

/// Parse a storage class specifier keyword into `StorageClass`.
pub(super) fn parse_storage_class(text: &str) -> StorageClass {
    match text {
        "static" => StorageClass::Static,
        "extern" => StorageClass::Extern,
        "register" => StorageClass::Register,
        "_Thread_local" | "thread_local" => StorageClass::ThreadLocal,
        _ => StorageClass::Auto,
    }
}
