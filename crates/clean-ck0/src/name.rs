// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hierarchical [`Name`]s (Lean `Name` — `Anonymous | Str parent s | Num parent n`).
//!
//! Interned **by value** via an `Arc`-shared cons-spine: each `Name` is a cheap
//! handle whose `Clone` is a refcount bump. There are **no global unsafe statics
//! and no global interner table** — equality is by value (structural over the
//! spine), so two independently-built `Name`s with the same components compare
//! equal. (The design forbids `unsafe`; an `Arc` spine gives O(1) clone without
//! it. A future perf pass may add a *local* dedup cache, never a global static.)

use std::sync::Arc;

/// A hierarchical name component.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Component {
    /// String component appended to `parent`.
    Str(Box<str>),
    /// Numeric component appended to `parent` (arbitrary-precision is overkill;
    /// Lean uses a machine integer here and these are *index* values, never
    /// arithmetic'd, so a `u64` handle is policy-safe — it is only ever
    /// compared and printed).
    Num(u64),
}

/// Internal shared cons-cell. Field-private; the only constructors are
/// [`Name::str`] / [`Name::num`] / [`Name::anonymous`].
#[derive(Debug, PartialEq, Eq, Hash)]
struct NameNode {
    parent: Name,
    component: Component,
}

/// A hierarchical name (e.g. `Nat.succ`, `List.cons`).
///
/// Cheap to clone (Arc bump). Equality and hashing are structural over the
/// spine, so value-equal names are `==` regardless of how they were built.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Name(NameRepr);

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
enum NameRepr {
    /// The empty / root name.
    #[default]
    Anonymous,
    /// A non-empty name: `parent` extended by `component`.
    Node(Arc<NameNode>),
}

impl Name {
    /// The anonymous (root) name.
    #[must_use]
    pub fn anonymous() -> Self {
        Name(NameRepr::Anonymous)
    }

    /// True if this is the anonymous root.
    #[must_use]
    pub fn is_anonymous(&self) -> bool {
        matches!(self.0, NameRepr::Anonymous)
    }

    /// Extend `self` with a string component: `self.s`.
    #[must_use]
    pub fn str(&self, s: &str) -> Self {
        Name(NameRepr::Node(Arc::new(NameNode {
            parent: self.clone(),
            component: Component::Str(s.into()),
        })))
    }

    /// Extend `self` with a numeric component: `self.n`.
    #[must_use]
    pub fn num(&self, n: u64) -> Self {
        Name(NameRepr::Node(Arc::new(NameNode {
            parent: self.clone(),
            component: Component::Num(n),
        })))
    }

    /// Build a name from a dotted path: `"Nat.succ"` -> `anonymous.str("Nat").str("succ")`.
    ///
    /// An empty string yields the anonymous name.
    #[must_use]
    pub fn from_dotted(path: &str) -> Self {
        if path.is_empty() {
            return Name::anonymous();
        }
        path.split('.')
            .fold(Name::anonymous(), |acc, seg| acc.str(seg))
    }

    /// The parent name, or `None` if this is anonymous.
    #[must_use]
    pub fn parent(&self) -> Option<Name> {
        match &self.0 {
            NameRepr::Anonymous => None,
            NameRepr::Node(node) => Some(node.parent.clone()),
        }
    }

    /// The final string component, if this name ends in one.
    #[must_use]
    pub fn last_str(&self) -> Option<&str> {
        match &self.0 {
            NameRepr::Node(node) => match &node.component {
                Component::Str(s) => Some(s),
                Component::Num(_) => None,
            },
            NameRepr::Anonymous => None,
        }
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Iterative spine walk (collect then render) avoids deep recursion on
        // long names. No arithmetic on values, only iteration.
        let mut parts: Vec<String> = Vec::new();
        let mut cur = self.clone();
        while let NameRepr::Node(node) = &cur.0 {
            match &node.component {
                Component::Str(s) => parts.push(s.to_string()),
                Component::Num(n) => parts.push(n.to_string()),
            }
            cur = node.parent.clone();
        }
        if parts.is_empty() {
            return write!(f, "[anonymous]");
        }
        parts.reverse();
        write!(f, "{}", parts.join("."))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interned_by_value_equality() {
        // Two independently-built names with the same components are ==.
        let a = Name::anonymous().str("Nat").str("succ");
        let b = Name::from_dotted("Nat.succ");
        assert_eq!(a, b);
    }

    #[test]
    fn test_distinct_names_differ() {
        assert_ne!(Name::from_dotted("Nat.succ"), Name::from_dotted("Nat.zero"));
        assert_ne!(Name::from_dotted("Nat"), Name::anonymous());
    }

    #[test]
    fn test_num_and_str_components_differ() {
        let n = Name::anonymous().num(0);
        let s = Name::anonymous().str("0");
        assert_ne!(n, s, "Num(0) and Str(\"0\") are distinct components");
    }

    #[test]
    fn test_parent_and_last_str() {
        let n = Name::from_dotted("List.cons");
        assert_eq!(n.last_str(), Some("cons"));
        assert_eq!(n.parent(), Some(Name::from_dotted("List")));
        assert!(Name::anonymous().parent().is_none());
    }

    #[test]
    fn test_display_roundtrips_dotted() {
        assert_eq!(Name::from_dotted("a.b.c").to_string(), "a.b.c");
        assert_eq!(Name::anonymous().to_string(), "[anonymous]");
    }

    #[test]
    fn test_empty_dotted_is_anonymous() {
        assert!(Name::from_dotted("").is_anonymous());
    }
}
