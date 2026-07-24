// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! General-purpose attribute registry persistent extension.
//!
//! Stores declaration-to-attribute registrations so they survive .olean
//! roundtrip. The folded state supports both forward lookup
//! (`decl_name -> attributes`) and inverted lookup
//! (`attr_name -> declarations`).
//!
//! In Lean 4, attributes like `@[simp]`, `@[inline]`, `@[reducible]`, and
//! `@[instance]` are stored in persistent env extensions. This module
//! implements a general-purpose attribute store that any attribute kind
//! can use.
//!
//! Reference: Lean 4 `src/Lean/Attributes.lean`

use crate::name::Name;
use std::collections::HashMap;
use std::sync::OnceLock;

use super::persistent_ext::{
    register_persistent_ext, ExtensionIdx, PersistentExtEntry, PersistentExtState,
};
use super::types::{EnvExtensionEntry, EnvExtensionEntryData};

/// The canonical name for the attribute extension.
const ATTR_EXT_NAME: &str = "attrExtension";

/// Lazily-initialized extension index for attributes.
static ATTR_EXT_IDX: OnceLock<ExtensionIdx> = OnceLock::new();

/// Get (or register) the attribute extension index.
///
/// Thread-safe: uses OnceLock for initialization.
pub fn attr_ext_idx() -> ExtensionIdx {
    *ATTR_EXT_IDX
        .get_or_init(|| register_persistent_ext::<AttrExtState>(Name::from_string(ATTR_EXT_NAME)))
}

// ============================================================================
// Entry type
// ============================================================================

/// A single attribute registration associated with a declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttrExtEntry {
    /// Name of the declaration carrying the attribute.
    pub decl_name: Name,
    /// Name of the attribute (e.g. `simp`, `inline`, `instance`).
    pub attr_name: Name,
    /// Optional attribute priority. `0` represents the default.
    pub priority: u32,
}

impl AttrExtEntry {
    fn encode_payload(&self) -> Vec<u8> {
        let attr_name = self.attr_name.to_string();
        let priority = self.priority.to_string();
        let mut payload = Vec::with_capacity(attr_name.len() + 1 + priority.len());
        payload.extend_from_slice(attr_name.as_bytes());
        payload.push(b':');
        payload.extend_from_slice(priority.as_bytes());
        payload
    }

    fn decode_payload(bytes: &[u8]) -> Option<(Name, u32)> {
        let payload = std::str::from_utf8(bytes).ok()?;
        let (attr_name, priority) = payload.rsplit_once(':')?;
        let priority = priority.parse::<u32>().ok()?;
        Some((Name::from_string(attr_name), priority))
    }
}

impl PersistentExtEntry for AttrExtEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: self.decl_name.clone(),
            data: EnvExtensionEntryData::Object(self.encode_payload()),
        }
    }

    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {
        let (attr_name, priority) = match &entry.data {
            EnvExtensionEntryData::Object(bytes) => Self::decode_payload(bytes)?,
            EnvExtensionEntryData::Scalar(_) => return None,
        };

        Some(Self {
            decl_name: entry.name.clone(),
            attr_name,
            priority,
        })
    }
}

// ============================================================================
// State type
// ============================================================================

/// A queryable attribute registration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttrRegistration {
    /// Name of the attribute (e.g. `simp`, `inline`, `instance`).
    pub attr_name: Name,
    /// Attribute priority. `0` represents the default.
    pub priority: u32,
}

/// Aggregated attribute state with forward and inverted indices.
///
/// Built by folding `AttrExtEntry` items from imported modules.
#[derive(Clone, Debug, Default)]
pub struct AttrExtState {
    attrs_by_decl: HashMap<Name, Vec<AttrRegistration>>,
    decls_by_attr: HashMap<Name, Vec<Name>>,
}

impl AttrExtState {
    /// Get all attributes registered for a declaration.
    pub fn get_attrs_for_decl(&self, decl_name: &Name) -> &[AttrRegistration] {
        self.attrs_by_decl.get(decl_name).map_or(&[], Vec::as_slice)
    }

    /// Get all declarations registered for an attribute.
    pub fn get_decls_with_attr(&self, attr_name: &Name) -> &[Name] {
        self.decls_by_attr.get(attr_name).map_or(&[], Vec::as_slice)
    }

    /// Check whether a declaration has a specific attribute.
    pub fn has_attr(&self, decl_name: &Name, attr_name: &Name) -> bool {
        self.get_attrs_for_decl(decl_name)
            .iter()
            .any(|registration| &registration.attr_name == attr_name)
    }

    /// Number of stored registrations.
    pub fn len(&self) -> usize {
        self.attrs_by_decl.values().map(Vec::len).sum()
    }

    /// Returns true if no attribute registrations are stored.
    pub fn is_empty(&self) -> bool {
        self.attrs_by_decl.is_empty()
    }
}

impl PersistentExtState for AttrExtState {
    type Entry = AttrExtEntry;

    fn add_entry(&mut self, entry: &AttrExtEntry) {
        self.attrs_by_decl
            .entry(entry.decl_name.clone())
            .or_default()
            .push(AttrRegistration {
                attr_name: entry.attr_name.clone(),
                priority: entry.priority,
            });
        self.decls_by_attr
            .entry(entry.attr_name.clone())
            .or_default()
            .push(entry.decl_name.clone());
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        self.attrs_by_decl
            .iter()
            .flat_map(|(decl_name, registrations)| {
                registrations.iter().map(move |registration| {
                    AttrExtEntry {
                        decl_name: decl_name.clone(),
                        attr_name: registration.attr_name.clone(),
                        priority: registration.priority,
                    }
                    .to_env_entry()
                })
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_attr_ext_entry_roundtrip_default_priority() {
        let entry = AttrExtEntry {
            decl_name: Name::from_string("Nat.add_comm"),
            attr_name: Name::from_string("simp"),
            priority: 0,
        };

        let raw = entry.to_env_entry();
        let decoded = AttrExtEntry::from_env_entry(&raw).unwrap();
        assert_eq!(decoded.decl_name.to_string(), "Nat.add_comm");
        assert_eq!(decoded.attr_name.to_string(), "simp");
        assert_eq!(decoded.priority, 0);
    }

    #[test]
    fn test_attr_ext_entry_roundtrip_custom_priority() {
        let entry = AttrExtEntry {
            decl_name: Name::from_string("List.length"),
            attr_name: Name::from_string("inline"),
            priority: 250,
        };

        let raw = entry.to_env_entry();
        let decoded = AttrExtEntry::from_env_entry(&raw).unwrap();
        assert_eq!(decoded.decl_name.to_string(), "List.length");
        assert_eq!(decoded.attr_name.to_string(), "inline");
        assert_eq!(decoded.priority, 250);
    }

    #[test]
    fn test_attr_ext_state_fold_and_query() {
        let mut state = AttrExtState::default();
        state.add_entry(&AttrExtEntry {
            decl_name: Name::from_string("lem1"),
            attr_name: Name::from_string("simp"),
            priority: 0,
        });
        state.add_entry(&AttrExtEntry {
            decl_name: Name::from_string("lem1"),
            attr_name: Name::from_string("inline"),
            priority: 10,
        });
        state.add_entry(&AttrExtEntry {
            decl_name: Name::from_string("lem2"),
            attr_name: Name::from_string("instance"),
            priority: 200,
        });

        assert_eq!(state.len(), 3);
        assert!(!state.is_empty());
        assert!(state.has_attr(&Name::from_string("lem1"), &Name::from_string("simp")));
        assert!(state.has_attr(&Name::from_string("lem1"), &Name::from_string("inline")));
        assert!(!state.has_attr(&Name::from_string("lem1"), &Name::from_string("instance")));
        assert!(!state.has_attr(&Name::from_string("missing"), &Name::from_string("simp")));

        let attrs = state.get_attrs_for_decl(&Name::from_string("lem1"));
        assert_eq!(attrs.len(), 2);
        assert_eq!(attrs[0].attr_name, Name::from_string("simp"));
        assert_eq!(attrs[0].priority, 0);
        assert_eq!(attrs[1].attr_name, Name::from_string("inline"));
        assert_eq!(attrs[1].priority, 10);
    }

    #[test]
    fn test_attr_ext_state_inverted_index() {
        let mut state = AttrExtState::default();
        state.add_entry(&AttrExtEntry {
            decl_name: Name::from_string("Nat.add_comm"),
            attr_name: Name::from_string("simp"),
            priority: 0,
        });
        state.add_entry(&AttrExtEntry {
            decl_name: Name::from_string("List.append_assoc"),
            attr_name: Name::from_string("simp"),
            priority: 25,
        });
        state.add_entry(&AttrExtEntry {
            decl_name: Name::from_string("instAddNat"),
            attr_name: Name::from_string("instance"),
            priority: 100,
        });

        let simp_decls = state.get_decls_with_attr(&Name::from_string("simp"));
        assert_eq!(simp_decls.len(), 2);
        assert_eq!(simp_decls[0], Name::from_string("Nat.add_comm"));
        assert_eq!(simp_decls[1], Name::from_string("List.append_assoc"));

        let instance_decls = state.get_decls_with_attr(&Name::from_string("instance"));
        assert_eq!(instance_decls.len(), 1);
        assert_eq!(instance_decls[0], Name::from_string("instAddNat"));

        assert!(state
            .get_decls_with_attr(&Name::from_string("reducible"))
            .is_empty());
    }

    #[test]
    fn test_attr_ext_state_export_import_roundtrip() {
        let mut state = AttrExtState::default();
        state.add_entry(&AttrExtEntry {
            decl_name: Name::from_string("foo"),
            attr_name: Name::from_string("simp"),
            priority: 0,
        });
        state.add_entry(&AttrExtEntry {
            decl_name: Name::from_string("foo"),
            attr_name: Name::from_string("inline"),
            priority: 100,
        });
        state.add_entry(&AttrExtEntry {
            decl_name: Name::from_string("bar"),
            attr_name: Name::from_string("instance"),
            priority: 42,
        });

        let exported = state.export_entries();
        assert_eq!(exported.len(), 3);

        let mut state2 = AttrExtState::default();
        for entry in &exported {
            if let Some(typed) = AttrExtEntry::from_env_entry(entry) {
                state2.add_entry(&typed);
            }
        }

        assert_eq!(state2.len(), 3);
        assert!(state2.has_attr(&Name::from_string("foo"), &Name::from_string("simp")));
        assert!(state2.has_attr(&Name::from_string("foo"), &Name::from_string("inline")));
        assert!(state2.has_attr(&Name::from_string("bar"), &Name::from_string("instance")));
        assert_eq!(
            state2.get_decls_with_attr(&Name::from_string("inline")),
            &[Name::from_string("foo")]
        );
    }

    #[test]
    fn test_attr_ext_idx_stable() {
        let idx1 = attr_ext_idx();
        let idx2 = attr_ext_idx();
        assert_eq!(idx1, idx2);
    }
}
