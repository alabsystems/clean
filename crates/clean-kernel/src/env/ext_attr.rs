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
pub(crate) const ATTR_EXT_NAME: &str = "attrExtension";

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
        super::ext_name_payload::encode(&self.attr_name, self.priority)
    }

    fn decode_payload(bytes: &[u8]) -> Option<(Name, u32)> {
        if super::ext_name_payload::is_versioned(bytes) {
            return super::ext_name_payload::decode(bytes);
        }
        // Explicit legacy compatibility: display-string payloads do not carry
        // exact typed identity. Never used for a malformed versioned payload.
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
#[derive(Clone, Debug, Default, PartialEq, Eq)]
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

    /// In declaration-name order, each declaration's registrations in the
    /// order they were made: the export of a state is a function of the
    /// state, not of its hash map's layout (two equal states built in
    /// different orders exported differently, which a local fact's replay
    /// check and `EnvEffect` read as a change).
    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        let mut by_decl: Vec<_> = self.attrs_by_decl.iter().collect();
        by_decl.sort_by(|a, b| a.0.cmp(b.0));
        by_decl
            .into_iter()
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

/// One appended registration as a local fact delta carries it:
/// `(declaration, attribute, priority)`.
pub(crate) type CarriedTag = (Name, Name, u32);

/// The typed state, an empty one when the extension holds nothing, or `Err`
/// while imported entries are still unfolded (the typed state would then
/// not say what the environment holds).
fn folded<'a>(
    env: &'a super::Environment,
    empty: &'a AttrExtState,
) -> Result<&'a AttrExtState, &'static str> {
    match env.get_ext_state::<AttrExtState>(attr_ext_idx()) {
        Some(state) => Ok(state),
        None if env.has_unfolded_extension_entries(ATTR_EXT_NAME) => {
            Err("the attribute extension's imported entries are not folded")
        }
        None => Ok(empty),
    }
}

/// Whether the two environments hold the same attribute registrations: per
/// declaration and per attribute, in registration order.
pub(crate) fn same_registrations(a: &super::Environment, b: &super::Environment) -> bool {
    let empty = AttrExtState::default();
    matches!((folded(a, &empty), folded(b, &empty)), (Ok(a), Ok(b)) if a == b)
}

/// The registrations `after` appended since `before`, in an order that
/// rebuilds `after`'s state exactly, with each touched declaration's
/// registrations before. `Err` when the change is anything but appended
/// registrations: `before` plus the returned tags must equal `after` in both
/// indexes (per declaration and per attribute, order included).
#[allow(clippy::type_complexity)]
pub(crate) fn tags_since(
    before: &super::Environment,
    after: &super::Environment,
) -> Result<(Vec<CarriedTag>, Vec<(Name, Vec<(Name, u32)>)>), &'static str> {
    let empty = AttrExtState::default();
    let (was, now) = (folded(before, &empty)?, folded(after, &empty)?);
    if was == now {
        return Ok((Vec::new(), Vec::new()));
    }
    // Per declaration, the appended suffix; the declarations in name order.
    let mut touched: Vec<(&Name, &[AttrRegistration])> = Vec::new();
    for (decl, registrations) in &now.attrs_by_decl {
        let had = was.get_attrs_for_decl(decl);
        if registrations.len() < had.len() || registrations[..had.len()] != *had {
            return Err("an attribute registration was changed or removed");
        }
        if registrations.len() > had.len() {
            touched.push((decl, &registrations[had.len()..]));
        }
    }
    touched.sort_by(|a, b| a.0.cmp(b.0));
    // Merge the suffixes into one order that also gives each attribute its
    // declarations in `after`'s order: repeatedly take a declaration whose
    // next registration is the next one its attribute's index expects.
    let mut expected: HashMap<&Name, &[Name]> = HashMap::new();
    for (attr, decls) in &now.decls_by_attr {
        let had = was.get_decls_with_attr(attr);
        if decls.len() < had.len() || decls[..had.len()] != *had {
            return Err("an attribute registration was changed or removed");
        }
        expected.insert(attr, &decls[had.len()..]);
    }
    let mut cursor = vec![0usize; touched.len()];
    let mut tags = Vec::new();
    loop {
        let next = touched.iter().enumerate().find(|(index, (decl, suffix))| {
            suffix.get(cursor[*index]).is_some_and(|registration| {
                expected
                    .get(&registration.attr_name)
                    .and_then(|decls| decls.first())
                    == Some(*decl)
            })
        });
        let Some((index, (decl, suffix))) = next else {
            break;
        };
        let registration = &suffix[cursor[index]];
        cursor[index] += 1;
        if let Some(decls) = expected.get_mut(&registration.attr_name) {
            *decls = &decls[1..];
        }
        tags.push((
            (*decl).clone(),
            registration.attr_name.clone(),
            registration.priority,
        ));
    }
    // The check that matters: replaying the tags rebuilds `after` exactly.
    let mut rebuilt = was.clone();
    for (decl_name, attr_name, priority) in &tags {
        rebuilt.add_entry(&AttrExtEntry {
            decl_name: decl_name.clone(),
            attr_name: attr_name.clone(),
            priority: *priority,
        });
    }
    if rebuilt != *now {
        return Err("the attribute registrations changed by more than appended tags");
    }
    let bases = touched
        .iter()
        .map(|(decl, _)| {
            let had = was.get_attrs_for_decl(decl);
            let had = had
                .iter()
                .map(|r| (r.attr_name.clone(), r.priority))
                .collect();
            ((*decl).clone(), had)
        })
        .collect();
    Ok((tags, bases))
}

/// Whether each declaration the carried tags touch holds here exactly the
/// registrations it held before the producing elaboration.
pub(crate) fn tags_fit(
    env: &super::Environment,
    bases: &[(Name, Vec<(Name, u32)>)],
) -> Result<(), String> {
    if bases.is_empty() {
        return Ok(());
    }
    let empty = AttrExtState::default();
    let state = folded(env, &empty).map_err(str::to_string)?;
    for (decl, base) in bases {
        let here = state.get_attrs_for_decl(decl);
        let same = here.len() == base.len()
            && here
                .iter()
                .zip(base)
                .all(|(registration, (attr, priority))| {
                    registration.attr_name == *attr && registration.priority == *priority
                });
        if !same {
            return Err(format!("the attributes of `{decl}` are different here"));
        }
    }
    Ok(())
}

/// Append carried tags (after [`tags_fit`]).
pub(crate) fn apply_tags(env: &mut super::Environment, tags: &[CarriedTag]) {
    for (decl_name, attr_name, priority) in tags {
        env.add_ext_entry::<AttrExtState>(
            attr_ext_idx(),
            &AttrExtEntry {
                decl_name: decl_name.clone(),
                attr_name: attr_name.clone(),
                priority: *priority,
            },
        );
    }
}

/// A declaration's registrations, for the elaboration record digest.
pub(crate) fn registrations_of<'a>(
    env: &'a super::Environment,
    decl: &Name,
) -> &'a [AttrRegistration] {
    env.get_ext_state::<AttrExtState>(attr_ext_idx())
        .map_or(&[], |state| state.get_attrs_for_decl(decl))
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
