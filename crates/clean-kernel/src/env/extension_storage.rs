// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The persistent-extension storage of an [`Environment`](super::Environment)
//! and the matcher index derived from it, held in one value.
//!
//! The index is a function of the `Clean.matcherInfo.v1` entries in this
//! storage. Holding both in one type with private fields makes that a property
//! of the type rather than of every caller: each constructor (the default, a
//! serde restore, a DAG restore, a clone) and each mutator below leaves the
//! index equal to [`MatcherIndex::decode`] of the storage, and there is no
//! other way to build one or to change its entries. The `Environment` derives
//! its serde impls directly, so its only deserialization of this field is
//! [`PersistentExtensions`]'s own, which derives the index
//! (`docs/DECISIONS.md`, 2026-11-15, "The matcher index lives in its storage").

use super::matcher::{is_matcher_storage, matcher_storage_key, MatcherIndex, MatcherInfo};
use super::{EnvExtensionEntry, PersistentEnvExtensionState};
use crate::Name;
use hashbrown::HashMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Every persistent extension's state, by extension name, and the matcher
/// index decoded from the matcher entries among them.
///
/// Plain data: two maps, no cell. Serialized as the map of states alone, the
/// form an `Environment` has always persisted; the index is never persisted.
#[derive(Clone, Debug, Default)]
pub(super) struct PersistentExtensions {
    states: HashMap<Name, PersistentEnvExtensionState>,
    matcher: MatcherIndex,
}

impl PersistentExtensions {
    /// Empty storage with room for `capacity` extensions.
    pub(super) fn with_capacity(capacity: usize) -> Self {
        Self {
            states: HashMap::with_capacity(capacity),
            matcher: MatcherIndex::default(),
        }
    }

    /// Adopt restored states, deriving their index. Every restore builds its
    /// storage here.
    pub(super) fn from_states(states: HashMap<Name, PersistentEnvExtensionState>) -> Self {
        let matcher = MatcherIndex::decode(states.get(&matcher_storage_key()));
        Self { states, matcher }
    }

    /// Every extension's state, read-only.
    pub(super) fn states(&self) -> &HashMap<Name, PersistentEnvExtensionState> {
        &self.states
    }

    /// One extension's state.
    pub(super) fn get(&self, extension: &Name) -> Option<&PersistentEnvExtensionState> {
        self.states.get(extension)
    }

    /// The decoded matcher storage.
    pub(super) fn matcher_index(&self) -> &MatcherIndex {
        &self.matcher
    }

    /// The matcher metadata every stored entry for `name` agrees on, if any.
    pub(super) fn matcher_info(&self, name: &Name) -> Option<&MatcherInfo> {
        self.matcher.lookup(name)
    }

    /// Register an extension with no entries; `false` when it is present.
    /// A present extension keeps its entries, so the index stays its decode.
    pub(super) fn register(&mut self, extension: Name) -> bool {
        if self.states.contains_key(&extension) {
            return false;
        }
        self.states
            .insert(extension, PersistentEnvExtensionState::default());
        true
    }

    /// Append `entries` to `extension` at `module_idx`. Every append to any
    /// extension takes this path; matcher entries are folded into the index
    /// here, each one (the fold does not depend on order, so the index stays
    /// equal to a decode of the whole storage).
    pub(super) fn append(
        &mut self,
        extension: &Name,
        module_idx: usize,
        entries: Vec<EnvExtensionEntry>,
    ) {
        if is_matcher_storage(extension) {
            for entry in &entries {
                self.matcher.absorb(entry);
            }
        }
        let state = self.states.entry(extension.clone()).or_default();
        if state.imported_entries.len() <= module_idx {
            state.imported_entries.resize_with(module_idx + 1, Vec::new);
        }
        state.imported_entries[module_idx].extend(entries);
    }

    /// Drop every stored matcher entry for `name`, in every module, and its
    /// index row: no entry for `name` is left, so a decode has no row for it.
    pub(super) fn forget_matcher_rows(&mut self, name: &Name) {
        if let Some(state) = self.states.get_mut(&matcher_storage_key()) {
            for module in &mut state.imported_entries {
                module.retain(|entry| &entry.name != name);
            }
        }
        self.matcher.remove(name);
    }

    /// Replace (`Some`) or remove (`None`) one extension's whole state, as a
    /// local fact delta does. Replacing the matcher storage re-derives the
    /// index from what replaced it.
    pub(super) fn set_state(
        &mut self,
        extension: &Name,
        state: Option<PersistentEnvExtensionState>,
    ) {
        match state {
            Some(state) => {
                self.states.insert(extension.clone(), state);
            }
            None => {
                self.states.remove(extension);
            }
        }
        if is_matcher_storage(extension) {
            self.matcher = MatcherIndex::decode(self.states.get(extension));
        }
    }
}

impl Serialize for PersistentExtensions {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.states.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for PersistentExtensions {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        HashMap::deserialize(deserializer).map(Self::from_states)
    }
}

#[cfg(test)]
#[path = "extension_storage_tests.rs"]
mod tests;
