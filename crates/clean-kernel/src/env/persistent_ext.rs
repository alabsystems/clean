// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed persistent environment extension framework.
//!
//! Implements Lean 4-style `registerPersistentEnvExtension` semantics: a global
//! registry of typed extensions that survive .olean roundtrip. On import, raw
//! entries are folded into typed state; on export, state is serialized back.
//!
//! Reference: Lean 4 `src/Lean/Environment.lean`.

use crate::name::Name;
use hashbrown::HashMap;
use std::any::Any;
use std::sync::OnceLock;

use super::types::{EnvExtensionEntry, PersistentEnvExtensionState};

/// Unique index for a registered environment extension.
/// Assigned sequentially during global registration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExtensionIdx(pub(crate) u32);

impl ExtensionIdx {
    /// Get the raw index value.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A typed persistent extension entry serializable to/from `EnvExtensionEntry`.
pub trait PersistentExtEntry: Clone + Send + Sync + 'static {
    /// Serialize this entry to an `EnvExtensionEntry` for .olean export.
    fn to_env_entry(&self) -> EnvExtensionEntry;

    /// Deserialize from an `EnvExtensionEntry` loaded from .olean.
    /// Returns `None` if the entry format is unrecognized.
    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self>;
}

/// Aggregated state for a persistent extension, built by folding entries.
///
/// Implementations accumulate entries into a queryable data structure
/// (e.g., a HashMap of simp lemmas, a set of registered attributes).
pub trait PersistentExtState: Clone + Default + Send + Sync + 'static {
    /// The entry type that this state is built from.
    type Entry: PersistentExtEntry;

    /// Fold a single entry into this state.
    fn add_entry(&mut self, entry: &Self::Entry);

    /// Export the current state as entries for .olean serialization.
    fn export_entries(&self) -> Vec<EnvExtensionEntry>;
}

// ============================================================================
// Type-erased extension state holder
// ============================================================================

/// Type-erased wrapper around extension state, enabling heterogeneous storage.
pub(crate) trait ExtensionStateHolder: Send + Sync {
    /// Clone into a new Box.
    fn clone_box(&self) -> Box<dyn ExtensionStateHolder>;

    /// Fold raw entries from .olean import into typed state.
    fn fold_raw_entries(&mut self, entries: &[EnvExtensionEntry]);

    /// Export typed state back to raw entries for .olean export.
    fn export_raw_entries(&self) -> Vec<EnvExtensionEntry>;

    /// Returns true if entries have been folded into state.
    fn is_initialized(&self) -> bool;

    /// Mark as initialized (for empty-import case).
    fn mark_initialized(&mut self);

    /// Downcast to concrete type for typed access.
    fn as_any(&self) -> &dyn Any;

    /// Downcast to concrete type for typed mutable access.
    fn as_any_mut(&mut self) -> &mut dyn Any;
}

/// Concrete typed holder for a specific extension state type.
pub(crate) struct TypedStateHolder<S: PersistentExtState> {
    pub(crate) state: S,
    initialized: bool,
}

impl<S: PersistentExtState> TypedStateHolder<S> {
    pub(crate) fn new() -> Self {
        Self {
            state: S::default(),
            initialized: false,
        }
    }

    pub(crate) fn state(&self) -> &S {
        &self.state
    }

    pub(crate) fn state_mut(&mut self) -> &mut S {
        &mut self.state
    }
}

impl<S: PersistentExtState + 'static> ExtensionStateHolder for TypedStateHolder<S> {
    fn clone_box(&self) -> Box<dyn ExtensionStateHolder> {
        Box::new(TypedStateHolder {
            state: self.state.clone(),
            initialized: self.initialized,
        })
    }

    fn fold_raw_entries(&mut self, entries: &[EnvExtensionEntry]) {
        for entry in entries {
            if let Some(typed) = S::Entry::from_env_entry(entry) {
                self.state.add_entry(&typed);
            }
        }
        self.initialized = true;
    }

    fn export_raw_entries(&self) -> Vec<EnvExtensionEntry> {
        self.state.export_entries()
    }

    fn is_initialized(&self) -> bool {
        self.initialized
    }

    fn mark_initialized(&mut self) {
        self.initialized = true;
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

// ============================================================================
// Extension Descriptor
// ============================================================================

/// Describes a persistent extension registration. Stored in the global
/// registry; used to create initial state holders in new environments.
pub(crate) struct ExtensionDescriptor {
    /// Unique extension name (e.g., "simpExtension").
    pub(crate) name: Name,

    /// Factory function: create a fresh, empty typed state holder.
    pub(crate) create_state: fn() -> Box<dyn ExtensionStateHolder>,
}

// ============================================================================
// Global Extension Registry
// ============================================================================

/// Global registry of all persistent environment extensions.
///
/// Extensions are registered once during initialization. The registry is
/// append-only (new extensions can be added, but existing ones never removed).
///
/// This mirrors Lean 4's global extension registration via `initialize_*`
/// functions called during module initialization.
pub(crate) struct ExtensionRegistry {
    descriptors: Vec<ExtensionDescriptor>,
    name_to_idx: HashMap<Name, ExtensionIdx>,
}

impl ExtensionRegistry {
    fn new() -> Self {
        Self {
            descriptors: Vec::new(),
            name_to_idx: HashMap::new(),
        }
    }

    /// Register a new persistent extension. Returns the assigned index.
    /// If already registered, returns the existing index.
    fn register<S: PersistentExtState>(&mut self, name: Name) -> ExtensionIdx {
        if let Some(&existing) = self.name_to_idx.get(&name) {
            return existing;
        }
        let idx = ExtensionIdx(self.descriptors.len() as u32);
        self.descriptors.push(ExtensionDescriptor {
            name: name.clone(),
            create_state: || Box::new(TypedStateHolder::<S>::new()),
        });
        self.name_to_idx.insert(name, idx);
        idx
    }

    pub(crate) fn get_idx(&self, name: &Name) -> Option<ExtensionIdx> {
        self.name_to_idx.get(name).copied()
    }

    pub(crate) fn get_descriptor(&self, idx: ExtensionIdx) -> Option<&ExtensionDescriptor> {
        self.descriptors.get(idx.index())
    }

    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(crate) fn len(&self) -> usize {
        self.descriptors.len()
    }

    pub(crate) fn descriptors(&self) -> &[ExtensionDescriptor] {
        &self.descriptors
    }
}

// ============================================================================
// Global registry singleton
// ============================================================================

static REGISTRY: OnceLock<std::sync::Mutex<ExtensionRegistry>> = OnceLock::new();

pub(crate) fn global_registry() -> &'static std::sync::Mutex<ExtensionRegistry> {
    REGISTRY.get_or_init(|| std::sync::Mutex::new(ExtensionRegistry::new()))
}

/// Register a persistent environment extension globally.
///
/// This is the Rust equivalent of Lean 4's `registerPersistentEnvExtension`.
/// Should be called once per extension, typically during initialization.
///
/// Returns the `ExtensionIdx` for fast typed state access.
///
/// # Thread Safety
/// Safe to call from multiple threads; registration is serialized.
pub fn register_persistent_ext<S: PersistentExtState>(name: Name) -> ExtensionIdx {
    let mut reg = global_registry()
        .lock()
        .expect("invariant: extension registry mutex not poisoned");
    reg.register::<S>(name)
}

/// Look up an extension index by name. Returns `None` if not registered.
pub fn get_ext_idx(name: &Name) -> Option<ExtensionIdx> {
    let reg = global_registry()
        .lock()
        .expect("invariant: extension registry mutex not poisoned");
    reg.get_idx(name)
}

/// Get the number of registered extensions.
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) fn registered_ext_count() -> usize {
    let reg = global_registry()
        .lock()
        .expect("invariant: extension registry mutex not poisoned");
    reg.len()
}

// ============================================================================
// Per-Environment Extension State Map
// ============================================================================

/// Per-environment extension state storage.
///
/// Each environment holds materialized typed state for every registered
/// extension. State is lazily initialized from imported raw entries.
pub(crate) struct EnvExtensionStates {
    /// Typed extension state holders, indexed by ExtensionIdx.
    states: Vec<Option<Box<dyn ExtensionStateHolder>>>,
}

impl Clone for EnvExtensionStates {
    fn clone(&self) -> Self {
        Self {
            states: self
                .states
                .iter()
                .map(|s| s.as_ref().map(|h| h.clone_box()))
                .collect(),
        }
    }
}

impl std::fmt::Debug for EnvExtensionStates {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let active = self.states.iter().filter(|s| s.is_some()).count();
        f.debug_struct("EnvExtensionStates")
            .field("active_count", &active)
            .finish()
    }
}

impl Default for EnvExtensionStates {
    fn default() -> Self {
        Self::new()
    }
}

impl EnvExtensionStates {
    /// Create a new empty extension state map.
    pub(crate) fn new() -> Self {
        Self { states: Vec::new() }
    }

    /// Ensure the state holder for the given extension exists.
    fn ensure_state(&mut self, idx: ExtensionIdx) {
        let index = idx.index();
        if self.states.len() <= index {
            self.states.resize_with(index + 1, || None);
        }
        if self.states[index].is_none() {
            let reg = global_registry()
                .lock()
                .expect("invariant: extension registry mutex not poisoned");
            if let Some(desc) = reg.get_descriptor(idx) {
                self.states[index] = Some((desc.create_state)());
            }
        }
    }

    /// Get a typed reference to extension state.
    ///
    /// Returns `None` if the extension is not registered, not yet
    /// materialized, or the type doesn't match.
    pub(crate) fn get_state<S: PersistentExtState + 'static>(
        &self,
        idx: ExtensionIdx,
    ) -> Option<&S> {
        self.states
            .get(idx.index())?
            .as_ref()?
            .as_any()
            .downcast_ref::<TypedStateHolder<S>>()
            .map(|h| h.state())
    }

    /// Get a mutable typed reference to extension state.
    ///
    /// Creates the state holder if it doesn't exist.
    pub(crate) fn get_state_mut<S: PersistentExtState + 'static>(
        &mut self,
        idx: ExtensionIdx,
    ) -> &mut S {
        self.ensure_state(idx);
        self.states[idx.index()]
            .as_mut()
            .expect("invariant: ensured above")
            .as_any_mut()
            .downcast_mut::<TypedStateHolder<S>>()
            .expect("invariant: extension type matches registration")
            .state_mut()
    }

    /// Fold imported entries from raw persistent extension store into
    /// typed state for a specific extension.
    pub(crate) fn fold_imported_entries(
        &mut self,
        idx: ExtensionIdx,
        raw_entries: &[EnvExtensionEntry],
    ) {
        self.ensure_state(idx);
        if let Some(holder) = self.states.get_mut(idx.index()).and_then(|s| s.as_mut()) {
            if !holder.is_initialized() {
                holder.fold_raw_entries(raw_entries);
            }
        }
    }

    /// Fold all imported entries from raw persistent extension store.
    /// Called after .olean import to materialize typed state for all
    /// registered extensions that have imported data.
    pub(crate) fn fold_all_imported(
        &mut self,
        raw_extensions: &HashMap<Name, PersistentEnvExtensionState>,
    ) {
        let descriptors: Vec<(Name, ExtensionIdx, fn() -> Box<dyn ExtensionStateHolder>)> = {
            let reg = global_registry()
                .lock()
                .expect("invariant: extension registry mutex not poisoned");
            reg.descriptors()
                .iter()
                .enumerate()
                .map(|(i, desc)| (desc.name.clone(), ExtensionIdx(i as u32), desc.create_state))
                .collect()
        };

        for (name, idx, create_fn) in descriptors {
            if let Some(raw_state) = raw_extensions.get(&name) {
                let index = idx.index();
                if self.states.len() <= index {
                    self.states.resize_with(index + 1, || None);
                }
                if self.states[index].is_none() {
                    self.states[index] = Some(create_fn());
                }

                if let Some(holder) = self.states[index].as_mut() {
                    if !holder.is_initialized() {
                        let entries_flat: Vec<EnvExtensionEntry> = raw_state
                            .imported_entries
                            .iter()
                            .flat_map(|module_entries| module_entries.iter())
                            .cloned()
                            .collect();
                        holder.fold_raw_entries(&entries_flat);
                    }
                }
            }
        }
    }

    /// Export all extension states to raw entries for .olean serialization.
    ///
    /// Returns pairs of (extension_name, entries).
    pub(crate) fn export_all(&self) -> Vec<(Name, Vec<EnvExtensionEntry>)> {
        let descriptors: Vec<Name> = {
            let reg = global_registry()
                .lock()
                .expect("invariant: extension registry mutex not poisoned");
            reg.descriptors().iter().map(|d| d.name.clone()).collect()
        };

        let mut result = Vec::new();
        for (i, state) in self.states.iter().enumerate() {
            if let Some(holder) = state {
                let entries = holder.export_raw_entries();
                if !entries.is_empty() {
                    if let Some(name) = descriptors.get(i) {
                        result.push((name.clone(), entries));
                    }
                }
            }
        }
        result
    }

    /// Check if a specific extension has initialized state.
    pub(crate) fn is_initialized(&self, idx: ExtensionIdx) -> bool {
        self.states
            .get(idx.index())
            .and_then(|s| s.as_ref())
            .is_some_and(|h| h.is_initialized())
    }

    /// Add a typed entry to an extension's state.
    ///
    /// If the state hasn't been initialized yet, it will be created and
    /// marked as initialized.
    pub(crate) fn add_entry<S: PersistentExtState + 'static>(
        &mut self,
        idx: ExtensionIdx,
        entry: &S::Entry,
    ) {
        self.ensure_state(idx);
        if let Some(holder) = self.states.get_mut(idx.index()).and_then(|s| s.as_mut()) {
            if !holder.is_initialized() {
                holder.mark_initialized();
            }
            holder
                .as_any_mut()
                .downcast_mut::<TypedStateHolder<S>>()
                .expect("invariant: extension type matches registration")
                .state
                .add_entry(entry);
        }
    }
}

// ============================================================================
// Serde support for EnvExtensionStates
// ============================================================================

// EnvExtensionStates is not directly serializable because it holds trait
// objects. Instead, it is reconstructed from `persistent_extensions` during
// deserialization (fold_all_imported). For Environment serialization, we
// skip the typed states and rely on the raw `persistent_extensions` field.

impl serde::Serialize for EnvExtensionStates {
    fn serialize<Ser: serde::Serializer>(&self, serializer: Ser) -> Result<Ser::Ok, Ser::Error> {
        // Serialize as unit — actual state is reconstructed from persistent_extensions
        serializer.serialize_unit()
    }
}

impl<'de> serde::Deserialize<'de> for EnvExtensionStates {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Deserialize as unit, return empty (will be populated from persistent_extensions)
        <()>::deserialize(deserializer)?;
        Ok(Self::new())
    }
}
