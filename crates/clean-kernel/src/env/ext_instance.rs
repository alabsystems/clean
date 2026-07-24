// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance registry persistent extension.
//!
//! Stores typeclass instance registrations so they survive .olean roundtrip.
//! Entries are folded into a class-indexed instance table with per-class
//! priority ordering matching the main environment registry.
//!
//! In Lean 4, instances are registered via `@[instance]` attribute and stored
//! in the `instanceExtension` persistent env extension. When a library module
//! is imported, all its instances become available for instance resolution in
//! downstream files.
//!
//! Reference: Lean 4 `src/Lean/Meta/Instances.lean`

use crate::name::Name;
use std::collections::HashMap;
use std::sync::OnceLock;

use super::persistent_ext::{
    register_persistent_ext, ExtensionIdx, PersistentExtEntry, PersistentExtState,
};
use super::types::{EnvExtensionEntry, EnvExtensionEntryData, DEFAULT_INSTANCE_PRIORITY};

/// The canonical name for the instance extension.
const INSTANCE_EXT_NAME: &str = "instanceExtension";

/// Number of bytes used to store the scalar priority prefix inside object data.
const PRIORITY_BYTES: usize = (u64::BITS / 8) as usize;

/// Lazily-initialized extension index for instances.
static INSTANCE_EXT_IDX: OnceLock<ExtensionIdx> = OnceLock::new();

/// Get (or register) the instance extension index.
///
/// Thread-safe: uses OnceLock for initialization.
pub fn instance_ext_idx() -> ExtensionIdx {
    *INSTANCE_EXT_IDX.get_or_init(|| {
        register_persistent_ext::<InstanceExtState>(Name::from_string(INSTANCE_EXT_NAME))
    })
}

// ============================================================================
// Entry type
// ============================================================================

/// A single instance registration entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstanceExtEntry {
    /// Name of the instance definition.
    pub instance_name: Name,
    /// Name of the class this instance belongs to.
    pub class_name: Name,
    /// Priority (higher = tried first).
    pub priority: u32,
}

impl InstanceExtEntry {
    fn encode_payload(&self) -> Vec<u8> {
        let mut payload = Vec::with_capacity(PRIORITY_BYTES + self.class_name.to_string().len());
        payload.extend_from_slice(&(self.priority as u64).to_le_bytes());
        payload.extend_from_slice(self.class_name.to_string().as_bytes());
        payload
    }

    fn decode_payload(bytes: &[u8]) -> Option<(Name, u32)> {
        if bytes.len() < PRIORITY_BYTES {
            return None;
        }

        let priority =
            u32::try_from(u64::from_le_bytes(bytes[..PRIORITY_BYTES].try_into().ok()?)).ok()?;
        let class_name = std::str::from_utf8(&bytes[PRIORITY_BYTES..]).ok()?;
        Some((Name::from_string(class_name), priority))
    }
}

impl PersistentExtEntry for InstanceExtEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: self.instance_name.clone(),
            data: EnvExtensionEntryData::Object(self.encode_payload()),
        }
    }

    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {
        let (class_name, priority) = match &entry.data {
            // Real Lean `.olean`s serialize each `instanceExtension` entry in
            // Lean's own `InstanceEntry` encoding (DiscrTree keys + priority),
            // NOT Clean's priority+class payload, so `decode_payload` cannot
            // recover the class. The entry NAME is authoritative either way, so
            // keep the entry with an ANONYMOUS class placeholder rather than
            // dropping it; `register_instances_from_extension` derives the real
            // class from the imported constant's own type at registration time.
            // (Without this, every imported stdlib `@[instance]` was silently
            // invisible to typeclass resolution.)
            EnvExtensionEntryData::Object(bytes) => {
                Self::decode_payload(bytes).unwrap_or((Name::anon(), DEFAULT_INSTANCE_PRIORITY))
            }
            EnvExtensionEntryData::Scalar(_) => return None,
        };

        Some(Self {
            instance_name: entry.name.clone(),
            class_name,
            priority,
        })
    }
}

// ============================================================================
// State type
// ============================================================================

/// Queryable instance metadata stored by the persistent extension.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstanceInfo {
    /// Name of the instance definition.
    pub instance_name: Name,
    /// Name of the class this instance belongs to.
    pub class_name: Name,
    /// Priority (higher = tried first).
    pub priority: u32,
}

/// Aggregated instance state: instances grouped by class name.
///
/// Built by folding `InstanceExtEntry` items from imported modules.
#[derive(Clone, Debug, Default)]
pub struct InstanceExtState {
    instances: HashMap<Name, Vec<InstanceInfo>>,
}

impl InstanceExtState {
    /// Get instances for a class, sorted by priority (highest first).
    pub fn get_instances_for_class(&self, class_name: &Name) -> &[InstanceInfo] {
        self.instances.get(class_name).map_or(&[], Vec::as_slice)
    }

    /// Check if an instance definition has been registered.
    pub fn contains_instance(&self, instance_name: &Name) -> bool {
        self.all_instances()
            .any(|info| &info.instance_name == instance_name)
    }

    /// Iterate over all registered instances across all classes.
    pub fn all_instances(&self) -> impl Iterator<Item = &InstanceInfo> {
        self.instances
            .values()
            .flat_map(|instances| instances.iter())
    }

    /// Number of registered instances.
    pub fn len(&self) -> usize {
        self.instances.values().map(Vec::len).sum()
    }

    /// Returns true if no instances are registered.
    pub fn is_empty(&self) -> bool {
        self.instances.is_empty()
    }
}

impl PersistentExtState for InstanceExtState {
    type Entry = InstanceExtEntry;

    fn add_entry(&mut self, entry: &InstanceExtEntry) {
        let instances = self.instances.entry(entry.class_name.clone()).or_default();
        let info = InstanceInfo {
            instance_name: entry.instance_name.clone(),
            class_name: entry.class_name.clone(),
            priority: entry.priority,
        };

        let pos = instances
            .iter()
            .position(|existing| existing.priority < info.priority)
            .unwrap_or(instances.len());
        instances.insert(pos, info);
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        self.instances
            .values()
            .flat_map(|instances| {
                instances.iter().map(|info| {
                    InstanceExtEntry {
                        instance_name: info.instance_name.clone(),
                        class_name: info.class_name.clone(),
                        priority: info.priority,
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
    fn test_instance_ext_entry_roundtrip() {
        let entry = InstanceExtEntry {
            instance_name: Name::from_string("instHAddNat"),
            class_name: Name::from_string("HAdd"),
            priority: 200,
        };

        let raw = entry.to_env_entry();
        assert_eq!(raw.name.to_string(), "instHAddNat");
        assert!(matches!(raw.data, EnvExtensionEntryData::Object(_)));

        let decoded = InstanceExtEntry::from_env_entry(&raw).unwrap();
        assert_eq!(decoded.instance_name.to_string(), "instHAddNat");
        assert_eq!(decoded.class_name.to_string(), "HAdd");
        assert_eq!(decoded.priority, 200);
    }

    #[test]
    fn test_instance_ext_state_fold_and_query() {
        let mut state = InstanceExtState::default();
        assert!(state.is_empty());

        state.add_entry(&InstanceExtEntry {
            instance_name: Name::from_string("instHAddNat"),
            class_name: Name::from_string("HAdd"),
            priority: 100,
        });
        state.add_entry(&InstanceExtEntry {
            instance_name: Name::from_string("instHAddInt"),
            class_name: Name::from_string("HAdd"),
            priority: 200,
        });
        state.add_entry(&InstanceExtEntry {
            instance_name: Name::from_string("instOfNatNat"),
            class_name: Name::from_string("OfNat"),
            priority: 50,
        });

        assert_eq!(state.len(), 3);
        assert!(!state.is_empty());
        assert!(state.contains_instance(&Name::from_string("instHAddNat")));
        assert!(state.contains_instance(&Name::from_string("instOfNatNat")));
        assert!(!state.contains_instance(&Name::from_string("instMissing")));

        let hadd_instances = state.get_instances_for_class(&Name::from_string("HAdd"));
        assert_eq!(hadd_instances.len(), 2);
        assert_eq!(
            hadd_instances[0].instance_name,
            Name::from_string("instHAddInt")
        );
        assert_eq!(hadd_instances[0].priority, 200);
        assert_eq!(
            hadd_instances[1].instance_name,
            Name::from_string("instHAddNat")
        );
        assert_eq!(hadd_instances[1].priority, 100);

        let all: Vec<_> = state.all_instances().collect();
        assert_eq!(all.len(), 3);
    }

    #[test]
    fn test_instance_ext_state_export_import_roundtrip() {
        let mut state = InstanceExtState::default();
        state.add_entry(&InstanceExtEntry {
            instance_name: Name::from_string("instLTNat"),
            class_name: Name::from_string("LT"),
            priority: 300,
        });
        state.add_entry(&InstanceExtEntry {
            instance_name: Name::from_string("instLENat"),
            class_name: Name::from_string("LE"),
            priority: 120,
        });
        state.add_entry(&InstanceExtEntry {
            instance_name: Name::from_string("instLTInt"),
            class_name: Name::from_string("LT"),
            priority: 500,
        });

        let exported = state.export_entries();
        assert_eq!(exported.len(), 3);

        let mut state2 = InstanceExtState::default();
        for entry in &exported {
            if let Some(typed) = InstanceExtEntry::from_env_entry(entry) {
                state2.add_entry(&typed);
            }
        }

        let lt_instances = state2.get_instances_for_class(&Name::from_string("LT"));
        assert_eq!(lt_instances.len(), 2);
        assert_eq!(
            lt_instances[0].instance_name,
            Name::from_string("instLTInt")
        );
        assert_eq!(
            lt_instances[1].instance_name,
            Name::from_string("instLTNat")
        );
        assert!(state2.contains_instance(&Name::from_string("instLENat")));
    }

    #[test]
    fn test_instance_ext_idx_stable() {
        let idx1 = instance_ext_idx();
        let idx2 = instance_ext_idx();
        assert_eq!(idx1, idx2);
    }
}
