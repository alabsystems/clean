// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Simp lemma persistent extension.
//!
//! This is the first concrete persistent extension, validating the
//! `PersistentExtState` / `PersistentExtEntry` design. It stores simp
//! lemma registrations (name + priority) so they survive .olean roundtrip.
//!
//! In Lean 4, simp lemmas are registered via `@[simp]` attribute and stored
//! in the `simpExtension` persistent env extension. When a library module
//! is imported, all its simp lemmas become available to `simp` in downstream
//! files.
//!
//! Reference: Lean 4 `src/Lean/Meta/Tactic/Simp/SimpLemmas.lean`

use crate::name::Name;
use std::collections::HashMap;
use std::sync::OnceLock;

use super::persistent_ext::{
    register_persistent_ext, ExtensionIdx, PersistentExtEntry, PersistentExtState,
};
use super::types::{EnvExtensionEntry, EnvExtensionEntryData, SimpLemmaInfo, SimpPriority};

/// The canonical name for the simp lemma extension.
const SIMP_EXT_NAME: &str = "simpExtension";

/// Lazily-initialized extension index for simp lemmas.
static SIMP_EXT_IDX: OnceLock<ExtensionIdx> = OnceLock::new();

/// Get (or register) the simp extension index.
///
/// Thread-safe: uses OnceLock for initialization.
pub fn simp_ext_idx() -> ExtensionIdx {
    *SIMP_EXT_IDX
        .get_or_init(|| register_persistent_ext::<SimpExtState>(Name::from_string(SIMP_EXT_NAME)))
}

// ============================================================================
// Entry type
// ============================================================================

/// A single simp lemma registration entry.
#[derive(Clone, Debug)]
pub struct SimpExtEntry {
    /// Name of the simp lemma.
    pub name: Name,
    /// Priority level.
    pub priority: SimpPriority,
}

impl PersistentExtEntry for SimpExtEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        // Encode priority as scalar: 0 = default, otherwise custom value.
        let priority_val = match self.priority {
            SimpPriority::Default => 0,
            SimpPriority::Custom(p) => p as u64 | (1u64 << 32), // Set bit 32 to mark custom
        };
        EnvExtensionEntry {
            name: self.name.clone(),
            data: EnvExtensionEntryData::Scalar(priority_val),
        }
    }

    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {
        let priority = match &entry.data {
            EnvExtensionEntryData::Scalar(val) => {
                if *val & (1u64 << 32) != 0 {
                    SimpPriority::Custom((*val & 0xFFFF_FFFF) as u32)
                } else {
                    SimpPriority::Default
                }
            }
            EnvExtensionEntryData::Object(_) => SimpPriority::Default,
        };
        Some(SimpExtEntry {
            name: entry.name.clone(),
            priority,
        })
    }
}

// ============================================================================
// State type
// ============================================================================

/// Aggregated simp lemma state: a map from lemma name to info.
///
/// Built by folding `SimpExtEntry` items from imported modules.
#[derive(Clone, Debug, Default)]
pub struct SimpExtState {
    lemmas: HashMap<Name, SimpLemmaInfo>,
}

impl SimpExtState {
    /// Check if a name is a registered simp lemma.
    pub fn contains(&self, name: &Name) -> bool {
        self.lemmas.contains_key(name)
    }

    /// Get simp lemma info for a name.
    pub fn get(&self, name: &Name) -> Option<&SimpLemmaInfo> {
        self.lemmas.get(name)
    }

    /// Iterate over all registered simp lemmas.
    pub fn iter(&self) -> impl Iterator<Item = &SimpLemmaInfo> {
        self.lemmas.values()
    }

    /// Number of registered simp lemmas.
    pub fn len(&self) -> usize {
        self.lemmas.len()
    }

    /// Returns true if no simp lemmas are registered.
    pub fn is_empty(&self) -> bool {
        self.lemmas.is_empty()
    }
}

impl PersistentExtState for SimpExtState {
    type Entry = SimpExtEntry;

    fn add_entry(&mut self, entry: &SimpExtEntry) {
        self.lemmas.insert(
            entry.name.clone(),
            SimpLemmaInfo {
                name: entry.name.clone(),
                priority: entry.priority,
            },
        );
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        self.lemmas
            .values()
            .map(|info| {
                SimpExtEntry {
                    name: info.name.clone(),
                    priority: info.priority,
                }
                .to_env_entry()
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simp_ext_entry_roundtrip_default_priority() {
        let entry = SimpExtEntry {
            name: Name::from_string("Nat.add_comm"),
            priority: SimpPriority::Default,
        };
        let raw = entry.to_env_entry();
        let decoded = SimpExtEntry::from_env_entry(&raw).unwrap();
        assert_eq!(decoded.name.to_string(), "Nat.add_comm");
        assert_eq!(decoded.priority, SimpPriority::Default);
    }

    #[test]
    fn test_simp_ext_entry_roundtrip_custom_priority() {
        let entry = SimpExtEntry {
            name: Name::from_string("List.length_nil"),
            priority: SimpPriority::Custom(500),
        };
        let raw = entry.to_env_entry();
        let decoded = SimpExtEntry::from_env_entry(&raw).unwrap();
        assert_eq!(decoded.name.to_string(), "List.length_nil");
        assert_eq!(decoded.priority, SimpPriority::Custom(500));
    }

    #[test]
    fn test_simp_ext_state_fold_and_query() {
        let mut state = SimpExtState::default();
        state.add_entry(&SimpExtEntry {
            name: Name::from_string("lem1"),
            priority: SimpPriority::Default,
        });
        state.add_entry(&SimpExtEntry {
            name: Name::from_string("lem2"),
            priority: SimpPriority::Custom(200),
        });

        assert_eq!(state.len(), 2);
        assert!(state.contains(&Name::from_string("lem1")));
        assert!(state.contains(&Name::from_string("lem2")));
        assert!(!state.contains(&Name::from_string("lem3")));

        let info = state.get(&Name::from_string("lem2")).unwrap();
        assert_eq!(info.priority, SimpPriority::Custom(200));
    }

    #[test]
    fn test_simp_ext_state_export_import_roundtrip() {
        let mut state = SimpExtState::default();
        state.add_entry(&SimpExtEntry {
            name: Name::from_string("a"),
            priority: SimpPriority::Default,
        });
        state.add_entry(&SimpExtEntry {
            name: Name::from_string("b"),
            priority: SimpPriority::Custom(42),
        });

        let exported = state.export_entries();
        assert_eq!(exported.len(), 2);

        // Re-import
        let mut state2 = SimpExtState::default();
        for entry in &exported {
            if let Some(typed) = SimpExtEntry::from_env_entry(entry) {
                state2.add_entry(&typed);
            }
        }
        assert_eq!(state2.len(), 2);
        assert!(state2.contains(&Name::from_string("a")));
        assert!(state2.contains(&Name::from_string("b")));
    }

    #[test]
    fn test_simp_ext_idx_stable() {
        let idx1 = simp_ext_idx();
        let idx2 = simp_ext_idx();
        assert_eq!(idx1, idx2);
    }
}
