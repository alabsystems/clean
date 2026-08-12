// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the persistent environment extension framework.
//!
//! Tests the full lifecycle: register extension, add entries to an Environment,
//! export to raw entries, re-import, and verify typed state survives.

use super::ext_simp::{simp_ext_idx, SimpExtEntry, SimpExtState};
use super::persistent_ext::{
    get_ext_idx, register_persistent_ext, EnvExtensionStates, PersistentExtEntry,
    PersistentExtState,
};
use super::types::{
    EnvExtensionEntry, EnvExtensionEntryData, PersistentEnvExtensionState, SimpPriority,
};
use super::Environment;
use crate::name::Name;
use hashbrown::HashMap;

// ============================================================================
// End-to-end test: simp extension through Environment API
// ============================================================================

#[test]
fn test_env_add_simp_ext_entry_and_query() {
    let mut env = Environment::default();
    let idx = simp_ext_idx();

    // Add a simp lemma via the typed extension API
    env.add_ext_entry::<SimpExtState>(
        idx,
        &SimpExtEntry {
            name: Name::from_string("Nat.add_comm"),
            priority: SimpPriority::Default,
        },
    );
    env.add_ext_entry::<SimpExtState>(
        idx,
        &SimpExtEntry {
            name: Name::from_string("List.length_nil"),
            priority: SimpPriority::Custom(500),
        },
    );

    // Query via typed API
    let state = env.get_ext_state::<SimpExtState>(idx).unwrap();
    assert_eq!(state.len(), 2);
    assert!(state.contains(&Name::from_string("Nat.add_comm")));
    assert!(state.contains(&Name::from_string("List.length_nil")));

    let info = state.get(&Name::from_string("List.length_nil")).unwrap();
    assert_eq!(info.priority, SimpPriority::Custom(500));
}

#[test]
fn test_env_export_and_reimport_simp_extension() {
    let mut env1 = Environment::default();
    let idx = simp_ext_idx();

    // Add entries
    env1.add_ext_entry::<SimpExtState>(
        idx,
        &SimpExtEntry {
            name: Name::from_string("Nat.add_zero"),
            priority: SimpPriority::Default,
        },
    );
    env1.add_ext_entry::<SimpExtState>(
        idx,
        &SimpExtEntry {
            name: Name::from_string("Nat.zero_add"),
            priority: SimpPriority::Custom(1200),
        },
    );

    // Export
    let exported = env1.export_extension_states();
    assert_eq!(exported.len(), 1, "one extension exported");
    let (ext_name, entries) = &exported[0];
    assert_eq!(ext_name.to_string(), "simpExtension");
    assert_eq!(entries.len(), 2);

    // Simulate .olean re-import: construct a new env with raw entries
    let mut env2 = Environment::default();
    // Store raw entries as if they came from .olean import
    let mut raw_state = PersistentEnvExtensionState::default();
    raw_state.imported_entries.push(entries.clone());
    env2.register_persistent_extension(ext_name.clone());
    env2.add_persistent_extension_entries(ext_name, 0, entries.clone());

    // Materialize typed states
    env2.materialize_extension_states();

    // Verify typed state survived roundtrip
    let state2 = env2.get_ext_state::<SimpExtState>(idx).unwrap();
    assert_eq!(state2.len(), 2);
    assert!(state2.contains(&Name::from_string("Nat.add_zero")));
    assert!(state2.contains(&Name::from_string("Nat.zero_add")));

    let info = state2.get(&Name::from_string("Nat.zero_add")).unwrap();
    assert_eq!(info.priority, SimpPriority::Custom(1200));
}

#[test]
fn test_env_lazy_init_from_raw_imports() {
    let mut env = Environment::default();
    let idx = simp_ext_idx();
    let ext_name = Name::from_string("simpExtension");

    // Simulate raw entries from .olean import (without calling materialize)
    let entry = SimpExtEntry {
        name: Name::from_string("imported_lemma"),
        priority: SimpPriority::Default,
    };
    let raw_entry = entry.to_env_entry();
    env.register_persistent_extension(ext_name.clone());
    env.add_persistent_extension_entries(&ext_name, 0, vec![raw_entry]);

    // State should not be materialized yet
    assert!(
        env.get_ext_state::<SimpExtState>(idx).is_none(),
        "state not materialized without explicit init"
    );

    // Lazy init via get_ext_state_or_init
    let state = env.get_ext_state_or_init::<SimpExtState>(idx).unwrap();
    assert_eq!(state.len(), 1);
    assert!(state.contains(&Name::from_string("imported_lemma")));
}

#[test]
fn test_env_clone_preserves_extension_state() {
    let mut env = Environment::default();
    let idx = simp_ext_idx();

    env.add_ext_entry::<SimpExtState>(
        idx,
        &SimpExtEntry {
            name: Name::from_string("cloned_lemma"),
            priority: SimpPriority::Default,
        },
    );

    // Clone the environment
    let env2 = env.clone();

    // Verify the cloned env has the same extension state
    let state = env2.get_ext_state::<SimpExtState>(idx).unwrap();
    assert_eq!(state.len(), 1);
    assert!(state.contains(&Name::from_string("cloned_lemma")));
}

#[test]
fn test_env_multiple_modules_fold_correctly() {
    let mut env = Environment::default();
    let idx = simp_ext_idx();
    let ext_name = Name::from_string("simpExtension");

    // Simulate entries from two different imported modules
    let entry_mod0 = SimpExtEntry {
        name: Name::from_string("mod0.lemma"),
        priority: SimpPriority::Default,
    };
    let entry_mod1 = SimpExtEntry {
        name: Name::from_string("mod1.lemma"),
        priority: SimpPriority::Custom(300),
    };

    env.register_persistent_extension(ext_name.clone());
    env.add_persistent_extension_entries(&ext_name, 0, vec![entry_mod0.to_env_entry()]);
    env.add_persistent_extension_entries(&ext_name, 1, vec![entry_mod1.to_env_entry()]);

    // Materialize
    env.materialize_extension_states();

    let state = env.get_ext_state::<SimpExtState>(idx).unwrap();
    assert_eq!(state.len(), 2);
    assert!(state.contains(&Name::from_string("mod0.lemma")));
    assert!(state.contains(&Name::from_string("mod1.lemma")));
}

// ============================================================================
// Custom extension test: attribute registry
// ============================================================================

/// Entry for a simple attribute extension (demonstrates framework generality).
#[derive(Clone, Debug)]
struct AttrEntry {
    decl_name: Name,
    attr_name: Name,
}

impl PersistentExtEntry for AttrEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        // Encode attr_name as object bytes (demonstrates Object variant)
        let attr_bytes = self.attr_name.to_string().into_bytes();
        EnvExtensionEntry {
            name: self.decl_name.clone(),
            data: EnvExtensionEntryData::Object(attr_bytes),
        }
    }

    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {
        let attr_name = match &entry.data {
            EnvExtensionEntryData::Object(bytes) => {
                let s = std::str::from_utf8(bytes).ok()?;
                Name::from_string(s)
            }
            EnvExtensionEntryData::Scalar(_) => return None,
        };
        Some(AttrEntry {
            decl_name: entry.name.clone(),
            attr_name,
        })
    }
}

/// State: maps declaration name -> set of attribute names.
#[derive(Clone, Debug, Default)]
struct AttrState {
    attrs: HashMap<Name, Vec<Name>>,
}

impl PersistentExtState for AttrState {
    type Entry = AttrEntry;

    fn add_entry(&mut self, entry: &AttrEntry) {
        self.attrs
            .entry(entry.decl_name.clone())
            .or_default()
            .push(entry.attr_name.clone());
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        self.attrs
            .iter()
            .flat_map(|(decl, attrs)| {
                attrs.iter().map(move |attr| {
                    AttrEntry {
                        decl_name: decl.clone(),
                        attr_name: attr.clone(),
                    }
                    .to_env_entry()
                })
            })
            .collect()
    }
}

#[test]
fn test_custom_attr_extension_roundtrip() {
    let idx = register_persistent_ext::<AttrState>(Name::from_string("test.attrExtension"));

    let mut env = Environment::default();

    // Register attributes
    env.add_ext_entry::<AttrState>(
        idx,
        &AttrEntry {
            decl_name: Name::from_string("myFunc"),
            attr_name: Name::from_string("inline"),
        },
    );
    env.add_ext_entry::<AttrState>(
        idx,
        &AttrEntry {
            decl_name: Name::from_string("myFunc"),
            attr_name: Name::from_string("simp"),
        },
    );
    env.add_ext_entry::<AttrState>(
        idx,
        &AttrEntry {
            decl_name: Name::from_string("otherFunc"),
            attr_name: Name::from_string("reducible"),
        },
    );

    // Query
    let state = env.get_ext_state::<AttrState>(idx).unwrap();
    assert_eq!(state.attrs.len(), 2);
    assert_eq!(
        state.attrs.get(&Name::from_string("myFunc")).unwrap().len(),
        2
    );
    assert_eq!(
        state
            .attrs
            .get(&Name::from_string("otherFunc"))
            .unwrap()
            .len(),
        1
    );

    // Export and re-import
    let exported = env.export_extension_states();
    let (_, entries) = exported
        .iter()
        .find(|(name, _)| name.to_string() == "test.attrExtension")
        .unwrap();

    let mut states2 = EnvExtensionStates::new();
    states2.fold_imported_entries(idx, entries);

    let state2 = states2.get_state::<AttrState>(idx).unwrap();
    assert_eq!(state2.attrs.len(), 2);
}

#[test]
fn test_env_generation_bumps_on_ext_entry() {
    let mut env = Environment::default();
    let idx = simp_ext_idx();
    let gen_before = env.generation();

    env.add_ext_entry::<SimpExtState>(
        idx,
        &SimpExtEntry {
            name: Name::from_string("gen_test"),
            priority: SimpPriority::Default,
        },
    );

    assert!(
        env.generation() > gen_before,
        "generation should increment on extension entry add"
    );
}

// ============================================================================
// Unit tests for persistent_ext core (moved from persistent_ext.rs inline)
// ============================================================================

// ---- Test extension: simple Name set ----

#[derive(Clone, Debug)]
struct TestEntry {
    name: Name,
}

impl PersistentExtEntry for TestEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: self.name.clone(),
            data: EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {
        Some(TestEntry {
            name: entry.name.clone(),
        })
    }
}

#[derive(Clone, Debug, Default)]
struct TestState {
    names: Vec<Name>,
}

impl PersistentExtState for TestState {
    type Entry = TestEntry;

    fn add_entry(&mut self, entry: &TestEntry) {
        self.names.push(entry.name.clone());
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        self.names
            .iter()
            .map(|n| EnvExtensionEntry {
                name: n.clone(),
                data: EnvExtensionEntryData::Scalar(0),
            })
            .collect()
    }
}

#[test]
fn test_register_extension_returns_stable_idx() {
    let name = Name::from_string("test.register_stable");
    let idx1 = register_persistent_ext::<TestState>(name.clone());
    let idx2 = register_persistent_ext::<TestState>(name);
    assert_eq!(idx1, idx2, "re-registering same name returns same index");
}

#[test]
fn test_extension_state_add_and_query() {
    let name = Name::from_string("test.add_query");
    let idx = register_persistent_ext::<TestState>(name);

    let mut states = EnvExtensionStates::new();
    let entry = TestEntry {
        name: Name::from_string("lemma1"),
    };
    states.add_entry::<TestState>(idx, &entry);

    let state = states.get_state::<TestState>(idx).unwrap();
    assert_eq!(state.names.len(), 1);
    assert_eq!(state.names[0].to_string(), "lemma1");
}

#[test]
fn test_extension_state_fold_imported() {
    let name = Name::from_string("test.fold_imported");
    let idx = register_persistent_ext::<TestState>(name);

    let raw_entries = vec![
        EnvExtensionEntry {
            name: Name::from_string("imported1"),
            data: EnvExtensionEntryData::Scalar(0),
        },
        EnvExtensionEntry {
            name: Name::from_string("imported2"),
            data: EnvExtensionEntryData::Scalar(0),
        },
    ];

    let mut states = EnvExtensionStates::new();
    states.fold_imported_entries(idx, &raw_entries);

    let state = states.get_state::<TestState>(idx).unwrap();
    assert_eq!(state.names.len(), 2);
    assert!(states.is_initialized(idx));
}

#[test]
fn test_extension_state_export_roundtrip() {
    let name = Name::from_string("test.export_roundtrip");
    let idx = register_persistent_ext::<TestState>(name);

    let mut states = EnvExtensionStates::new();
    states.add_entry::<TestState>(
        idx,
        &TestEntry {
            name: Name::from_string("a"),
        },
    );
    states.add_entry::<TestState>(
        idx,
        &TestEntry {
            name: Name::from_string("b"),
        },
    );

    let exported = states.export_all();
    assert_eq!(exported.len(), 1);
    assert_eq!(exported[0].1.len(), 2);

    // Re-import
    let mut states2 = EnvExtensionStates::new();
    states2.fold_imported_entries(idx, &exported[0].1);
    let state2 = states2.get_state::<TestState>(idx).unwrap();
    assert_eq!(state2.names.len(), 2);
}

#[test]
fn test_extension_state_clone() {
    let name = Name::from_string("test.clone");
    let idx = register_persistent_ext::<TestState>(name);

    let mut states = EnvExtensionStates::new();
    states.add_entry::<TestState>(
        idx,
        &TestEntry {
            name: Name::from_string("x"),
        },
    );

    let cloned = states.clone();
    let state = cloned.get_state::<TestState>(idx).unwrap();
    assert_eq!(state.names.len(), 1);
}

#[test]
fn test_extension_get_ext_idx() {
    let name = Name::from_string("test.get_idx");
    let idx = register_persistent_ext::<TestState>(name.clone());

    let found = get_ext_idx(&name);
    assert_eq!(found, Some(idx));

    let not_found = get_ext_idx(&Name::from_string("nonexistent.ext"));
    assert!(not_found.is_none());
}

#[test]
fn test_extension_uninitialized_state_returns_none() {
    let name = Name::from_string("test.uninit");
    let idx = register_persistent_ext::<TestState>(name);

    let states = EnvExtensionStates::new();
    // State not yet created
    assert!(states.get_state::<TestState>(idx).is_none());
    assert!(!states.is_initialized(idx));
}

#[test]
fn test_extension_fold_all_imported() {
    let name = Name::from_string("test.fold_all");
    let idx = register_persistent_ext::<TestState>(name.clone());

    let mut raw_extensions = HashMap::new();
    let mut raw_state = PersistentEnvExtensionState::default();
    raw_state.imported_entries.push(vec![
        EnvExtensionEntry {
            name: Name::from_string("mod0_entry1"),
            data: EnvExtensionEntryData::Scalar(0),
        },
        EnvExtensionEntry {
            name: Name::from_string("mod0_entry2"),
            data: EnvExtensionEntryData::Scalar(0),
        },
    ]);
    raw_state.imported_entries.push(vec![EnvExtensionEntry {
        name: Name::from_string("mod1_entry1"),
        data: EnvExtensionEntryData::Scalar(0),
    }]);
    raw_extensions.insert(name, raw_state);

    let mut states = EnvExtensionStates::new();
    states.fold_all_imported(&raw_extensions);

    let state = states.get_state::<TestState>(idx).unwrap();
    assert_eq!(state.names.len(), 3);
    assert!(states.is_initialized(idx));
}
