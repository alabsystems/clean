// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The storage keeps the matcher index it holds equal to a decode of its
//! entries through every constructor and mutator. Each test also reads every
//! entry's metadata against what the test stored, an oracle independent of
//! [`MatcherIndex::decode`], so a decode that skipped entries could not hide
//! behind the comparison.

use super::*;
use crate::env::EnvExtensionEntryData;

/// The payload prefix `register_matcher_info` writes.
const PREFIX: &[u8] = b"Clean.matcherInfo.v1\0";

fn info(alternatives: u32) -> MatcherInfo {
    MatcherInfo {
        num_params: 0,
        num_discrs: 0,
        alt_num_params: vec![0; alternatives as usize],
        u_elim_pos: None,
        discr_names: vec![],
        details: None,
    }
}

fn name(text: &str) -> Name {
    Name::from_string(text)
}

fn encoded(entry_name: &Name, info: &MatcherInfo) -> EnvExtensionEntry {
    let mut bytes = PREFIX.to_vec();
    bytes.extend(serde_json::to_vec(info).expect("matcher metadata encodes"));
    EnvExtensionEntry {
        name: entry_name.clone(),
        data: EnvExtensionEntryData::Object(bytes),
    }
}

fn malformed(entry_name: &Name) -> EnvExtensionEntry {
    EnvExtensionEntry {
        name: entry_name.clone(),
        data: EnvExtensionEntryData::Object(b"malformed".to_vec()),
    }
}

#[track_caller]
fn assert_index_is_storage(storage: &PersistentExtensions, after: &str) {
    assert_eq!(
        storage.matcher,
        MatcherIndex::decode(storage.states.get(&matcher_storage_key())),
        "after {after}, the matcher index disagrees with a decode of its storage"
    );
}

/// Every name's lookup is exactly what the test stored for it.
#[track_caller]
fn assert_lookups(storage: &PersistentExtensions, expected: &[(&Name, Option<&MatcherInfo>)]) {
    for (entry_name, want) in expected {
        assert_eq!(
            storage.matcher_info(entry_name),
            *want,
            "lookup of `{entry_name}`"
        );
    }
}

/// Five names in one seven-entry append call (two valid names, an identical
/// duplicate pair, a conflicting pair and a malformed entry), then a second
/// multi-entry call at an EARLIER module. The production import appends each module's rows in
/// one call, so an index that folded only part of a call is the failure
/// this test exists for.
fn multi_entry_storage() -> (PersistentExtensions, Vec<(Name, Option<MatcherInfo>)>) {
    let key = matcher_storage_key();
    let [a, b, same, split, broken, late] =
        ["m.a", "m.b", "m.same", "m.split", "m.broken", "m.late"].map(name);
    let mut storage = PersistentExtensions::default();
    assert!(storage.register(key.clone()));
    storage.append(
        &key,
        3,
        vec![
            encoded(&a, &info(1)),
            encoded(&b, &info(2)),
            encoded(&same, &info(3)),
            encoded(&same, &info(3)),
            encoded(&split, &info(1)),
            encoded(&split, &info(2)),
            malformed(&broken),
        ],
    );
    assert_index_is_storage(&storage, "a seven-entry append at module 3");
    storage.append(
        &key,
        0,
        vec![
            encoded(&late, &info(4)),
            encoded(&a, &info(1)),
            malformed(&b),
        ],
    );
    assert_index_is_storage(&storage, "a three-entry append at module 0");
    let expected = vec![
        (a, Some(info(1))),
        (b, None),
        (same, Some(info(3))),
        (split, None),
        (broken, None),
        (late, Some(info(4))),
    ];
    (storage, expected)
}

fn as_refs(expected: &[(Name, Option<MatcherInfo>)]) -> Vec<(&Name, Option<&MatcherInfo>)> {
    expected
        .iter()
        .map(|(entry_name, want)| (entry_name, want.as_ref()))
        .collect()
}

#[test]
fn test_extension_storage_multi_entry_append_indexes_every_entry() {
    let (storage, expected) = multi_entry_storage();
    assert_lookups(&storage, &as_refs(&expected));
    // Every stored name has a row, including the malformed and the split ones.
    for (entry_name, _) in &expected {
        assert!(
            storage.matcher_index().row(entry_name).is_some(),
            "`{entry_name}` has no index row"
        );
    }
}

#[test]
fn test_extension_storage_append_to_another_extension_leaves_the_index() {
    let (mut storage, expected) = multi_entry_storage();
    let before = storage.matcher.clone();
    let other = name("Other.extension");
    storage.append(
        &other,
        0,
        vec![
            malformed(&expected[0].0),
            encoded(&name("m.other"), &info(1)),
        ],
    );
    assert_eq!(storage.matcher, before);
    assert_index_is_storage(&storage, "an append to another extension");
    assert_lookups(&storage, &as_refs(&expected));
}

#[test]
fn test_extension_storage_register_keeps_present_entries() {
    let (mut storage, expected) = multi_entry_storage();
    assert!(!storage.register(matcher_storage_key()));
    assert_index_is_storage(&storage, "registering a present extension");
    assert_lookups(&storage, &as_refs(&expected));
}

#[test]
fn test_extension_storage_forget_drops_the_name_from_every_module() {
    let (mut storage, expected) = multi_entry_storage();
    // `m.a` is stored at module 3 and at module 0, among other rows.
    let forgotten = &expected[0].0;
    storage.forget_matcher_rows(forgotten);
    let state = storage.get(&matcher_storage_key()).expect("storage exists");
    for (module, rows) in state.imported_entries.iter().enumerate() {
        assert!(
            rows.iter().all(|entry| &entry.name != forgotten),
            "module {module} still stores `{forgotten}`"
        );
    }
    assert_index_is_storage(&storage, "forgetting a name stored in two modules");
    assert!(storage.matcher_index().row(forgotten).is_none());
    let mut rest = as_refs(&expected);
    rest[0].1 = None;
    assert_lookups(&storage, &rest);
}

#[test]
fn test_extension_storage_set_state_rederives_on_replace_and_remove() {
    let (source, expected) = multi_entry_storage();
    let key = matcher_storage_key();
    let state = source.get(&key).expect("storage exists").clone();

    let mut storage = PersistentExtensions::default();
    storage.set_state(&name("A.sorts.before.the.matcher.key"), Some(state.clone()));
    assert!(storage.matcher_info(&expected[0].0).is_none());
    storage.set_state(&key, Some(state));
    assert_index_is_storage(&storage, "replacing the matcher storage");
    assert_lookups(&storage, &as_refs(&expected));

    storage.set_state(&key, None);
    assert_index_is_storage(&storage, "removing the matcher storage");
    for (entry_name, _) in &expected {
        assert!(storage.matcher_index().row(entry_name).is_none());
    }
}

#[test]
fn test_extension_storage_restores_derive_the_index_from_the_same_bytes() {
    let (storage, expected) = multi_entry_storage();
    // The persisted form is the map of states alone, byte for byte.
    let bytes = bincode::serde::encode_to_vec(&storage, bincode::config::standard())
        .expect("storage encodes");
    let map_bytes = bincode::serde::encode_to_vec(storage.states(), bincode::config::standard())
        .expect("states encode");
    assert_eq!(
        bytes, map_bytes,
        "the storage must persist as its map alone"
    );

    let (restored, used): (PersistentExtensions, usize) =
        bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
            .expect("storage decodes");
    assert_eq!(used, bytes.len());
    assert_index_is_storage(&restored, "a bincode restore");
    assert_eq!(restored.matcher, storage.matcher);
    assert_lookups(&restored, &as_refs(&expected));

    let adopted = PersistentExtensions::from_states(storage.states().clone());
    assert_index_is_storage(&adopted, "adopting restored states");
    assert_lookups(&adopted, &as_refs(&expected));

    let cloned = storage.clone();
    assert_index_is_storage(&cloned, "a clone");
    assert_lookups(&cloned, &as_refs(&expected));
}

/// Negative control for every comparison above: a storage whose index was
/// left behind is caught, and it answers lookups differently.
#[test]
fn test_extension_storage_stale_index_is_caught() {
    let (storage, expected) = multi_entry_storage();
    let stale = PersistentExtensions {
        states: storage.states.clone(),
        matcher: MatcherIndex::default(),
    };
    assert_ne!(
        stale.matcher,
        MatcherIndex::decode(stale.states.get(&matcher_storage_key()))
    );
    assert!(stale.matcher_info(&expected[0].0).is_none());
    assert_eq!(storage.matcher_info(&expected[0].0), Some(&info(1)));

    let mut partial = MatcherIndex::default();
    let state = storage.get(&matcher_storage_key()).expect("storage exists");
    // A fold of the first entry of each module only.
    for rows in &state.imported_entries {
        if let Some(first) = rows.first() {
            partial.absorb(first);
        }
    }
    assert_ne!(partial, storage.matcher);
}
