// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The matcher index is plain data kept equal to its storage. Every test here
//! drives one write or restore path and then checks the index against a fresh
//! decode of the persistent-extension entries it is derived from.

use super::*;
use crate::env::Declaration;
use crate::expr::Expr;
use crate::BinderInfo;

fn matcher_definition(env: &mut Environment, name: &str, alternatives: u32) -> Name {
    let name = Name::from_string(name);
    let prop = Expr::prop();
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: (0..=alternatives).fold(prop.clone(), |body, _| {
            Expr::pi(BinderInfo::Default, prop.clone(), body)
        }),
        value: (0..=alternatives).fold(Expr::bvar(alternatives), |body, _| {
            Expr::lam(BinderInfo::Default, prop.clone(), body)
        }),
        is_reducible: false,
    })
    .unwrap_or_else(|e| panic!("`{name}` is well-typed: {e:?}"));
    name
}

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

/// A stored entry spelled exactly as `register_matcher_info` spells one.
fn encoded(name: &Name, info: &MatcherInfo) -> EnvExtensionEntry {
    let mut bytes = PAYLOAD_PREFIX.to_vec();
    bytes.extend(serde_json::to_vec(info).expect("matcher metadata encodes"));
    EnvExtensionEntry {
        name: name.clone(),
        data: EnvExtensionEntryData::Object(bytes),
    }
}

fn malformed(name: &Name) -> EnvExtensionEntry {
    EnvExtensionEntry {
        name: name.clone(),
        data: EnvExtensionEntryData::Object(b"malformed".to_vec()),
    }
}

fn decoded_storage(env: &Environment) -> MatcherIndex {
    MatcherIndex::decode(env.persistent_extensions.get(&storage_key()))
}

#[track_caller]
fn assert_index_is_storage(env: &Environment, after: &str) {
    assert_eq!(
        env.matcher_info,
        decoded_storage(env),
        "after {after}, the matcher index disagrees with a decode of its storage"
    );
}

fn append(env: &mut Environment, module: usize, entries: Vec<EnvExtensionEntry>) {
    let key = storage_key();
    env.register_persistent_extension(key.clone());
    env.add_persistent_extension_entries(&key, module, entries);
}

/// An environment whose storage holds a valid row, a malformed row and a
/// conflicting pair, so every restore below has all three verdicts to carry.
fn populated() -> (Environment, Name, MatcherInfo) {
    let mut env = Environment::default();
    let good = matcher_definition(&mut env, "matcher_index.good", 1);
    let broken = matcher_definition(&mut env, "matcher_index.broken", 1);
    let split = matcher_definition(&mut env, "matcher_index.split", 2);
    let good_info = info(1);
    env.register_matcher_info(good.clone(), good_info.clone())
        .expect("a well-formed matcher registers");
    append(&mut env, 1, vec![malformed(&broken)]);
    append(&mut env, 2, vec![encoded(&split, &info(2))]);
    append(&mut env, 3, vec![encoded(&split, &info(1))]);
    assert_index_is_storage(&env, "populating");
    (env, good, good_info)
}

#[test]
fn test_matcher_index_register_and_raw_appends_track_storage() {
    let mut env = Environment::default();
    let name = matcher_definition(&mut env, "matcher_index.register", 1);
    let other = matcher_definition(&mut env, "matcher_index.other", 2);
    assert_index_is_storage(&env, "no registration");

    env.register_matcher_info(name.clone(), info(1))
        .expect("a well-formed matcher registers");
    assert_index_is_storage(&env, "a registration");
    assert_eq!(env.get_matcher_info(&name), Some(&info(1)));

    env.register_matcher_info(name.clone(), info(1))
        .expect("an identical duplicate is accepted");
    assert_index_is_storage(&env, "an identical duplicate");
    assert!(env.register_matcher_info(name.clone(), info(2)).is_err());
    assert_index_is_storage(&env, "a refused conflicting registration");
    assert_eq!(env.get_matcher_info(&name), Some(&info(1)));

    // A raw append at a LATER module, then one at an EARLIER module.
    append(&mut env, 4, vec![encoded(&other, &info(2))]);
    assert_index_is_storage(&env, "a raw append at module 4");
    assert_eq!(env.get_matcher_info(&other), Some(&info(2)));
    append(&mut env, 2, vec![malformed(&other)]);
    assert_index_is_storage(&env, "a malformed raw append at module 2");
    assert!(env.get_matcher_info(&other).is_none());
    assert!(env.register_matcher_info(other.clone(), info(2)).is_err());

    // Another extension's entries leave the index alone.
    let unrelated = Name::from_string("matcher_index.unrelated_extension");
    let before = env.matcher_info.clone();
    env.register_persistent_extension(unrelated.clone());
    env.add_persistent_extension_entries(&unrelated, 0, vec![encoded(&name, &info(2))]);
    assert_eq!(env.matcher_info, before);
    assert_index_is_storage(&env, "an append to another extension");
}

#[test]
fn test_matcher_index_append_order_does_not_change_the_index() {
    let mut forward = Environment::default();
    let name = matcher_definition(&mut forward, "matcher_index.ordered", 1);
    let mut backward = forward.clone();
    let rows = [
        (0, encoded(&name, &info(1))),
        (1, encoded(&name, &info(1))),
        (2, malformed(&name)),
    ];
    for (module, entry) in rows.iter().cloned() {
        append(&mut forward, module, vec![entry]);
    }
    for (module, entry) in rows.iter().rev().cloned() {
        append(&mut backward, module, vec![entry]);
    }
    assert_index_is_storage(&forward, "appends in module order");
    assert_index_is_storage(&backward, "appends in reverse module order");
    assert_eq!(forward.matcher_info, backward.matcher_info);
    assert!(forward.get_matcher_info(&name).is_none());
}

#[test]
fn test_matcher_index_constant_removal_drops_the_row() {
    let (mut env, name, _) = populated();
    assert!(env.forget_decl(&name));
    assert_index_is_storage(&env, "removing the matcher's constant");
    assert!(!env.matcher_info.0.contains_key(&name));
    assert!(env.get_matcher_info(&name).is_none());
}

#[test]
fn test_matcher_index_fact_delta_application_rederives_it() {
    let (mut before, name, info) = populated();
    let other = matcher_definition(&mut before, "matcher_index.delta", 1);
    let mut after = before.clone();
    // `init_nat` moves generically captured scalars too, so the delta is
    // applied through scalar reassembly and its heavy-field transplant.
    after.init_nat().expect("Nat initializes");
    after
        .register_matcher_info(other.clone(), info.clone())
        .expect("a well-formed matcher registers");
    append(&mut after, 5, vec![malformed(&name)]);
    let delta = after
        .local_fact_delta_since(&before)
        .expect("the delta replays");
    before
        .apply_local_fact_delta(&delta)
        .expect("the delta applies to its base");
    assert_index_is_storage(&before, "applying a fact delta");
    assert_eq!(before.matcher_info, after.matcher_info);
    assert_eq!(before.get_matcher_info(&other), Some(&info));
    assert!(before.get_matcher_info(&name).is_none());
}

#[test]
fn test_matcher_index_fact_delta_without_matcher_rows_keeps_it() {
    let (mut before, name, info) = populated();
    let mut after = before.clone();
    // `init_nat` moves generically captured scalars and no matcher row, so
    // the index reaches the result only through scalar reassembly's
    // heavy-field transplant: `apply_typed` re-derives it only when matcher
    // storage changed.
    after.init_nat().expect("Nat initializes");
    assert_eq!(
        after.persistent_extensions.get(&storage_key()),
        before.persistent_extensions.get(&storage_key()),
        "this delta must leave matcher storage alone"
    );
    let delta = after
        .local_fact_delta_since(&before)
        .expect("the delta replays");
    before
        .apply_local_fact_delta(&delta)
        .expect("the delta applies to its base");
    assert_index_is_storage(&before, "a fact delta that moved no matcher row");
    assert_eq!(before.matcher_info, after.matcher_info);
    assert_eq!(before.get_matcher_info(&name), Some(&info));
}

#[test]
fn test_matcher_index_every_restore_rederives_it() {
    let (env, name, info) = populated();
    let restored = [
        ("a clone", env.clone()),
        (
            "a serde bincode restore",
            Environment::from_bincode(&env.to_bincode().expect("bincode encodes"))
                .expect("bincode decodes"),
        ),
        (
            "a DAG restore",
            Environment::from_dag_bincode(&env.to_dag_bincode().expect("DAG encodes"))
                .expect("DAG decodes"),
        ),
    ];
    for (path, restored) in &restored {
        assert_index_is_storage(restored, path);
        assert_eq!(restored.matcher_info, env.matcher_info, "{path}");
        assert_eq!(restored.get_matcher_info(&name), Some(&info), "{path}");
    }
}

#[test]
fn test_matcher_index_restore_inside_an_outer_decode_budget() {
    let (mut env, name, good_info) = populated();
    // A named discriminant equation is a recursive kernel node, so this
    // payload's decode counts against whatever budget scope it runs in.
    let named = matcher_definition(&mut env, "matcher_index.named", 2);
    let named_info = MatcherInfo {
        num_discrs: 1,
        discr_names: vec![Some(Name::from_string("matcher_index.named.h"))],
        ..info(1)
    };
    env.register_matcher_info(named.clone(), named_info.clone())
        .expect("a matcher with a named discriminant equation registers");
    let bytes = env.to_dag_bincode().expect("DAG encodes");
    let restored = with_decode_resource_limits(
        DecodeResourceLimits {
            max_nodes: 1,
            max_depth: 1,
        },
        || Environment::from_dag_bincode(&bytes).expect("DAG decodes"),
    );
    assert_index_is_storage(&restored, "a DAG restore inside an outer decode budget");
    assert_eq!(restored.get_matcher_info(&name), Some(&good_info));
    assert_eq!(restored.get_matcher_info(&named), Some(&named_info));
}

/// Negative control for every check above: an index left behind by its
/// storage is caught, and it changes what a lookup answers.
#[test]
fn test_matcher_index_stale_index_is_caught() {
    let (env, name, info) = populated();
    let mut stale = env.clone();
    stale.matcher_info = MatcherIndex::default();
    assert_ne!(stale.matcher_info, decoded_storage(&stale));
    assert!(stale.get_matcher_info(&name).is_none());
    assert_eq!(env.get_matcher_info(&name), Some(&info));

    let mut lagging = env.clone();
    lagging
        .persistent_extensions
        .get_mut(&storage_key())
        .expect("the storage exists")
        .imported_entries[0]
        .push(malformed(&name));
    assert_ne!(lagging.matcher_info, decoded_storage(&lagging));
}

/// Conventional associated-call syntax must not bypass matcher rebuilding.
#[test]
fn test_matcher_index_direct_deserialize_rederives_without_verification_stamps() {
    struct DirectRestore(Environment);
    impl<'de> Deserialize<'de> for DirectRestore {
        fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            Environment::deserialize(deserializer).map(Self)
        }
    }

    let (env, good, good_info) = populated();
    assert_eq!(
        env.declaration_verification(&good),
        Some(crate::env::DeclarationVerification::FullKernelCheck)
    );
    assert_eq!(
        env.clone().declaration_verification(&good),
        env.declaration_verification(&good),
        "cloning retains existing in-memory verification"
    );
    let bytes = env.to_bincode().expect("the populated environment encodes");
    let (DirectRestore(restored), consumed) =
        bincode::serde::decode_from_slice::<DirectRestore, _>(&bytes, bincode::config::standard())
            .expect("the direct Deserialize call restores the environment");
    assert_eq!(consumed, bytes.len());
    assert_index_is_storage(&restored, "the direct Deserialize call");
    assert_eq!(restored.matcher_info, env.matcher_info);
    assert_eq!(restored.get_matcher_info(&good), Some(&good_info));
    assert!(restored
        .get_matcher_info(&Name::from_string("matcher_index.broken"))
        .is_none());
    assert!(restored
        .get_matcher_info(&Name::from_string("matcher_index.split"))
        .is_none());
    assert!(restored.declaration_verification(&good).is_none());
    assert!(restored.declaration_verification.is_empty());
}

#[test]
fn test_matcher_index_generic_nested_deserialize_rederives_without_verification_stamps() {
    #[derive(serde::Serialize, serde::Deserialize)]
    struct Nested {
        before: u8,
        environments: Vec<Environment>,
        after: String,
    }

    fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> T {
        let (value, consumed) =
            bincode::serde::decode_from_slice(bytes, bincode::config::standard())
                .expect("generic serde decoding succeeds");
        assert_eq!(consumed, bytes.len());
        value
    }

    let (env, good, good_info) = populated();
    assert_eq!(
        env.declaration_verification(&good),
        Some(crate::env::DeclarationVerification::FullKernelCheck)
    );
    let nested = Nested {
        before: 37,
        environments: vec![env.clone(), env.clone()],
        after: "after the environments".to_string(),
    };
    let bytes = bincode::serde::encode_to_vec(&nested, bincode::config::standard())
        .expect("the nested populated environments encode");
    let restored: Nested = decode(&bytes);
    assert_eq!(restored.before, 37);
    assert_eq!(restored.after, "after the environments");
    assert_eq!(restored.environments.len(), 2);
    for restored in &restored.environments {
        assert_index_is_storage(restored, "generic nested serde decoding");
        assert_eq!(restored.matcher_info, env.matcher_info);
        assert_eq!(restored.get_matcher_info(&good), Some(&good_info));
        assert!(restored
            .get_matcher_info(&Name::from_string("matcher_index.broken"))
            .is_none());
        assert!(restored
            .get_matcher_info(&Name::from_string("matcher_index.split"))
            .is_none());
        assert!(restored.declaration_verification(&good).is_none());
        assert!(restored.declaration_verification.is_empty());
    }
}
