// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The matcher index is plain data kept equal to its storage. Every test here
//! drives one write or restore path of an `Environment` and then checks the
//! index against a fresh decode of the persistent-extension entries it is
//! derived from, and each lookup against what the test stored. The storage
//! type's own constructors and mutators are tested in
//! `extension_storage_tests.rs`.

use super::*;
use crate::env::{Declaration, TrustedEnvExt};
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

#[test]
fn source_matcher_effects_agree_across_independent_siblings() {
    let mut base = Environment::new();
    let left = matcher_definition(&mut base, "Left.f.match_1", 3);
    let right = matcher_definition(&mut base, "Right.g.match_1", 3);
    let branches = MatcherInfo {
        num_params: 0,
        num_discrs: 1,
        alt_num_params: vec![1, 1],
        u_elim_pos: None,
        discr_names: vec![None],
        details: Some(MatcherDetails {
            alt_infos: vec![
                MatcherAltInfo {
                    num_fields: 0,
                    num_overlaps: 0,
                    has_unit_thunk: true,
                },
                MatcherAltInfo {
                    num_fields: 1,
                    num_overlaps: 0,
                    has_unit_thunk: false,
                },
            ],
            overlaps: Vec::new(),
        }),
    };
    let mut alone = base.clone();
    alone
        .register_matcher_info(right.clone(), branches.clone())
        .unwrap();
    let own = alone.effect_since(&base);
    let mut sibling = base.clone();
    sibling
        .register_matcher_info(left.clone(), branches.clone())
        .unwrap();
    let difference = |after: &Environment| own.disagreement(&after.effect_since(&sibling), after);
    let key = matcher_storage_key();
    let mut together = sibling.clone();
    together
        .register_matcher_info(right.clone(), branches.clone())
        .unwrap();
    assert_eq!(together.get_matcher_info(&right), Some(&branches));
    assert_eq!(difference(&together), None);
    assert_eq!(
        own.disagreement(&together.effect_since(&together), &together),
        None
    );
    assert!(difference(&sibling).is_some());

    // A row for another name is independent only when the sibling already
    // contributed it. Adding it as part of this replay is a divergence.
    let mut extra = together.clone();
    extra.add_persistent_extension_entries(&key, 0, vec![malformed(&left)]);
    assert!(difference(&extra).is_some());

    // Identical duplicates still differ in raw multiplicity, even when lookup
    // agrees. The extension's opaque state and module buckets are observed too.
    let mut duplicate = together.clone();
    duplicate.add_persistent_extension_entries(&key, 0, vec![encoded(&right, &branches)]);
    assert_eq!(duplicate.get_matcher_info(&right), Some(&branches));
    assert!(difference(&duplicate).is_some());
    let mut storage = together.persistent_extensions.get(&key).unwrap().clone();
    storage.state.push(1);
    let mut changed_header = together.clone();
    changed_header
        .persistent_extensions
        .set_state(&key, Some(storage));
    assert!(difference(&changed_header).is_some());
    let mut moved = sibling.clone();
    moved.add_persistent_extension_entries(&key, 1, vec![encoded(&right, &branches)]);
    assert!(difference(&moved).is_some());

    let mut changed = sibling.clone();
    let mut other = branches.clone();
    other.details = None;
    changed
        .register_matcher_info(right.clone(), other.clone())
        .unwrap();
    assert!(difference(&changed).is_some());
    assert!(together
        .register_matcher_info(right.clone(), other.clone())
        .is_err());
    together.add_persistent_extension_entries(&key, 0, vec![encoded(&right, &other)]);
    assert!(together.get_matcher_info(&right).is_none());
    assert!(difference(&together).is_some());
}

#[test]
fn removing_the_last_matcher_row_requires_its_final_table() {
    let mut base = Environment::new();
    let name = matcher_definition(&mut base, "M.f.match_1", 2);
    let mut registered = base.clone();
    registered
        .register_matcher_info(name.clone(), info(2))
        .unwrap();
    let mut removed = registered.clone();
    assert!(removed.forget_decl(&name));
    let own = removed.effect_since(&registered);
    let mut absent = base.clone();
    assert!(absent.forget_decl(&name));
    assert!(removed
        .persistent_extensions
        .get(&matcher_storage_key())
        .is_some());
    assert!(absent
        .persistent_extensions
        .get(&matcher_storage_key())
        .is_none());
    assert!(own
        .disagreement(&absent.effect_since(&base), &absent)
        .is_some());
    assert_eq!(
        own.disagreement(&removed.effect_since(&removed), &removed),
        None
    );

    // An opaque header change made only beside a stranger still diverges
    // even when that change restores the expected final header.
    let key = matcher_storage_key();
    let mut different = registered.clone();
    let mut storage = registered.persistent_extensions.get(&key).unwrap().clone();
    storage.state.push(7);
    different
        .persistent_extensions
        .set_state(&key, Some(storage));
    assert!(own
        .disagreement(&removed.effect_since(&different), &removed)
        .is_some());
}

#[test]
fn other_persistent_extensions_still_compare_the_whole_state() {
    let base = Environment::new();
    let key = Name::from_string("unrelated.extension");
    let left = malformed(&Name::from_string("L"));
    let right = malformed(&Name::from_string("R"));
    let mut alone = base.clone();
    alone.add_persistent_extension_entries(&key, 0, vec![right.clone()]);
    let mut sibling = base.clone();
    sibling.add_persistent_extension_entries(&key, 0, vec![left]);
    let mut together = sibling.clone();
    together.add_persistent_extension_entries(&key, 0, vec![right]);
    assert!(alone
        .effect_since(&base)
        .disagreement(&together.effect_since(&sibling), &together)
        .is_some());
}

fn decoded_storage(env: &Environment) -> MatcherIndex {
    MatcherIndex::decode(env.persistent_extensions.get(&matcher_storage_key()))
}

fn index(env: &Environment) -> &MatcherIndex {
    env.persistent_extensions.matcher_index()
}

#[track_caller]
fn assert_index_is_storage(env: &Environment, after: &str) {
    assert_eq!(
        index(env),
        &decoded_storage(env),
        "after {after}, the matcher index disagrees with a decode of its storage"
    );
}

/// Every name's lookup is exactly what the test stored for it.
#[track_caller]
fn assert_lookups(env: &Environment, expected: &[(Name, Option<MatcherInfo>)], after: &str) {
    for (name, want) in expected {
        assert_eq!(
            env.get_matcher_info(name),
            want.as_ref(),
            "after {after}, lookup of `{name}`"
        );
    }
}

fn append(env: &mut Environment, module: usize, entries: Vec<EnvExtensionEntry>) {
    let key = matcher_storage_key();
    env.register_persistent_extension(key.clone());
    env.add_persistent_extension_entries(&key, module, entries);
}

/// Six matcher definitions and two multi-entry appends, the first through the
/// inherent funnel and the second through [`TrustedEnvExt`], the path the
/// production `.olean` import takes, which appends a module's rows in one
/// call. Returns each name with the metadata its entries agree on.
fn multi_entry_environment() -> (Environment, Vec<(Name, Option<MatcherInfo>)>) {
    let mut env = Environment::default();
    let [a, b, same, split, broken, late] = [
        ("matcher_index.multi.a", 1),
        ("matcher_index.multi.b", 2),
        ("matcher_index.multi.same", 3),
        ("matcher_index.multi.split", 2),
        ("matcher_index.multi.broken", 1),
        ("matcher_index.multi.late", 4),
    ]
    .map(|(name, alternatives)| matcher_definition(&mut env, name, alternatives));
    let key = matcher_storage_key();
    env.register_persistent_extension(key.clone());
    env.add_persistent_extension_entries(
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
    assert_index_is_storage(&env, "a seven-entry append at module 3");
    TrustedEnvExt::add_persistent_extension_entries(
        &mut env,
        &key,
        0,
        vec![
            encoded(&late, &info(4)),
            encoded(&a, &info(1)),
            encoded(&b, &info(1)),
        ],
    );
    assert_index_is_storage(&env, "a three-entry trait append at module 0");
    let expected = vec![
        (a, Some(info(1))),
        (b, None),
        (same, Some(info(3))),
        (split, None),
        (broken, None),
        (late, Some(info(4))),
    ];
    assert_lookups(&env, &expected, "the multi-entry appends");
    (env, expected)
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
    // A module holding several rows: a restore that decoded only part of a
    // module would lose `good`'s second row agreeing and `tail`'s only row.
    let tail = matcher_definition(&mut env, "matcher_index.tail", 2);
    append(
        &mut env,
        4,
        vec![
            encoded(&broken, &info(1)),
            encoded(&good, &good_info),
            encoded(&tail, &info(2)),
        ],
    );
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
    let before = index(&env).clone();
    env.register_persistent_extension(unrelated.clone());
    env.add_persistent_extension_entries(&unrelated, 0, vec![encoded(&name, &info(2))]);
    assert_eq!(index(&env), &before);
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
    assert_eq!(index(&forward), index(&backward));
    assert!(forward.get_matcher_info(&name).is_none());
}

#[test]
fn test_matcher_index_constant_removal_drops_the_row() {
    let (mut env, name, _) = populated();
    assert!(env.forget_decl(&name));
    assert_index_is_storage(&env, "removing the matcher's constant");
    assert!(index(&env).row(&name).is_none());
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
    assert_eq!(index(&before), index(&after));
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
        after.persistent_extensions.get(&matcher_storage_key()),
        before.persistent_extensions.get(&matcher_storage_key()),
        "this delta must leave matcher storage alone"
    );
    let delta = after
        .local_fact_delta_since(&before)
        .expect("the delta replays");
    before
        .apply_local_fact_delta(&delta)
        .expect("the delta applies to its base");
    assert_index_is_storage(&before, "a fact delta that moved no matcher row");
    assert_eq!(index(&before), index(&after));
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
        assert_eq!(index(restored), index(&env), "{path}");
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

#[test]
fn test_matcher_index_multi_entry_appends_index_every_entry() {
    let (env, expected) = multi_entry_environment();
    for (name, _) in &expected {
        assert!(index(&env).row(name).is_some(), "`{name}` has no index row");
    }
    // `info(0)` is valid against every definition here (control), so a
    // refusal below comes from the row the appends left, not from validation:
    // the conflict check reads the same rows as the lookups.
    let mut control = Environment::default();
    let fresh = matcher_definition(&mut control, "matcher_index.multi.a", 1);
    control
        .register_matcher_info(fresh, info(0))
        .expect("info(0) is valid against these definitions");
    for (name, want) in &expected {
        let refused = env
            .clone()
            .register_matcher_info(name.clone(), info(0))
            .is_err();
        assert!(refused, "`{name}` accepted other metadata over {want:?}");
    }
}

#[test]
fn test_matcher_index_constant_removal_drops_rows_from_every_module() {
    let (mut env, expected) = multi_entry_environment();
    // `a` is stored at module 3 and at module 0, among other rows.
    let removed = expected[0].0.clone();
    assert!(env.forget_decl(&removed));
    let state = env
        .persistent_extensions
        .get(&matcher_storage_key())
        .expect("the storage exists");
    for (module, rows) in state.imported_entries.iter().enumerate() {
        assert!(
            rows.iter().all(|entry| entry.name != removed),
            "module {module} still stores `{removed}`"
        );
    }
    assert_index_is_storage(&env, "removing a constant stored in two modules");
    assert!(index(&env).row(&removed).is_none());
    let mut rest = expected.clone();
    rest[0].1 = None;
    assert_lookups(&env, &rest, "removing a constant");
}

#[test]
fn test_matcher_index_fact_delta_over_several_extensions_rederives_it() {
    let (mut before, _) = multi_entry_environment();
    let late = matcher_definition(&mut before, "matcher_index.delta.late", 1);
    let other = matcher_definition(&mut before, "matcher_index.delta.other", 2);
    let mut after = before.clone();
    // The delta changes an extension that sorts BEFORE the matcher key and
    // the matcher storage itself, both with multi-entry appends; it moves no
    // constant.
    let neighbour = Name::from_string("AMatcherIndexNeighbour.extension");
    after.register_persistent_extension(neighbour.clone());
    after.add_persistent_extension_entries(
        &neighbour,
        0,
        vec![malformed(&neighbour), malformed(&matcher_storage_key())],
    );
    append(
        &mut after,
        7,
        vec![
            encoded(&late, &info(1)),
            encoded(&other, &info(2)),
            malformed(&Name::from_string("matcher_index.multi.same")),
        ],
    );
    let delta = after
        .local_fact_delta_since(&before)
        .expect("the delta replays");
    before
        .apply_local_fact_delta(&delta)
        .expect("the delta applies to its base");
    assert_index_is_storage(&before, "a fact delta over two extensions");
    assert_eq!(index(&before), index(&after));
    let mut expected = vec![
        (late, Some(info(1))),
        (other, Some(info(2))),
        (Name::from_string("matcher_index.multi.same"), None),
    ];
    expected.push((Name::from_string("matcher_index.multi.late"), Some(info(4))));
    assert_lookups(&before, &expected, "a fact delta over two extensions");
}

#[test]
fn test_matcher_index_restores_of_multi_entry_storage_read_every_entry() {
    let (env, expected) = multi_entry_environment();
    let restored = [
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
        assert_eq!(index(restored), index(&env), "{path}");
        assert_lookups(restored, &expected, path);
    }
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
    assert_eq!(index(&restored), index(&env));
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
        assert_eq!(index(restored), index(&env));
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
