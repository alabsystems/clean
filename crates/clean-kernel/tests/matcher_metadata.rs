// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::env::{
    EnvExtensionEntry, EnvExtensionEntryData, MatcherAltInfo, MatcherDetails, MatcherInfo,
    MatcherOverlap, TrustedEnvExt,
};
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};
const STORAGE_KEY: &str = "Clean.matcherInfo.v1";

fn fixture() -> (Environment, Name, MatcherInfo) {
    fixture_with_alternatives(1)
}

fn fixture_with_alternatives(alternatives: u32) -> (Environment, Name, MatcherInfo) {
    let mut env = Environment::default();
    let name = Name::from_string("matcher_storage_fixture");
    let nat = Expr::prop();
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: (0..=alternatives).fold(nat.clone(), |body, _| {
            Expr::pi(BinderInfo::Default, nat.clone(), body)
        }),
        value: (0..=alternatives).fold(Expr::bvar(alternatives), |body, _| {
            Expr::lam(BinderInfo::Default, nat.clone(), body)
        }),
        is_reducible: false,
    })
    .unwrap();
    let info = MatcherInfo {
        num_params: 0,
        num_discrs: 0,
        alt_num_params: vec![0; alternatives as usize],
        u_elim_pos: None,
        discr_names: vec![],
        details: None,
    };
    (env, name, info)
}

#[test]
fn matcher_metadata_roundtrips_in_the_existing_dag_carrier() {
    let (mut env, name, info) = fixture();
    assert!(env.get_matcher_info(&name).is_none());
    let absent = Environment::from_dag_bincode(&env.to_dag_bincode().unwrap()).unwrap();
    assert!(absent.get_matcher_info(&name).is_none());
    env.register_matcher_info(name.clone(), info.clone())
        .unwrap();
    assert_eq!(env.get_matcher_info(&name), Some(&info));
    let bytes = env.to_dag_bincode().unwrap();
    let restored = Environment::from_dag_bincode(&bytes).unwrap();
    assert_eq!(restored.get_matcher_info(&name), Some(&info));
    assert_eq!(restored.to_dag_bincode().unwrap(), bytes);
}

#[test]
fn generic_extension_mutation_invalidates_the_matcher_lookup() {
    let (mut env, name, info) = fixture();
    env.register_matcher_info(name.clone(), info.clone())
        .unwrap();
    assert_eq!(env.get_matcher_info(&name), Some(&info));
    env.add_persistent_extension_entries(
        &Name::from_string(STORAGE_KEY),
        0,
        vec![EnvExtensionEntry {
            name: name.clone(),
            data: EnvExtensionEntryData::Object(b"malformed".to_vec()),
        }],
    );
    assert!(env.get_matcher_info(&name).is_none());
    assert!(env.register_matcher_info(name, info).is_err());
}

#[test]
fn cloned_matcher_caches_follow_only_their_own_environment() {
    for warm_cache in [false, true] {
        let (mut original, name, info) = fixture();
        if warm_cache {
            original
                .register_matcher_info(name.clone(), info.clone())
                .unwrap();
        }
        let mut fork = original.clone();
        if !warm_cache {
            // Initializing the original must not initialize the fork's cache
            // from persistent storage that the fork does not possess.
            original
                .register_matcher_info(name.clone(), info.clone())
                .unwrap();
            assert!(fork.get_matcher_info(&name).is_none());
            fork.register_matcher_info(name.clone(), info.clone())
                .unwrap();
        }
        assert_eq!(original.get_matcher_info(&name), Some(&info));
        assert_eq!(fork.get_matcher_info(&name), Some(&info));

        // A conflicting raw append invalidates only this environment's cache.
        fork.add_persistent_extension_entries(
            &Name::from_string(STORAGE_KEY),
            0,
            vec![EnvExtensionEntry {
                name: name.clone(),
                data: EnvExtensionEntryData::Object(b"malformed".to_vec()),
            }],
        );
        assert!(fork.get_matcher_info(&name).is_none());
        assert!(fork
            .register_matcher_info(name.clone(), info.clone())
            .is_err());
        assert_eq!(original.get_matcher_info(&name), Some(&info));
        original.register_matcher_info(name.clone(), info).unwrap();
    }
}

#[test]
fn replayed_extension_delta_invalidates_the_matcher_lookup() {
    let (mut before, name, info) = fixture();
    assert!(before.get_matcher_info(&name).is_none());
    let mut after = before.clone();
    // A lazy initialization also exercises scalar reassembly, whose
    // heavy-field transplant must preserve/invalidate the derived cache.
    after.init_nat().unwrap();
    after
        .register_matcher_info(name.clone(), info.clone())
        .unwrap();
    let delta = after.local_fact_delta_since(&before).unwrap();
    before.apply_local_fact_delta(&delta).unwrap();
    assert_eq!(before.get_matcher_info(&name), Some(&info));
}

fn detailed_info() -> MatcherDetails {
    MatcherDetails {
        alt_infos: vec![MatcherAltInfo {
            num_fields: 0,
            num_overlaps: 0,
            has_unit_thunk: false,
        }],
        overlaps: vec![],
    }
}

#[test]
fn recent_matcher_details_survive_dag_and_fact_delta_replay() {
    let (mut before, name, mut info) = fixture();
    info.details = Some(detailed_info());
    let mut after = before.clone();
    after
        .register_matcher_info(name.clone(), info.clone())
        .unwrap();
    let delta = after.local_fact_delta_since(&before).unwrap();
    before.apply_local_fact_delta(&delta).unwrap();
    assert_eq!(before.get_matcher_info(&name), Some(&info));
    let bytes = before.to_dag_bincode().unwrap();
    let restored = Environment::from_dag_bincode(&bytes).unwrap();
    assert_eq!(restored.get_matcher_info(&name), Some(&info));
    assert_eq!(restored.to_dag_bincode().unwrap(), bytes);
}

#[test]
fn matcher_details_cannot_disagree_with_the_stored_alternative_arities() {
    let (mut env, name, mut info) = fixture();
    let mut details = detailed_info();
    details.alt_infos[0].has_unit_thunk = true;
    info.details = Some(details);
    assert!(env.register_matcher_info(name.clone(), info).is_err());
    assert!(env.get_matcher_info(&name).is_none());
}

#[test]
fn raw_persistent_storage_cannot_bypass_matcher_detail_validation() {
    for warm_cache in [false, true] {
        let (mut env, name, mut info) = fixture();
        if warm_cache {
            env.register_matcher_info(name.clone(), info.clone())
                .unwrap();
        }
        let mut details = detailed_info();
        details.alt_infos[0].has_unit_thunk = true;
        info.details = Some(details);
        let mut bytes = b"Clean.matcherInfo.v1\0".to_vec();
        bytes.extend(serde_json::to_vec(&info).unwrap());
        let key = Name::from_string(STORAGE_KEY);
        env.register_persistent_extension(key.clone());
        env.add_persistent_extension_entries(
            &key,
            0,
            vec![EnvExtensionEntry {
                name: name.clone(),
                data: EnvExtensionEntryData::Object(bytes),
            }],
        );
        assert!(env.get_matcher_info(&name).is_none());
    }
}

#[test]
fn matcher_details_refuse_duplicate_or_out_of_range_overlap_rows() {
    for overlaps in [
        vec![MatcherOverlap {
            alternative: 0,
            overlapping: vec![0],
        }],
        vec![MatcherOverlap {
            alternative: 1,
            overlapping: vec![],
        }],
        vec![MatcherOverlap {
            alternative: 0,
            overlapping: vec![1],
        }],
        vec![
            MatcherOverlap {
                alternative: 0,
                overlapping: vec![],
            },
            MatcherOverlap {
                alternative: 0,
                overlapping: vec![],
            },
        ],
    ] {
        let (mut env, name, mut info) = fixture();
        let mut details = detailed_info();
        details.overlaps = overlaps;
        info.details = Some(details);
        assert!(env.register_matcher_info(name, info).is_err());
    }

    // Graph edges describe earlier alternatives, independently of the number
    // of splitter hypotheses retained in each alternative's binder list.
    let (mut valid, name, mut info) = fixture_with_alternatives(3);
    let mut details = detailed_info();
    details.alt_infos = vec![details.alt_infos[0].clone(); 3];
    details.overlaps = vec![
        MatcherOverlap {
            alternative: 1,
            overlapping: vec![0],
        },
        MatcherOverlap {
            alternative: 2,
            overlapping: vec![0, 1],
        },
    ];
    info.details = Some(details);
    valid
        .register_matcher_info(name.clone(), info.clone())
        .unwrap();
    let restored = Environment::from_dag_bincode(&valid.to_dag_bincode().unwrap()).unwrap();
    assert_eq!(restored.get_matcher_info(&name), Some(&info));
    for target in [1, 2] {
        let mut malformed = info.clone();
        malformed.details.as_mut().unwrap().overlaps[0].overlapping = vec![target];
        let (mut direct, _, _) = fixture_with_alternatives(3);
        assert!(direct
            .register_matcher_info(name.clone(), malformed.clone())
            .is_err());
        assert!(direct.get_matcher_info(&name).is_none());
        for warm_cache in [false, true] {
            let (mut env, _, _) = fixture_with_alternatives(3);
            if warm_cache {
                env.register_matcher_info(name.clone(), info.clone())
                    .unwrap();
            }
            let mut before = env.clone();
            let mut bytes = b"Clean.matcherInfo.v1\0".to_vec();
            bytes.extend(serde_json::to_vec(&malformed).unwrap());
            let key = Name::from_string(STORAGE_KEY);
            env.register_persistent_extension(key.clone());
            env.add_persistent_extension_entries(
                &key,
                0,
                vec![EnvExtensionEntry {
                    name: name.clone(),
                    data: EnvExtensionEntryData::Object(bytes),
                }],
            );
            assert!(env.get_matcher_info(&name).is_none());
            let restored = Environment::from_dag_bincode(&env.to_dag_bincode().unwrap()).unwrap();
            assert!(restored.get_matcher_info(&name).is_none());
            let delta = env.local_fact_delta_since(&before).unwrap();
            before.apply_local_fact_delta(&delta).unwrap();
            assert!(before.get_matcher_info(&name).is_none());
        }
    }
}

fn definition(env: &mut Environment, name: &str, alternatives: u32) -> Name {
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
    .unwrap();
    name
}

fn alternatives(count: u32) -> MatcherInfo {
    MatcherInfo {
        num_params: 0,
        num_discrs: 0,
        alt_num_params: vec![0; count as usize],
        u_elim_pos: None,
        discr_names: vec![],
        details: None,
    }
}

fn stored(name: &Name, info: &MatcherInfo) -> EnvExtensionEntry {
    let mut bytes = b"Clean.matcherInfo.v1\0".to_vec();
    bytes.extend(serde_json::to_vec(info).unwrap());
    EnvExtensionEntry {
        name: name.clone(),
        data: EnvExtensionEntryData::Object(bytes),
    }
}

/// The `.olean` import appends each module's rows to the matcher storage in
/// ONE call through `TrustedEnvExt` (`clean-olean` `load_register.rs`). Every
/// row of such a call must reach the lookup, and a restore, which derives the
/// index from the stored rows, must answer every lookup the same way.
#[test]
fn a_multi_entry_trait_append_reaches_every_lookup_and_every_restore() {
    let mut env = Environment::default();
    let names: Vec<Name> = (1..=6)
        .map(|k| definition(&mut env, &format!("matcher_import_row_{k}"), k))
        .collect();
    let key = Name::from_string(STORAGE_KEY);
    TrustedEnvExt::register_persistent_extension(&mut env, key.clone());
    TrustedEnvExt::add_persistent_extension_entries(
        &mut env,
        &key,
        0,
        names
            .iter()
            .zip(1..)
            .map(|(name, k)| stored(name, &alternatives(k)))
            .collect(),
    );
    let mut expected: Vec<Option<MatcherInfo>> = (1..=6).map(|k| Some(alternatives(k))).collect();
    // A second call poisons the third name and confirms the fifth.
    TrustedEnvExt::add_persistent_extension_entries(
        &mut env,
        &key,
        2,
        vec![
            stored(&names[4], &alternatives(5)),
            EnvExtensionEntry {
                name: names[2].clone(),
                data: EnvExtensionEntryData::Object(b"malformed".to_vec()),
            },
        ],
    );
    expected[2] = None;
    let restored = [
        (
            "serde",
            Environment::from_bincode(&env.to_bincode().unwrap()).unwrap(),
        ),
        (
            "DAG",
            Environment::from_dag_bincode(&env.to_dag_bincode().unwrap()).unwrap(),
        ),
    ];
    for (name, want) in names.iter().zip(&expected) {
        assert_eq!(env.get_matcher_info(name), want.as_ref(), "`{name}`");
        for (path, restored) in &restored {
            assert_eq!(
                restored.get_matcher_info(name),
                want.as_ref(),
                "`{name}` after a {path} restore"
            );
        }
    }
}

#[test]
fn alternative_arity_reconstruction_refuses_overflow() {
    let mut details = detailed_info();
    details.alt_infos[0].has_unit_thunk = true;
    assert!(details.alt_num_params(u32::MAX).is_none());
}

#[test]
fn legacy_matcher_json_keeps_the_original_five_fields() {
    let (_, _, info) = fixture();
    let value = serde_json::to_value(&info).unwrap();
    assert_eq!(value.as_object().unwrap().len(), 5);
    assert!(value.get("details").is_none());
    let restored: MatcherInfo = serde_json::from_value(value).unwrap();
    assert_eq!(restored, info);
}
