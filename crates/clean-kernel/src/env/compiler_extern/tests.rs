// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn represented() -> CompilerExternMetadata {
    CompilerExternMetadata::Complete(CompilerExternDescriptor {
        arity: CompilerExternArity::Legacy(Some(3)),
        entries: vec![
            CompilerExternEntry::Standard {
                backend: name("llvm"),
                symbol: "same".into(),
            },
            CompilerExternEntry::Standard {
                backend: name("c"),
                symbol: "different".into(),
            },
            CompilerExternEntry::Standard {
                backend: name("all"),
                symbol: "conflict".into(),
            },
            CompilerExternEntry::Adhoc {
                backend: name("cpp"),
            },
            CompilerExternEntry::Inline {
                backend: name("c"),
                pattern: "#1 + #2".into(),
            },
            CompilerExternEntry::Foreign {
                backend: name("c"),
                symbol: "foreign".into(),
            },
            CompilerExternEntry::Opaque,
        ],
    })
}

#[test]
fn complete_metadata_survives_clone_json_bincode_and_owned_dag() {
    let mut env = Environment::default();
    env.register_extern_metadata(name("subject"), represented())
        .expect("represented data");
    let restored = [
        env.clone(),
        Environment::from_json(&env.to_json().expect("JSON encode")).expect("JSON restore"),
        Environment::from_bincode(&env.to_bincode().expect("bincode encode"))
            .expect("bincode restore"),
        Environment::from_dag_bincode(&env.to_dag_bincode().expect("DAG encode"))
            .expect("DAG restore"),
    ];
    for restored in restored {
        assert_eq!(
            restored.get_extern(&name("subject")),
            Some(&"same".to_owned())
        );
        assert_eq!(
            restored
                .extern_metadata(&name("subject"))
                .expect("typed data"),
            Some(represented())
        );
    }
}

#[test]
fn legacy_symbol_never_inherits_complete_metadata_even_with_same_spelling() {
    let mut env = Environment::default();
    env.register_extern_metadata(name("subject"), represented())
        .expect("typed");
    env.register_extern(name("subject"), "same".into());
    assert_eq!(
        env.extern_metadata(&name("subject"))
            .expect("legacy status"),
        Some(CompilerExternMetadata::from("same".to_owned()))
    );
    let restored =
        Environment::from_dag_bincode(&env.to_dag_bincode().expect("encode")).expect("restore");
    assert_eq!(
        restored
            .extern_metadata(&name("subject"))
            .expect("legacy status"),
        Some(CompilerExternMetadata::from("same".to_owned()))
    );
}

#[test]
fn unavailable_and_legacy_arity_are_distinct_from_modern_unspecified() {
    let absent = CompilerExternMetadata::Incomplete {
        diagnostic: String::new(),
        reason: CompilerExternIncomplete::UnspecifiedSourceBinding,
    };
    let mut env = Environment::default();
    env.register_extern_metadata(name("unavailable"), absent.clone())
        .expect("incomplete data");
    assert_eq!(
        env.extern_metadata(&name("unavailable")).expect("status"),
        Some(absent)
    );
    let CompilerExternMetadata::Complete(mut a) = represented() else {
        panic!("fixture")
    };
    let mut b = a.clone();
    a.arity = CompilerExternArity::Legacy(None);
    b.arity = CompilerExternArity::Unspecified;
    assert_ne!(
        encode(&CompilerExternMetadata::Complete(a)).expect("legacy none"),
        encode(&CompilerExternMetadata::Complete(b)).expect("modern absent field")
    );
    assert!(env
        .extern_metadata(&name("not_registered"))
        .expect("absent")
        .is_none());
}

#[test]
fn corrupt_unknown_and_conflicting_storage_remain_typed_refusals() {
    let mut env = Environment::default();
    env.register_extern_metadata(name("subject"), represented())
        .expect("typed");
    let mut changed = represented();
    if let CompilerExternMetadata::Complete(descriptor) = &mut changed {
        descriptor.entries.reverse();
    }
    env.persistent_extensions.append(
        &storage_key(),
        0,
        vec![EnvExtensionEntry {
            name: name("subject"),
            data: EnvExtensionEntryData::Object(encode(&changed).expect("different ordered data")),
        }],
    );
    assert!(matches!(
        env.extern_metadata(&name("subject")),
        Err(CompilerExternMetadataError::Conflict)
    ));
    for bytes in [
        b"Clean.compilerExtern.v2\0{}".to_vec(),
        b"Clean.compilerExtern.v1\0{\"Unknown\":0}".to_vec(),
    ] {
        let mut state = env
            .persistent_extensions
            .get(&storage_key())
            .expect("storage")
            .clone();
        state.imported_entries[0] = vec![EnvExtensionEntry {
            name: name("subject"),
            data: EnvExtensionEntryData::Object(bytes),
        }];
        env.persistent_extensions
            .set_state(&storage_key(), Some(state));
        assert!(env.extern_metadata(&name("subject")).is_err());
        let restored =
            Environment::from_dag_bincode(&env.to_dag_bincode().expect("encode raw refusal"))
                .expect("restore raw refusal");
        assert!(restored.extern_metadata(&name("subject")).is_err());
    }
}

#[test]
fn empty_or_oversized_carrier_refuses_without_replacing_the_binding() {
    let mut env = Environment::default();
    env.register_extern(name("subject"), "old".into());
    let empty = CompilerExternMetadata::Complete(CompilerExternDescriptor {
        arity: CompilerExternArity::Unspecified,
        entries: vec![],
    });
    assert!(matches!(
        env.register_extern_metadata(name("subject"), empty),
        Err(CompilerExternMetadataError::Empty)
    ));
    assert_eq!(env.get_extern(&name("subject")), Some(&"old".to_owned()));
    let huge = CompilerExternMetadata::Complete(CompilerExternDescriptor {
        arity: CompilerExternArity::Unspecified,
        entries: vec![CompilerExternEntry::Inline {
            backend: name("c"),
            pattern: "x".repeat(MAX_BYTES),
        }],
    });
    assert!(matches!(
        env.register_extern_metadata(name("subject"), huge),
        Err(CompilerExternMetadataError::Resource)
    ));
    assert_eq!(env.get_extern(&name("subject")), Some(&"old".to_owned()));
}

#[test]
fn unreadable_small_candidate_preserves_the_previous_complete_binding() {
    let mut env = Environment::default();
    env.register_extern_metadata(name("subject"), represented())
        .expect("original complete binding");
    let before = env.to_dag_bincode().expect("original complete state");
    let unreadable = CompilerExternMetadata::Complete(CompilerExternDescriptor {
        arity: CompilerExternArity::Unspecified,
        entries: vec![CompilerExternEntry::Standard {
            backend: name(&format!("{}end", "part.".repeat(256))),
            symbol: "replacement".into(),
        }],
    });
    // This is within the entry/byte limits; it exercises the reader's JSON
    // recursion limit rather than the existing oversized-carrier refusal.
    let encoded = encode(&unreadable).expect("small serializable candidate");
    assert!(encoded.len() <= MAX_BYTES);
    assert!(matches!(
        env.register_extern_metadata(name("subject"), unreadable),
        Err(CompilerExternMetadataError::Encoding(error))
            if error.to_string().contains("recursion limit")
    ));
    assert_eq!(env.get_extern(&name("subject")), Some(&"same".to_owned()));
    assert_eq!(
        env.extern_metadata(&name("subject"))
            .expect("original metadata remains readable"),
        Some(represented())
    );
    assert_eq!(env.to_dag_bincode().expect("unchanged state"), before);
}

#[test]
fn metadata_is_part_of_replayed_effects_and_local_fact_deltas() {
    let before = Environment::default();
    let mut after = before.clone();
    after
        .register_extern_metadata(name("subject"), represented())
        .expect("typed");
    let delta = after
        .local_fact_delta_since(&before)
        .expect("plain data is replayable");
    let delta = super::super::EnvFactDelta::decode(&delta.encode().expect("encode delta"))
        .expect("decode delta");
    let mut replayed = before.clone();
    replayed
        .apply_local_fact_delta(&delta)
        .expect("exact base replay");
    assert_eq!(
        replayed
            .extern_metadata(&name("subject"))
            .expect("metadata"),
        Some(represented())
    );
    let effect = after.effect_since(&before);
    let replayed_effect = replayed.effect_since(&before);
    assert!(effect.disagreement(&replayed_effect, &replayed).is_none());
}
