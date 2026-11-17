// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::extension_binding_pins::PINNED_WORLDS;
use super::super::fingerprint::Fingerprinter;
use super::{encode_hex, PINNED_TABLE_LABEL};
use clean_kernel::env::Environment;
use clean_kernel::{LeanWorld, Name};
use std::collections::BTreeMap;
use std::path::Path;

fn library() -> std::path::PathBuf {
    let decision =
        crate::source_world_for_file(Path::new("Bindings435.lean"), Some(LeanWorld::Lean435))
            .expect("the exact official 4.35 SDK is required");
    let Ok(crate::ImportWorld::Explicit { lib, .. }) = decision.imports() else {
        panic!("explicit 4.35 library required")
    };
    lib.clone()
}

#[test]
fn genuine_435_partial_world_rederives_from_prelude_full_init_and_query_order() {
    assert_eq!(
        PINNED_TABLE_LABEL,
        PINNED_WORLDS
            .iter()
            .map(|world| world.label)
            .collect::<Vec<_>>()
            .join(" | "),
        "every admitted world's identity must remain disclosed"
    );
    let world = PINNED_WORLDS
        .iter()
        .find(|world| world.label == "lean-v4.35.0-literals-div-mod")
        .unwrap();
    let expected = world
        .rows
        .iter()
        .map(|(name, digest)| ((*name).to_owned(), (*digest).to_owned()))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        expected.len(),
        5,
        "this is a partial world, never an all-key qualification"
    );
    let lib = library();
    for root in ["Init.Prelude", "Init"] {
        let mut env = Environment::for_lean_replay();
        crate::declare_environment_world(&mut env, LeanWorld::Lean435.tag()).unwrap();
        let summaries =
            crate::load_module_with_deps(&mut env, root, std::slice::from_ref(&lib)).unwrap();
        eprintln!(
            "LEAN435_FINGERPRINT_ROOT {root} modules={} constants={}",
            summaries.len(),
            env.constants().count()
        );
        for reverse in [false, true] {
            let mut names = expected.keys().collect::<Vec<_>>();
            if reverse {
                names.reverse();
            }
            let mut together = Fingerprinter::new(&env);
            for key in names {
                let name = Name::from_string(key);
                let actual = encode_hex(&together.constant(&name));
                let isolated = encode_hex(&Fingerprinter::new(&env).constant(&name));
                eprintln!("LEAN435_FINGERPRINT {root} reverse={reverse} {key} {actual}");
                assert_eq!(actual, expected[key]);
                assert_eq!(actual, isolated, "query-order changed {root}/{key}");
            }
        }
    }
}

#[test]
fn genuine_435_artifacts_still_require_the_matching_declared_world() {
    let lib = library();
    let mut implicit = Environment::for_lean_replay();
    let error =
        crate::load_module_with_deps(&mut implicit, "Init.Prelude", std::slice::from_ref(&lib))
            .unwrap_err();
    assert!(
        matches!(error, crate::ImportError::UnsupportedLeanWorld { .. }),
        "{error:?}"
    );
    eprintln!("LEAN435_IMPLICIT_REFUSAL {error}");
    let mut wrong = Environment::for_lean_replay();
    crate::declare_environment_world(&mut wrong, LeanWorld::ORACLE.tag()).unwrap();
    let error = crate::load_module_with_deps(&mut wrong, "Init.Prelude", &[lib]).unwrap_err();
    assert!(
        matches!(error, crate::ImportError::MixedLeanWorlds { .. }),
        "{error:?}"
    );
    eprintln!("LEAN435_WRONG_WORLD_REFUSAL {error}");
}
