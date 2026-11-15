// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The world rule over an injected table holding every state, Measured and
//! Canary included, and the
//! environment binding over the real table.

use super::{
    admit_part, check_part_bytes, decide, declaration, declare, environment_world, Decision,
    DECLARATION,
};
use crate::import::ImportError;
use crate::world::{HeaderIdentity, LeanWorldRow, PartWriter, WorldState};
use clean_kernel::env::Environment;
use std::path::Path;

const fn identity(fill: u8) -> HeaderIdentity {
    HeaderIdentity::from_parts(2, 1, [fill; 40])
}

const fn row(world: &'static str, state: WorldState, fill: u8) -> LeanWorldRow {
    LeanWorldRow {
        world,
        state,
        identity: identity(fill),
        lean_version: None,
    }
}

static TABLE: &[LeanWorldRow] = &[
    row("oracle", WorldState::Oracle, b'0'),
    row("historical", WorldState::Historical, b'1'),
    row("frontend", WorldState::FrontendOnly, b'2'),
    row("measured", WorldState::Measured, b'3'),
    row("canary", WorldState::Canary, b'4'),
];

fn lean(fill: u8) -> PartWriter {
    PartWriter::Lean {
        identity: identity(fill),
        lean_version: Some("4.99.0".to_string()),
    }
}

fn unsupported_found(result: Result<Decision, ImportError>) -> (String, Vec<String>) {
    match result {
        Err(ImportError::UnsupportedLeanWorld {
            module,
            found,
            supported,
        }) => {
            assert_eq!(module, "M", "names the part");
            (found, supported)
        }
        other => panic!("expected UnsupportedLeanWorld, got {other:?}"),
    }
}

#[test]
fn test_world_gate_clean_part_is_neutral_under_any_binding() {
    for bound in [None, Some(("oracle", "A")), Some(("measured", DECLARATION))] {
        assert_eq!(
            decide(TABLE, bound, "M", &PartWriter::Clean).expect("neutral"),
            Decision::Neutral
        );
    }
}

#[test]
fn test_world_gate_implicit_worlds_bind_an_unbound_environment() {
    for (fill, world) in [(b'0', "oracle"), (b'1', "historical"), (b'2', "frontend")] {
        assert_eq!(
            decide(TABLE, None, "M", &lean(fill)).expect("readable"),
            Decision::Bind(world)
        );
        assert_eq!(
            decide(TABLE, Some((world, "A")), "M", &lean(fill)).expect("same world"),
            Decision::Same
        );
    }
}

#[test]
fn test_world_gate_unknown_identity_is_refused_naming_it_and_the_readable_worlds() {
    let (found, supported) = unsupported_found(decide(TABLE, None, "M", &lean(b'9')));
    assert!(
        found.contains(&"9".repeat(40)),
        "names the githash: {found}"
    );
    assert!(
        found.contains("4.99.0"),
        "names the header version: {found}"
    );
    assert_eq!(
        supported.len(),
        4,
        "every world but the canary: {supported:?}"
    );
    assert!(supported.iter().all(|s| !s.starts_with("canary")));
    assert!(
        supported
            .iter()
            .any(|s| s.starts_with("measured (measured, once declared)")),
        "{supported:?}"
    );
    // A binding does not change the answer for an identity no row carries.
    unsupported_found(decide(TABLE, Some(("oracle", "A")), "M", &lean(b'9')));
}

#[test]
fn test_world_gate_canary_is_refused_by_name_even_when_declared_elsewhere() {
    for bound in [None, Some(("oracle", "A"))] {
        let (found, _) = unsupported_found(decide(TABLE, bound, "M", &lean(b'4')));
        assert!(
            found.contains("canary") && found.contains("Canary"),
            "{found}"
        );
    }
}

#[test]
fn test_world_gate_measured_world_needs_a_declaration() {
    let (found, _) = unsupported_found(decide(TABLE, None, "M", &lean(b'3')));
    assert!(found.contains("has not declared"), "{found}");
    assert_eq!(
        decide(TABLE, Some(("measured", DECLARATION)), "M", &lean(b'3')).expect("declared"),
        Decision::Same
    );
}

#[test]
fn test_world_gate_second_world_is_mixed() {
    match decide(TABLE, Some(("oracle", "A")), "M", &lean(b'1')) {
        Err(ImportError::MixedLeanWorlds {
            module,
            world,
            first,
            first_world,
        }) => {
            assert_eq!(
                (
                    module.as_str(),
                    world.as_str(),
                    first.as_str(),
                    first_world.as_str()
                ),
                ("M", "historical", "A", "oracle")
            );
        }
        other => panic!("expected MixedLeanWorlds, got {other:?}"),
    }
    // A Measured part over an Oracle binding is mixed too, not "undeclared".
    assert!(matches!(
        decide(TABLE, Some(("oracle", "A")), "M", &lean(b'3')),
        Err(ImportError::MixedLeanWorlds { .. })
    ));
}

#[test]
fn test_world_gate_declaration_rules() {
    assert!(matches!(
        declaration(TABLE, None, "nowhere"),
        Err(ImportError::UnknownLeanWorld { .. })
    ));
    assert!(matches!(
        declaration(TABLE, None, "canary"),
        Err(ImportError::UnknownLeanWorld { .. })
    ));
    assert_eq!(
        declaration(TABLE, None, "measured").expect("binds"),
        Some("measured")
    );
    assert_eq!(
        declaration(TABLE, None, "oracle").expect("binds"),
        Some("oracle")
    );
    assert_eq!(
        declaration(TABLE, Some(("measured", "A")), "measured").expect("already"),
        None
    );
    match declaration(TABLE, Some(("oracle", "A")), "measured") {
        Err(ImportError::MixedLeanWorlds { module, .. }) => assert_eq!(module, DECLARATION),
        other => panic!("expected MixedLeanWorlds, got {other:?}"),
    }
}

fn fixture(rel: &str) -> Vec<u8> {
    std::fs::read(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(rel),
    )
    .expect("tracked fixture")
}

/// Over the real table: the first Lean part binds, a check never does, and
/// a declaration of another world is then refused.
#[test]
fn test_world_gate_environment_binding_over_the_real_table() {
    let rc2 = fixture("tests/fixtures/olean/v4.30.0/closure_cache/Init.olean");
    let v13 = fixture("tests/fixtures/olean/v4.13.0/custom/Minimal.olean");
    let mut env = Environment::new();
    assert_eq!(environment_world(&env), None);

    check_part_bytes(&env, "Init", &rc2).expect("readable");
    assert_eq!(environment_world(&env), None, "a check does not bind");

    admit_part(&mut env, Some("Init"), &rc2).expect("binds");
    assert_eq!(environment_world(&env), Some("v4.30.0-rc2"));
    admit_part(&mut env, Some("Init"), &rc2).expect("same world");

    assert!(matches!(
        check_part_bytes(&env, "Minimal", &v13),
        Err(ImportError::MixedLeanWorlds { .. })
    ));
    assert!(matches!(
        admit_part(&mut env, Some("Minimal"), &v13),
        Err(ImportError::MixedLeanWorlds { .. })
    ));
    assert!(matches!(
        declare(&mut env, "v4.13.0"),
        Err(ImportError::MixedLeanWorlds { .. })
    ));
    declare(&mut env, "v4.30.0-rc2").expect("the world it reads");
    assert_eq!(environment_world(&env), Some("v4.30.0-rc2"));

    let mut fresh = Environment::new();
    declare(&mut fresh, "v4.13.0").expect("a readable world");
    assert_eq!(environment_world(&fresh), Some("v4.13.0"));
    assert!(matches!(
        admit_part(&mut fresh, Some("Init"), &rc2),
        Err(ImportError::MixedLeanWorlds { first, .. }) if first == DECLARATION
    ));
}

#[test]
fn recent_native_worlds_require_exact_declarations_and_keep_universe_profile() {
    for version in ["v4.35.0", "v4.36.0-rc2"] {
        let bytes = fixture(&format!(
            "tests/fixtures/olean/{version}/matcher-metadata/MatcherParity.olean"
        ));
        let row = crate::world::lean_worlds()
            .iter()
            .find(|row| row.world == version)
            .unwrap();
        assert_eq!(row.state, WorldState::Measured);
        let mut env = Environment::new();
        assert!(matches!(
            check_part_bytes(&env, "MatcherParity", &bytes),
            Err(ImportError::UnsupportedLeanWorld { .. })
        ));
        assert_eq!(environment_world(&env), None);
        declare(&mut env, version).unwrap();
        assert_eq!(environment_world(&env), Some(version));
        assert_eq!(
            env.lean_level_profile(),
            clean_kernel::level::LeanLevelProfile::Lean430
        );
        check_part_bytes(&env, "MatcherParity", &bytes).unwrap();
        admit_part(&mut env, Some("MatcherParity"), &bytes).unwrap();
        assert_eq!(environment_world(&env), Some(version));
    }
}

#[test]
fn recent_native_worlds_refuse_mixed_and_unmeasured_headers() {
    for (version, other) in [("v4.35.0", "v4.36.0-rc2"), ("v4.36.0-rc2", "v4.35.0")] {
        let bytes = fixture(&format!(
            "tests/fixtures/olean/{version}/matcher-metadata/MatcherParity.olean"
        ));
        let mut env = Environment::new();
        declare(&mut env, other).unwrap();
        assert!(matches!(
            admit_part(&mut env, Some("MatcherParity"), &bytes),
            Err(ImportError::MixedLeanWorlds { .. })
        ));
        assert_eq!(environment_world(&env), Some(other));
        let mut unknown = bytes.clone();
        unknown[40..80].fill(b'f');
        let mut exact = Environment::new();
        declare(&mut exact, version).unwrap();
        assert!(matches!(
            admit_part(&mut exact, Some("UnknownMatcherParity"), &unknown),
            Err(ImportError::UnsupportedLeanWorld { .. })
        ));
        assert_eq!(environment_world(&exact), Some(version));
    }
}
