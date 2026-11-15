// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Isolated genuine source admission, before default String migration.

use clean_kernel::{Environment, Name};

fn source_world(bytes: &[u8]) -> Environment {
    source_world_for_roots(
        bytes,
        &[
            "String.ofByteArray",
            "String.toByteArray",
            "String.isValidUTF8",
            "String.casesOn",
            "String.recOn",
            "ByteArray.mk",
            "ByteArray.data",
            "ByteArray.casesOn",
            "Array.mk",
            "Array.toList",
            "Array.casesOn",
        ],
    )
}

pub(crate) fn source_world_for_roots(bytes: &[u8], roots: &[&str]) -> Environment {
    let mut env = Environment::for_lean_replay();
    env.admit_builtin_source_for_testing(bytes, roots)
        .expect("official source families and their complete checked dependencies");
    for (structure, fields) in [
        ("Array", vec!["toList"]),
        ("ByteArray", vec!["data"]),
        ("String", vec!["toByteArray", "isValidUTF8"]),
    ] {
        env.register_structure_fields(
            Name::from_string(structure),
            fields.into_iter().map(Name::from_string).collect(),
        )
        .expect("actual source structure fields");
    }
    env
}

fn check_layout(bytes: &[u8]) {
    let env = source_world(bytes);
    assert!(clean_compiler::string_layout::has_byte_array_string_layout(
        &env
    ));
    assert!(
        crate::native_string_layout_policy::StringLayoutPolicy::from_env(&env)
            .permits_byte_backed_bodies()
    );
    assert!(env
        .get_constructor(&Name::from_string("String.mk"))
        .is_none());
    assert!(
        env.axiom_deps(&Name::from_string("String.ofByteArray"))
            .expect("checked dependency closure")
            .iter()
            .all(|name| env.is_canonical_foundational_axiom(name)),
        "the source constructor has no domain-specific axioms"
    );
}

#[test]
fn actual_pinned_string_layout_admits_without_legacy_defaults() {
    check_layout(include_bytes!(
        "../tests/fixtures/string_bytearray/layout-lean-4.30.0-rc2.json"
    ));
}

#[test]
fn actual_latest_string_layout_admits_without_legacy_defaults() {
    check_layout(include_bytes!(
        "../tests/fixtures/string_bytearray/layout-lean-4.35.0.json"
    ));
}
