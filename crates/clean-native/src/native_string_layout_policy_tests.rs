// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use serde_json::json;

const PACKET: &[u8] =
    include_bytes!("../tests/fixtures/string_bytearray/layout-lean-4.30.0-rc2.json");
const ROOTS: &[&str] = &[
    "String.ofByteArray",
    "String.toByteArray",
    "ByteArray.data",
    "Array.toList",
];

fn world() -> Environment {
    crate::native_string_source_bridge_tests::source_world_for_roots(PACKET, ROOTS)
}

#[test]
fn checked_model_permission_rejects_unsafe_or_partial_residents() {
    let env = world();
    assert!(StringLayoutPolicy::from_env(&env).permits_byte_backed_bodies());
    for unsafe_flag in [false, true] {
        let mut candidate = env.clone();
        let name = Name::from_string("String.toByteArray");
        if unsafe_flag {
            candidate.mark_unsafe(name.clone());
        } else {
            candidate.mark_partial(name.clone());
        }
        assert_eq!(
            candidate.declaration_verification(&name),
            Some(DeclarationVerification::FullKernelCheck)
        );
        assert!(!StringLayoutPolicy::from_env(&candidate).permits_byte_backed_bodies());
    }
}

#[test]
fn a_checked_same_typed_counterfeit_getter_cannot_authorize_native_projection() {
    let mut packet: serde_json::Value = serde_json::from_slice(PACKET).expect("packet");
    let getter = packet["declarations"]
        .as_array()
        .expect("declarations")
        .iter()
        .position(|decl| decl["name"] == json!(["str", ["str", ["anon"], "String"], "toByteArray"]))
        .expect("actual getter");
    let nodes = packet["expressions"].as_array_mut().expect("nodes");
    let mut add = |value| {
        let id = nodes.len();
        nodes.push(value);
        id
    };
    let byte = add(json!(["const", ["str", ["anon"], "UInt8"], []]));
    let nil = add(json!([
        "const",
        ["str", ["str", ["anon"], "List"], "nil"],
        [["zero"]]
    ]));
    let empty = add(json!(["app", nil, byte]));
    let array = add(json!([
        "const",
        ["str", ["str", ["anon"], "Array"], "mk"],
        [["zero"]]
    ]));
    let array = add(json!(["app", array, byte]));
    let array = add(json!(["app", array, empty]));
    let bytes = add(json!([
        "const",
        ["str", ["str", ["anon"], "ByteArray"], "mk"],
        []
    ]));
    let bytes = add(json!(["app", bytes, array]));
    let string = add(json!(["const", ["str", ["anon"], "String"], []]));
    let value = add(json!([
        "lam",
        ["str", ["anon"], "self"],
        "default",
        string,
        bytes
    ]));
    packet["declarations"][getter]["value"] = json!(value);
    let mut env = Environment::for_lean_replay();
    env.admit_builtin_source_for_testing(&serde_json::to_vec(&packet).expect("encode"), ROOTS)
        .expect("the constant-empty function really has type String → ByteArray");
    assert_eq!(
        env.declaration_verification(&Name::from_string("String.toByteArray")),
        Some(DeclarationVerification::FullKernelCheck)
    );
    assert!(clean_compiler::string_layout::has_byte_array_string_layout(
        &env
    ));
    assert!(!StringLayoutPolicy::from_env(&env).permits_byte_backed_bodies());
}

#[test]
fn raw_c_has_no_checked_source_permission() {
    let _checked_world = world();
    let body = "clean_obj* l_String_casesOn(clean_obj* x) {\nreturn x;\n}\n";
    let error =
        crate::native_build::select_shims_for_c_text(body).expect_err("raw C keeps its refusal");
    assert!(error.to_string().contains("source-lowered String body"));
}

#[test]
fn declaration_permission_preserves_typed_component_identity() {
    let env = world();
    let policy = StringLayoutPolicy::from_env(&env);
    assert!(policy.permits_byte_backed_bodies());
    let canonical = Name::from_string("String.toByteArray");
    let twin = Name::anon().str("String.toByteArray");
    assert_ne!(canonical, twin);
    assert_eq!(canonical.to_string(), twin.to_string());
    assert!(policy.permits_source_decl(&env, &canonical));
    assert!(
        !policy.permits_source_decl(&env, &twin),
        "an absent twin cannot inherit provenance"
    );
    let getter = env.get_const(&canonical).expect("canonical getter");
    let mut with_twin = env.clone();
    with_twin
        .add_decl(clean_kernel::Declaration::Definition {
            name: twin.clone(),
            level_params: vec![],
            type_: getter.type_.clone(),
            value: getter.value.clone().expect("projection body"),
            is_reducible: false,
        })
        .expect("distinct checked declaration identity");
    assert!(policy.permits_source_decl(&with_twin, &twin));
    for unsafe_flag in [false, true] {
        let mut candidate = with_twin.clone();
        if unsafe_flag {
            candidate.mark_unsafe(twin.clone());
        } else {
            candidate.mark_partial(twin.clone());
        }
        assert!(StringLayoutPolicy::from_env(&candidate).permits_byte_backed_bodies());
        assert!(policy.permits_source_decl(&candidate, &canonical));
        assert!(!policy.permits_source_decl(&candidate, &twin));
    }
}

#[test]
fn constant_permission_uses_typed_canonical_names() {
    let env = world();
    let decl = Name::from_string("String.toByteArray");
    let canonical = Name::from_string("String.ofByteArray");
    let twin = Name::anon().str("String.ofByteArray");
    assert_ne!(canonical, twin);
    assert_eq!(canonical.to_string(), twin.to_string());
    crate::native_string_carrier_audit::check_string_carrier_in_env(
        &env,
        &decl,
        &Expr::const_(canonical, vec![]),
    )
    .expect("actual canonical constructor permission");
    crate::native_string_carrier_audit::check_string_carrier_in_env(
        &env,
        &decl,
        &Expr::const_(twin, vec![]),
    )
    .expect_err("the diagnostic spelling is not a constructor identity");
}
