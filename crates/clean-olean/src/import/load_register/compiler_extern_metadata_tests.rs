// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use clean_kernel::env::{
    CompilerExternArity, CompilerExternDescriptor, CompilerExternEntry, CompilerExternMetadata,
};

fn metadata() -> CompilerExternMetadata {
    CompilerExternMetadata::Complete(CompilerExternDescriptor {
        arity: CompilerExternArity::Legacy(Some(1)),
        entries: vec![
            CompilerExternEntry::Standard {
                backend: Name::from_string("llvm"),
                symbol: "first".into(),
            },
            CompilerExternEntry::Standard {
                backend: Name::from_string("c"),
                symbol: "conflict".into(),
            },
        ],
    })
}
fn seed(env: &mut Environment, name: &Name) {
    env.add_decl(clean_kernel::Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::arrow(Expr::prop(), Expr::prop()),
        value: Expr::lam(
            clean_kernel::BinderInfo::Default,
            Expr::prop(),
            Expr::bvar(0),
        ),
        is_reducible: false,
    })
    .expect("real kernel checked setup");
}
#[test]
fn real_extension_registration_preserves_metadata_only_for_its_own_declaration() {
    let subject = Name::from_string("Owned.f");
    let mut env = Environment::default();
    seed(&mut env, &subject);
    let row = || TypedExtension {
        extension_name: Name::from_string("Lean.externAttr"),
        source_rows: Some(1),
        undecoded_entries: 0,
        compiler_names: None,
        entries: vec![TypedExtensionEntry::Extern {
            decl: subject.clone(),
            symbol: "first".into(),
            metadata: metadata(),
        }],
    };
    let mut registered = Vec::new();
    register_real_compiler_attr_entries(
        &mut env,
        &Some("Incoming".to_owned()),
        &[row()],
        &super::super::late_binding::CompilerNames::unknown(),
        &mut registered,
    )
    .expect("foreign row is observed");
    assert!(env.extern_metadata(&subject).expect("absent").is_none());
    env.set_constant_origins(
        vec![subject.clone()],
        clean_kernel::ConstantOrigin::olean_import(Some("Owned".into())),
    );
    register_real_compiler_attr_entries(
        &mut env,
        &Some("Owned".to_owned()),
        &[row()],
        &super::super::late_binding::CompilerNames::unknown(),
        &mut registered,
    )
    .expect("owned row registers");
    assert_eq!(
        env.extern_metadata(&subject).expect("metadata"),
        Some(metadata())
    );
    let mut changed = metadata();
    if let CompilerExternMetadata::Complete(d) = &mut changed {
        d.entries.reverse();
    }
    assert!(matches!(
        register_imported_extern_metadata(&mut env, Some("Owned"), &subject, &metadata())
            .expect("identical repeated carrier"),
        Registration::NotRegistered
    ));
    assert!(
        register_imported_extern_metadata(&mut env, Some("Owned"), &subject, &changed).is_err(),
        "a conflicting owned row must not disappear behind first-writer handling"
    );
    assert_eq!(
        env.extern_metadata(&subject).expect("unchanged"),
        Some(metadata())
    );
}

#[test]
fn clean_payload_carrier_roundtrip_and_legacy_status_remain_distinct() {
    let subject = Name::from_string("Owned.f");
    let mut env = Environment::default();
    seed(&mut env, &subject);
    env.set_constant_origins(
        vec![subject.clone()],
        clean_kernel::ConstantOrigin::clean_payload(Some("Owned".into())),
    );
    let payload = crate::CleanPayload {
        compiler_context: crate::CompilerContextKind::Source,
        externs: vec![(subject.clone(), "first".into())],
        extern_metadata: vec![(subject.clone(), metadata())],
        ..crate::CleanPayload::default()
    };
    let bytes = crate::payload::encode_clean_payload(&payload).expect("encode");
    let restored = crate::payload::decode_clean_payload(&bytes)
        .expect("decode")
        .expect("payload");
    apply_payload_compiler_attrs(&mut env, &restored, Some("Owned")).expect("metadata import");
    assert_eq!(
        env.extern_metadata(&subject).expect("complete"),
        Some(metadata())
    );
    let mut legacy = Environment::default();
    seed(&mut legacy, &subject);
    legacy.set_constant_origins(
        vec![subject.clone()],
        clean_kernel::ConstantOrigin::clean_payload(Some("Owned".into())),
    );
    let payload = crate::CleanPayload {
        compiler_context: crate::CompilerContextKind::Source,
        externs: vec![(subject.clone(), "first".into())],
        ..crate::CleanPayload::default()
    };
    apply_payload_compiler_attrs(&mut legacy, &payload, Some("Owned"))
        .expect("legacy label import");
    assert_eq!(
        legacy.extern_metadata(&subject).expect("incomplete status"),
        Some(CompilerExternMetadata::from("first".to_owned()))
    );
}

#[test]
fn payload_descriptor_must_agree_with_the_actual_diagnostic_row() {
    let mut env = Environment::default();
    let subject = Name::from_string("Owned.f");
    seed(&mut env, &subject);
    let payload = crate::CleanPayload {
        compiler_context: crate::CompilerContextKind::Source,
        externs: vec![(subject.clone(), "different".into())],
        extern_metadata: vec![(subject.clone(), metadata())],
        ..crate::CleanPayload::default()
    };
    let error = apply_payload_compiler_attrs(&mut env, &payload, Some("Owned"))
        .expect_err("descriptor and diagnostic label must agree");
    assert!(
        error
            .to_string()
            .contains("contradictory payload extern metadata"),
        "{error}"
    );
    assert!(env.extern_metadata(&subject).expect("unchanged").is_none());
}
