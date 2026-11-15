// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! v40 `FatPtrKind::ContainerVtable` — the exact vtable twin of v38's
//! `ContainerLen`, for the `*const ArcInner<dyn T>` interior of every
//! `Arc<dyn T>` / `Rc<dyn T>`.
//!
//! Written as CONTRASTS, because the whole hazard here is a near-miss spelling
//! that compiles, serializes and validates while asserting something false.

use trust_ir::Module;
use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::ty::{FatPtrKind, Ty};

fn module_with_every_fat_ptr_kind() -> Module {
    let mut m = Module::new("fatptr_kinds");
    let elem = m.add_type(Ty::U8).expect("Module::add_type: test fixture");
    m.add_type(Ty::FatPtr(FatPtrKind::Slice(elem)))
        .expect("Module::add_type: test fixture");
    m.add_type(Ty::FatPtr(FatPtrKind::Str))
        .expect("Module::add_type: test fixture");
    m.add_type(Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 7 }))
        .expect("Module::add_type: test fixture");
    m.add_type(Ty::FatPtr(FatPtrKind::ContainerLen))
        .expect("Module::add_type: test fixture");
    m.add_type(Ty::FatPtr(FatPtrKind::ContainerVtable))
        .expect("Module::add_type: test fixture");
    m
}

#[test]
fn container_vtable_round_trips_all_four_formats() {
    let m = module_with_every_fat_ptr_kind();

    assert_eq!(
        deserialize_module(&serialize_module(&m).expect("serialize_module: test fixture")).unwrap(),
        m,
        "binary"
    );

    let text = trust_ir::format::canonical(&m);
    assert!(
        text.contains("fatptr<container_vtable>"),
        "the text spelling must be its own token, not a `dyn.` near-miss: {text}"
    );
    assert_eq!(
        trust_ir::parser::parse_module(&text).unwrap().types,
        m.types,
        "text"
    );

    let j = serde_json::to_string(&m).unwrap();
    assert_eq!(serde_json::from_str::<Module>(&j).unwrap(), m, "json");
    let mp = rmp_serde::to_vec(&m).unwrap();
    assert_eq!(rmp_serde::from_slice::<Module>(&mp).unwrap(), m, "msgpack");
}

/// The identity half, at MODULE scope: no two fat-pointer kinds may collapse
/// into the same module identity. A stable digest is content-derived, and two
/// different meanings must never hash equal.
#[test]
fn every_fat_pointer_kind_has_its_own_module_identity() {
    let kinds = [
        FatPtrKind::Str,
        FatPtrKind::TraitObject { trait_id: 7 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ];
    let digests: Vec<_> = kinds
        .iter()
        .map(|kind| {
            let mut m = Module::new("k");
            m.add_type(Ty::FatPtr(*kind))
                .expect("Module::add_type: test fixture");
            m.stable_digest()
        })
        .collect();

    for (i, a) in digests.iter().enumerate() {
        for (j, b) in digests.iter().enumerate() {
            if i != j {
                assert_ne!(a, b, "{:?} and {:?} hash equal", kinds[i], kinds[j]);
            }
        }
    }
}

/// A v38-LABELLED blob must REFUSE fat-pointer-kind tag 4. An unknown tag fails
/// closed on its own; the version gate is what stops a v38 blob carrying tag 4
/// from being taken as well-formed by a reader that would otherwise accept it.
#[test]
fn a_v38_labelled_blob_refuses_the_container_vtable_tag() {
    let mut m = Module::new("relabelled");
    m.add_type(Ty::FatPtr(FatPtrKind::ContainerVtable))
        .expect("Module::add_type: test fixture");

    let mut bytes = serialize_module(&m).expect("serialize_module: test fixture");
    assert!(
        deserialize_module(&bytes).is_ok(),
        "the v40 blob must decode"
    );
    bytes[8..12].copy_from_slice(&38u32.to_le_bytes());
    let err = deserialize_module(&bytes)
        .expect_err("a v38-labelled blob must not decode a v40 fat-pointer kind");
    assert!(
        format!("{err:?}").contains("InvalidTag"),
        "expected a tag refusal, got {err:?}"
    );
}
