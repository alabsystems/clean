// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Independent images and selector/declaration boundaries.
use super::*;
use crate::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumVariant};
use crate::value::EnumId;

fn fixture(active: usize) -> Module {
    let mut module = Module::new("nominal_single_inhabited");
    module.add_enum(EnumDef::new(
        EnumId::new(0),
        "core::convert::Infallible",
        vec![],
    ));
    let payload = EnumVariant {
        name: "Value".into(),
        fields: vec![Ty::U32],
        field_names: vec!["value".into()],
    };
    let absent = EnumVariant {
        name: "Impossible".into(),
        fields: vec![Ty::Enum(EnumId::new(0))],
        field_names: vec!["nominal_void".into()],
    };
    let variants = if active == 0 {
        vec![payload, absent]
    } else {
        vec![absent, payload]
    };
    let mut definition = EnumDef::new(EnumId::new(1), "Result", variants);
    definition.discriminants = vec![Some(7), Some(23)];
    definition.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::SingleInhabited {
            variant: active as u32,
        },
        size: 4,
        align: 4,
        variant_field_offsets: if active == 0 {
            vec![vec![0], vec![]]
        } else {
            vec![vec![], vec![0]]
        },
    });
    module.add_enum(definition);
    module
}

fn state() -> ExecState {
    ExecState {
        values: BTreeMap::new(),
        memory: MemoryState::default(),
        globals: BTreeMap::new(),
        frames: BTreeSet::new(),
        next_frame_id: 0,
        steps: 0,
        remaining_fuel: u64::MAX,
        host: HostState::new(),
        host_calls: 0,
        drop_glue: None,
        unwind: UnwindState::default(),
    }
}

#[test]
fn single_inhabited_payload_images_recover_actual_effective_discriminant() {
    for active in [0, 1] {
        let module = fixture(active);
        let ty = Ty::Enum(EnumId::new(1));
        let layout = module.enum_layout_shape(EnumId::new(1)).unwrap();
        assert_eq!((layout.size_bits, layout.align_bits), (32, 32));
        let interpreter = Interpreter::with_module(&module);
        for payload in [0, 1, 0x1234_5678, u32::MAX] {
            let value = InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Aggregate(vec![
                    InterpretValue::int(Ty::U8, if active == 0 { 7 } else { 23 }).unwrap(),
                    InterpretValue::int(Ty::U32, i128::from(payload)).unwrap(),
                ]),
            };
            let memory = state();
            let image = interpreter
                .encode_value(&value, &memory, BlockId::new(0))
                .unwrap();
            assert_eq!(image.as_slice(), &payload.to_le_bytes());
            assert_eq!(
                interpreter
                    .decode_value(&ty, &image, &memory, BlockId::new(0))
                    .unwrap(),
                value
            );
        }
        assert!(module.ty_layout_shape(&Ty::Enum(EnumId::new(0))).is_err());
        assert!(
            interpreter
                .decode_value(&Ty::Enum(EnumId::new(0)), &[], &state(), BlockId::new(0))
                .is_err()
        );
    }
}

#[test]
fn invalid_single_inhabited_metadata_cannot_form_an_image() {
    for case in 0..6 {
        let mut module = fixture(1);
        match case {
            0 => {
                module.enums[1].layout.as_mut().unwrap().encoding =
                    EnumTagEncoding::SingleInhabited { variant: 2 }
            }
            1 => {
                module.enums[1].layout.as_mut().unwrap().encoding =
                    EnumTagEncoding::SingleInhabited { variant: 0 }
            }
            2 => module.enums[0].variants.push(EnumVariant {
                name: "ActuallyInhabited".into(),
                fields: vec![],
                field_names: vec![],
            }),
            3 => module.enums[1]
                .layout
                .as_mut()
                .unwrap()
                .variant_field_offsets[0]
                .push(0),
            4 => module.enums[1].variants[0].fields = vec![Ty::Enum(EnumId::new(999))],
            _ => module.enums[1].layout.as_mut().unwrap().encoding = EnumTagEncoding::Untagged,
        }
        assert!(
            module.enum_layout_shape(EnumId::new(1)).is_err(),
            "case {case}"
        );
        assert!(
            Interpreter::with_module(&module)
                .enum_layout(&Ty::Enum(EnumId::new(1)), BlockId::new(0))
                .is_err(),
            "case {case}"
        );
    }
}

#[test]
fn an_inactive_variant_value_is_refused_without_prior_module_validation() {
    let module = fixture(1);
    let value = InterpretValue {
        ty: Ty::Enum(EnumId::new(1)),
        kind: InterpretValueKind::Aggregate(vec![InterpretValue::int(Ty::U8, 7).unwrap()]),
    };
    let error = Interpreter::with_module(&module)
        .encode_value(&value, &state(), BlockId::new(0))
        .unwrap_err();
    assert!(format!("{error:?}").contains("uninhabited"));
}

#[test]
fn new_wire_images_bind_selector_and_do_not_promote_old_headers() {
    let module = fixture(1);
    // Empty declarations independently require the new version, even with no
    // SingleInhabited descriptor elsewhere to raise it accidentally.
    let mut declaration_only = Module::new("nominal_empty_declaration");
    declaration_only.add_enum(module.enums[0].clone());
    let mut empty_bytes = crate::binary::serialize_module(&declaration_only).unwrap();
    assert_eq!(
        u32::from_le_bytes(empty_bytes[8..12].try_into().unwrap()),
        65
    );
    assert_eq!(
        crate::binary::deserialize_module(&empty_bytes).unwrap(),
        declaration_only
    );
    empty_bytes[8..12].copy_from_slice(&64u32.to_le_bytes());
    assert!(
        matches!(crate::binary::deserialize_module(&empty_bytes), Err(crate::binary::BinaryError::InvalidData(message)) if message.contains("empty nominal enum"))
    );
    let bytes = crate::binary::serialize_module(&module).unwrap();
    assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 65);
    assert_eq!(crate::binary::deserialize_module(&bytes).unwrap(), module);
    let mut old_header = bytes.clone();
    old_header[8..12].copy_from_slice(&64u32.to_le_bytes());
    assert!(
        matches!(crate::binary::deserialize_module(&old_header), Err(crate::binary::BinaryError::InvalidData(message)) if message.contains("empty nominal enum"))
    );
    let mut no_empty = Module::new("direct_never_inactive");
    let mut definition = module.enums[1].clone();
    definition.variants[0].fields = vec![Ty::Never];
    no_empty.add_enum(definition);
    let mut bytes = crate::binary::serialize_module(&no_empty).unwrap();
    bytes[8..12].copy_from_slice(&64u32.to_le_bytes());
    assert!(matches!(
        crate::binary::deserialize_module(&bytes),
        Err(crate::binary::BinaryError::InvalidTag(3))
    ));
    let mut changed = module.clone();
    changed.enums[1].layout.as_mut().unwrap().encoding =
        EnumTagEncoding::SingleInhabited { variant: 0 };
    assert_ne!(
        module.executable_content_digest_v1(),
        changed.executable_content_digest_v1()
    );
    #[cfg(feature = "diff")]
    {
        // Diff fingerprints nominal definitions at their uses; deliberately
        // unreferenced declarations are not module-metadata changes.
        let mut referenced = module.clone();
        let signature = referenced
            .add_func_type(crate::FuncTy::unrecorded(
                vec![Ty::Enum(EnumId::new(1))],
                vec![],
                false,
            ))
            .unwrap();
        referenced.functions.push(crate::Function::new(
            FuncId::new(0),
            "uses_selected_enum",
            signature,
            BlockId::new(0),
        ));
        let mut changed = referenced.clone();
        changed.enums[1].layout.as_mut().unwrap().encoding =
            EnumTagEncoding::SingleInhabited { variant: 0 };
        assert!(!crate::diff::diff(&referenced, &changed).is_empty());
    }
}

#[cfg(all(feature = "parser", feature = "fmt", feature = "serde"))]
#[test]
fn new_encoding_and_empty_nominal_declarations_roundtrip_text_and_json() {
    let module = fixture(1);
    let text = crate::format::canonical(&module);
    assert!(text.contains("single inhabited=1"));
    assert_eq!(crate::parser::parse_module(&text).unwrap(), module);
    let json = serde_json::to_vec(&module).unwrap();
    assert_eq!(serde_json::from_slice::<Module>(&json).unwrap(), module);
}
