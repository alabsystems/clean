// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment S (`docs/SPEC_RATIFICATIONS.md` §1 and §22): the FORMAT half of
// level-S templates — the `TRUST_IS` blob, the text form, JSON and
// MessagePack — and the refusals that keep a template from ever being read as
// a module (by magic, and by the `Ext` tags 39 / 17 under a forged magic).

#![cfg(all(feature = "binary", feature = "parser", feature = "serde"))]

use trust_ir::template::{
    HoleDef, HoleKind, HostKey, TEMPLATE_BODY_NAME, Template, TemplateArg, TemplateError,
    TemplateHeader, TemplateParam, TypeContract, hole_row_name,
};
use trust_ir::{
    BlockG, BlockId, ConstantG, FuncId, FuncTyG, FunctionG, GlobalG, HoleId, InstG, InstrNodeG,
    Linkage, ModuleG, ParamId, TemplateRef, Ty, TyG, ValueId,
};

type T = TemplateRef;

#[path = "../../trust-ir-conformance/tests/generate/signature_abi.rs"]
mod signature_abi_fixture;

#[test]
fn polymorphic_abi_placement_cannot_reuse_concrete_source_bindings() {
    let mut template = ident_param();
    assert!(template.structural_violations().is_empty());
    template.module.func_types[0].abi = Some(signature_abi_fixture::descriptor());
    assert!(template.structural_violations().iter().any(|error| {
        matches!(error, TemplateError::TemplateUnsupported { what } if what.contains("polymorphic signature 0"))
    }));
    assert!(template.digest().is_err());
    assert!(trust_ir::binary::serialize_template(&template).is_err());
}

#[test]
fn ground_template_descriptor_limits_fail_closed_before_writing() {
    let mut template = ident_param();
    let signature = signature_abi_fixture::signature()
        .try_map_level(&mut |ty| {
            ty.try_map_ext::<T, std::convert::Infallible>(&mut |ext| match *ext {})
        })
        .unwrap();
    template
        .module
        .add_func_type(signature)
        .expect("Module::add_func_type: test fixture");
    template.module.target_info = signature_abi_fixture::module()
        .expect("signature_abi::module: test fixture")
        .target_info;
    assert!(template.structural_violations().is_empty());
    let bytes = trust_ir::binary::serialize_template(&template).unwrap();
    assert_eq!(
        trust_ir::binary::deserialize_template(&bytes).unwrap(),
        template
    );

    let mut oversized_identity = template.clone();
    oversized_identity.module.func_types[1]
        .abi
        .as_mut()
        .unwrap()
        .frontend
        .revision = "r".repeat(trust_ir::signature_abi::MAX_ABI_TEXT_BYTES + 1);
    let mut excessive_nodes = template.clone();
    excessive_nodes.module.func_types[1]
        .abi
        .as_mut()
        .unwrap()
        .target
        .features = vec!["n".to_owned(); 70_000];
    let mut outcomes = Vec::new();
    for (name, mutant) in [
        ("identity bytes", oversized_identity),
        ("node count", excessive_nodes),
    ] {
        let result = std::panic::catch_unwind(|| trust_ir::binary::serialize_template(&mutant));
        outcomes.push((name, matches!(result, Ok(Err(_)))));
    }
    assert!(outcomes.iter().all(|(_, refused)| *refused), "{outcomes:?}");
}

/// D1a: a template the binary writer itself refuses — here the
/// producer-internal `Ty::Error`, which no structural rule names — is refused
/// by `serialize_template` (and so by `Template::digest`) as
/// `TemplateUnsupported`, never a panic: the writer's own arms run first over
/// the check sink, exactly as `Module::wire_image_refusal` runs them over a
/// module (`docs/SPEC_RATIFICATIONS.md`, "A construct or count with no wire
/// image is refused by the writer's own arm, at every trust-ir entry point").
/// Kind (i): before D1a the blob writer's `Ty::Error` arm panicked inside the
/// `Result`-returning entry. Mutation check: skipping the check walk turns
/// the `catch_unwind` assertion red.
#[test]
fn a_template_the_writer_refuses_is_refused_never_a_panic() {
    let mut template = ident_param();
    template.module.types.push(TyG::Error);
    assert!(
        template.structural_violations().is_empty(),
        "no structural rule names it: only the writer refuses it"
    );
    let serialized = std::panic::catch_unwind(|| trust_ir::binary::serialize_template(&template))
        .expect("a refusal, never a panic");
    assert!(
        matches!(
            &serialized,
            Err(TemplateError::TemplateUnsupported { what }) if what.contains("Ty::Error")
        ),
        "{serialized:?}"
    );
    let digest = std::panic::catch_unwind(|| template.digest()).expect("a refusal, never a panic");
    assert!(digest.is_err(), "{digest:?}");
    assert!(trust_ir::binary::serialize_template(&ident_param()).is_ok());
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn param(n: u32) -> TyG<T> {
    TyG::Ext(TemplateRef::Param(ParamId::new(n)))
}
fn hole(n: u32) -> TyG<T> {
    TyG::Ext(TemplateRef::Hole(HoleId::new(n)))
}
fn key(byte: u8) -> HostKey {
    HostKey::new("rust", vec![byte, 0xa5])
}
fn node(inst: InstG<T>) -> InstrNodeG<T> {
    InstrNodeG::new(inst)
}
fn result(inst: InstG<T>, value: u32) -> InstrNodeG<T> {
    InstrNodeG::new(inst).with_result(v(value))
}

fn body(module: &mut ModuleG<T>, params: Vec<TyG<T>>, returns: Vec<TyG<T>>) -> FunctionG<T> {
    let ty = module
        .add_func_type(FuncTyG {
            abi: None,
            params,
            returns,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    FunctionG::new(FuncId::new(0), TEMPLATE_BODY_NAME, ty, BlockId::new(0))
}

/// `fn identity<T>(x: T) -> T { x }`.
pub fn ident_param() -> Template {
    let mut module = ModuleG::new("core");
    let mut f = body(&mut module, vec![param(0)], vec![param(0)]);
    let mut entry = BlockG::new(BlockId::new(0)).with_param(v(0), param(0));
    entry.body.push(node(InstG::Return { values: vec![v(0)] }));
    f.blocks.push(entry);
    module.functions.push(f);
    Template {
        header: TemplateHeader {
            identity: "core::convert::identity".into(),
            params: vec![TemplateParam::Type],
            holes: vec![],
        },
        module,
    }
}

/// `fn len<T>(v: &Vec<T>) -> usize { v.len }`: a struct contract whose first
/// field names a LATER hole (review R6).
pub fn struct_contract_field_read() -> Template {
    let mut module = ModuleG::new("alloc");
    let mut f = body(&mut module, vec![TyG::Ptr], vec![TyG::Usize]);
    let mut entry = BlockG::new(BlockId::new(0)).with_param(v(0), TyG::Ptr);
    entry.body.push(result(
        InstG::Load {
            ty: hole(0),
            ptr: v(0),
            volatile: false,
            align: None,
        },
        1,
    ));
    entry.body.push(result(
        InstG::ExtractField {
            ty: TyG::Usize,
            aggregate: v(1),
            field: 1,
        },
        2,
    ));
    entry.body.push(node(InstG::Return { values: vec![v(2)] }));
    f.blocks.push(entry);
    module.functions.push(f);
    Template {
        header: TemplateHeader {
            identity: "alloc::vec::Vec::<T>::len".into(),
            params: vec![TemplateParam::Type],
            holes: vec![
                HoleDef {
                    kind: HoleKind::Type {
                        contract: TypeContract::Struct {
                            fields: vec![hole(1), TyG::Usize],
                        },
                    },
                    key: key(1),
                    args: vec![TemplateArg::Type(param(0))],
                },
                HoleDef {
                    kind: HoleKind::Type {
                        contract: TypeContract::Opaque,
                    },
                    key: key(2),
                    args: vec![TemplateArg::Type(param(0))],
                },
            ],
        },
        module,
    }
}

/// `fn dup<T: Clone>(x: &T) -> T { x.clone() }`: a callee hole.
pub fn callee_hole_trait_call() -> Template {
    let mut module = ModuleG::new("core");
    let mut f = body(&mut module, vec![TyG::Ptr], vec![param(0)]);
    let callee_ty = module
        .add_func_type(FuncTyG {
            abi: None,
            params: vec![TyG::Ptr],
            returns: vec![param(0)],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = BlockG::new(BlockId::new(0)).with_param(v(0), TyG::Ptr);
    entry.body.push(result(
        InstG::Call {
            callee: FuncId::new(1),
            args: vec![v(0)],
        },
        1,
    ));
    entry.body.push(node(InstG::Return { values: vec![v(1)] }));
    f.blocks.push(entry);
    module.functions.push(f);
    module.functions.push(FunctionG::new(
        FuncId::new(1),
        hole_row_name(HoleId::new(0)),
        callee_ty,
        BlockId::new(0),
    ));
    Template {
        header: TemplateHeader {
            identity: "core::clone::dup".into(),
            params: vec![TemplateParam::Type],
            holes: vec![HoleDef {
                kind: HoleKind::Callee {
                    decl: FuncId::new(1),
                },
                key: key(3),
                args: vec![TemplateArg::Type(param(0))],
            }],
        },
        module,
    }
}

/// Every remaining header form in one template: a host parameter, a const
/// parameter, an enum contract, a const hole, a global hole, and const and
/// host hole arguments.
pub fn every_header_form() -> Template {
    let mut module = ModuleG::new("core");
    // $0 host, $1 const usize, $2 type.
    let mut f = body(&mut module, vec![hole(1)], vec![TyG::Usize]);
    let mut entry = BlockG::new(BlockId::new(0)).with_param(v(0), hole(1));
    entry.body.push(result(
        InstG::Const {
            ty: TyG::Usize,
            value: ConstantG::Ext(TemplateRef::Param(ParamId::new(1))),
        },
        1,
    ));
    entry.body.push(result(
        InstG::Const {
            ty: TyG::Usize,
            value: ConstantG::Ext(TemplateRef::Hole(HoleId::new(2))),
        },
        2,
    ));
    entry.body.push(result(
        InstG::GlobalAddr {
            global: trust_ir::value::GlobalId::new(0),
        },
        3,
    ));
    entry.body.push(result(InstG::Undef { ty: hole(0) }, 4));
    entry.body.push(node(InstG::Return { values: vec![v(1)] }));
    f.blocks.push(entry);
    module.functions.push(f);
    module.globals.push(GlobalG {
        name: hole_row_name(HoleId::new(3)),
        ty: param(2),
        mutable: false,
        initializer: None,
        linkage: Linkage::default(),
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::default(),
        retained: false,
    });
    Template {
        header: TemplateHeader {
            identity: "core::every::<T, N, U>".into(),
            params: vec![
                TemplateParam::Host,
                TemplateParam::Const { ty: Ty::Usize },
                TemplateParam::Type,
            ],
            holes: vec![
                HoleDef {
                    kind: HoleKind::Type {
                        contract: TypeContract::Enum {
                            variants: vec![vec![], vec![param(2)]],
                            discriminants: vec![None, Some(7)],
                            repr: Some(trust_ir::EnumTagRepr::U8),
                        },
                    },
                    key: key(4),
                    args: vec![TemplateArg::Type(param(2))],
                },
                HoleDef {
                    kind: HoleKind::Type {
                        contract: TypeContract::Opaque,
                    },
                    key: key(5),
                    args: vec![TemplateArg::Host(ParamId::new(0))],
                },
                HoleDef {
                    kind: HoleKind::Const { ty: Ty::Usize },
                    key: key(6),
                    args: vec![TemplateArg::Const {
                        value: ConstantG::Ext(TemplateRef::Param(ParamId::new(1))),
                        ty: Ty::Usize,
                    }],
                },
                HoleDef {
                    kind: HoleKind::Global {
                        decl: trust_ir::value::GlobalId::new(0),
                    },
                    key: key(7),
                    args: vec![TemplateArg::Type(param(2))],
                },
            ],
        },
        module,
    }
}

fn corpus() -> Vec<(&'static str, Template)> {
    vec![
        ("ident_param", ident_param()),
        ("struct_contract_field_read", struct_contract_field_read()),
        ("callee_hole_trait_call", callee_hole_trait_call()),
        ("every_header_form", every_header_form()),
    ]
}

#[test]
fn every_sample_is_structurally_valid() {
    for (name, template) in corpus() {
        assert_eq!(
            template.structural_violations(),
            vec![],
            "{name} must satisfy T1–T5, T7–T9"
        );
    }
}

#[test]
fn template_round_trips_in_four_formats() {
    for (name, template) in corpus() {
        // Binary: a TRUST_IS blob at the template version floor, decoded to
        // the same template and re-encoded to the same bytes.
        let bytes = trust_ir::binary::serialize_template(&template).expect("encodes");
        assert_eq!(&bytes[..8], b"TRUST_IS", "{name}");
        assert_eq!(
            u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
            trust_ir::binary::TEMPLATE_FORMAT_VERSION,
            "{name}: a template blob is written at its version floor"
        );
        let back = trust_ir::binary::deserialize_template(&bytes).expect("decodes");
        assert_eq!(back, template, "{name}: binary round trip");
        assert_eq!(
            trust_ir::binary::serialize_template(&back).unwrap(),
            bytes,
            "{name}: the writer is deterministic"
        );
        // Text.
        let text = template.to_string();
        assert!(text.contains("template \""), "{name}: {text}");
        let parsed = trust_ir::parser::parse_template(&text)
            .unwrap_or_else(|e| panic!("{name}: text does not parse back: {e}\n{text}"));
        assert_eq!(parsed, template, "{name}: text round trip\n{text}");
        // JSON.
        let json = serde_json::to_string_pretty(&template).expect("json");
        let from_json: Template = serde_json::from_str(&json).expect("json back");
        assert_eq!(from_json, template, "{name}: JSON round trip");
        // MessagePack.
        let packed = rmp_serde::to_vec(&template).expect("msgpack");
        let from_packed: Template = rmp_serde::from_slice(&packed).expect("msgpack back");
        assert_eq!(from_packed, template, "{name}: MessagePack round trip");
    }
}

#[test]
fn module_reader_refuses_a_template_blob_by_magic() {
    let bytes = trust_ir::binary::serialize_template(&ident_param()).unwrap();
    assert!(matches!(
        trust_ir::binary::deserialize_module(&bytes),
        Err(trust_ir::binary::BinaryError::InvalidMagic)
    ));
}

#[test]
fn forged_ext_tag_under_module_magic_is_invalid_tag() {
    // A template's `Ext` spelling under the MODULE magic: a module blob whose
    // one type row's tag byte is replaced by 39 (`Ty::Ext`) or whose one
    // constant's tag byte is replaced by 17 (`Constant::Ext`), each followed by
    // a well-formed `TemplateRef`. The level-R reader refuses both tags at
    // every version: `NoExt` has no value to read.
    let tag_position = |a: &[u8], b: &[u8]| {
        a.iter()
            .zip(b)
            .position(|(x, y)| x != y)
            .expect("the samples differ at their tag byte")
    };
    let type_row = |ty: Ty| {
        let mut module = trust_ir::Module::new("forged");
        module.types.push(ty);
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture")
    };
    let (unit, boolean) = (type_row(Ty::Unit), type_row(Ty::Bool));
    let at = tag_position(&unit, &boolean);
    let mut forged = unit.clone();
    forged.splice(at..=at, [39u8, 0, 0]);
    assert_eq!(
        trust_ir::binary::deserialize_module(&forged),
        Err(trust_ir::binary::BinaryError::InvalidTag(39))
    );

    let global = |value: trust_ir::Constant| {
        let mut module = trust_ir::Module::new("forged");
        module.globals.push(trust_ir::Global {
            name: "g".into(),
            ty: Ty::I64,
            mutable: false,
            initializer: Some(value),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::default(),
            retained: false,
        });
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture")
    };
    let (zero, yes) = (
        global(trust_ir::Constant::Int(0)),
        global(trust_ir::Constant::Bool(true)),
    );
    let at = tag_position(&zero, &yes);
    let mut forged = zero.clone();
    forged.splice(at..at + 2, [17u8, 1, 0]);
    assert_eq!(
        trust_ir::binary::deserialize_module(&forged),
        Err(trust_ir::binary::BinaryError::InvalidTag(17))
    );
}

#[test]
fn template_reader_refuses_a_module_blob() {
    let bytes = trust_ir::binary::serialize_module(&trust_ir::Module::new("m"))
        .expect("serialize_module: test fixture");
    assert_eq!(
        trust_ir::binary::deserialize_template(&bytes),
        Err(TemplateError::NotATemplate)
    );
}

#[test]
fn template_below_its_version_is_refused() {
    let mut bytes = trust_ir::binary::serialize_template(&ident_param()).unwrap();
    let below = trust_ir::binary::TEMPLATE_FORMAT_VERSION - 1;
    bytes[8..12].copy_from_slice(&below.to_le_bytes());
    assert!(matches!(
        trust_ir::binary::deserialize_template(&bytes),
        Err(TemplateError::Binary(why)) if why.contains("UnsupportedVersion")
    ));
}

#[test]
fn template_trailing_bytes_are_refused() {
    let mut bytes = trust_ir::binary::serialize_template(&ident_param()).unwrap();
    bytes.push(0);
    assert!(matches!(
        trust_ir::binary::deserialize_template(&bytes),
        Err(TemplateError::Binary(why)) if why.contains("trailing bytes")
    ));
}

#[test]
fn template_writer_refuses_a_structurally_invalid_template() {
    let mut template = ident_param();
    template.header.identity = String::new();
    assert_eq!(
        trust_ir::binary::serialize_template(&template),
        Err(TemplateError::InvalidIdentity)
    );
    assert_eq!(template.digest(), Err(TemplateError::InvalidIdentity));
}

#[test]
fn level_r_parser_refuses_the_template_keyword() {
    let text = ident_param().to_string();
    let error = trust_ir::parser::parse_module(&text).expect_err("a template is not a module");
    assert!(error.message.contains("template"), "{error}");
}

#[test]
fn template_digest_is_its_blob_under_its_domain() {
    let template = ident_param();
    let bytes = trust_ir::binary::serialize_template(&template).unwrap();
    assert_eq!(
        template.digest().unwrap(),
        trust_ir::proof::ProofDigest::sha256_domain("trust_ir.template.v1", &bytes)
    );
    assert_ne!(
        template.digest().unwrap(),
        struct_contract_field_read().digest().unwrap()
    );
}
