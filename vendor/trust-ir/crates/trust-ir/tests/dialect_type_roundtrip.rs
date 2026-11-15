// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![cfg(all(
    feature = "binary",
    feature = "fmt",
    feature = "parser",
    feature = "serde"
))]

use trust_ir::binary::{self, ModuleBinaryBody, ModuleBinaryOptions, ProjectedModuleBinaryPlan};
use trust_ir::{
    Block, BlockId, DialectTy, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

fn nominal(namespace: &str, name: &str, version: u32) -> Ty {
    Ty::Dialect(Box::new(DialectTy::new(namespace, name, version)))
}

fn module(ty: Ty) -> Module {
    let mut module = Module::new("nominal_identity");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "identity", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), ty.clone());
    block.body.push(
        InstrNode::new(Inst::Copy {
            ty,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn projected(module: &Module, body: ModuleBinaryBody) -> Vec<u8> {
    ProjectedModuleBinaryPlan::try_new(
        module,
        ModuleBinaryOptions {
            body,
            ..Default::default()
        },
    )
    .unwrap()
    .to_vec()
    .expect("to_vec: test fixture")
}

#[test]
fn nominal_identity_roundtrips_all_formats_and_binds_all_module_identities() {
    let mut binaries = std::collections::BTreeSet::new();
    let mut canonicals = std::collections::BTreeSet::new();
    let mut digests = std::collections::BTreeSet::new();
    let mut executables = std::collections::BTreeSet::new();
    for ty in [
        nominal("example", "value", 1),
        nominal("other", "value", 1),
        nominal("example", "other", 1),
        nominal("example", "value", 2),
    ] {
        let module = module(ty);
        let bytes = binary::serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(&bytes[8..12], &39u32.to_le_bytes());
        let back = binary::deserialize_module(&bytes).unwrap();
        assert_eq!(
            binary::serialize_module(&back).expect("serialize_module: test fixture"),
            bytes
        );
        let text = trust_ir::format::canonical(&module);
        assert_eq!(
            trust_ir::format::canonical(&trust_ir::parser::parse_module(&text).unwrap()),
            text
        );
        let json = serde_json::to_vec(&module).unwrap();
        assert_eq!(
            serde_json::to_vec(&serde_json::from_slice::<Module>(&json).unwrap()).unwrap(),
            json
        );
        let msgpack = rmp_serde::to_vec(&module).unwrap();
        assert_eq!(
            rmp_serde::to_vec(&rmp_serde::from_slice::<Module>(&msgpack).unwrap()).unwrap(),
            msgpack
        );
        binaries.insert(bytes);
        canonicals.insert(projected(&module, ModuleBinaryBody::Canonical));
        digests.insert(format!("{:?}", module.stable_digest()));
        executables.insert(format!("{:?}", module.executable_content_digest_v1()));
    }
    assert_eq!(
        (
            binaries.len(),
            canonicals.len(),
            digests.len(),
            executables.len()
        ),
        (4, 4, 4, 4)
    );
}

#[test]
fn adaptive_writer_keeps_legacy_header_and_projection_bytes() {
    let module = module(Ty::I64);
    let bytes = binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(&bytes[8..12], &38u32.to_le_bytes());
    assert_eq!(bytes, projected(&module, ModuleBinaryBody::RawV38));
    assert_eq!(bytes, projected(&module, ModuleBinaryBody::Raw));
    assert_eq!(
        projected(&module, ModuleBinaryBody::CanonicalV38),
        projected(&module, ModuleBinaryBody::Canonical)
    );
    // Serde enum discriminants of existing types stay frozen as well.
    assert_eq!(
        rmp_serde::to_vec(&Ty::I64).unwrap(),
        vec![0xa3, b'I', b'6', b'4']
    );
}

#[test]
fn explicit_v38_and_downgraded_headers_reject_nominal_types() {
    let module = module(nominal("example", "value", 1));
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        assert!(matches!(
            ProjectedModuleBinaryPlan::try_new(
                &module,
                ModuleBinaryOptions {
                    body,
                    ..Default::default()
                }
            ),
            Err(binary::BinaryProjectionError::DialectTypeRequiresV39)
        ));
    }
    let mut bytes = binary::serialize_module(&module).expect("serialize_module: test fixture");
    bytes[8..12].copy_from_slice(&38u32.to_le_bytes());
    assert!(binary::deserialize_module(&bytes).is_err());
}

#[test]
fn malformed_names_and_zero_versions_are_rejected_by_text_and_binary_readers() {
    let module = module(nominal("example", "value", 1));
    let text = trust_ir::format::canonical(&module);
    for spelling in [
        "dialect<example, bad.name, 1>",
        "dialect<example, value, 0>",
        "dialect<, value, 1>",
        "dialect<é, value, 1>",
        "dialect<example, 値, 1>",
    ] {
        assert!(
            trust_ir::parser::parse_module(&text.replace("dialect<example, value, 1>", spelling))
                .is_err()
        );
    }
    let mut bytes = binary::serialize_module(&module).expect("serialize_module: test fixture");
    let position = bytes
        .windows(7)
        .position(|window| window == b"example")
        .unwrap();
    bytes[position] = b'.';
    assert!(binary::deserialize_module(&bytes).is_err());
    let mut bytes = binary::serialize_module(&module).expect("serialize_module: test fixture");
    // In this fixture the nominal namespace/name are pool entries1/2.
    // The exact tag37/namespace/name/version payload is independently framed.
    let position = bytes
        .windows(4)
        .position(|window| window == [37, 1, 2, 1])
        .unwrap();
    bytes[position + 3] = 0;
    assert!(binary::deserialize_module(&bytes).is_err());
}

#[test]
fn malformed_nominal_identity_can_be_hashed_before_structural_validation_without_panicking() {
    let module = module(nominal("", "value", 0));
    let bytes = binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert!(binary::deserialize_module(&bytes).is_err());
    let digest = module.stable_digest();
    let bundle = trust_ir::NativeVerificationBundle::new(
        trust_ir::NativeBundleProducer::TrustIr,
        trust_ir::NativeAdapterInput::TrustIrModule,
        digest,
        module,
        trust_ir::proof::ProofLineageManifest::new(),
    );
    // Transport validation is separate from structural validation. Its
    // response may be an error; malformed identity must never cause a panic
    // merely because admission hashes the untrusted module first.
    let _ = bundle.validate();
}

#[test]
fn canonical_projection_orders_nominal_parameter_strings_by_canonical_blocks() {
    let mut module = Module::new("block_type_order");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "f", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![],
    }));
    let mut first =
        Block::new(BlockId::new(1)).with_param(ValueId::new(17), nominal("first", "value", 1));
    first.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(2),
        args: vec![],
    }));
    let mut second =
        Block::new(BlockId::new(2)).with_param(ValueId::new(29), nominal("second", "value", 1));
    second
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks = vec![entry, first, second];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    let expected = projected(&module, ModuleBinaryBody::Canonical);
    module.functions[0].blocks.swap(1, 2);
    module.functions[0].blocks[1].params[0].0 = ValueId::new(333);
    module.functions[0].blocks[2].params[0].0 = ValueId::new(444);
    assert_eq!(expected, projected(&module, ModuleBinaryBody::Canonical));
    assert_eq!(
        expected,
        binary::serialize_module(&trust_ir::format::canonicalize(&module))
            .expect("serialize_module: test fixture")
    );
}
