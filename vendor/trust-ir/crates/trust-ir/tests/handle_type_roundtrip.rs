// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// v43 nominal opaque runtime handles: wire, text, serde and identity
// behaviour of `Ty::Handle`. The validator's origin/transport rules live in
// trust-ir-build (tests/handle_types.rs); this file pins the FORMAT half.

#![cfg(all(
    feature = "binary",
    feature = "diff",
    feature = "fmt",
    feature = "parser",
    feature = "serde"
))]

use trust_ir::binary::{
    self, BinaryError, HANDLE_TYPE_FORMAT_VERSION, ModuleBinaryBody, ModuleBinaryOptions,
    ProjectedModuleBinaryPlan,
};
use trust_ir::shape::TyShape;
use trust_ir::{
    Block, BlockId, CallingConv, Constant, Endianness, FuncId, FuncTy, Function, HandleTy,
    HandleTyError, Inst, InstrNode, Module, StructPassingPolicy, TargetInfo, Ty, ValueId,
};

fn nat() -> Ty {
    Ty::handle("Nat", "trust_bignum::Nat")
}

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn b(index: u32) -> BlockId {
    BlockId::new(index)
}

/// The pinned `trust_bignum::Nat` declarations plus a `pred(H) -> H`
/// transport body: `if is_zero(x) { x } else { sub(x, from_u64(1)) }`.
fn nat_module() -> Module {
    let h = nat();
    let mut module = Module::new("nat_pred");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let from_u64 = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![h.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let binop = module
        .add_func_type(FuncTy {
            params: vec![h.clone(), h.clone()],
            returns: vec![h.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let is_zero = module
        .add_func_type(FuncTy {
            params: vec![h.clone()],
            returns: vec![Ty::Bool],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let unop = module
        .add_func_type(FuncTy {
            params: vec![h.clone()],
            returns: vec![h.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for (id, symbol, ty, path) in [
        (
            0,
            "trust_bignum_nat_from_u64",
            from_u64,
            "trust_bignum::Nat::from_u64",
        ),
        (1, "trust_bignum_nat_add", binop, "trust_bignum::Nat::add"),
        (2, "trust_bignum_nat_sub", binop, "trust_bignum::Nat::sub"),
        (
            3,
            "trust_bignum_nat_is_zero",
            is_zero,
            "trust_bignum::Nat::is_zero",
        ),
    ] {
        let mut decl = Function::new(FuncId::new(id), symbol, ty, b(0));
        decl.calling_conv = CallingConv::C;
        decl.display_path = Some(path.into());
        module
            .try_add_function(decl)
            .expect("Module::try_add_function: test fixture");
    }
    let mut pred = Function::new(FuncId::new(4), "pred", unop, b(0));
    let mut entry = Block::new(b(0)).with_param(v(0), h.clone());
    entry.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(3),
            args: vec![v(0)],
        })
        .with_result(v(1)),
    );
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond: v(1),
        then_target: b(1),
        then_args: vec![],
        else_target: b(2),
        else_args: vec![],
    }));
    let mut zero = Block::new(b(1));
    zero.body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    let mut step = Block::new(b(2));
    step.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(1),
        })
        .with_result(v(2)),
    );
    step.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![v(2)],
        })
        .with_result(v(3)),
    );
    step.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(2),
            args: vec![v(0), v(3)],
        })
        .with_result(v(4)),
    );
    step.body
        .push(InstrNode::new(Inst::Return { values: vec![v(4)] }));
    pred.blocks = vec![entry, zero, step];
    module
        .try_add_function(pred)
        .expect("Module::try_add_function: test fixture");
    module
}

fn identity_module(ty: Ty) -> Module {
    let mut module = Module::new("identity");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "identity", signature, b(0));
    let mut block = Block::new(b(0)).with_param(v(0), ty.clone());
    block
        .body
        .push(InstrNode::new(Inst::Copy { ty, operand: v(0) }).with_result(v(1)));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
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

fn header_version(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[8..12].try_into().unwrap())
}

#[test]
fn handle_module_roundtrips_byte_exactly_through_all_four_formats_at_v43() {
    let module = nat_module();

    let bytes = binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), HANDLE_TYPE_FORMAT_VERSION);
    assert_eq!(header_version(&bytes), 43);
    let back = binary::deserialize_module(&bytes).unwrap();
    assert_eq!(back, module);
    assert_eq!(
        binary::serialize_module(&back).expect("serialize_module: test fixture"),
        bytes
    );
    // The adaptive projections agree with the plain writer.
    assert_eq!(projected(&module, ModuleBinaryBody::Raw), bytes);
    let canonical = projected(&module, ModuleBinaryBody::Canonical);
    assert_eq!(
        binary::serialize_module(&binary::deserialize_module(&canonical).unwrap())
            .expect("serialize_module: test fixture"),
        canonical
    );

    let text = trust_ir::format::canonical(&module);
    assert!(
        text.contains("handle<\"Nat\", \"trust_bignum::Nat\">"),
        "{text}"
    );
    let parsed = trust_ir::parser::parse_module(&text).unwrap();
    assert_eq!(trust_ir::format::canonical(&parsed), text);
    assert_eq!(parsed.func_types, module.func_types);

    let json = serde_json::to_vec(&module).unwrap();
    let from_json: Module = serde_json::from_slice(&json).unwrap();
    assert_eq!(from_json, module);
    assert_eq!(serde_json::to_vec(&from_json).unwrap(), json);

    let msgpack = rmp_serde::to_vec(&module).unwrap();
    let from_msgpack: Module = rmp_serde::from_slice(&msgpack).unwrap();
    assert_eq!(from_msgpack, module);
    assert_eq!(rmp_serde::to_vec(&from_msgpack).unwrap(), msgpack);
}

#[test]
fn explicit_v38_projections_refuse_handles_and_handle_free_modules_keep_v38_bytes() {
    let module = nat_module();
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        assert!(matches!(
            ProjectedModuleBinaryPlan::try_new(
                &module,
                ModuleBinaryOptions {
                    body,
                    ..Default::default()
                }
            ),
            Err(binary::BinaryProjectionError::HandleTypeRequiresV43)
        ));
    }

    let legacy = identity_module(Ty::I64);
    let bytes = binary::serialize_module(&legacy).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), 38);
    assert_eq!(bytes, projected(&legacy, ModuleBinaryBody::RawV38));
    assert_eq!(bytes, projected(&legacy, ModuleBinaryBody::Raw));
    assert_eq!(
        projected(&legacy, ModuleBinaryBody::CanonicalV38),
        projected(&legacy, ModuleBinaryBody::Canonical)
    );
}

#[test]
fn a_pre_v43_header_carrying_type_tag_38_is_refused_at_the_tag() {
    let module = identity_module(nat());
    let bytes = binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), 43);
    for older in [42_u32, 41, 40, 39, 38] {
        let mut forged = bytes.clone();
        forged[8..12].copy_from_slice(&older.to_le_bytes());
        assert_eq!(
            binary::deserialize_module(&forged),
            Err(BinaryError::InvalidTag(38)),
            "v{older}"
        );
    }
}

#[test]
fn malformed_handle_identities_are_refused_by_every_reader() {
    for (name, runtime, expected) in [
        ("", "trust_bignum::Nat", HandleTyError::InvalidName),
        ("Nat", "trust_bignum::", HandleTyError::InvalidRuntime),
        ("Nat", "-", HandleTyError::InvalidRuntime),
        ("Nat", "", HandleTyError::InvalidRuntime),
        ("Nat", "::Nat", HandleTyError::InvalidRuntime),
        ("Na.t", "trust_bignum::Nat", HandleTyError::InvalidName),
    ] {
        let identity = HandleTy::new(name, runtime);
        assert_eq!(identity.validate(), Err(expected), "{name:?} {runtime:?}");
        // The writer encodes the claim exactly; the reader refuses it.
        let module = identity_module(Ty::Handle(Box::new(identity)));
        let bytes = binary::serialize_module(&module).expect("serialize_module: test fixture");
        assert!(
            matches!(
                binary::deserialize_module(&bytes),
                Err(BinaryError::InvalidData(_))
            ),
            "{name:?} {runtime:?}"
        );
        // Hashing a malformed identity must not panic (admission hashes
        // untrusted modules before structural validation).
        let _ = module.stable_digest();
        // The text reader refuses the same spellings.
        let text = trust_ir::format::canonical(&identity_module(nat()));
        let spelling = format!("handle<{name:?}, {runtime:?}>");
        assert!(
            trust_ir::parser::parse_module(
                &text.replace("handle<\"Nat\", \"trust_bignum::Nat\">", &spelling)
            )
            .is_err(),
            "{spelling}"
        );
    }
    assert_eq!(HandleTy::new("Nat", "trust_bignum::Nat").validate(), Ok(()));
    assert_eq!(HandleTy::new("Nat", "Nat").validate(), Ok(()));
    assert_eq!(HandleTy::new("N_1", "a::b::c").validate(), Ok(()));
}

#[test]
fn handle_is_one_pointer_word_but_never_pointer_like_and_never_ptr() {
    let handle = nat();
    assert_ne!(handle, Ty::Ptr);
    assert_ne!(handle, Ty::handle("Int", "trust_bignum::Nat"));
    assert_ne!(handle, Ty::handle("Nat", "other::Nat"));
    assert_eq!(handle.bit_width(), None);
    assert_eq!(handle.bit_width_with(64), Some(64));
    assert_eq!(handle.bit_width_with(32), Some(32));
    assert!(handle.is_handle());
    assert_eq!(
        handle.handle_ty(),
        Some(&HandleTy::new("Nat", "trust_bignum::Nat"))
    );
    assert!(!handle.is_pointer_like());
    assert!(!handle.is_thin_pointer_like());
    assert!(!handle.is_reference());
    assert!(!handle.is_aggregate());
    assert!(!handle.is_numeric());
    assert!(handle.pointer_layout_shape(64).is_none());
    assert!(handle.pointer_metadata_ty(64).is_none());
    assert_eq!(handle.shape(), TyShape::Handle);
    assert_eq!(TyShape::Handle.to_string(), "handle");
    assert_eq!(handle.to_string(), "handle<\"Nat\", \"trust_bignum::Nat\">");
    assert!(handle.contains_handle());
    assert!(!handle.contains_dialect());
    assert!(!Ty::Ptr.contains_handle());

    // Layout: a pointer-sized SCALAR on the module's target, never a pointer.
    let module = nat_module();
    let layout = module.ty_layout_shape(&handle).unwrap();
    assert_eq!(layout.size_bits, 64);
    assert_eq!(layout.align_bits, Some(64));
    assert!(matches!(
        layout.kind,
        trust_ir::shape::TyLayoutKind::Scalar(TyShape::Handle)
    ));
    let ptr = module.ty_layout_shape(&Ty::Ptr).unwrap();
    assert_eq!((ptr.size_bits, ptr.align_bits), (64, Some(64)));
    assert_ne!(format!("{:?}", ptr.kind), format!("{:?}", layout.kind));
}

#[test]
fn serde_spellings_are_the_exact_pair_and_earlier_discriminants_are_frozen() {
    let handle = nat();
    assert_eq!(
        serde_json::to_string(&handle).unwrap(),
        r#"{"Handle":{"name":"Nat","runtime":"trust_bignum::Nat"}}"#
    );
    let msgpack = rmp_serde::to_vec(&handle).unwrap();
    // Externally tagged newtype over a positional two-field struct: a
    // one-entry map whose value is a two-element array, no field names.
    assert_eq!(
        msgpack,
        [
            &[0x81, 0xa6][..],
            b"Handle",
            &[0x92, 0xa3],
            b"Nat",
            &[0xb1],
            b"trust_bignum::Nat"
        ]
        .concat()
    );
    assert_eq!(rmp_serde::from_slice::<Ty>(&msgpack).unwrap(), handle);
    assert_eq!(
        rmp_serde::to_vec(&Ty::I64).unwrap(),
        vec![0xa3, b'I', b'6', b'4']
    );
    assert_eq!(
        rmp_serde::to_vec(&Ty::Dialect(Box::new(trust_ir::DialectTy::new(
            "example", "value", 1
        ))))
        .unwrap()[..9],
        [0x81, 0xa7, b'D', b'i', b'a', b'l', b'e', b'c', b't']
    );
}

#[test]
fn handle_identity_binds_every_module_digest_and_distinct_runtimes_never_collide() {
    let mut binaries = std::collections::BTreeSet::new();
    let mut digests = std::collections::BTreeSet::new();
    let mut executables = std::collections::BTreeSet::new();
    for ty in [
        nat(),
        Ty::handle("Int", "trust_bignum::Nat"),
        Ty::handle("Nat", "other::Nat"),
        Ty::Ptr,
    ] {
        let module = identity_module(ty);
        binaries.insert(binary::serialize_module(&module).expect("serialize_module: test fixture"));
        digests.insert(format!("{:?}", module.stable_digest()));
        executables.insert(format!("{:?}", module.executable_content_digest_v1()));
    }
    assert_eq!(
        (binaries.len(), digests.len(), executables.len()),
        (4, 4, 4)
    );
}

#[test]
fn semantic_diff_distinguishes_handles_by_pair_and_from_ptr() {
    let a = identity_module(nat());
    let b = identity_module(Ty::handle("Nat", "other::Nat"));
    let c = identity_module(Ty::Ptr);
    assert!(trust_ir::diff::diff(&a, &a.clone()).is_empty());
    assert!(!trust_ir::diff::diff(&a, &b).is_empty());
    assert!(!trust_ir::diff::diff(&a, &c).is_empty());
}
