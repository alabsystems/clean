// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(feature = "binary")]

use trust_ir::binary::{BinaryError, FORMAT_VERSION, deserialize_module, serialize_module};
use trust_ir::{DialectTy, FuncTy, Module, Ty};

fn empty_module_at_version(version: u32) -> (Module, Vec<u8>) {
    let module = Module::new("exact-input");
    let mut bytes = serialize_module(&module).expect("serialize_module: test fixture");
    bytes[8..12].copy_from_slice(&version.to_le_bytes());
    // Empty records need no other version-specific representation changes in
    // the supported range. v30 added the two final empty typed-value tables.
    if version < 30 {
        assert_eq!(&bytes[bytes.len() - 2..], &[0, 0]);
        bytes.truncate(bytes.len() - 2);
    }
    // An empty module is written at v38. v41 appended two more trailing tables
    // (`global_asm`, then `imports`), each an empty count on an empty module.
    if version >= trust_ir::binary::CONTRACT_SURFACE_FORMAT_VERSION {
        bytes.extend_from_slice(&[0, 0]);
    }
    // v42 appends the declared tuple-layout table after imports. v43 adds NO
    // section — a handle is a row of the type table — so a v43 empty module
    // is byte-identical to a v42 one save for the header word.
    if version >= trust_ir::binary::TUPLE_LAYOUT_FORMAT_VERSION {
        bytes.push(0);
    }
    // v55 appends the drop-glue table after the tuple layouts (amendment D):
    // one more empty count.
    if version >= trust_ir::binary::DROP_GLUE_FORMAT_VERSION {
        bytes.push(0);
    }
    // v44 adds NO section either (the identity scheme is a per-row tag of the
    // imports table). v58 appends the declared closure-layout table after the
    // drop-glue table: one more empty count. The per-definition origin byte
    // costs nothing on a module with no definitions.
    if version >= trust_ir::binary::NOMINAL_IDENTITY_FORMAT_VERSION {
        bytes.push(0);
    }
    // v70 appends the weight-blob table after the closure layouts: one more
    // empty count.
    if version >= trust_ir::binary::TENSOR_BLOB_FORMAT_VERSION {
        bytes.push(0);
    }
    (module, bytes)
}

fn assert_trailing_input_rejected(bytes: &[u8]) {
    assert!(
        matches!(
            deserialize_module(bytes),
            Err(BinaryError::InvalidData(message)) if message.contains("trailing bytes")
        ),
        "an exact module decoder must reject unconsumed input"
    );
}

#[test]
fn supported_empty_module_versions_still_decode_exactly() {
    for version in (23..=FORMAT_VERSION).filter(|version| !(26..=28).contains(version)) {
        let (module, bytes) = empty_module_at_version(version);
        assert_eq!(deserialize_module(&bytes).unwrap(), module, "v{version}");
    }
}

#[test]
fn exact_module_decoder_rejects_trailers_and_concatenated_modules() {
    for version in (23..=FORMAT_VERSION).filter(|version| !(26..=28).contains(version)) {
        let (_, bytes) = empty_module_at_version(version);
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert_trailing_input_rejected(&trailing);
        let mut concatenated = bytes.clone();
        concatenated.extend_from_slice(&bytes);
        assert_trailing_input_rejected(&concatenated);
    }
}

#[test]
fn nominal_dialect_v39_roundtrip_requires_exact_input() {
    let mut module = Module::new("dialect-input");
    module
        .types
        .push(Ty::Dialect(Box::new(DialectTy::new("example", "token", 1))));
    let mut bytes = serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 39);
    assert_eq!(deserialize_module(&bytes).unwrap(), module);
    bytes.push(0);
    assert_trailing_input_rejected(&bytes);
}

#[test]
fn v43_handle_modules_reject_trailing_input() {
    let mut module = Module::new("handle-input");
    module.types.push(Ty::handle("Nat", "trust_bignum::Nat"));
    let mut bytes = serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 43);
    assert_eq!(deserialize_module(&bytes).unwrap(), module);
    bytes.push(0);
    assert_trailing_input_rejected(&bytes);
}

#[test]
fn foreign_v39_parameter_modes_cannot_be_erased_to_strict() {
    let mut module = Module::new("foreign-parammode");
    module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for mode in [1, 2] {
        let mut bytes = serialize_module(&module).expect("serialize_module: test fixture");
        bytes[8..12].copy_from_slice(&39u32.to_le_bytes());
        // Divergent parammode lineage at 991f5a4: after the v38 body, v39
        // appends a varint row count, FuncTyId, varint mode count, then the
        // modes (1 = Lazy, 2 = ByRef). The nominal-dialect v39 reader must not
        // silently discard this row and manufacture an all-Strict signature.
        bytes.extend_from_slice(&[1, 0, 1, mode]);
        assert_trailing_input_rejected(&bytes);
    }
}
