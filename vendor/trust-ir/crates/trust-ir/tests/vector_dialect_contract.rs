// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![cfg(all(feature = "parser", feature = "binary"))]

use trust_ir::dialect::DialectRegistry;
use trust_ir::dialect::vector::{self, VectorDialect, VectorSpec};
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, FuncTy, Function, Module, Ty};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn b(index: u32) -> BlockId {
    BlockId::new(index)
}

fn vector_dialect_module() -> Module {
    let v4i32 = Ty::v4_i32();
    let v2i64 = Ty::v2_i64();
    let v4bool = Ty::v4_bool();
    let v2bool = Ty::v2_bool();
    let v8bool = Ty::v8_bool();
    let v16bool = Ty::v16_bool();
    let mut module = Module::new("vector_dialect_lane_contract");

    let ft = module.add_func_type(FuncTy {
        params: vec![
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I64,
            Ty::I64,
            v4i32.clone(),
            v2i64.clone(),
            v4bool.clone(),
            v2bool.clone(),
            v8bool.clone(),
            v16bool.clone(),
        ],
        returns: vec![
            v4i32.clone(),
            v2i64.clone(),
            Ty::I32,
            Ty::I64,
            v4i32.clone(),
            v2i64.clone(),
            Ty::I32,
            Ty::I64,
            v4i32.clone(),
            v2i64.clone(),
            Ty::I32,
            Ty::I32,
        ],
        is_vararg: false,
    });

    let mut func = Function::new(FuncId::new(0), "vector_lane_contract", ft, b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32));
    block.params.push((v(1), Ty::I32));
    block.params.push((v(2), Ty::I32));
    block.params.push((v(3), Ty::I32));
    block.params.push((v(4), Ty::I64));
    block.params.push((v(5), Ty::I64));
    block.params.push((v(6), v4i32.clone()));
    block.params.push((v(7), v2i64.clone()));
    block.params.push((v(8), v4bool));
    block.params.push((v(9), v2bool));
    block.params.push((v(20), v8bool));
    block.params.push((v(21), v16bool));

    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::pack_lanes(
            v4i32.clone(),
            [v(0), v(1), v(2), v(3)],
        ))))
        .with_result(v(10)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::pack_lanes(
            v2i64.clone(),
            [v(4), v(5)],
        ))))
        .with_result(v(11)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::extract_lane(
            v4i32.clone(),
            v(6),
            2,
        ))))
        .with_result(v(12)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::extract_lane(
            v2i64.clone(),
            v(7),
            1,
        ))))
        .with_result(v(13)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::insert_lane(
            v4i32,
            v(6),
            0,
            v(0),
        ))))
        .with_result(v(14)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::insert_lane(
            v2i64,
            v(7),
            0,
            v(4),
        ))))
        .with_result(v(15)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::mask_to_bits(
            Ty::v4_bool(),
            v(8),
            Ty::I32,
        ))))
        .with_result(v(16)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::mask_to_bits(
            Ty::v2_bool(),
            v(9),
            Ty::I64,
        ))))
        .with_result(v(17)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(
            vector::v4_i32_splat_lane(v(0)).expect("v4 i32 splat helper is canonical"),
        )))
        .with_result(v(18)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(
            vector::v2_i64_splat_lane(v(4)).expect("v2 i64 splat helper is canonical"),
        )))
        .with_result(v(19)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::mask_to_bits(
            Ty::v8_bool(),
            v(20),
            Ty::I32,
        ))))
        .with_result(v(22)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::mask_to_bits(
            Ty::v16_bool(),
            v(21),
            Ty::I32,
        ))))
        .with_result(v(23)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![
            v(10),
            v(11),
            v(12),
            v(13),
            v(14),
            v(15),
            v(16),
            v(17),
            v(18),
            v(19),
            v(22),
            v(23),
        ],
    }));

    func.blocks.push(block);
    module.add_function(func);
    module
}

fn vector_registry() -> DialectRegistry {
    let mut registry = DialectRegistry::new();
    registry.register(Box::new(VectorDialect));
    registry
}

/// Build the on-wire encoding of a pooled string in the v4 binary format:
/// an unsigned LEB128 (varint) length prefix followed by the UTF-8 bytes.
/// This matches `binary::write_raw_str` (`write_v32` -> varint length).
fn varint_prefixed_str(value: &str) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(1 + value.len());
    let mut len = value.len() as u64;
    while len >= 0x80 {
        bytes.push((len as u8) | 0x80);
        len >>= 7;
    }
    bytes.push(len as u8);
    bytes.extend_from_slice(value.as_bytes());
    bytes
}

fn count_subslice(haystack: &[u8], needle: &[u8]) -> usize {
    haystack
        .windows(needle.len())
        .filter(|window| *window == needle)
        .count()
}

#[test]
fn vector_dialect_payloads_validate_and_roundtrip_text_and_binary() {
    let module = vector_dialect_module();
    let registry = vector_registry();
    registry
        .validate_module(&module)
        .expect("well-formed vector dialect payloads");

    let text = format!("{module}");
    assert!(text.contains("%10 = dialect_op vector.pack_lanes(%0, %1, %2, %3) -> <4 x i32>"));
    assert!(text.contains("%11 = dialect_op vector.pack_lanes(%4, %5) -> <2 x i64>"));
    assert!(text.contains(
        "%12 = dialect_op vector.extract_lane(%6) -> i32 [vector_ty=ty:<4 x i32>] [lane=u64:2]"
    ));
    assert!(text.contains(
        "%13 = dialect_op vector.extract_lane(%7) -> i64 [vector_ty=ty:<2 x i64>] [lane=u64:1]"
    ));
    assert!(text.contains("%14 = dialect_op vector.insert_lane(%6, %0) -> <4 x i32> [lane=u64:0]"));
    assert!(text.contains("%15 = dialect_op vector.insert_lane(%7, %4) -> <2 x i64> [lane=u64:0]"));
    assert!(text.contains(
        "%16 = dialect_op vector.mask_to_bits(%8) -> i32 [mask_ty=ty:<4 x bool>] [bit_order=str:\"lsb_lane0\"]"
    ));
    assert!(text.contains(
        "%17 = dialect_op vector.mask_to_bits(%9) -> i64 [mask_ty=ty:<2 x bool>] [bit_order=str:\"lsb_lane0\"]"
    ));
    assert!(text.contains("%18 = dialect_op vector.pack_lanes(%0, %0, %0, %0) -> <4 x i32>"));
    assert!(text.contains("%19 = dialect_op vector.pack_lanes(%4, %4) -> <2 x i64>"));
    assert!(text.contains(
        "%22 = dialect_op vector.mask_to_bits(%20) -> i32 [mask_ty=ty:<8 x bool>] [bit_order=str:\"lsb_lane0\"]"
    ));
    assert!(text.contains(
        "%23 = dialect_op vector.mask_to_bits(%21) -> i32 [mask_ty=ty:<16 x bool>] [bit_order=str:\"lsb_lane0\"]"
    ));

    let parsed = trust_ir::parser::parse_module(&text).expect("text roundtrip");
    assert_eq!(parsed, module);
    registry
        .validate_module(&parsed)
        .expect("parsed vector dialect payloads");

    let bytes = trust_ir::binary::serialize_module(&module);
    let decoded = trust_ir::binary::deserialize_module(&bytes).expect("binary roundtrip");
    assert_eq!(decoded, module);
    registry
        .validate_module(&decoded)
        .expect("binary vector dialect payloads");
}

#[test]
fn vector_dialect_binary_contract_carries_stable_op_and_attr_payloads() {
    let module = vector_dialect_module();
    let bytes = trust_ir::binary::serialize_module(&module);

    // The V4 binary format interns every string into a single pool and prefixes
    // each pool entry with a *varint* length (`write_v32`), so each distinct op
    // name / attribute key / attribute string appears exactly once. The old
    // expectations below (vector=12, pack_lanes=4, ...) and the 4-byte
    // `length_prefixed_str` helper predate string interning (format <= v3, when
    // names were written inline at every use site with a fixed u32 length) and
    // never matched the v4 payload — every 4-byte needle counted zero, masking a
    // real round-trip bug in this same module. Assert the v4 contract: each
    // payload string is present exactly once under its varint-prefixed pool entry.
    for name in [
        "vector",
        "pack_lanes",
        "extract_lane",
        "insert_lane",
        "mask_to_bits",
        "vector_ty",
        "lane",
        "mask_ty",
        "bit_order",
        "lsb_lane0",
    ] {
        let needle = varint_prefixed_str(name);
        assert_eq!(
            count_subslice(&bytes, &needle),
            1,
            "v4 string pool should carry {name:?} exactly once"
        );
    }

    let decoded = trust_ir::binary::deserialize_module(&bytes).expect("binary roundtrip");
    assert_eq!(decoded, module);
}

#[test]
fn vector_dialect_validation_rejects_dynamic_lane_payload_shapes() {
    let registry = vector_registry();

    let mut dynamic_extract = vector_dialect_module();
    let Inst::DialectOp(op) = &mut dynamic_extract.functions[0].blocks[0].body[2].inst else {
        panic!("expected extract_lane dialect op");
    };
    op.operands.push(v(0));
    op.attrs.retain(|attr| attr.name != "lane");
    let err = registry
        .validate_module(&dynamic_extract)
        .expect_err("dynamic extract lane payload must fail closed");
    assert!(
        err.to_string().contains("expects 1 operand"),
        "expected dynamic extract operand rejection, got {err}"
    );

    let mut dynamic_insert = vector_dialect_module();
    let Inst::DialectOp(op) = &mut dynamic_insert.functions[0].blocks[0].body[4].inst else {
        panic!("expected insert_lane dialect op");
    };
    op.operands.push(v(1));
    op.attrs.retain(|attr| attr.name != "lane");
    let err = registry
        .validate_module(&dynamic_insert)
        .expect_err("dynamic insert lane payload must fail closed");
    assert!(
        err.to_string().contains("expects 2 operand"),
        "expected dynamic insert operand rejection, got {err}"
    );
}

#[cfg(feature = "serde")]
#[test]
fn vector_dialect_payloads_roundtrip_json_and_messagepack() {
    let module = vector_dialect_module();
    let registry = vector_registry();

    let json = serde_json::to_string_pretty(&module).expect("serialize vector dialect module");
    let from_json: Module = serde_json::from_str(&json).expect("deserialize vector dialect module");
    assert_eq!(from_json, module);
    registry
        .validate_module(&from_json)
        .expect("JSON vector dialect payloads");

    let msgpack = rmp_serde::to_vec(&module).expect("serialize vector dialect module");
    let from_msgpack: Module =
        rmp_serde::from_slice(&msgpack).expect("deserialize vector dialect module");
    assert_eq!(from_msgpack, module);
    registry
        .validate_module(&from_msgpack)
        .expect("MessagePack vector dialect payloads");
}

#[test]
fn vector_dialect_typed_decoding_matches_canonical_payload_shapes() {
    let module = vector_dialect_module();
    let func = &module.functions[0];
    let body = &func.blocks[0].body;

    let pack_v4 = match &body[0].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert!(matches!(
        vector::decode_with_operand_tys(pack_v4, &[Ty::I32, Ty::I32, Ty::I32, Ty::I32]).unwrap(),
        VectorSpec::PackLanes(_)
    ));

    let pack_v2 = match &body[1].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert!(matches!(
        vector::decode_with_operand_tys(pack_v2, &[Ty::I64, Ty::I64]).unwrap(),
        VectorSpec::PackLanes(_)
    ));

    let extract_v4 = match &body[2].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert!(matches!(
        vector::decode_with_operand_tys(extract_v4, &[Ty::v4_i32()]).unwrap(),
        VectorSpec::ExtractLane(_)
    ));

    let extract_v2 = match &body[3].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert!(matches!(
        vector::decode_with_operand_tys(extract_v2, &[Ty::v2_i64()]).unwrap(),
        VectorSpec::ExtractLane(_)
    ));

    let insert_v4 = match &body[4].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert!(matches!(
        vector::decode_with_operand_tys(insert_v4, &[Ty::v4_i32(), Ty::I32]).unwrap(),
        VectorSpec::InsertLane(_)
    ));

    let insert_v2 = match &body[5].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert!(matches!(
        vector::decode_with_operand_tys(insert_v2, &[Ty::v2_i64(), Ty::I64]).unwrap(),
        VectorSpec::InsertLane(_)
    ));

    let mask_v4 = match &body[6].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert!(matches!(
        vector::decode_with_operand_tys(mask_v4, &[Ty::v4_bool()]).unwrap(),
        VectorSpec::MaskToBits(_)
    ));

    let mask_v2 = match &body[7].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert!(matches!(
        vector::decode_with_operand_tys(mask_v2, &[Ty::v2_bool()]).unwrap(),
        VectorSpec::MaskToBits(_)
    ));

    let splat_v4 = match &body[8].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert_eq!(splat_v4.operands, vec![v(0), v(0), v(0), v(0)]);
    assert!(matches!(
        vector::decode_with_operand_tys(splat_v4, &[Ty::I32, Ty::I32, Ty::I32, Ty::I32]).unwrap(),
        VectorSpec::PackLanes(_)
    ));

    let splat_v2 = match &body[9].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert_eq!(splat_v2.operands, vec![v(4), v(4)]);
    assert!(matches!(
        vector::decode_with_operand_tys(splat_v2, &[Ty::I64, Ty::I64]).unwrap(),
        VectorSpec::PackLanes(_)
    ));

    let mask_v8 = match &body[10].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert!(matches!(
        vector::decode_with_operand_tys(mask_v8, &[Ty::v8_bool()]).unwrap(),
        VectorSpec::MaskToBits(_)
    ));

    let mask_v16 = match &body[11].inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected vector dialect op, got {other:?}"),
    };
    assert!(matches!(
        vector::decode_with_operand_tys(mask_v16, &[Ty::v16_bool()]).unwrap(),
        VectorSpec::MaskToBits(_)
    ));
}
