// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Integration roundtrip coverage for the binding-frame instructions
// (`OpenFrame`, `BindSlot`, `LoadSlot`, `CloseFrame`) and for opaque
// `DialectOp`s. Issue #58.
//
// Coverage policy:
//
// - Binary (`trust-ir::binary`): always covered (feature = "binary").
// - serde JSON + MessagePack: gated on `feature = "serde"`.
// - Text parser (`trust-ir::parser`): covered here for `DialectOp`. Parser
//   coverage for the binding-frame quartet (`OpenFrame` / `BindSlot` /
//   `LoadSlot` / `CloseFrame`) lives in
//   `binding_frame_text_roundtrip.rs` (issue #64 closed the parser
//   parity gap). Keeping the two files separate lets each fixture stay
//   focused on its instruction family.

#![cfg(feature = "binary")]

use trust_ir::dialect::{AttrValue, DialectInst};
use trust_ir::inst::{BindingFrameDef, BindingSlot, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BindingFrameId, BlockId, FuncId, ValueId};
use trust_ir::{Block, Function, Module};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

/// Build a module exercising the full binding-frame lifecycle:
/// `open_frame` -> `bind_slot` -> `load_slot` -> `close_frame`, with
/// a multi-slot frame so slot indexing is covered.
fn module_with_binding_frame() -> Module {
    let mut module = Module::new("frame_rt");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::Bool],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "exists_lower", ft, b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I64));
    block.params.push((v(1), Ty::Bool));

    let def_ = BindingFrameDef::new(
        BindingFrameId::new(0),
        "E",
        vec![
            BindingSlot::new("i", Ty::I64),
            BindingSlot::new("seen", Ty::Bool),
        ],
    );
    // %2 = open_frame
    block
        .body
        .push(InstrNode::new(Inst::OpenFrame { def: def_ }).with_result(v(2)));
    // %3 = bind_slot %2, 0, %0
    block.body.push(
        InstrNode::new(Inst::BindSlot {
            frame: v(2),
            slot: 0,
            value: v(0),
        })
        .with_result(v(3)),
    );
    // %4 = bind_slot %3, 1, %1
    block.body.push(
        InstrNode::new(Inst::BindSlot {
            frame: v(3),
            slot: 1,
            value: v(1),
        })
        .with_result(v(4)),
    );
    // %5 = load_slot %4, 0, I64
    block.body.push(
        InstrNode::new(Inst::LoadSlot {
            frame: v(4),
            slot: 0,
            ty: Ty::I64,
        })
        .with_result(v(5)),
    );
    // close_frame %4 (void)
    block
        .body
        .push(InstrNode::new(Inst::CloseFrame { frame: v(4) }));
    // return %5
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(5)] }));
    func.blocks.push(block);
    module.add_function(func);
    module
}

/// Build a module with a `DialectOp` from an *unknown* dialect, carrying
/// every `AttrValue` variant. The core IR doesn't know `"acme.graph"`,
/// but it must still round-trip opaquely (issue #58 acceptance).
fn module_with_unknown_dialect_op() -> Module {
    let mut module = Module::new("unknown_dialect_rt");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::I64],
        returns: vec![Ty::Ptr, Ty::Bool],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::Ptr));
    block.params.push((v(1), Ty::I64));

    // Unknown dialect ("acme") with no registered lowering; must
    // round-trip byte-for-byte through every format. Dialect names are
    // single identifiers in the text form (`<dialect>.<op>`), but the
    // structured binary/serde forms preserve the exact dialect string.
    let op = DialectInst::new("acme", "bfs_visit")
        .with_operand(v(0))
        .with_operand(v(1))
        .with_result_ty(Ty::Ptr)
        .with_result_ty(Ty::Bool)
        .with_attr("parallel", AttrValue::Bool(true))
        .with_attr("delta", AttrValue::I64(-7))
        .with_attr("size", AttrValue::U64(1024))
        .with_attr("weight", AttrValue::F64(1.5))
        .with_attr("label", AttrValue::Str("frontier-zero".to_string()))
        .with_attr("payload", AttrValue::Bytes(vec![0xDE, 0xAD, 0xBE, 0xEF]))
        .with_attr("elem_ty", AttrValue::Ty(Ty::I32))
        .with_version(7);
    let node = InstrNode::new(Inst::DialectOp(Box::new(op)))
        .with_result(v(2))
        .with_result(v(3));
    block.body.push(node);
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![v(2), v(3)],
    }));
    func.blocks.push(block);
    module.add_function(func);
    module
}

// --- Binary roundtrip ---

fn binary_round_trip(module: &Module) {
    let bytes = trust_ir::binary::serialize_module(module);
    let back = trust_ir::binary::deserialize_module(&bytes).expect("deserialize");
    assert_eq!(module, &back, "binary round-trip mismatch");
}

#[test]
fn binding_frame_binary_round_trip() {
    binary_round_trip(&module_with_binding_frame());
}

#[test]
fn unknown_dialect_op_binary_round_trip() {
    binary_round_trip(&module_with_unknown_dialect_op());
}

// --- Parser (text) roundtrip — DialectOp only ---
//
// Binding-frame instructions have no text-format support yet
// (`crates/trust_ir/src/parser.rs`). When they do, add parser coverage
// here.

#[cfg(feature = "parser")]
#[test]
fn unknown_dialect_op_parser_round_trip() {
    // Keep this as a text fixed-point check because binding-frame coverage
    // below owns the full lifecycle surface syntax for the parser.
    let module = module_with_unknown_dialect_op();
    let text1 = module.to_string();
    let parsed = trust_ir::parser::parse_module(&text1).expect("parse text form");
    let text2 = parsed.to_string();
    assert_eq!(text1, text2, "text round-trip mismatch");
}

// --- serde JSON + MessagePack roundtrip ---

#[cfg(feature = "serde")]
fn serde_round_trip(module: &Module) {
    // JSON
    let json = serde_json::to_string_pretty(module).expect("to_json");
    let back_json: Module = serde_json::from_str(&json).expect("from_json");
    assert_eq!(module, &back_json, "JSON round-trip mismatch");

    // MessagePack
    let msgpack = rmp_serde::to_vec(module).expect("to_msgpack");
    let back_msgpack: Module = rmp_serde::from_slice(&msgpack).expect("from_msgpack");
    assert_eq!(module, &back_msgpack, "MessagePack round-trip mismatch");
}

#[cfg(feature = "serde")]
#[test]
fn binding_frame_serde_round_trip() {
    serde_round_trip(&module_with_binding_frame());
}

#[cfg(feature = "serde")]
#[test]
fn unknown_dialect_op_serde_round_trip() {
    serde_round_trip(&module_with_unknown_dialect_op());
}

// --- Opaque preservation for unknown dialects ---

#[test]
fn unknown_dialect_op_preserves_fields_through_binary() {
    let module = module_with_unknown_dialect_op();
    let bytes = trust_ir::binary::serialize_module(&module);
    let back = trust_ir::binary::deserialize_module(&bytes).expect("deserialize");

    // Fish out the DialectOp node from the round-tripped module and check
    // that every structured field survived byte-for-byte — this is the
    // acceptance criterion for "unknown dialects round-trip opaquely".
    let node = &back.functions[0].blocks[0].body[0];
    let op = match &node.inst {
        Inst::DialectOp(op) => op.as_ref(),
        other => panic!("expected DialectOp, got {other:?}"),
    };
    assert_eq!(op.dialect, "acme");
    assert_eq!(op.op, "bfs_visit");
    assert_eq!(op.qualified_name(), "acme.bfs_visit");
    assert_eq!(op.operands, vec![v(0), v(1)]);
    assert_eq!(op.result_tys, vec![Ty::Ptr, Ty::Bool]);
    assert_eq!(op.version, 7);
    assert_eq!(op.attr("parallel"), Some(&AttrValue::Bool(true)));
    assert_eq!(op.attr("delta"), Some(&AttrValue::I64(-7)));
    assert_eq!(op.attr("size"), Some(&AttrValue::U64(1024)));
    assert_eq!(op.attr("weight"), Some(&AttrValue::F64(1.5)));
    assert_eq!(
        op.attr("label"),
        Some(&AttrValue::Str("frontier-zero".to_string()))
    );
    assert_eq!(
        op.attr("payload"),
        Some(&AttrValue::Bytes(vec![0xDE, 0xAD, 0xBE, 0xEF]))
    );
    assert_eq!(op.attr("elem_ty"), Some(&AttrValue::Ty(Ty::I32)));
    assert_eq!(node.results, vec![v(2), v(3)]);
}
