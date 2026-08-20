// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Text round-trip coverage for the binding-frame instructions
// (`OpenFrame`, `BindSlot`, `LoadSlot`, `CloseFrame`). Issue #64.
//
// Before this coverage landed, the four binding-frame instructions were
// supported by the binary codec (`trust-ir::binary`), the serde derives, the
// display printer (`trust-ir::display`), and the canonical formatter
// (`trust-ir::format::canonical`), but **not** by the text parser
// (`trust-ir::parser`). That meant `trust-ir-fmt` produced text that `trust-ir
// validate` could not read back — a format-hole for a user-facing CLI.
//
// The tests here lock in the fix:
//
// 1. `binding_frame_text_round_trip`: text -> parse -> text is identity
//    on a fixture exercising all four variants, including empty-slot and
//    multi-slot frames. Mirrors the existing
//    `unknown_dialect_op_parser_round_trip` convention — the parser does
//    not reconstruct `Module::func_types`, so full `Module == Module`
//    equality is not available; we compare text forms, which is the
//    property `trust-ir-fmt -> trust_ir validate` actually relies on.
//
// 2. `binding_frame_canonical_fmt_parse_fmt_fixed_point`: the stronger
//    canonical-form property `canonical(parse(canonical(m))) ==
//    canonical(m)` — i.e. the canonical text is a fixed point of
//    round-tripping through the parser. This is the diff-stability
//    guarantee (#62) extended to binding frames.
//
// 3. `binding_frame_full_lifecycle_text`: sanity-checks the exact text
//    produced by the fixture against a hand-written expected string so
//    the parser's accepted syntax is pinned. If the `display::write_inst`
//    format for binding frames ever changes, this test fails loudly.

#![cfg(all(feature = "parser", feature = "fmt"))]

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

/// Fixture module that exercises every binding-frame instruction:
///
/// - `OpenFrame` with a multi-slot frame (heterogeneous slot types).
/// - `OpenFrame` with an empty slot list (surface-level edge case of
///   `{}` rather than `{...}`).
/// - `BindSlot` into slots of both types (SSA threading of frame
///   handles).
/// - `LoadSlot` from a non-zero slot ordinal with the correctly
///   declared slot type.
/// - `CloseFrame` for both frames (emits no result value).
fn module_with_all_binding_frames() -> Module {
    let mut module = Module::new("binding_frame_text_rt");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::Bool],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "exists_lower", ft, b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I64));
    block.params.push((v(1), Ty::Bool));

    // Frame E: two slots (I64, Bool).
    let e_def = BindingFrameDef::new(
        BindingFrameId::new(0),
        "E",
        vec![
            BindingSlot::new("i", Ty::I64),
            BindingSlot::new("seen", Ty::Bool),
        ],
    );
    // %2 = open_frame #0 "E" {i: I64, seen: Bool}
    block
        .body
        .push(InstrNode::new(Inst::OpenFrame { def: e_def }).with_result(v(2)));
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
    // %5 = load_slot I64 %4, 0
    block.body.push(
        InstrNode::new(Inst::LoadSlot {
            frame: v(4),
            slot: 0,
            ty: Ty::I64,
        })
        .with_result(v(5)),
    );
    // close_frame %4
    block
        .body
        .push(InstrNode::new(Inst::CloseFrame { frame: v(4) }));

    // Frame marker: empty-slot frame exercises the `{}` surface form.
    // %6 = open_frame #1 "marker" {}
    let marker_def = BindingFrameDef::new(BindingFrameId::new(1), "marker", Vec::new());
    block
        .body
        .push(InstrNode::new(Inst::OpenFrame { def: marker_def }).with_result(v(6)));
    // close_frame %6
    block
        .body
        .push(InstrNode::new(Inst::CloseFrame { frame: v(6) }));

    // return %5
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(5)] }));
    func.blocks.push(block);
    module.add_function(func);
    module
}

#[test]
fn binding_frame_text_round_trip() {
    // This suite pins the binding-frame surface syntax; parser.rs owns
    // structural round-trip coverage for shared module tables.
    let module = module_with_all_binding_frames();
    let text1 = module.to_string();
    let parsed = trust_ir::parser::parse_module(&text1).expect("parse text form");
    let text2 = parsed.to_string();
    assert_eq!(text1, text2, "text round-trip mismatch");
}

#[test]
fn binding_frame_canonical_fmt_parse_fmt_fixed_point() {
    // The canonical formatter must be idempotent under parsing: the
    // string `canonical(m)` must parse to a module whose canonical form
    // is again `canonical(m)`. This is the diff-stability property
    // (`designs/...` issue #62) extended to binding frames.
    let module = module_with_all_binding_frames();
    let canon1 = trust_ir::format::canonical(&module);
    let parsed = trust_ir::parser::parse_module(&canon1).expect("parse canonical form");
    let canon2 = trust_ir::format::canonical(&parsed);
    assert_eq!(
        canon1, canon2,
        "canonical fmt+parse+fmt fixed point violated"
    );
}

#[test]
fn binding_frame_full_lifecycle_text() {
    // Pin the exact surface syntax the parser accepts. If the display
    // format for binding frames (`crates/trust_ir/src/display.rs:431-455`)
    // ever changes, this test fails loudly so the parser can be updated
    // in the same commit.
    let module = module_with_all_binding_frames();
    let text = module.to_string();

    // Each binding-frame instruction must render on its own line. We
    // check for the distinctive fragments rather than the whole text so
    // unrelated formatting tweaks (e.g., whitespace between top-level
    // decls) don't falsely trip this test.
    // `Ty::Display` emits lowercase primitive names (`i64`, `bool`),
    // so the expected fragments match the actual display output rather
    // than the Rust identifier casing (`Ty::I64`, `Ty::Bool`).
    let expected_fragments = [
        "= open_frame #0 \"E\" {i: i64, seen: bool}",
        "= bind_slot %",
        "= load_slot i64 %",
        "close_frame %",
        "= open_frame #1 \"marker\" {}",
    ];
    for frag in expected_fragments {
        assert!(
            text.contains(frag),
            "expected fragment {frag:?} not found in:\n{text}"
        );
    }

    // And each fragment must re-parse without error.
    let _ = trust_ir::parser::parse_module(&text).expect("parse fixture");
}

#[test]
fn empty_slot_open_frame_parser() {
    // Directly parse a minimal snippet containing only an empty-slot
    // `open_frame`. Guards the `{}` branch of the parser.
    let text = r#"module "t"
fn @f(functy.0) {
bb0:
  %0 = open_frame #7 "empty" {}
  close_frame %0
  ret
}
"#;
    let module = trust_ir::parser::parse_module(text).expect("parse empty-slot open_frame");
    let inst = &module.functions[0].blocks[0].body[0].inst;
    match inst {
        Inst::OpenFrame { def } => {
            assert_eq!(def.id, BindingFrameId::new(7));
            assert_eq!(def.name, "empty");
            assert!(def.slots.is_empty());
        }
        other => panic!("expected OpenFrame, got {other:?}"),
    }
}

#[test]
fn bind_load_close_parser_operands() {
    // Spot-check operand decoding: `bind_slot`, `load_slot`, and
    // `close_frame` must capture frame, slot index, value, and type in
    // the right positions.
    let text = r#"module "t"
fn @f(functy.0) {
bb0:
  %0 = open_frame #0 "F" {x: i32}
  %1 = bind_slot %0, 0, %0
  %2 = load_slot i32 %1, 0
  close_frame %1
  ret
}
"#;
    let module = trust_ir::parser::parse_module(text).expect("parse binding-frame ops");
    let body = &module.functions[0].blocks[0].body;

    match &body[1].inst {
        Inst::BindSlot { frame, slot, value } => {
            assert_eq!(*frame, ValueId::new(0));
            assert_eq!(*slot, 0);
            assert_eq!(*value, ValueId::new(0));
        }
        other => panic!("expected BindSlot, got {other:?}"),
    }
    match &body[2].inst {
        Inst::LoadSlot { frame, slot, ty } => {
            assert_eq!(*frame, ValueId::new(1));
            assert_eq!(*slot, 0);
            assert_eq!(*ty, Ty::I32);
        }
        other => panic!("expected LoadSlot, got {other:?}"),
    }
    match &body[3].inst {
        Inst::CloseFrame { frame } => {
            assert_eq!(*frame, ValueId::new(1));
        }
        other => panic!("expected CloseFrame, got {other:?}"),
    }
}
