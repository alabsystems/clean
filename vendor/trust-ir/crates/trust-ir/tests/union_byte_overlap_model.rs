// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// G18-3: the RATIFIED representation of a C/Rust `union` in TrustIr.
//
// DECISION (see `lowering-target-subset.md`, "Unions"): TrustIr does NOT get a
// nominal `Ty::Union(UnionId)` + `UnionDef`. A union is spelled as
// BYTE-OVERLAPPING STORAGE: one allocation sized to the largest field and
// aligned to the strictest field alignment, written and read through TYPED
// `Store` / `Load` at a shared base address. This file is the executable half
// of that ruling — it demonstrates, through the reference interpreter, that
// every property a `UnionDef` was proposed to carry is already stateable:
//
//   * size and alignment            -> the carrier's `Alloca { ty, align }`
//   * the per-field TYPE            -> the `Load`/`Store` `ty` at the access
//   * the deliberate ALIASING       -> two typed accesses at one address
//   * per-field `NoUndef`/`Aligned` -> `InstrNode.proofs` on the ACCESS, which
//                                      is the only place they have operational
//                                      content: a claim about a field that is
//                                      not the active one is false, and a
//                                      `UnionDef` could only ever carry the
//                                      unconditional (false) form.
//
// The one thing a `UnionDef` would add — a list of the field types — states
// nothing checkable, because the format cannot say which field is ACTIVE, and
// neither can rustc: `union` field activity is not tracked in the type system,
// which is exactly why reading a union field is `unsafe`. A per-field
// annotation on a definition would therefore be a claim that is false whenever
// the field is not the live one, which is strictly worse than the per-access
// annotation this model already supports.
//
// WS3.18 (F-050) added the producer guidance on top of this ruling: by-value
// moves are `MemCopy` between carriers, call edges pass a carrier by address,
// and the struct spelling of a union is refused toward the carrier. Its
// executable pins are `trust-ir-conformance/tests/union_carrier.rs`.

use trust_ir::inst::Inst;
use trust_ir::interpret::{InterpretValueKind, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::proof::ProofAnnotation;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Constant, FuncTy, Function, Module, Ty};

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}
fn b(i: u32) -> BlockId {
    BlockId::new(i)
}

/// `union U { a: u32, b: f32 }` — size 4, align 4.
///
/// Writes the `a` field, reads back the (inactive) `b` field, and returns both
/// the round-tripped `a` and the punned `b`. The carrier is `[u8; 4]`, which
/// is a STRUCTURAL type: `Array(U8, 4)` denotes the same thing in every module
/// with no nominal id to reconcile, which is the second half of the ruling.
#[test]
fn union_of_u32_and_f32_is_byte_overlapping_storage() {
    let mut module = Module::new("union-model");
    let u8_ty = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let carrier = Ty::Array(u8_ty, 4);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U32, Ty::F32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut f = Function::new(FuncId::new(0), "pun", sig, b(0));
    let mut blk = Block::new(b(0));

    // The union's storage: max field size, max field alignment. Both facts are
    // stated by the `Alloca` itself; no `UnionDef` is consulted.
    blk.body.push(
        InstrNode::new(Inst::Alloca {
            ty: carrier,
            count: None,
            align: Some(4),
        })
        .with_result(v(0)),
    );
    blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            // 1.0f32 == 0x3F800000
            value: Constant::Int(0x3F80_0000),
        })
        .with_result(v(1)),
    );
    // Write the ACTIVE field `a: u32` at offset 0. The per-field alignment and
    // definedness claims ride HERE, on the access, where they are true.
    blk.body.push(
        InstrNode::new(Inst::Store {
            ty: Ty::U32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(4),
        })
        .with_proof(ProofAnnotation::Aligned(4))
        .with_proof(ProofAnnotation::NoUndef),
    );
    // Read the same bytes back as `a`.
    blk.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U32,
            ptr: v(0),
            volatile: false,
            align: Some(4),
        })
        .with_result(v(2))
        .with_proof(ProofAnnotation::Aligned(4)),
    );
    // ...and as the OVERLAPPING field `b: f32`, from the same address. The
    // deliberate aliasing is the two typed accesses at one pointer; nothing
    // else needs to state it.
    blk.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::F32,
            ptr: v(0),
            volatile: false,
            align: Some(4),
        })
        .with_result(v(3))
        .with_proof(ProofAnnotation::Aligned(4)),
    );
    blk.body.push(InstrNode::new(Inst::Return {
        values: vec![v(2), v(3)],
    }));
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    let out = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect("the byte-overlap union model executes on the existing surface");

    assert_eq!(out.returns[0].as_int().unwrap().as_unsigned(), 0x3F80_0000);
    // The inactive field reads the SAME bytes, reinterpreted: 1.0f32.
    let InterpretValueKind::FloatBits(bits) = out.returns[1].kind else {
        panic!(
            "the f32 lane must decode as a float, got {:?}",
            out.returns[1]
        );
    };
    assert_eq!(bits as u32, 0x3F80_0000);
    assert_eq!(f32::from_bits(bits as u32), 1.0_f32);
}

/// The carrier is sized by the LARGEST field and aligned by the STRICTEST, and
/// a smaller field occupies its prefix — `union V { small: u8, big: u64 }`.
/// A nominal `UnionDef` would restate exactly these two numbers.
#[test]
fn union_carrier_states_size_and_alignment_without_a_uniondef() {
    let mut module = Module::new("union-size");
    let u8_ty = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let carrier = Ty::Array(u8_ty, 8);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U8, Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut f = Function::new(FuncId::new(0), "prefix", sig, b(0));
    let mut blk = Block::new(b(0));
    blk.body.push(
        InstrNode::new(Inst::Alloca {
            ty: carrier,
            count: None,
            // The union's alignment: max over fields (u64 -> 8).
            align: Some(8),
        })
        .with_result(v(0)),
    );
    // Write the WIDE field first so every byte of the carrier is initialized;
    // reading the narrow field then observes its low byte, which is the whole
    // content of the byte-overlap model on a little-endian target.
    blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(0x0102_0304_0506_0708),
        })
        .with_result(v(1)),
    );
    blk.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U64,
        ptr: v(0),
        value: v(1),
        volatile: false,
        align: Some(8),
    }));
    blk.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U8,
            ptr: v(0),
            volatile: false,
            align: Some(1),
        })
        .with_result(v(2)),
    );
    blk.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U64,
            ptr: v(0),
            volatile: false,
            align: Some(8),
        })
        .with_result(v(3)),
    );
    blk.body.push(InstrNode::new(Inst::Return {
        values: vec![v(2), v(3)],
    }));
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    let out = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect("a wide/narrow union pair executes");
    assert_eq!(out.returns[0].as_int().unwrap().as_unsigned(), 0x08);
    assert_eq!(
        out.returns[1].as_int().unwrap().as_unsigned(),
        0x0102_0304_0506_0708
    );
}

/// FAIL CLOSED, and the reason the ruling is not a loss of safety: reading a
/// union field whose bytes were never written is UNINITIALIZED-READ UB, and the
/// reference interpreter refuses it rather than inventing a value. A `UnionDef`
/// carrying an unconditional per-field `NoUndef` would have CLAIMED the
/// opposite for exactly this program.
#[test]
fn reading_an_unwritten_union_field_is_refused_not_guessed() {
    let mut module = Module::new("union-uninit");
    let u8_ty = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let carrier = Ty::Array(u8_ty, 8);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut f = Function::new(FuncId::new(0), "uninit", sig, b(0));
    let mut blk = Block::new(b(0));
    blk.body.push(
        InstrNode::new(Inst::Alloca {
            ty: carrier,
            count: None,
            align: Some(8),
        })
        .with_result(v(0)),
    );
    // Only the low byte (the `small` field) is written...
    blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(1),
        })
        .with_result(v(1)),
    );
    blk.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U8,
        ptr: v(0),
        value: v(1),
        volatile: false,
        align: Some(1),
    }));
    // ...and the WIDE field is read, so 7 of its 8 bytes are uninitialized.
    blk.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U64,
            ptr: v(0),
            volatile: false,
            align: Some(8),
        })
        .with_result(v(2))
        // A per-field `NoUndef` of the kind a `UnionDef` would carry: here it
        // is a FALSE claim, and the model does not honour it.
        .with_proof(ProofAnnotation::NoUndef),
    );
    blk.body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    let err = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect_err("a partially-initialized union read must be refused");
    let msg = format!("{err}").to_ascii_lowercase();
    assert!(
        msg.contains("uninitialized") || msg.contains("undef") || msg.contains("poison"),
        "unexpected diagnostic: {err}"
    );
}
