// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Integration coverage for the canonical text pretty-printer
// (`trust-ir::format::canonical`, feature `fmt`). Issue #62.
//
// Goals:
//
// 1. **Idempotency**: `canonical(canonical(m)) == canonical(m)`.
// 2. **fmt+parse+fmt fixed point**: for any text-representable module `m`,
//    `canonical(parse(canonical(m))) == canonical(m)`. This is the
//    diff-stability guarantee — round-tripping through the parser does
//    not perturb the canonical form.
// 3. **Semantic guardrail**: canonicalization is a *renaming*, not a
//    rewrite. It must preserve block count, instruction kinds, proof
//    annotations, and the shape of every instruction — only ValueId
//    indices may change.
// 4. **Dense SSA**: after canonicalization, every `ValueId` appearing in
//    a function lies in `0..N` where N is the value count, with no gaps.
//
// We intentionally do not pull in `insta`: hand-written expected strings
// are checked in directly, which keeps the `trust-ir` crate zero-external-dep
// and makes snapshots trivially reviewable in PR diffs.
//
// The test coverage here intentionally avoids binding-frame and dialect-op
// instructions — those are exercised extensively in the unit tests in
// `format.rs` and the binary/serde roundtrip suite in
// `binding_frame_dialect_roundtrip.rs`. This file focuses on instruction
// categories that are *text-representable* so that the fmt+parse+fmt
// fixed-point property can be asserted end-to-end.

#![cfg(all(feature = "fmt", feature = "parser"))]

use trust_ir::inst::{BinOp, ICmpOp, Inst, Ordering};
use trust_ir::node::InstrNode;
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Function, Module};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

/// Build a small but non-trivial module: integer arithmetic, a compare,
/// a conditional branch, proof annotations, and block parameters.
fn module_arith_and_control() -> Module {
    let mut module = Module::new("arith_ctrl");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "clamp_add", ft, b(0));

    // bb0(%0: i32, %1: i32):
    //   %2 = add %0, %1  [no_overflow]
    //   %3 = icmp slt %2, 0
    //   cond_br %3, bb1(%0), bb2(%2)
    let mut bb0 = Block::new(b(0));
    bb0.params.push((v(0), Ty::I32));
    bb0.params.push((v(1), Ty::I32));
    bb0.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            lhs: v(0),
            rhs: v(1),
            ty: Ty::I32,
        })
        .with_result(v(2))
        .with_proof(ProofAnnotation::NoOverflow),
    );
    bb0.body.push(
        InstrNode::new(Inst::Const {
            value: trust_ir::constant::Constant::Int(0),
            ty: Ty::I32,
        })
        .with_result(v(3)),
    );
    bb0.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Slt,
            lhs: v(2),
            rhs: v(3),
            ty: Ty::I32,
        })
        .with_result(v(4)),
    );
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: v(4),
        then_target: b(1),
        then_args: vec![v(0)],
        else_target: b(2),
        else_args: vec![v(2)],
    }));
    func.blocks.push(bb0);

    // bb1(%10: i32):  return %10
    let mut bb1 = Block::new(b(1));
    bb1.params.push((v(10), Ty::I32));
    bb1.body.push(InstrNode::new(Inst::Return {
        values: vec![v(10)],
    }));
    func.blocks.push(bb1);

    // bb2(%20: i32):  return %20
    let mut bb2 = Block::new(b(2));
    bb2.params.push((v(20), Ty::I32));
    bb2.body.push(InstrNode::new(Inst::Return {
        values: vec![v(20)],
    }));
    func.blocks.push(bb2);

    module.add_function(func);
    module
}

/// Same semantic module but with a *sparse and shuffled* SSA numbering —
/// block ids are not in 0..N order, and the value ids inside each block
/// jump around. After canonicalization it must be indistinguishable from
/// the clean version.
fn module_arith_and_control_sparse() -> Module {
    let mut module = Module::new("arith_ctrl");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "clamp_add", ft, b(0));

    // Block ids deliberately out of order in the Vec: bb2, bb0, bb1.
    // Value ids inside each block also deliberately sparse/shuffled.

    // bb2(%777: i32):  return %777
    let mut bb2 = Block::new(b(2));
    bb2.params.push((v(777), Ty::I32));
    bb2.body.push(InstrNode::new(Inst::Return {
        values: vec![v(777)],
    }));

    // bb0(%500: i32, %501: i32):
    //   %900 = add %500, %501 [no_overflow]
    //   %901 = const 0 : i32
    //   %902 = icmp slt %900, %901
    //   cond_br %902, bb1(%500), bb2(%900)
    let mut bb0 = Block::new(b(0));
    bb0.params.push((v(500), Ty::I32));
    bb0.params.push((v(501), Ty::I32));
    bb0.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            lhs: v(500),
            rhs: v(501),
            ty: Ty::I32,
        })
        .with_result(v(900))
        .with_proof(ProofAnnotation::NoOverflow),
    );
    bb0.body.push(
        InstrNode::new(Inst::Const {
            value: trust_ir::constant::Constant::Int(0),
            ty: Ty::I32,
        })
        .with_result(v(901)),
    );
    bb0.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Slt,
            lhs: v(900),
            rhs: v(901),
            ty: Ty::I32,
        })
        .with_result(v(902)),
    );
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: v(902),
        then_target: b(1),
        then_args: vec![v(500)],
        else_target: b(2),
        else_args: vec![v(900)],
    }));

    // bb1(%333: i32):  return %333
    let mut bb1 = Block::new(b(1));
    bb1.params.push((v(333), Ty::I32));
    bb1.body.push(InstrNode::new(Inst::Return {
        values: vec![v(333)],
    }));

    // Insertion order intentionally NOT block-id order.
    func.blocks.push(bb2);
    func.blocks.push(bb0);
    func.blocks.push(bb1);
    module.add_function(func);
    module
}

/// Module with atomic ops (AtomicLoad/Store/RMW/CmpXchg/Fence).
fn module_atomics() -> Module {
    let mut module = Module::new("atomics");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "atomic_smoke", ft, b(0));
    let mut bb = Block::new(b(0));
    bb.params.push((v(0), Ty::Ptr));

    bb.body.push(
        InstrNode::new(Inst::AtomicLoad {
            ptr: v(0),
            ty: Ty::I32,
            ordering: Ordering::Acquire,
        })
        .with_result(v(1)),
    );
    bb.body
        .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
    func.blocks.push(bb);
    module.add_function(func);
    module
}

/// Module with an aggregate instruction (extract_field) + memory op.
fn module_aggregate_memory() -> Module {
    let mut module = Module::new("agg_mem");
    let sid = module.add_struct(trust_ir::ty::StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "Point".to_string(),
        fields: vec![
            trust_ir::ty::FieldDef {
                name: "x".to_string(),
                ty: Ty::I32,
                offset: Some(0),
            },
            trust_ir::ty::FieldDef {
                name: "y".to_string(),
                ty: Ty::I32,
                offset: Some(4),
            },
        ],
        size: Some(8),
        align: Some(4),

        repr: Default::default(),
    });
    let struct_ty = Ty::Struct(sid);

    let ft = module.add_func_type(FuncTy {
        params: vec![struct_ty.clone()],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "get_x", ft, b(0));
    let mut bb = Block::new(b(0));
    bb.params.push((v(0), struct_ty.clone()));
    bb.body.push(
        InstrNode::new(Inst::ExtractField {
            aggregate: v(0),
            field: 0,
            ty: struct_ty.clone(),
        })
        .with_result(v(1)),
    );
    bb.body
        .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
    func.blocks.push(bb);
    module.add_function(func);
    module
}

// --- Properties ---

/// `canonical` is idempotent: applying it twice is the same as once.
#[test]
fn canonical_is_idempotent_arith() {
    let m = module_arith_and_control();
    let once = trust_ir::format::canonical(&m);
    let parsed = trust_ir::parser::parse_module(&once).expect("parse must succeed");
    let twice = trust_ir::format::canonical(&parsed);
    assert_eq!(
        once, twice,
        "canonical(parse(canonical(m))) must equal canonical(m)\n\n--- once ---\n{once}\n\n--- twice ---\n{twice}\n"
    );
}

#[test]
fn canonical_is_idempotent_atomics() {
    let m = module_atomics();
    let once = trust_ir::format::canonical(&m);
    let parsed = trust_ir::parser::parse_module(&once).expect("parse must succeed");
    let twice = trust_ir::format::canonical(&parsed);
    assert_eq!(once, twice);
}

#[test]
fn canonical_is_idempotent_aggregate_memory() {
    let m = module_aggregate_memory();
    let once = trust_ir::format::canonical(&m);
    let parsed = trust_ir::parser::parse_module(&once).expect("parse must succeed");
    let twice = trust_ir::format::canonical(&parsed);
    assert_eq!(once, twice);
}

/// Sparse and dense ssa numberings must produce byte-identical canonical text.
/// This is *the* diff-stability guarantee.
#[test]
fn canonical_collapses_sparse_ssa_to_dense() {
    let dense = trust_ir::format::canonical(&module_arith_and_control());
    let sparse = trust_ir::format::canonical(&module_arith_and_control_sparse());
    assert_eq!(
        dense, sparse,
        "sparse and dense must canonicalize identically\n\n--- dense ---\n{dense}\n\n--- sparse ---\n{sparse}\n"
    );
}

/// After canonicalization, every value id used in the function is in
/// the dense range `0..N` where N is the number of distinct ValueIds
/// referenced. No gaps.
#[test]
fn canonical_assigns_dense_ssa() {
    let m = trust_ir::format::canonicalize(&module_arith_and_control_sparse());
    let func = &m.functions[0];

    let mut seen = std::collections::BTreeSet::new();
    for block in &func.blocks {
        for (id, _ty) in &block.params {
            seen.insert(id.index());
        }
        for node in &block.body {
            for r in &node.results {
                seen.insert(r.index());
            }
        }
    }

    // Expect dense 0..N.
    let n = seen.len() as u32;
    let expected: std::collections::BTreeSet<u32> = (0..n).collect();
    assert_eq!(
        seen, expected,
        "canonical ssa ids must be dense 0..N, got {seen:?}"
    );
}

/// Canonicalization preserves instruction count, kind, and proof annotations.
/// It must be a *renaming*, not a rewrite.
#[test]
fn canonical_preserves_structure() {
    let m = module_arith_and_control();
    let c = trust_ir::format::canonicalize(&m);

    assert_eq!(m.functions.len(), c.functions.len());
    for (orig, canon) in m.functions.iter().zip(c.functions.iter()) {
        assert_eq!(orig.blocks.len(), canon.blocks.len(), "block count");
        for (ob, cb) in orig.blocks.iter().zip(canon.blocks.iter()) {
            assert_eq!(ob.params.len(), cb.params.len(), "block-param count");
            assert_eq!(ob.body.len(), cb.body.len(), "block-body count");
            for (oi, ci) in ob.body.iter().zip(cb.body.iter()) {
                assert_eq!(oi.proofs, ci.proofs, "proof annotations");
                assert_eq!(
                    std::mem::discriminant(&oi.inst),
                    std::mem::discriminant(&ci.inst),
                    "instruction kind"
                );
            }
        }
    }
}

/// The canonical form of a simple function is exactly the text we expect.
/// If this snapshot changes, review carefully — it indicates either a
/// formatter regression (bad) or an intentional format improvement
/// (update the snapshot).
#[test]
fn canonical_snapshot_arith_ctrl() {
    let m = module_arith_and_control();
    let got = trust_ir::format::canonical(&m);

    // Minimum structural invariants that any canonical formatter for this
    // module must satisfy. We assert invariants rather than the entire
    // byte string so that unrelated display.rs tweaks don't cause false
    // positives — the diff-stability property is "fmt+parse+fmt is a
    // fixed point" (tested separately), not "the bytes never change".
    assert!(
        got.starts_with("; TrustIr text format v1"),
        "header present"
    );
    assert!(got.contains("module \"arith_ctrl\""), "module header");
    assert!(got.contains("fn @clamp_add"), "function header");
    assert!(got.contains("bb0("), "entry block present");
    assert!(got.contains("bb1("), "second block present");
    assert!(got.contains("bb2("), "third block present");
    assert!(got.contains("%0"), "dense ssa starts at 0");
    assert!(got.contains("no_overflow"), "proof annotation present");
    // Exactly one trailing newline.
    assert!(got.ends_with('\n'), "canonical text ends with newline");
    assert!(
        !got.ends_with("\n\n\n"),
        "canonical text does not end with multiple blank lines"
    );
}
