// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The tensor region's map, reduce and view (PKG-U13c): `Inst::TensorMap`
//! (Inst tag 72), `Inst::TensorReduce` (73) and `Inst::TensorView` (74), each
//! read-gated on `TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION`. The codec spells
//! exactly what it is given; whether a map's lanes are in scope, a
//! reduction's axes ascend or a view's shape reads a coordinate is the
//! validator's to decide, so one fixture below is deliberately ill-typed.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, ObservedSession,
};
use crate::{
    Block, Function, InstrNode, TensorIndexExpr as E, TensorMapNode, TensorReduceOp,
    TensorReduceOrder,
};

type Node = TensorMapNode<crate::NoExt>;

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn tensor(elem: Ty, rank: u32) -> Ty {
    Ty::Tensor(Box::new(elem), rank)
}

fn header_version(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[8..12].try_into().unwrap())
}

fn relabel(bytes: &[u8], version: u32) -> Vec<u8> {
    let mut forged = bytes.to_vec();
    forged[8..12].copy_from_slice(&version.to_le_bytes());
    forged
}

/// `f(params..) -> result` whose one instruction is `inst` (its result the
/// value after the parameters), returned.
fn one_instruction_module(params: Vec<Ty>, result: Ty, inst: Inst) -> Module {
    let mut module = Module::new("tensor_map_reduce_view_codec");
    let sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: params.clone(),
            returns: vec![result],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "tensor", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    let out = v(params.len() as u32);
    for (i, ty) in params.into_iter().enumerate() {
        entry.params.push((v(i as u32), ty));
    }
    entry
        .body
        .push(InstrNode::new(inst).with_results(vec![out]));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![out] }));
    f.blocks.push(entry);
    module.functions.push(f);
    module
}

/// Every node kind: `tensor_map tensor<i32, 2> (%0, %1, %2) { add i32 $0,
/// $1; neg i32 $3; icmp sgt i32 $4, $2; select i32 $5, $4, $2; trunc i32 $6
/// to i8; sext i8 $7 to i32 }`.
fn map_module() -> Module {
    let matrix = tensor(Ty::I32, 2);
    one_instruction_module(
        vec![matrix.clone(), matrix.clone(), Ty::I32],
        matrix.clone(),
        Inst::TensorMap {
            ty: matrix,
            args: vec![v(0), v(1), v(2)],
            body: vec![
                Node::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I32,
                    lhs: 0,
                    rhs: 1,
                },
                Node::UnOp {
                    op: UnOp::Neg,
                    ty: Ty::I32,
                    operand: 3,
                },
                Node::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I32,
                    lhs: 4,
                    rhs: 2,
                },
                Node::Select {
                    ty: Ty::I32,
                    cond: 5,
                    then_lane: 4,
                    else_lane: 2,
                },
                Node::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I32,
                    dst_ty: Ty::I8,
                    operand: 6,
                },
                Node::Cast {
                    op: CastOp::SExt,
                    src_ty: Ty::I8,
                    dst_ty: Ty::I32,
                    operand: 7,
                },
            ],
        },
    )
}

/// `tensor_reduce smax tensor<i64, 1> %0 axes [0, 2] order row_major` of a
/// `tensor<i64, 3>`.
fn reduce_module() -> Module {
    one_instruction_module(
        vec![tensor(Ty::I64, 3)],
        tensor(Ty::I64, 1),
        Inst::TensorReduce {
            ty: tensor(Ty::I64, 1),
            src: v(0),
            op: TensorReduceOp::SMax,
            axes: vec![0, 2],
            order: TensorReduceOrder::RowMajor,
        },
    )
}

/// A left pad with a fill: `tensor_view tensor<i32, 1> %0 params [%1] exprs
/// [src_extent(0), param(0), add($0, $1), coord(0), sub($3, $1)] shape [$2]
/// index [$4] fill %2`.
fn view_module() -> Module {
    let row = tensor(Ty::I32, 1);
    one_instruction_module(
        vec![row.clone(), Ty::Usize, Ty::I32],
        row.clone(),
        Inst::TensorView {
            ty: row,
            src: v(0),
            params: vec![v(1)],
            exprs: vec![
                E::SrcExtent(0),
                E::Param(0),
                E::Add(0, 1),
                E::Coord(0),
                E::Sub(3, 1),
            ],
            shape: vec![2],
            index: vec![4],
            fill: Some(v(2)),
        },
    )
}

/// Every index node kind, a literal at the top of `u64`, and no fill: a
/// `[n]` view of a `tensor<u8, 2>` (well-formed or not is the validator's).
fn every_index_node_module() -> Module {
    one_instruction_module(
        vec![tensor(Ty::U8, 2), Ty::Usize],
        tensor(Ty::U8, 1),
        Inst::TensorView {
            ty: tensor(Ty::U8, 1),
            src: v(0),
            params: vec![v(1)],
            exprs: vec![
                E::Lit(u64::MAX),
                E::Param(0),
                E::SrcExtent(1),
                E::Coord(0),
                E::Add(0, 1),
                E::Sub(4, 2),
                E::Mul(5, 3),
                E::Div(6, 1),
                E::Rem(7, 2),
                E::Min(8, 1),
                E::Max(9, 2),
            ],
            shape: vec![2],
            index: vec![9, 10],
            fill: None,
        },
    )
}

/// A map with NO tensor type anywhere (ill-typed on purpose: `ty` and the
/// operand are `i32`), so only the instruction's own raise can select the
/// version, and only Inst tag 72 is read-gated in its bytes.
fn map_only_module() -> Module {
    one_instruction_module(
        vec![Ty::I32],
        Ty::I32,
        Inst::TensorMap {
            ty: Ty::I32,
            args: vec![v(0)],
            body: vec![Node::UnOp {
                op: UnOp::Neg,
                ty: Ty::I32,
                operand: 0,
            }],
        },
    )
}

fn fixtures() -> Vec<(&'static str, Module)> {
    vec![
        ("map", map_module()),
        ("reduce", reduce_module()),
        ("view", view_module()),
        ("every-index-node", every_index_node_module()),
        ("map-only", map_only_module()),
    ]
}

fn the_instruction(module: &Module) -> &Inst {
    &module.functions[0].blocks[0].body[0].inst
}

fn spell(module: &Module) -> Vec<u8> {
    SealedStringPool::by_replay(|pool, bytes| {
        write_inst(bytes, pool, None, the_instruction(module));
    })
}

fn tag_of(write: impl Fn(&mut Vec<u8>)) -> u8 {
    let mut buf = Vec::new();
    write(&mut buf);
    assert_eq!(buf.len(), 1, "a one-byte tag");
    buf[0]
}

#[test]
fn modules_round_trip_at_exactly_the_map_reduce_view_version() {
    for (name, module) in fixtures() {
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(
            header_version(&bytes),
            TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION,
            "{name}"
        );
        let (decoded, version) =
            deserialize_module_with_wire_version(&bytes).expect("lossless module");
        assert_eq!(
            version.get(),
            TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION,
            "{name}"
        );
        assert_eq!(decoded, module, "{name}");
        assert_eq!(decoded.stable_digest(), module.stable_digest(), "{name}");
        assert_eq!(
            serialize_module(&decoded).expect("serialize_module: decoded fixture"),
            bytes,
            "{name}: re-encoding is byte-identical"
        );
    }
}

/// The exact tag-72, tag-73 and tag-74 spellings, pinned byte for byte so a
/// reordering is a failure, not a silent re-encoding. The scalar operators
/// are spelled by their own instructions' tags.
#[test]
fn wire_spellings_are_pinned() {
    let add = tag_of(|b| write_binop(b, &BinOp::Add));
    let neg = tag_of(|b| write_unop(b, &UnOp::Neg));
    let sgt = tag_of(|b| write_icmp_op(b, &ICmpOp::Sgt));
    let trunc = tag_of(|b| write_cast_op(b, &CastOp::Trunc));
    let sext = tag_of(|b| write_cast_op(b, &CastOp::SExt));
    // i32 is Ty tag 2, i8 tag 0, i64 tag 3, u8 tag 5; a tensor is tag 41 then the rank
    // then the element.
    assert_eq!(
        spell(&map_module()),
        vec![
            72, 41, 2, 2, // tensor_map tensor<i32, 2>
            3, 0, 1, 2, // (%0, %1, %2)
            6, // six nodes
            0, add, 2, 0, 1, // add i32 $0, $1
            1, neg, 2, 3, // neg i32 $3
            2, sgt, 2, 4, 2, // icmp sgt i32 $4, $2
            3, 2, 5, 4, 2, // select i32 $5, $4, $2
            4, trunc, 2, 0, 6, // trunc i32 $6 to i8
            4, sext, 0, 2, 7, // sext i8 $7 to i32
        ]
    );
    assert_eq!(
        spell(&reduce_module()),
        // tensor_reduce | tensor<i64, 1> | %0 | smax (6) | axes [0, 2] |
        // row_major (0)
        vec![73, 41, 1, 3, 0, 6, 2, 0, 2, 0]
    );
    assert_eq!(
        spell(&view_module()),
        vec![
            74, 41, 1, 2, // tensor_view tensor<i32, 1>
            0, // %0
            1, 1, // params [%1]
            5, // five nodes
            2, 0, // src_extent(0)
            1, 0, // param(0)
            4, 0, 1, // add($0, $1)
            3, 0, // coord(0)
            5, 3, 1, // sub($3, $1)
            1, 2, // shape [$2]
            1, 4, // index [$4]
            1, 2, // fill %2
        ]
    );
    // Every index node tag in declaration order, the literal a v64 (ten
    // bytes at `u64::MAX`), and an absent fill one zero byte.
    let every = spell(&every_index_node_module());
    let mut lit = Vec::new();
    write_v64(&mut lit, u64::MAX);
    let mut expected = vec![74, 41, 1, 5, 0, 1, 1, 11, 0];
    expected.extend_from_slice(&lit);
    expected.extend_from_slice(&[
        1, 0, 2, 1, 3, 0, 4, 0, 1, 5, 4, 2, 6, 5, 3, 7, 6, 1, 8, 7, 2, 9, 8, 1, 10, 9, 2, 1, 2, 2,
        9, 10, 0,
    ]);
    assert_eq!(every, expected);
}

/// Every reduction operator round trips at its declaration-order tag.
#[test]
fn every_reduction_operator_has_its_tag() {
    for (tag, op) in TensorReduceOp::ALL.into_iter().enumerate() {
        assert_eq!(usize::from(tensor_reduce_op_tag(op)), tag, "{op:?}");
        let byte = [u8::try_from(tag).expect("nine tags")];
        let mut reader = Reader::new(&byte);
        assert_eq!(read_tensor_reduce_op(&mut reader), Ok(op));
    }
}

/// A byte past each new tag space is refused by name, never read as the
/// nearest variant.
#[test]
fn bytes_past_each_tag_space_are_refused() {
    let mut reader = Reader::new(&[5, 0, 2, 0]);
    assert_eq!(
        read_tensor_map_node::<crate::NoExt>(&mut reader),
        Err(BinaryError::InvalidTag(5))
    );
    let mut reader = Reader::new(&[9]);
    assert_eq!(
        read_tensor_reduce_op(&mut reader),
        Err(BinaryError::InvalidTag(9))
    );
    let mut reader = Reader::new(&[1]);
    assert_eq!(
        read_tensor_reduce_order(&mut reader),
        Err(BinaryError::InvalidTag(1))
    );
    let mut reader = Reader::new(&[11, 0]);
    assert_eq!(
        read_tensor_index_expr(&mut reader),
        Err(BinaryError::InvalidTag(11))
    );
    // A fill byte other than 0 or 1.
    let mut bytes = spell(&view_module());
    let fill = bytes.len() - 2;
    assert_eq!(bytes[fill], 1);
    bytes[fill] = 2;
    let mut reader = Reader::new(&bytes);
    assert_eq!(
        read_inst::<crate::NoExt>(&mut reader).map(|_| ()),
        Err(BinaryError::InvalidTag(2))
    );
}

#[test]
fn bytes_below_their_version_are_refused_at_the_instruction_tag() {
    for (name, module, tag) in [
        ("map", map_module(), 72),
        ("reduce", reduce_module(), 73),
        ("view", view_module(), 74),
        ("every-index-node", every_index_node_module(), 74),
        ("map-only", map_only_module(), 72),
    ] {
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        // One version down still allocates the tensor type, so the reader
        // reaches the instruction.
        assert_eq!(
            deserialize_module(&relabel(&bytes, TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION - 1)),
            Err(BinaryError::InvalidTag(tag)),
            "{name}"
        );
    }
    // Every readable older label is refused. (Below the versions whose
    // function layout these bytes share, the reader stops at an earlier
    // field; the instruction tag is the refusal only where the layout is
    // otherwise the same.)
    let bytes = serialize_module(&map_only_module()).expect("serialize_module: test fixture");
    for version in MIN_READ_VERSION..TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION {
        assert!(
            deserialize_module(&relabel(&bytes, version)).is_err(),
            "a v{version} label carrying Inst tag 72 is refused"
        );
    }
}

#[test]
fn v38_projections_refuse_map_reduce_and_view_by_name() {
    for (name, module) in fixtures() {
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&module, options).err(),
                Some(BinaryProjectionError::TensorMapReduceViewRequiresV68),
                "{name}"
            );
        }
    }
    assert!(
        BinaryProjectionError::TensorMapReduceViewRequiresV68
            .to_string()
            .contains(&format!(
                "v{TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION} binary projection"
            ))
    );
}

/// The three instructions separate identities: no field of any is erased by
/// the digest. Each mutant changes exactly one field (of the instruction, or
/// of one map node) and must move `stable_digest`.
#[test]
fn every_field_moves_the_digest() {
    type Mutant = (&'static str, fn(&mut Inst));
    let map: [Mutant; 19] = [
        ("map ty", |i| {
            if let Inst::TensorMap { ty, .. } = i {
                *ty = tensor(Ty::I32, 1);
            }
        }),
        ("map args", |i| {
            if let Inst::TensorMap { args, .. } = i {
                args.swap(0, 1);
            }
        }),
        ("map body length", |i| {
            if let Inst::TensorMap { body, .. } = i {
                body.pop();
            }
        }),
        ("binop op", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::BinOp { op, .. } = &mut body[0]
            {
                *op = BinOp::Sub;
            }
        }),
        ("binop ty", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::BinOp { ty, .. } = &mut body[0]
            {
                *ty = Ty::I64;
            }
        }),
        ("binop lanes", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::BinOp { lhs, rhs, .. } = &mut body[0]
            {
                core::mem::swap(lhs, rhs);
            }
        }),
        ("unop op", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::UnOp { op, .. } = &mut body[1]
            {
                *op = UnOp::Not;
            }
        }),
        ("unop ty", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::UnOp { ty, .. } = &mut body[1]
            {
                *ty = Ty::I16;
            }
        }),
        ("unop operand", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::UnOp { operand, .. } = &mut body[1]
            {
                *operand = 0;
            }
        }),
        ("icmp op", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::ICmp { op, .. } = &mut body[2]
            {
                *op = ICmpOp::Slt;
            }
        }),
        ("icmp ty", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::ICmp { ty, .. } = &mut body[2]
            {
                *ty = Ty::I64;
            }
        }),
        ("icmp lanes", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::ICmp { lhs, rhs, .. } = &mut body[2]
            {
                core::mem::swap(lhs, rhs);
            }
        }),
        ("select ty", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::Select { ty, .. } = &mut body[3]
            {
                *ty = Ty::U32;
            }
        }),
        ("select cond", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::Select { cond, .. } = &mut body[3]
            {
                *cond = 0;
            }
        }),
        ("select lanes", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::Select {
                    then_lane,
                    else_lane,
                    ..
                } = &mut body[3]
            {
                core::mem::swap(then_lane, else_lane);
            }
        }),
        ("cast op", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::Cast { op, .. } = &mut body[4]
            {
                *op = CastOp::ZExt;
            }
        }),
        ("cast source", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::Cast { src_ty, .. } = &mut body[4]
            {
                *src_ty = Ty::U32;
            }
        }),
        ("cast destination", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::Cast { dst_ty, .. } = &mut body[4]
            {
                *dst_ty = Ty::I16;
            }
        }),
        ("cast operand", |i| {
            if let Inst::TensorMap { body, .. } = i
                && let Node::Cast { operand, .. } = &mut body[4]
            {
                *operand = 5;
            }
        }),
    ];
    let reduce: [Mutant; 4] = [
        ("reduce ty", |i| {
            if let Inst::TensorReduce { ty, .. } = i {
                *ty = tensor(Ty::I64, 2);
            }
        }),
        ("reduce src", |i| {
            if let Inst::TensorReduce { src, .. } = i {
                *src = v(1);
            }
        }),
        ("reduce op", |i| {
            if let Inst::TensorReduce { op, .. } = i {
                *op = TensorReduceOp::UMax;
            }
        }),
        ("reduce axes", |i| {
            if let Inst::TensorReduce { axes, .. } = i {
                axes[1] = 1;
            }
        }),
    ];
    let view: [Mutant; 8] = [
        ("view ty", |i| {
            if let Inst::TensorView { ty, .. } = i {
                *ty = tensor(Ty::I32, 2);
            }
        }),
        ("view src", |i| {
            if let Inst::TensorView { src, .. } = i {
                *src = v(2);
            }
        }),
        ("view params", |i| {
            if let Inst::TensorView { params, .. } = i {
                params.push(v(1));
            }
        }),
        ("view exprs", |i| {
            if let Inst::TensorView { exprs, .. } = i {
                exprs[4] = E::Sub(3, 0);
            }
        }),
        ("view expr kind", |i| {
            if let Inst::TensorView { exprs, .. } = i {
                exprs[0] = E::Lit(0);
            }
        }),
        ("view shape", |i| {
            if let Inst::TensorView { shape, .. } = i {
                shape[0] = 1;
            }
        }),
        ("view index", |i| {
            if let Inst::TensorView { index, .. } = i {
                index[0] = 3;
            }
        }),
        ("view fill", |i| {
            if let Inst::TensorView { fill, .. } = i {
                *fill = None;
            }
        }),
    ];
    for (base, mutants) in [
        (map_module(), &map[..]),
        (reduce_module(), &reduce[..]),
        (view_module(), &view[..]),
    ] {
        let original = base.stable_digest();
        for (name, mutate) in mutants {
            let mut module = base.clone();
            mutate(&mut module.functions[0].blocks[0].body[0].inst);
            assert_ne!(
                module.functions[0].blocks[0].body[0].inst,
                base.functions[0].blocks[0].body[0].inst,
                "{name}: the mutant changes nothing"
            );
            assert_ne!(module.stable_digest(), original, "{name}");
        }
    }
}

struct Admit;

impl ExecutionObserver for Admit {
    type Refusal = ();

    fn admit(&mut self, _progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        Ok(())
    }
}

/// The observed identity walk (its own collector and writer) states the same
/// identity as the canonical writer, header included, for every fixture.
#[test]
fn observed_identity_matches_the_canonical_writer() {
    for (name, module) in fixtures() {
        let mut observer = Admit;
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let site = ExecutionSite::Entry(FuncId::new(0));
        assert_eq!(
            module
                .stable_digest_observed(&mut session, site)
                .expect("observed identity: test fixture"),
            module.stable_digest(),
            "{name}"
        );
        assert_eq!(
            module
                .checked_stable_digest_observed(&mut session, site)
                .expect("checked observed identity: test fixture"),
            module.stable_digest(),
            "{name}"
        );
    }
}
