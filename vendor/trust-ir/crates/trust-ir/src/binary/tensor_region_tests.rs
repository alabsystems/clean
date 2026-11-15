// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The tensor region's first slice (PKG-U13a, Trust TENSOR-REOPEN):
//! `Ty::Tensor` (Ty tag 41) and `Inst::TensorContract` (Inst tag 71), both
//! read-gated on `TENSOR_FORMAT_VERSION`. The codec spells exactly what it is
//! given; whether a tensor's element is an integer and whether a
//! contraction's ranks and axes agree is the validator's to decide, so some
//! fixtures below are deliberately ill-typed.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, ObservedSession,
};
use crate::{Block, Function, InstrNode};

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

/// `f(%0: lhs, %1: rhs) -> ty` whose one instruction is `%2 =
/// tensor_contract ty %0, %1 batch [..] contract [..]`, returned. The tensor
/// types occur in the signature, the block parameters and the instruction's
/// inline result type.
fn contraction_module(
    ty: Ty,
    lhs: Ty,
    rhs: Ty,
    batch: Vec<(u32, u32)>,
    contract: Vec<(u32, u32)>,
) -> Module {
    let mut module = Module::new("tensor_region_codec");
    let sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![lhs.clone(), rhs.clone()],
            returns: vec![ty.clone()],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "contract", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((v(0), lhs));
    entry.params.push((v(1), rhs));
    entry.body.push(
        InstrNode::new(Inst::TensorContract {
            ty,
            lhs: v(0),
            rhs: v(1),
            batch,
            contract,
        })
        .with_results(vec![v(2)]),
    );
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    f.blocks.push(entry);
    module.functions.push(f);
    module
}

/// A matrix multiply: `tensor<i32, 2> x tensor<i32, 2> -> tensor<i32, 2>`,
/// `batch []`, `contract [1:0]`.
fn matmul_module() -> Module {
    contraction_module(
        tensor(Ty::I32, 2),
        tensor(Ty::I32, 2),
        tensor(Ty::I32, 2),
        vec![],
        vec![(1, 0)],
    )
}

/// A batched contraction with both pair lists populated:
/// `tensor<i64, 3> x tensor<i64, 3> -> tensor<i64, 3>`, `batch [0:0]`,
/// `contract [2:1]` (result rank `1 + 1 + 1`).
fn batched_module() -> Module {
    contraction_module(
        tensor(Ty::I64, 3),
        tensor(Ty::I64, 3),
        tensor(Ty::I64, 3),
        vec![(0, 0)],
        vec![(2, 1)],
    )
}

/// A contraction with NO tensor type anywhere (ill-typed on purpose: `ty`,
/// `lhs` and `rhs` are `i32`), so only the instruction's own raise can select
/// the tensor version and only Inst tag 71 is read-gated in its bytes.
fn contraction_only_module() -> Module {
    contraction_module(Ty::I32, Ty::I32, Ty::I32, vec![(0, 1)], vec![])
}

/// Tensor types in the type table only, no function: an integer element, a
/// float element and a tensor element (the last two refused by the
/// validator, never by the codec), so only the type's own raise can select
/// the tensor version.
fn type_table_module() -> Module {
    let mut module = Module::new("tensor_region_types");
    module.types.push(tensor(Ty::U8, 0));
    module.types.push(tensor(Ty::F32, 1));
    module.types.push(tensor(tensor(Ty::Usize, 2), 4));
    module
}

fn tensor_fixtures() -> Vec<(&'static str, Module)> {
    vec![
        ("matmul", matmul_module()),
        ("batched", batched_module()),
        ("contraction-only", contraction_only_module()),
        ("type-table", type_table_module()),
    ]
}

/// The tensor-free twin of [`matmul_module`]: the same shape at `i32`, with
/// a `BinOp::Mul` where the contraction was.
fn tensor_free_module() -> Module {
    let mut module = Module::new("tensor_region_codec");
    let sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "contract", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((v(0), Ty::I32));
    entry.params.push((v(1), Ty::I32));
    entry.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Mul,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_results(vec![v(2)]),
    );
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    f.blocks.push(entry);
    module.functions.push(f);
    module
}

fn the_contraction(module: &Module) -> &Inst {
    &module.functions[0].blocks[0].body[0].inst
}

#[test]
fn tensor_modules_round_trip_at_exactly_the_tensor_version() {
    for (name, module) in tensor_fixtures() {
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(header_version(&bytes), TENSOR_FORMAT_VERSION, "{name}");
        let (decoded, version) =
            deserialize_module_with_wire_version(&bytes).expect("lossless tensor module");
        assert_eq!(version.get(), TENSOR_FORMAT_VERSION, "{name}");
        assert_eq!(decoded, module, "{name}");
        assert_eq!(decoded.stable_digest(), module.stable_digest(), "{name}");
        assert_eq!(
            serialize_module(&decoded).expect("serialize_module: decoded fixture"),
            bytes,
            "{name}: re-encoding is byte-identical"
        );
    }
}

/// The exact tag-41 and tag-71 spellings, pinned byte for byte so a
/// reordering is a failure, not a silent re-encoding.
#[test]
fn tensor_wire_spellings_are_pinned() {
    let ty = tensor(Ty::I32, 2);
    let ty_bytes = SealedStringPool::by_replay(|pool, bytes| write_ty(bytes, pool, &ty));
    // tag 41 | rank 2 | element i32 (tag 2)
    assert_eq!(ty_bytes, vec![41, 2, 2]);

    let matmul = matmul_module();
    let encoded = SealedStringPool::by_replay(|pool, bytes| {
        write_inst(bytes, pool, None, the_contraction(&matmul));
    });
    // tag 71 | tensor<i32, 2> | lhs %0 | rhs %1 | 0 batch pairs |
    // 1 contract pair (1, 0)
    assert_eq!(encoded, vec![71, 41, 2, 2, 0, 1, 0, 1, 1, 0]);

    let batched = batched_module();
    let encoded = SealedStringPool::by_replay(|pool, bytes| {
        write_inst(bytes, pool, None, the_contraction(&batched));
    });
    // tag 71 | tensor<i64, 3> | lhs %0 | rhs %1 | 1 batch pair (0, 0) |
    // 1 contract pair (2, 1)
    assert_eq!(encoded, vec![71, 41, 3, 3, 0, 1, 1, 0, 0, 1, 2, 1]);
}

#[test]
fn tensor_bytes_below_their_version_are_refused_at_the_tag() {
    for (name, module, tag) in [
        ("matmul", matmul_module(), 41),
        ("batched", batched_module(), 41),
        ("contraction-only", contraction_only_module(), 71),
        ("type-table", type_table_module(), 41),
    ] {
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(
            deserialize_module(&relabel(&bytes, TENSOR_FORMAT_VERSION - 1)),
            Err(BinaryError::InvalidTag(tag)),
            "{name}: the same bytes under the previous header are refused at tag {tag}"
        );
    }
    // The signature is the first section after the module name, and its
    // first parameter is a tensor, so EVERY readable older label reaches tag
    // 41 before anything else could differ.
    let bytes = serialize_module(&matmul_module()).expect("serialize_module: test fixture");
    for version in MIN_READ_VERSION..TENSOR_FORMAT_VERSION {
        // v26..=v28 are refused before any tag is read (ambiguous lineage).
        if AMBIGUOUS_LINEAGE_VERSIONS.contains(&version) {
            continue;
        }
        assert_eq!(
            deserialize_module(&relabel(&bytes, version)),
            Err(BinaryError::InvalidTag(41)),
            "a v{version} label carrying Ty tag 41 is refused"
        );
    }
}

#[test]
fn v38_projections_refuse_the_tensor_region_by_name() {
    for (name, module) in tensor_fixtures() {
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&module, options).err(),
                Some(BinaryProjectionError::TensorRequiresV67),
                "{name}"
            );
        }
    }
    assert!(
        BinaryProjectionError::TensorRequiresV67
            .to_string()
            .contains(&format!("v{TENSOR_FORMAT_VERSION} binary projection"))
    );
}

#[test]
fn a_module_without_tensors_keeps_its_older_version() {
    let plain = tensor_free_module();
    let bytes = serialize_module(&plain).expect("serialize_module: test fixture");
    assert!(header_version(&bytes) < TENSOR_FORMAT_VERSION);
    assert_eq!(header_version(&bytes), BASE_FORMAT_VERSION);
    assert_eq!(deserialize_module(&bytes).unwrap(), plain);
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        let options = ModuleBinaryOptions {
            body,
            ..Default::default()
        };
        assert!(ProjectedModuleBinaryPlan::try_new(&plain, options).is_ok());
    }

    // A module at a later feature version keeps THAT version: a storage-only
    // type selects v64, never the tensor version.
    let mut storage = Module::new("tensor_region_storage");
    storage
        .types
        .push(Ty::Storage(crate::StorageLayout::new(80, 8)));
    let bytes = serialize_module(&storage).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), STORAGE_LAYOUT_FORMAT_VERSION);
    assert_eq!(deserialize_module(&bytes).unwrap(), storage);

    // And the tensor separates the two identities.
    assert_ne!(plain.stable_digest(), matmul_module().stable_digest());
}

struct Admit;

impl ExecutionObserver for Admit {
    type Refusal = ();

    fn admit(&mut self, _progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        Ok(())
    }
}

/// The observed identity walk (its own collector and writer) states the same
/// identity as the canonical writer, header included, for every tensor
/// fixture and for a storage-only type (whose v64 raise the observed
/// collector now mirrors too).
#[test]
fn observed_identity_matches_the_canonical_writer_on_tensor_modules() {
    let mut storage = Module::new("tensor_region_storage");
    storage
        .types
        .push(Ty::Storage(crate::StorageLayout::new(80, 8)));
    let mut modules = tensor_fixtures();
    modules.push(("storage", storage));
    for (name, module) in modules {
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
