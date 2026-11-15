// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The tensor region's gather and scatter (PKG-U13d, SPEC_RATIFICATIONS §26):
//! `Inst::TensorGather` (Inst tag 75) and `Inst::TensorScatter` (76), each
//! read-gated on `TENSOR_GATHER_SCATTER_FORMAT_VERSION`. The codec spells
//! exactly what it is given; whether the coordinate operands match the data's
//! rank or the result's is the validator's to decide (rules G1-G3, S1-S3), so
//! two fixtures below are deliberately ill-typed.

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

/// `f(params..) -> result` whose one instruction is `inst` (its result the
/// value after the parameters), returned.
fn one_instruction_module(params: Vec<Ty>, result: Ty, inst: Inst) -> Module {
    let mut module = Module::new("tensor_gather_scatter_codec");
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

/// A two-axis gather whose coordinate tensors have different elements:
/// `tensor_gather tensor<i32, 1> %0 coords [%1, %2]` of a `tensor<i32, 2>`
/// with a `tensor<i64, 1>` and a `tensor<u8, 1>`.
fn gather_module() -> Module {
    one_instruction_module(
        vec![tensor(Ty::I32, 2), tensor(Ty::I64, 1), tensor(Ty::U8, 1)],
        tensor(Ty::I32, 1),
        Inst::TensorGather {
            ty: tensor(Ty::I32, 1),
            data: v(0),
            coords: vec![v(1), v(2)],
        },
    )
}

/// A two-axis scatter: `tensor_scatter tensor<i32, 2> %0, %1 coords [%2,
/// %3]` of a `tensor<i32, 1>` source with a `tensor<i64, 1>` and a
/// `tensor<u8, 1>`.
fn scatter_module() -> Module {
    one_instruction_module(
        vec![
            tensor(Ty::I32, 2),
            tensor(Ty::I32, 1),
            tensor(Ty::I64, 1),
            tensor(Ty::U8, 1),
        ],
        tensor(Ty::I32, 2),
        Inst::TensorScatter {
            ty: tensor(Ty::I32, 2),
            init: v(0),
            src: v(1),
            coords: vec![v(2), v(3)],
        },
    )
}

/// A gather with NO tensor type anywhere (ill-typed on purpose: every type
/// is `i32`), so only the instruction's own raise can select the version, and
/// only Inst tag 75 is read-gated in its bytes.
fn gather_only_module() -> Module {
    one_instruction_module(
        vec![Ty::I32],
        Ty::I32,
        Inst::TensorGather {
            ty: Ty::I32,
            data: v(0),
            coords: vec![v(0)],
        },
    )
}

/// The scatter twin of [`gather_only_module`] (Inst tag 76).
fn scatter_only_module() -> Module {
    one_instruction_module(
        vec![Ty::I32],
        Ty::I32,
        Inst::TensorScatter {
            ty: Ty::I32,
            init: v(0),
            src: v(0),
            coords: vec![v(0)],
        },
    )
}

/// An empty coordinate list (rules G2 and S2 refuse it; the codec spells it).
fn empty_coordinates_module() -> Module {
    one_instruction_module(
        vec![tensor(Ty::I8, 0)],
        tensor(Ty::I8, 0),
        Inst::TensorGather {
            ty: tensor(Ty::I8, 0),
            data: v(0),
            coords: vec![],
        },
    )
}

fn fixtures() -> Vec<(&'static str, Module)> {
    vec![
        ("gather", gather_module()),
        ("scatter", scatter_module()),
        ("gather-only", gather_only_module()),
        ("scatter-only", scatter_only_module()),
        ("empty-coordinates", empty_coordinates_module()),
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

#[test]
fn modules_round_trip_at_exactly_the_gather_scatter_version() {
    for (name, module) in fixtures() {
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(
            header_version(&bytes),
            TENSOR_GATHER_SCATTER_FORMAT_VERSION,
            "{name}"
        );
        let (decoded, version) =
            deserialize_module_with_wire_version(&bytes).expect("lossless module");
        assert_eq!(
            version.get(),
            TENSOR_GATHER_SCATTER_FORMAT_VERSION,
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

/// The exact tag-75 and tag-76 spellings, pinned byte for byte so a
/// reordering is a failure, not a silent re-encoding: the result type, then
/// the operands in field order, `coords` a counted value-id list.
#[test]
fn wire_spellings_are_pinned() {
    // i32 is Ty tag 2, i8 tag 0; a tensor is tag 41 then the rank then the
    // element.
    assert_eq!(
        spell(&gather_module()),
        vec![
            75, 41, 1, 2, // tensor_gather tensor<i32, 1>
            0, // %0
            2, 1, 2, // coords [%1, %2]
        ]
    );
    assert_eq!(
        spell(&scatter_module()),
        vec![
            76, 41, 2, 2, // tensor_scatter tensor<i32, 2>
            0, 1, // %0, %1
            2, 2, 3, // coords [%2, %3]
        ]
    );
    assert_eq!(spell(&gather_only_module()), vec![75, 2, 0, 1, 0]);
    assert_eq!(spell(&scatter_only_module()), vec![76, 2, 0, 0, 1, 0]);
    assert_eq!(spell(&empty_coordinates_module()), vec![75, 41, 0, 0, 0, 0]);
}

/// A truncated instruction is refused, never read with a defaulted field.
#[test]
fn truncated_instructions_are_refused() {
    for (name, module) in [("gather", gather_module()), ("scatter", scatter_module())] {
        let bytes = spell(&module);
        for cut in 1..bytes.len() {
            let mut reader = Reader::new(&bytes[..cut]);
            reader.version = TENSOR_GATHER_SCATTER_FORMAT_VERSION;
            assert!(
                read_inst::<crate::NoExt>(&mut reader).is_err(),
                "{name}: {cut} of {} bytes read as an instruction",
                bytes.len()
            );
        }
    }
}

#[test]
fn bytes_below_their_version_are_refused_at_the_instruction_tag() {
    for (name, module, tag) in [
        ("gather", gather_module(), 75),
        ("scatter", scatter_module(), 76),
        ("gather-only", gather_only_module(), 75),
        ("scatter-only", scatter_only_module(), 76),
        ("empty-coordinates", empty_coordinates_module(), 75),
    ] {
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        // One version down still allocates the tensor type, so the reader
        // reaches the instruction.
        assert_eq!(
            deserialize_module(&relabel(&bytes, TENSOR_GATHER_SCATTER_FORMAT_VERSION - 1)),
            Err(BinaryError::InvalidTag(tag)),
            "{name}"
        );
    }
    // Every readable older label is refused. (Below the versions whose
    // function layout these bytes share, the reader stops at an earlier
    // field; the instruction tag is the refusal only where the layout is
    // otherwise the same.)
    for (name, module) in [
        ("gather-only", gather_only_module()),
        ("scatter-only", scatter_only_module()),
    ] {
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        for version in MIN_READ_VERSION..TENSOR_GATHER_SCATTER_FORMAT_VERSION {
            assert!(
                deserialize_module(&relabel(&bytes, version)).is_err(),
                "{name}: a v{version} label carrying its instruction tag is refused"
            );
        }
    }
}

#[test]
fn v38_projections_refuse_gather_and_scatter_by_name() {
    for (name, module) in fixtures() {
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&module, options).err(),
                Some(BinaryProjectionError::TensorGatherScatterRequiresV69),
                "{name}"
            );
        }
    }
    assert!(
        BinaryProjectionError::TensorGatherScatterRequiresV69
            .to_string()
            .contains(&format!(
                "v{TENSOR_GATHER_SCATTER_FORMAT_VERSION} binary projection"
            ))
    );
}

/// The two instructions separate identities: no field of either is erased by
/// the digest. Each mutant changes exactly one field and must move
/// `stable_digest`.
#[test]
fn every_field_moves_the_digest() {
    type Mutant = (&'static str, fn(&mut Inst));
    let gather: [Mutant; 4] = [
        ("gather ty", |i| {
            if let Inst::TensorGather { ty, .. } = i {
                *ty = tensor(Ty::I32, 2);
            }
        }),
        ("gather data", |i| {
            if let Inst::TensorGather { data, .. } = i {
                *data = v(1);
            }
        }),
        ("gather coordinate order", |i| {
            if let Inst::TensorGather { coords, .. } = i {
                coords.swap(0, 1);
            }
        }),
        ("gather coordinate count", |i| {
            if let Inst::TensorGather { coords, .. } = i {
                coords.push(v(1));
            }
        }),
    ];
    let scatter: [Mutant; 5] = [
        ("scatter ty", |i| {
            if let Inst::TensorScatter { ty, .. } = i {
                *ty = tensor(Ty::I32, 1);
            }
        }),
        ("scatter init", |i| {
            if let Inst::TensorScatter { init, .. } = i {
                *init = v(1);
            }
        }),
        ("scatter src", |i| {
            if let Inst::TensorScatter { src, .. } = i {
                *src = v(0);
            }
        }),
        ("scatter coordinate order", |i| {
            if let Inst::TensorScatter { coords, .. } = i {
                coords.swap(0, 1);
            }
        }),
        ("scatter coordinate count", |i| {
            if let Inst::TensorScatter { coords, .. } = i {
                coords.pop();
            }
        }),
    ];
    for (base, mutants) in [
        (gather_module(), &gather[..]),
        (scatter_module(), &scatter[..]),
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
    // The gather and the scatter of the same operand list are different
    // instructions.
    let as_gather = gather_only_module();
    let as_scatter = scatter_only_module();
    assert_ne!(as_gather.stable_digest(), as_scatter.stable_digest());
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
