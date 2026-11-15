// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::request::{NativeUnsupportedMode, NativeUnsupportedModeReason};
use crate::{Block, BlockId, CastOp, FuncTyId, ICmpOp, ProofDigest, ProofDigestAlgorithm};

mod parity;
mod stops;

struct Fixture {
    module: Module,
    pointer: NativePointerOffsetFact,
    cast: NativeCastFact,
    metadata: NativeTraitObjectMetadataFact,
    functions: BTreeSet<FuncId>,
    obligations: BTreeSet<ProofId>,
}
fn fixture() -> Fixture {
    let mut module = super::module();
    let mut function = Function::new(
        FuncId::new(7),
        "primitive-facts",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::Isize)];
    block.body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::U32,
            base: ValueId::new(0),
            indices: vec![ValueId::new(1)],
            inbounds: false,
        })
        .with_result(ValueId::new(2)),
    );
    block.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: Ty::U32,
            dst_ty: Ty::U32,
            operand: ValueId::new(9),
        })
        .with_result(ValueId::new(4)),
    );
    function.blocks.push(block);
    module.functions.push(function);
    let pointer = NativePointerOffsetFact {
        id: NativeCompilerFactId::new(4),
        function: FuncId::new(7),
        result: Some(ValueId::new(2)),
        base: ValueId::new(0),
        base_ty: Ty::Ptr,
        pointee_ty: Ty::U32,
        element_layout: (*LayoutTable::new(&module).ty_layout(&Ty::U32).unwrap()).clone(),
        stride_bits: 32,
        offset: ValueId::new(1),
        offset_ty: Ty::Isize,
        signed_offset_const: Some(1),
        provenance: NativePointerOffsetProvenance::SameAsBase,
        span: None,
        obligations: vec![ProofId::new(1)],
    };
    let cast = NativeCastFact {
        id: NativeCompilerFactId::new(5),
        function: FuncId::new(7),
        result: Some(ValueId::new(4)),
        op: CastOp::Bitcast,
        source_ty: Ty::U32,
        target_ty: Ty::U32,
        evidence: CastLayoutEvidence::SameSize {
            size_bits: 32,
            src_align_bits: Some(32),
            dst_align_bits: Some(32),
        },
        span: None,
        obligations: vec![ProofId::new(1)],
    };
    let metadata = NativeTraitObjectMetadataFact {
        id: NativeCompilerFactId::new(6),
        ty: Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 9 }),
        source_ty: Some(Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 8 })),
        trait_id: 9,
        source_trait_id: Some(8),
        upcast_path: vec![8, 9],
        vtable_symbol: "vtable".into(),
        stable_digest: ProofDigest::sha256([5; 32]),
        function: Some(FuncId::new(7)),
        obligations: vec![ProofId::new(1)],
    };
    Fixture {
        module,
        pointer,
        cast,
        metadata,
        functions: BTreeSet::from([FuncId::new(7)]),
        obligations: BTreeSet::from([ProofId::new(1)]),
    }
}

#[derive(Clone, Copy)]
enum Mode {
    Pointer,
    PointerValues,
    Cast,
    CastResult,
    Metadata,
    Upcast,
}
fn invoke(f: &Fixture, mode: Mode, session: &mut ObservedSession<'_, Observer>) -> R<Vec<E>> {
    match mode {
        Mode::Pointer => {
            let table = LayoutTable::new_observed(&f.module, session, site())?;
            f.pointer.validation_errors_observed(
                &table,
                &f.functions,
                &f.obligations,
                session,
                site(),
            )
        }
        Mode::PointerValues => f.pointer.value_errors_observed(&f.module, session, site()),
        Mode::Cast => {
            let table = LayoutTable::new_observed(&f.module, session, site())?;
            f.cast
                .validation_errors_observed(&table, &f.functions, &f.obligations, session, site())
        }
        Mode::CastResult => f.cast.result_errors_observed(&f.module, session, site()),
        Mode::Metadata => f.metadata.validation_errors_observed(
            &f.module,
            &f.functions,
            &f.obligations,
            session,
            site(),
        ),
        Mode::Upcast => f.metadata.upcast_errors_observed(session, site()),
    }
}
fn ordinary(f: &Fixture, mode: Mode) -> Vec<E> {
    let mut errors = Vec::new();
    match mode {
        Mode::Pointer => crate::request::validate_pointer_offset_fact(
            &LayoutTable::new(&f.module),
            &f.pointer,
            &f.functions,
            &f.obligations,
            &mut errors,
        ),
        Mode::PointerValues => {
            crate::request::validate_pointer_offset_fact_values(&f.module, &f.pointer, &mut errors)
        }
        Mode::Cast => crate::request::validate_cast_fact(
            &LayoutTable::new(&f.module),
            &f.cast,
            &f.functions,
            &f.obligations,
            &mut errors,
        ),
        Mode::CastResult => {
            crate::request::validate_cast_fact_result(&f.module, &f.cast, &mut errors)
        }
        Mode::Metadata => crate::request::validate_trait_object_metadata_fact(
            &f.module,
            &f.metadata,
            &f.functions,
            &f.obligations,
            &mut errors,
        ),
        Mode::Upcast => crate::request::validate_trait_object_upcast_metadata_fact(
            &f.metadata,
            NativeCompilerFactRef::TraitObjectMetadata(f.metadata.id),
            &mut errors,
        ),
    }
    errors
}
fn parity(f: &Fixture, mode: Mode) -> Vec<E> {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual = invoke(f, mode, &mut session).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(actual, ordinary(f, mode));
    actual
}
