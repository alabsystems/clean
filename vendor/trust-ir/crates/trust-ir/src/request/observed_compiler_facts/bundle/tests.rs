// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::interpret::InterpretOptions;
use crate::request::{NativeUnsupportedMode, NativeUnsupportedModeReason};
use crate::{CastOp, Endianness, StructDef, StructId, StructRepr, TargetInfo};
mod parity;
mod stops;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    stop_retirement: bool,
    work: usize,
    bytes: usize,
    work_limit: Option<usize>,
    byte_limit: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        if self.stop_retirement && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_limit.is_some_and(|limit| self.work > limit) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|limit| self.bytes > limit) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(974))
}

fn fixture() -> NativeVerificationBundle {
    let mut bundle = crate::request::tests::native_bundle();
    bundle.module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    bundle.module.structs.push(StructDef {
        id: StructId::new(9),
        name: "fact-struct".into(),
        fields: vec![crate::FieldDef {
            name: "field".into(),
            ty: Ty::U32,
            offset: Some(0),
        }],
        size: Some(4),
        align: Some(4),
        repr: StructRepr::Rust,
        origin: None,
    });
    let block = &mut bundle.module.functions[0].blocks[0];
    block
        .params
        .extend([(ValueId::new(1), Ty::Ptr), (ValueId::new(2), Ty::Isize)]);
    block.body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::U32,
            base: ValueId::new(1),
            indices: vec![ValueId::new(2)],
            inbounds: false,
        })
        .with_result(ValueId::new(3)),
    );
    block.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: Ty::I32,
            dst_ty: Ty::I32,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(4)),
    );
    add_facts(&mut bundle);
    bundle
}

fn add_facts(bundle: &mut NativeVerificationBundle) {
    let id = NativeCompilerFactId::new(4);
    let table = LayoutTable::new(&bundle.module);
    let adt = (*table.ty_layout(&Ty::Struct(StructId::new(9))).unwrap()).clone();
    let element = (*table.ty_layout(&Ty::U32).unwrap()).clone();
    drop(table);
    bundle.compiler_facts.adt_layouts.push(NativeAdtLayoutFact {
        id,
        ty: Ty::Struct(StructId::new(9)),
        layout: adt,
        enum_layout: None,
    });
    let trait_ty = Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id: 9 });
    bundle
        .compiler_facts
        .fat_pointers
        .push(NativeFatPointerFact {
            id,
            ty: trait_ty.clone(),
            layout: crate::PointerLayoutShape::fat(
                64,
                crate::PointerMetadataShape::VTable { trait_id: 9 },
            ),
        });
    bundle
        .compiler_facts
        .trait_object_metadata
        .push(NativeTraitObjectMetadataFact {
            id,
            ty: trait_ty,
            source_ty: None,
            trait_id: 9,
            source_trait_id: None,
            upcast_path: vec![],
            vtable_symbol: "vtable".into(),
            stable_digest: ProofDigest::sha256([9; 32]),
            function: Some(FuncId::new(0)),
            obligations: vec![ProofId::new(0)],
        });
    bundle
        .compiler_facts
        .pointer_offsets
        .push(NativePointerOffsetFact {
            id,
            function: FuncId::new(0),
            result: Some(ValueId::new(3)),
            base: ValueId::new(1),
            base_ty: Ty::Ptr,
            pointee_ty: Ty::U32,
            element_layout: element,
            stride_bits: 32,
            offset: ValueId::new(2),
            offset_ty: Ty::Isize,
            signed_offset_const: Some(1),
            provenance: NativePointerOffsetProvenance::SameAsBase,
            span: None,
            obligations: vec![ProofId::new(0)],
        });
    bundle.compiler_facts.casts.push(NativeCastFact {
        id,
        function: FuncId::new(0),
        result: Some(ValueId::new(4)),
        op: CastOp::Bitcast,
        source_ty: Ty::I32,
        target_ty: Ty::I32,
        evidence: CastLayoutEvidence::SameSize {
            size_bits: 32,
            src_align_bits: Some(32),
            dst_align_bits: Some(32),
        },
        span: None,
        obligations: vec![ProofId::new(0)],
    });
    bundle.compiler_facts.obligation_sources[0].facts.extend([
        NativeCompilerFactRef::AdtLayout(id),
        NativeCompilerFactRef::FatPointer(id),
        NativeCompilerFactRef::TraitObjectMetadata(id),
        NativeCompilerFactRef::PointerOffset(id),
        NativeCompilerFactRef::Cast(id),
    ]);
}

fn family(error: &E) -> bool {
    matches!(
        error,
        E::DuplicateModuleObligationId(_)
            | E::DuplicateCompilerFactId(_)
            | E::DuplicateMonomorphizationId(_)
            | E::InvalidCompilerFact { .. }
            | E::UnknownCompilerFactFunction { .. }
            | E::UnknownCompilerFactObligation { .. }
            | E::DuplicateObligationSource(_)
            | E::InvalidPublicObligationId { .. }
            | E::DuplicatePublicObligationSource { .. }
            | E::UnknownObligationSource(_)
            | E::UnknownObligationSourceFunction { .. }
            | E::MissingObligationSource { .. }
            | E::MissingEmbeddedObligationSource { .. }
            | E::MissingEmbeddedPublicObligationIdentity { .. }
            | E::InvalidEmbeddedObligationSource { .. }
            | E::EmbeddedPublicObligationIdMismatch { .. }
            | E::EmbeddedObligationSourceSpanMismatch { .. }
            | E::UnknownMonomorphization { .. }
            | E::UnknownCompilerFactReference { .. }
            | E::MissingObligationSourceCastFact { .. }
            | E::MissingObligationSourcePointerOffsetFact { .. }
            | E::MissingObligationSourceTraitObjectMetadataFact { .. }
            | E::ObligationSourceFactMonomorphizationMismatch { .. }
            | E::ObligationSourceFactFunctionMismatch { .. }
            | E::ObligationSourceFactObligationMismatch { .. }
    )
}
fn ordinary(bundle: &NativeVerificationBundle) -> Vec<E> {
    // The original private constituent is exercised through its public caller.
    // Retain exactly its error family; request-only span/assertion checks and
    // unrelated whole-bundle checks are deliberately outside this oracle.
    bundle
        .validate()
        .err()
        .unwrap_or_default()
        .into_iter()
        .filter(family)
        .collect()
}
fn parity(bundle: &NativeVerificationBundle) -> Vec<E> {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual = bundle
        .compiler_fact_errors_observed(&mut session, site())
        .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(actual, ordinary(bundle));
    actual
}
