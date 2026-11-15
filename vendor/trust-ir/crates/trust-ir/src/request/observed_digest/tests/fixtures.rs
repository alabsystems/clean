// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

/// Identity fixtures deliberately cover every carrier. This does not attest
/// semantic validity or issue source/evidence authority for the added claims.
pub(super) fn populate(value: &mut NativeVerificationBundle) {
    value.evidence_bundles = value
        .requests
        .iter()
        .enumerate()
        .map(|(index, request)| {
            value
                .evidence_bundle_for_request(
                    request,
                    vec![
                        NativeEvidenceArtifact::new(
                            "same",
                            NativeEvidenceArtifactKind::Other,
                            ProofDigest::sha256([3; 32]),
                        ),
                        NativeEvidenceArtifact::new(
                            "same",
                            NativeEvidenceArtifactKind::ReplayTranscript,
                            ProofDigest::sha256([2; 32]),
                        ),
                        NativeEvidenceArtifact::new(
                            "same",
                            NativeEvidenceArtifactKind::Other,
                            ProofDigest::sha256([1; 32]),
                        ),
                        NativeEvidenceArtifact::new(
                            format!("variant-{index}"),
                            NativeEvidenceArtifactKind::NativeCompiledArtifact,
                            ProofDigest::sha256([4; 32]),
                        ),
                    ],
                )
                .expect("all three typed evidence variants")
        })
        .collect();
    let layout = value
        .module
        .ty_layout_shape(&Ty::I32)
        .expect("i32 fixture layout");
    value.compiler_facts.adt_layouts.push(NativeAdtLayoutFact {
        id: NativeCompilerFactId::new(20),
        ty: Ty::I32,
        layout: layout.clone(),
        enum_layout: None,
    });
    let wide = Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id: 7 });
    value
        .compiler_facts
        .fat_pointers
        .push(NativeFatPointerFact {
            id: NativeCompilerFactId::new(30),
            layout: wide
                .pointer_layout_shape(value.module.pointer_bits())
                .expect("fat pointer fixture layout"),
            ty: wide.clone(),
        });
    value
        .compiler_facts
        .trait_object_metadata
        .push(NativeTraitObjectMetadataFact {
            id: NativeCompilerFactId::new(31),
            ty: wide,
            source_ty: Some(Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id: 3 })),
            trait_id: 7,
            source_trait_id: Some(3),
            upcast_path: vec![3, 7],
            vtable_symbol: "vtable_λ".into(),
            stable_digest: ProofDigest::sha256([31; 32]),
            function: Some(FuncId::new(0)),
            obligations: vec![ProofId::new(1), ProofId::new(0)],
        });
    value
        .compiler_facts
        .pointer_offsets
        .push(NativePointerOffsetFact {
            id: NativeCompilerFactId::new(40),
            function: FuncId::new(0),
            result: Some(ValueId::new(20)),
            base: ValueId::new(0),
            base_ty: Ty::Ptr,
            pointee_ty: Ty::I32,
            element_layout: layout,
            stride_bits: 32,
            offset: ValueId::new(1),
            offset_ty: Ty::I64,
            signed_offset_const: Some(-1),
            provenance: NativePointerOffsetProvenance::Unsupported(NativeUnsupportedMode::new(
                NativeUnsupportedModeReason::Other,
                "identity-only refusal payload",
            )),
            span: None,
            obligations: vec![ProofId::new(1)],
        });
    value.compiler_facts.casts.push(NativeCastFact {
        id: NativeCompilerFactId::new(41),
        function: FuncId::new(0),
        result: Some(ValueId::new(21)),
        op: CastOp::Bitcast,
        source_ty: Ty::I32,
        target_ty: Ty::U32,
        evidence: CastLayoutEvidence::SameSize {
            size_bits: 32,
            src_align_bits: Some(32),
            dst_align_bits: Some(32),
        },
        span: None,
        obligations: vec![ProofId::new(0)],
    });
    value.compiler_facts.monomorphizations[0]
        .generic_args
        .extend([
            NativeGenericArg::Const {
                ty: Ty::U128,
                value: Constant::U128(u128::MAX),
            },
            NativeGenericArg::LifetimeErased,
            NativeGenericArg::Placeholder { index: 9 },
        ]);
    value.compiler_facts.obligation_sources[0].facts.extend([
        NativeCompilerFactRef::AdtLayout(NativeCompilerFactId::new(20)),
        NativeCompilerFactRef::FatPointer(NativeCompilerFactId::new(30)),
        NativeCompilerFactRef::TraitObjectMetadata(NativeCompilerFactId::new(31)),
        NativeCompilerFactRef::PointerOffset(NativeCompilerFactId::new(40)),
        NativeCompilerFactRef::Cast(NativeCompilerFactId::new(41)),
    ]);
}
