// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact existing canonical field/tag spelling, with fallible inner writes.

use super::*;

pub(super) fn write_proof_formula<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    formula: &ProofFormula,
) -> Result {
    out.poll()?;
    write_str(out, &formula.schema)?;
    write_str(out, &formula.payload)?;
    write_option_str(out, formula.smtlib.as_deref())?;
    write_option_str(out, formula.sort.as_deref())?;

    Ok(())
}

pub(super) fn write_replay_atom_kind<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    kind: NativeReplayAtomKind,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match kind {
            NativeReplayAtomKind::Assumption => 0,
            NativeReplayAtomKind::Assertion => 1,
        },
    )?;

    Ok(())
}

pub(super) fn write_option_proof_id<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    value: Option<ProofId>,
) -> Result {
    out.poll()?;
    match value {
        None => write_u8(out, 0)?,
        Some(value) => {
            write_u8(out, 1)?;
            write_u32(out, value.index())?;
        }
    }

    Ok(())
}

pub(super) fn write_replay_atom<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    atom: &NativeReplayAtom,
) -> Result {
    out.poll()?;
    write_u32(out, atom.id.index())?;
    write_replay_atom_kind(out, atom.kind)?;
    write_proof_formula(out, &atom.formula)?;
    write_digest(out, &atom.payload_digest)?;
    write_option_proof_id(out, atom.obligation)?;
    write_option_assertion_id(out, atom.assertion_id)?;
    write_option_source_span(out, atom.span)?;

    Ok(())
}

pub(super) fn write_unsupported_mode_reason<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    reason: NativeUnsupportedModeReason,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match reason {
            NativeUnsupportedModeReason::UnsupportedVerifierMode => 0,
            NativeUnsupportedModeReason::UnsupportedFormulaSchema => 1,
            NativeUnsupportedModeReason::UnsupportedCompilerFact => 2,
            NativeUnsupportedModeReason::MissingSourceSpan => 3,
            NativeUnsupportedModeReason::MissingReplayTranscript => 4,
            NativeUnsupportedModeReason::Other => 5,
        },
    )?;

    Ok(())
}

pub(super) fn write_unsupported_mode<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    unsupported: &NativeUnsupportedMode,
) -> Result {
    out.poll()?;
    write_unsupported_mode_reason(out, unsupported.reason)?;
    write_str(out, &unsupported.detail)?;

    Ok(())
}

pub(super) fn write_certificate_ref<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    cert: &ProofCertificateRef,
) -> Result {
    out.poll()?;
    write_u32(out, cert.obligation.index())?;
    write_str(out, &cert.prover)?;
    write_digest(out, &cert.evidence_digest)?;

    Ok(())
}

pub(super) fn write_trust_vc_mode<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    mode: TrustVcVerificationMode,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match mode {
            TrustVcVerificationMode::ImportProofCertificates => 0,
            TrustVcVerificationMode::MergeProofCertificates => 1,
            TrustVcVerificationMode::DischargeProofObligations => 2,
        },
    )?;

    Ok(())
}

pub(super) fn write_trust_vc_options<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    options: &TrustVcRequestOptions,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match options.memory_semantics {
            TrustVcMemorySemantics::RustMir => 0,
            TrustVcMemorySemantics::TrustIr => 1,
            TrustVcMemorySemantics::StackedBorrows => 2,
        },
    )?;
    write_u8(
        out,
        match options.trusted_evidence {
            TrustVcTrustedEvidencePolicy::Reject => 0,
            TrustVcTrustedEvidencePolicy::AllowWithDiagnostic => 1,
            TrustVcTrustedEvidencePolicy::Allow => 2,
        },
    )?;
    write_u8(
        out,
        match options.merge_strategy {
            TrustVcMergeStrategy::RequireSameObligation => 0,
            TrustVcMergeStrategy::UnionDischargedObligations => 1,
            TrustVcMergeStrategy::PreferNewestLineage => 2,
        },
    )?;
    write_bool(out, options.require_replay_identity)?;

    Ok(())
}

pub(super) fn write_trust_mc_mode<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    mode: TrustMcVerificationMode,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match mode {
            TrustMcVerificationMode::BoundedModelCheck => 0,
            TrustMcVerificationMode::Chc => 1,
            TrustMcVerificationMode::Pdr => 2,
        },
    )?;

    Ok(())
}

pub(super) fn write_trust_mc_options<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    options: &TrustMcRequestOptions,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match options.memory_model {
            TrustMcMemoryModel::TrustIrPlaces => 0,
            TrustMcMemoryModel::FlatArrays => 1,
            TrustMcMemoryModel::StackedBorrows => 2,
        },
    )?;
    write_u8(
        out,
        match options.arithmetic_model {
            TrustMcArithmeticModel::FixedWidthBitvectors => 0,
            TrustMcArithmeticModel::MathematicalIntegers => 1,
            TrustMcArithmeticModel::RustChecked => 2,
        },
    )?;
    write_u32(out, options.bmc.unwind_limit)?;
    write_bool(out, options.bmc.unwinding_assertions)?;
    write_u8(
        out,
        match options.chc.engine {
            TrustMcChcEngine::Z3Fixedpoint => 0,
            TrustMcChcEngine::Spacer => 1,
            TrustMcChcEngine::NativePdr => 2,
        },
    )?;
    write_u8(
        out,
        match options.chc.invariant_source {
            TrustMcInvariantSource::None => 0,
            TrustMcInvariantSource::TrustIrProofObligations => 1,
            TrustMcInvariantSource::TrustWp => 2,
            TrustMcInvariantSource::TrustVc => 3,
            TrustMcInvariantSource::UserSupplied => 4,
        },
    )?;
    write_bool(out, options.chc.pdr.enabled)?;
    write_option_u32(out, options.chc.pdr.max_frames)?;
    write_u8(
        out,
        match options.chc.pdr.generalization {
            TrustMcPdrGeneralization::None => 0,
            TrustMcPdrGeneralization::Cubes => 1,
            TrustMcPdrGeneralization::Interpolants => 2,
        },
    )?;
    write_bool(out, options.chc.emit_horn_clauses)?;
    write_u8(
        out,
        match options.slicing {
            TrustMcSlicingMode::None => 0,
            TrustMcSlicingMode::ObligationBackwardSlice => 1,
            TrustMcSlicingMode::ConstraintIndependence => 2,
        },
    )?;

    Ok(())
}

pub(super) fn write_trust_wp_mode<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    mode: TrustWpVerificationMode,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match mode {
            TrustWpVerificationMode::WeakestPrecondition => 0,
            TrustWpVerificationMode::StrongestPostcondition => 1,
            TrustWpVerificationMode::Abduction => 2,
        },
    )?;

    Ok(())
}

pub(super) fn write_trust_wp_options<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    options: &TrustWpRequestOptions,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match options.heap_model {
            TrustWpHeapModel::TrustIrMemory => 0,
            TrustWpHeapModel::RustBorrowGraph => 1,
            TrustWpHeapModel::SeparationLogic => 2,
        },
    )?;
    write_u8(
        out,
        match options.loop_strategy {
            TrustWpLoopStrategy::RequireInvariants => 0,
            TrustWpLoopStrategy::InferInvariants => 1,
            TrustWpLoopStrategy::Havoc => 2,
        },
    )?;
    write_u8(
        out,
        match options.frame_policy {
            TrustWpFramePolicy::Minimal => 0,
            TrustWpFramePolicy::BorrowRegions => 1,
            TrustWpFramePolicy::FullHeap => 2,
        },
    )?;
    write_u8(
        out,
        match options.panic_semantics {
            TrustWpPanicSemantics::PanicFreeRequired => 0,
            TrustWpPanicSemantics::EncodePanicsAsErrors => 1,
            TrustWpPanicSemantics::Unwind => 2,
        },
    )?;
    write_u32(out, options.max_abduced_preconditions)?;
    write_bool(out, options.emit_verification_conditions)?;

    Ok(())
}

pub(super) fn write_cast_op<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    op: CastOp,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match op {
            CastOp::Trunc => 0,
            CastOp::ZExt => 1,
            CastOp::SExt => 2,
            CastOp::FPTrunc => 3,
            CastOp::FPExt => 4,
            CastOp::FPToUI => 5,
            CastOp::FPToSI => 6,
            CastOp::UIToFP => 7,
            CastOp::SIToFP => 8,
            CastOp::PtrToInt => 9,
            CastOp::IntToPtr => 10,
            CastOp::PtrToPtr => 11,
            CastOp::Bitcast => 12,
            CastOp::Transmute => 13,
            CastOp::ReifyFnPointer => 14,
            CastOp::FPToSISat => 15,
            CastOp::FPToUISat => 16,
        },
    )?;

    Ok(())
}

pub(super) fn write_enum_tag_encoding<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    encoding: NativeEnumTagEncoding,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match encoding {
            NativeEnumTagEncoding::Direct => 0,
            NativeEnumTagEncoding::Niche => 1,
            NativeEnumTagEncoding::Untagged => 2,
        },
    )?;

    Ok(())
}

pub(super) fn write_integer_range<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    range: NativeIntegerRange,
) -> Result {
    out.poll()?;
    write_i128(out, range.start)?;
    write_i128(out, range.end)?;

    Ok(())
}

pub(super) fn write_enum_niche_fact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    niche: &NativeEnumNicheFact,
) -> Result {
    out.poll()?;
    write_u32(out, niche.variant_index)?;
    write_option_u32(out, niche.field)?;
    write_integer_range(out, niche.valid_range)?;

    Ok(())
}

pub(super) fn write_option_enum_niche_fact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    niche: Option<&NativeEnumNicheFact>,
) -> Result {
    out.poll()?;
    match niche {
        None => write_u8(out, 0)?,
        Some(niche) => {
            write_u8(out, 1)?;
            write_enum_niche_fact(out, niche)?;
        }
    }

    Ok(())
}

pub(super) fn write_enum_variant_layout_fact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    variant: &NativeEnumVariantLayoutFact,
) -> Result {
    out.poll()?;
    write_u32(out, variant.variant_index)?;
    write_str(out, &variant.name)?;
    write_option_i128(out, variant.discriminant)?;
    write_len(out, variant.fields.len())?;
    for field in &variant.fields {
        out.poll()?;
        write_field_offset_shape(out, field)?;
    }
    write_u64(out, variant.size_bits)?;
    write_option_u64(out, variant.align_bits)?;

    Ok(())
}

pub(super) fn write_enum_layout_fact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    layout: &NativeEnumLayoutFact,
) -> Result {
    out.poll()?;
    write_enum_id(out, layout.enum_id)?;
    write_enum_tag_encoding(out, layout.tag_encoding)?;
    write_option_u32(out, layout.tag_bits)?;
    write_option_u64(out, layout.discriminant_offset_bits)?;
    write_option_enum_niche_fact(out, layout.niche.as_ref())?;
    write_len(out, layout.variants.len())?;
    for variant in &layout.variants {
        out.poll()?;
        write_enum_variant_layout_fact(out, variant)?;
    }

    Ok(())
}

pub(super) fn write_option_enum_layout_fact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    layout: Option<&NativeEnumLayoutFact>,
) -> Result {
    out.poll()?;
    match layout {
        None => write_u8(out, 0)?,
        Some(layout) => {
            write_u8(out, 1)?;
            write_enum_layout_fact(out, layout)?;
        }
    }

    Ok(())
}

pub(super) fn write_adt_layout_fact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    fact: &NativeAdtLayoutFact,
) -> Result {
    out.poll()?;
    write_u32(out, fact.id.index())?;
    write_ty(out, &fact.ty)?;
    write_ty_layout_shape(out, &fact.layout)?;
    write_option_enum_layout_fact(out, fact.enum_layout.as_ref())?;

    Ok(())
}

pub(super) fn write_fat_pointer_fact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    fact: &NativeFatPointerFact,
) -> Result {
    out.poll()?;
    write_u32(out, fact.id.index())?;
    write_ty(out, &fact.ty)?;
    write_pointer_layout_shape(out, fact.layout)?;

    Ok(())
}
