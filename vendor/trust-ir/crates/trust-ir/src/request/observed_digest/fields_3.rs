// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact existing canonical field/tag spelling, with fallible inner writes.

use super::*;

pub(super) fn write_trait_object_metadata_fact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    fact: &NativeTraitObjectMetadataFact,
) -> Result {
    out.poll()?;
    write_u32(out, fact.id.index())?;
    write_ty(out, &fact.ty)?;
    match &fact.source_ty {
        None => write_u8(out, 0)?,
        Some(ty) => {
            write_u8(out, 1)?;
            write_ty(out, ty)?;
        }
    }
    write_u32(out, fact.trait_id)?;
    write_option_u32(out, fact.source_trait_id)?;
    write_len(out, fact.upcast_path.len())?;
    for trait_id in &fact.upcast_path {
        out.poll()?;
        write_u32(out, *trait_id)?;
    }
    write_str(out, &fact.vtable_symbol)?;
    write_digest(out, &fact.stable_digest)?;
    match fact.function {
        None => write_u8(out, 0)?,
        Some(function) => {
            write_u8(out, 1)?;
            write_u32(out, function.index())?;
        }
    }
    write_proof_ids(out, &fact.obligations)?;

    Ok(())
}

pub(super) fn write_pointer_offset_provenance<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    provenance: &NativePointerOffsetProvenance,
) -> Result {
    out.poll()?;
    match provenance {
        NativePointerOffsetProvenance::SameAsBase => write_u8(out, 0)?,
        NativePointerOffsetProvenance::Unsupported(unsupported) => {
            write_u8(out, 1)?;
            write_unsupported_mode(out, unsupported)?;
        }
    }

    Ok(())
}

pub(super) fn write_pointer_offset_fact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    fact: &NativePointerOffsetFact,
) -> Result {
    out.poll()?;
    write_u32(out, fact.id.index())?;
    write_u32(out, fact.function.index())?;
    match fact.result {
        None => write_u8(out, 0)?,
        Some(result) => {
            write_u8(out, 1)?;
            write_u32(out, result.index())?;
        }
    }
    write_u32(out, fact.base.index())?;
    write_ty(out, &fact.base_ty)?;
    write_ty(out, &fact.pointee_ty)?;
    write_ty_layout_shape(out, &fact.element_layout)?;
    write_u64(out, fact.stride_bits)?;
    write_u32(out, fact.offset.index())?;
    write_ty(out, &fact.offset_ty)?;
    write_option_i128(out, fact.signed_offset_const)?;
    write_pointer_offset_provenance(out, &fact.provenance)?;
    write_option_source_span(out, fact.span)?;
    write_proof_ids(out, &fact.obligations)?;

    Ok(())
}

pub(super) fn write_cast_fact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    fact: &NativeCastFact,
) -> Result {
    out.poll()?;
    write_u32(out, fact.id.index())?;
    write_u32(out, fact.function.index())?;
    match fact.result {
        None => write_u8(out, 0)?,
        Some(result) => {
            write_u8(out, 1)?;
            write_u32(out, result.index())?;
        }
    }
    write_cast_op(out, fact.op)?;
    write_ty(out, &fact.source_ty)?;
    write_ty(out, &fact.target_ty)?;
    write_cast_layout_evidence(out, &fact.evidence)?;
    write_option_source_span(out, fact.span)?;
    write_proof_ids(out, &fact.obligations)?;

    Ok(())
}

pub(super) fn write_generic_arg<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    arg: &NativeGenericArg,
) -> Result {
    out.poll()?;
    match arg {
        NativeGenericArg::Ty(ty) => {
            write_u8(out, 0)?;
            write_ty(out, ty)?;
        }
        NativeGenericArg::Const { ty, value } => {
            write_u8(out, 1)?;
            write_ty(out, ty)?;
            write_constant(out, value)?;
        }
        NativeGenericArg::LifetimeErased => write_u8(out, 2)?,
        NativeGenericArg::Placeholder { index } => {
            write_u8(out, 3)?;
            write_u32(out, *index)?;
        }
    }

    Ok(())
}

pub(super) fn write_monomorphization_fact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    fact: &NativeMonomorphizationFact,
) -> Result {
    out.poll()?;
    write_u32(out, fact.id.index())?;
    write_str(out, &fact.source_item)?;
    write_str(out, &fact.symbol)?;
    write_len(out, fact.generic_args.len())?;
    for arg in &fact.generic_args {
        out.poll()?;
        write_generic_arg(out, arg)?;
    }
    match fact.function {
        None => write_u8(out, 0)?,
        Some(function) => {
            write_u8(out, 1)?;
            write_u32(out, function.index())?;
        }
    }
    write_digest(out, &fact.stable_digest)?;

    Ok(())
}

pub(super) fn write_obligation_cause<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    cause: NativeObligationCause,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match cause {
            NativeObligationCause::Precondition => 0,
            NativeObligationCause::Postcondition => 1,
            NativeObligationCause::Assert => 2,
            NativeObligationCause::BoundsCheck => 3,
            NativeObligationCause::OverflowCheck => 4,
            NativeObligationCause::LayoutCheck => 5,
            NativeObligationCause::CastCheck => 6,
            NativeObligationCause::BorrowCheck => 7,
            NativeObligationCause::Translation => 8,
            NativeObligationCause::Panic => 9,
            NativeObligationCause::Other => 10,
            NativeObligationCause::PointerOffset => 11,
            NativeObligationCause::Temporal => 12,
        },
    )?;

    Ok(())
}

pub(super) fn write_compiler_fact_ref<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    fact: NativeCompilerFactRef,
) -> Result {
    out.poll()?;
    match fact {
        NativeCompilerFactRef::AdtLayout(id) => {
            write_u8(out, 0)?;
            write_u32(out, id.index())?;
        }
        NativeCompilerFactRef::FatPointer(id) => {
            write_u8(out, 1)?;
            write_u32(out, id.index())?;
        }
        NativeCompilerFactRef::TraitObjectMetadata(id) => {
            write_u8(out, 2)?;
            write_u32(out, id.index())?;
        }
        NativeCompilerFactRef::Cast(id) => {
            write_u8(out, 3)?;
            write_u32(out, id.index())?;
        }
        NativeCompilerFactRef::Monomorphization(id) => {
            write_u8(out, 4)?;
            write_u32(out, id.index())?;
        }
        NativeCompilerFactRef::PointerOffset(id) => {
            write_u8(out, 5)?;
            write_u32(out, id.index())?;
        }
    }

    Ok(())
}

pub(super) fn write_obligation_source<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    source: &NativeObligationSource,
) -> Result {
    out.poll()?;
    write_u32(out, source.obligation.index())?;
    write_str(out, &source.public_obligation_id)?;
    match source.function {
        None => write_u8(out, 0)?,
        Some(function) => {
            write_u8(out, 1)?;
            write_u32(out, function.index())?;
        }
    }
    write_option_source_span(out, source.span)?;
    write_option_assertion_id(out, source.assertion_id)?;
    write_obligation_cause(out, source.cause)?;
    match source.monomorphization {
        None => write_u8(out, 0)?,
        Some(id) => {
            write_u8(out, 1)?;
            write_u32(out, id.index())?;
        }
    }
    write_sorted(
        &source.facts,
        out,
        |left, right, out| {
            out.poll()?;
            Ok(left.cmp(right))
        },
        |fact, out| write_compiler_fact_ref(out, *fact),
    )?;

    Ok(())
}

pub(super) fn write_native_request<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    request: &NativeVerificationRequest,
) -> Result {
    out.poll()?;
    match request {
        NativeVerificationRequest::TrustVc(request) => {
            write_u8(out, 0)?;
            write_u32(out, request.id.index())?;
            write_trust_vc_mode(out, request.mode)?;
            write_proof_ids(out, &request.obligations)?;
            write_certificate_refs(out, &request.certificates)?;
            write_lineage_ids(out, &request.lineage_roots)?;
            write_trust_vc_options(out, &request.options)?;
            write_diagnostics_policy(out, &request.diagnostics)?;
            write_request_provenance(out, &request.provenance)?;
            // DELIBERATE: `function` is written LAST and UNTAGGED, so `None`
            // emits zero bytes and every pre-existing TrustVc request digest
            // stays byte-identical. Do NOT normalize this to match the TrustMc
            // / TrustWp arms below, which write `function` mid-record, and do
            // NOT route it through `write_option_u32` — either change
            // appends a discriminant byte to every existing stream and moves
            // every TrustVc request digest, the bundle digest, every evidence
            // `request_digest`, and every compiler artifact metadata value,
            // forcing a version bump of both the request and bundle domains.
            //
            // "None writes nothing" is NOT the whole argument. This is the
            // SECOND stacked trailing conditional: `write_request_provenance`
            // already ends in one (`if !provenance.replay_context.is_empty()`).
            // Non-collision holds only because a written replay_context is >=16
            // bytes — `write_replay_context` emits two unconditional u64
            // length prefixes — while this tail is exactly 4. So (empty ctx,
            // Some) and (non-empty ctx, None) cannot alias. Adding a THIRD
            // trailing conditional, or making this one variable-width, breaks
            // that argument and needs a fresh proof.
            if let Some(function) = request.function {
                write_u32(out, function.index())?;
            }
        }
        NativeVerificationRequest::TrustMc(request) => {
            write_u8(out, 1)?;
            write_u32(out, request.id.index())?;
            write_trust_mc_mode(out, request.mode)?;
            write_u32(out, request.function.index())?;
            write_proof_ids(out, &request.obligations)?;
            write_lineage_ids(out, &request.lineage_roots)?;
            write_trust_mc_options(out, &request.options)?;
            write_diagnostics_policy(out, &request.diagnostics)?;
            write_request_provenance(out, &request.provenance)?;
        }
        NativeVerificationRequest::TrustWp(request) => {
            write_u8(out, 2)?;
            write_u32(out, request.id.index())?;
            write_trust_wp_mode(out, request.mode)?;
            write_u32(out, request.function.index())?;
            write_proof_ids(out, &request.obligations)?;
            write_lineage_ids(out, &request.lineage_roots)?;
            write_trust_wp_options(out, &request.options)?;
            write_diagnostics_policy(out, &request.diagnostics)?;
            write_request_provenance(out, &request.provenance)?;
        }
    }

    Ok(())
}

pub(super) fn write_evidence_artifact_kind<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    kind: NativeEvidenceArtifactKind,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match kind {
            NativeEvidenceArtifactKind::TrustVcCertificateImport => 0,
            NativeEvidenceArtifactKind::TrustVcMergedCertificate => 1,
            NativeEvidenceArtifactKind::TrustMcHornClauses => 2,
            NativeEvidenceArtifactKind::TrustMcPdrTrace => 3,
            NativeEvidenceArtifactKind::TrustMcModel => 4,
            NativeEvidenceArtifactKind::TrustWpVerificationCondition => 5,
            NativeEvidenceArtifactKind::TrustWpReplayTrace => 6,
            NativeEvidenceArtifactKind::TrustWpAbducedPrecondition => 7,
            NativeEvidenceArtifactKind::ReplayTranscript => 8,
            NativeEvidenceArtifactKind::Other => 9,
            NativeEvidenceArtifactKind::Btor2Trace => 10,
            NativeEvidenceArtifactKind::Btor2Proof => 11,
            NativeEvidenceArtifactKind::NativeCompiledArtifact => 12,
            NativeEvidenceArtifactKind::BackendCapabilityMetadata => 13,
        },
    )?;

    Ok(())
}

pub(super) fn write_evidence_artifact<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    artifact: &NativeEvidenceArtifact,
) -> Result {
    out.poll()?;
    write_str(out, &artifact.name)?;
    write_evidence_artifact_kind(out, artifact.kind)?;
    write_digest(out, &artifact.digest)?;

    Ok(())
}

pub(super) fn write_native_evidence_bundle<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    bundle: &NativeEvidenceBundle,
) -> Result {
    out.poll()?;
    match bundle {
        NativeEvidenceBundle::TrustVc(bundle) => {
            write_u8(out, 0)?;
            write_u32(out, bundle.request.index())?;
            write_trust_vc_mode(out, bundle.mode)?;
            write_proof_ids(out, &bundle.obligations)?;
            write_tool_identity(out, &bundle.verifier)?;
            write_tool_identities(out, &bundle.solvers)?;
            write_replay_identity(out, &bundle.replay)?;
            write_digest(out, &bundle.trust_ir_module_digest)?;
            write_digest(out, &bundle.request_digest)?;
            write_evidence_artifacts(out, &bundle.artifacts)?;
        }
        NativeEvidenceBundle::TrustMc(bundle) => {
            write_u8(out, 1)?;
            write_u32(out, bundle.request.index())?;
            write_trust_mc_mode(out, bundle.mode)?;
            write_proof_ids(out, &bundle.obligations)?;
            write_tool_identity(out, &bundle.verifier)?;
            write_tool_identities(out, &bundle.solvers)?;
            write_replay_identity(out, &bundle.replay)?;
            write_digest(out, &bundle.trust_ir_module_digest)?;
            write_digest(out, &bundle.request_digest)?;
            write_evidence_artifacts(out, &bundle.artifacts)?;
        }
        NativeEvidenceBundle::TrustWp(bundle) => {
            write_u8(out, 2)?;
            write_u32(out, bundle.request.index())?;
            write_trust_wp_mode(out, bundle.mode)?;
            write_proof_ids(out, &bundle.obligations)?;
            write_tool_identity(out, &bundle.verifier)?;
            write_tool_identities(out, &bundle.solvers)?;
            write_replay_identity(out, &bundle.replay)?;
            write_digest(out, &bundle.trust_ir_module_digest)?;
            write_digest(out, &bundle.request_digest)?;
            write_evidence_artifacts(out, &bundle.artifacts)?;
        }
    }

    Ok(())
}
