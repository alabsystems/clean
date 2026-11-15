// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact existing canonical field/tag spelling, with fallible inner writes.

use super::*;

pub(super) fn write_ty_layout_kind<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    kind: &TyLayoutKind,
) -> Result {
    out.poll()?;
    match kind {
        TyLayoutKind::Storage => write_u8(out, 11)?,
        TyLayoutKind::Scalar(shape) => {
            write_u8(out, 0)?;
            write_ty_shape(out, *shape)?;
        }
        TyLayoutKind::ThinPointer => write_u8(out, 1)?,
        TyLayoutKind::FatPointer(metadata) => {
            write_u8(out, 2)?;
            write_pointer_metadata_shape(out, *metadata)?;
        }
        TyLayoutKind::Struct { id, fields } => {
            write_u8(out, 3)?;
            write_struct_id(out, *id)?;
            write_len(out, fields.len())?;
            for field in fields {
                out.poll()?;
                write_field_offset_shape(out, field)?;
            }
        }
        TyLayoutKind::Enum { id, variants } => {
            write_u8(out, 4)?;
            write_enum_id(out, *id)?;
            write_u64(out, *variants as u64)?;
        }
        TyLayoutKind::Array {
            elem,
            len,
            stride_bits,
        } => {
            write_u8(out, 5)?;
            write_ty_id(out, *elem)?;
            write_u64(out, *len)?;
            write_u64(out, *stride_bits)?;
        }
        TyLayoutKind::Unit => write_u8(out, 6)?,
        TyLayoutKind::Never => write_u8(out, 7)?,
        TyLayoutKind::Tuple { fields } => {
            write_u8(out, 9)?;
            write_len(out, fields.len())?;
            for field in fields {
                out.poll()?;
                write_field_offset_shape(out, field)?;
            }
        }
        // v58: additive, exactly as `Tuple` took tag 9 in v42 — every
        // previous tag is preserved, so no existing request digest moves.
        TyLayoutKind::Closure { id, captures } => {
            write_u8(out, 10)?;
            write_closure_ty_id(out, *id)?;
            write_len(out, captures.len())?;
            for capture in captures {
                out.poll()?;
                write_field_offset_shape(out, capture)?;
            }
        }
        TyLayoutKind::Vector {
            elem_shape,
            lanes,
            lane_bits,
        } => {
            write_u8(out, 8)?;
            write_ty_shape(out, *elem_shape)?;
            write_u32(out, *lanes)?;
            write_u64(out, *lane_bits)?;
        }
    }

    Ok(())
}

pub(super) fn write_ty_layout_shape<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    layout: &TyLayoutShape,
) -> Result {
    out.poll()?;
    write_u64(out, layout.size_bits)?;
    write_option_u64(out, layout.align_bits)?;
    write_ty_layout_kind(out, &layout.kind)?;

    Ok(())
}

pub(super) fn write_cast_layout_evidence<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    evidence: &CastLayoutEvidence,
) -> Result {
    out.poll()?;
    match evidence {
        CastLayoutEvidence::NotLayoutSensitive => write_u8(out, 0)?,
        CastLayoutEvidence::PointerCast { src, dst } => {
            write_u8(out, 1)?;
            write_pointer_layout_shape(out, *src)?;
            write_pointer_layout_shape(out, *dst)?;
        }
        CastLayoutEvidence::SameSize {
            size_bits,
            src_align_bits,
            dst_align_bits,
        } => {
            write_u8(out, 2)?;
            write_u64(out, *size_bits)?;
            write_option_u64(out, *src_align_bits)?;
            write_option_u64(out, *dst_align_bits)?;
        }
        CastLayoutEvidence::ReifyFnPointer { pointer_bits } => {
            write_u8(out, 3)?;
            write_u32(out, *pointer_bits)?;
        }
    }

    Ok(())
}

pub(super) fn write_bundle_producer<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    producer: NativeBundleProducer,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match producer {
            NativeBundleProducer::TRust => 0,
            NativeBundleProducer::TSwift => 1,
            NativeBundleProducer::TC => 2,
            NativeBundleProducer::TrustIr => 3,
            NativeBundleProducer::Clean => 4,
        },
    )?;

    Ok(())
}

pub(super) fn write_adapter_input<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    input: &NativeAdapterInput,
) -> Result {
    out.poll()?;
    match input {
        NativeAdapterInput::RustMir { body_digest } => {
            write_u8(out, 0)?;
            write_digest(out, body_digest)?;
        }
        NativeAdapterInput::TrustIrModule => write_u8(out, 1)?,
    }

    Ok(())
}

pub(super) fn write_source_language<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    language: NativeSourceLanguage,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match language {
            NativeSourceLanguage::Unknown => 0,
            NativeSourceLanguage::Rust => 1,
            NativeSourceLanguage::Swift => 2,
            NativeSourceLanguage::C => 3,
            NativeSourceLanguage::TrustIr => 4,
            NativeSourceLanguage::Other => 5,
            NativeSourceLanguage::Lean => 6,
            NativeSourceLanguage::Clean => 7,
        },
    )?;

    Ok(())
}

pub(super) fn write_source_languages<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    languages: &BTreeSet<NativeSourceLanguage>,
) -> Result {
    out.poll()?;
    write_len(out, languages.len())?;
    for language in languages {
        out.poll()?;
        write_source_language(out, *language)?;
    }

    Ok(())
}

pub(super) fn write_verifier_suite<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    suite: NativeVerifierSuite,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match suite {
            NativeVerifierSuite::Unknown => 0,
            NativeVerifierSuite::TrustVc => 1,
            NativeVerifierSuite::TrustMc => 2,
            NativeVerifierSuite::TrustWp => 3,
            NativeVerifierSuite::AY => 4,
            NativeVerifierSuite::TRust => 5,
            NativeVerifierSuite::TrustIr => 6,
            NativeVerifierSuite::Other => 7,
        },
    )?;

    Ok(())
}

pub(super) fn write_bundle_provenance<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    provenance: &NativeBundleProvenance,
) -> Result {
    out.poll()?;
    write_str(out, &provenance.producer_version)?;
    write_source_language(out, provenance.source_language)?;
    write_source_languages(out, &provenance.source_languages)?;
    write_option_str(out, provenance.source_artifact.as_deref())?;
    write_option_digest(out, provenance.source_digest)?;

    write_tool_identities(out, &provenance.toolchain)?;

    Ok(())
}

pub(super) fn write_unknown_field_policy<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    policy: NativeUnknownFieldPolicy,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match policy {
            NativeUnknownFieldPolicy::Reject => 0,
            NativeUnknownFieldPolicy::Preserve => 1,
            NativeUnknownFieldPolicy::Ignore => 2,
        },
    )?;

    Ok(())
}

pub(super) fn write_serialization_policy<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    policy: &NativeSerializationPolicy,
) -> Result {
    out.poll()?;
    write_u32(out, policy.schema_version)?;
    write_bool(out, policy.canonical_order)?;
    write_bool(out, policy.sort_unordered_sets)?;
    write_bool(out, policy.messagepack_named_fields)?;
    write_unknown_field_policy(out, policy.unknown_fields)?;

    Ok(())
}

pub(super) fn write_diagnostic_level<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    level: NativeDiagnosticLevel,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match level {
            NativeDiagnosticLevel::Off => 0,
            NativeDiagnosticLevel::Error => 1,
            NativeDiagnosticLevel::Warn => 2,
            NativeDiagnosticLevel::Info => 3,
            NativeDiagnosticLevel::Trace => 4,
        },
    )?;

    Ok(())
}

pub(super) fn write_diagnostics_policy<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    policy: &NativeDiagnosticsPolicy,
) -> Result {
    out.poll()?;
    write_diagnostic_level(out, policy.level)?;
    write_bool(out, policy.include_source_spans)?;
    write_bool(out, policy.include_lineage)?;
    write_bool(out, policy.emit_counterexamples)?;
    write_bool(out, policy.emit_unsat_cores)?;
    write_bool(out, policy.emit_proof_traces)?;
    write_u32(out, policy.max_counterexamples)?;

    Ok(())
}

pub(super) fn write_replay_identity<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    replay: &ProofReplayIdentity,
) -> Result {
    out.poll()?;
    write_str(out, &replay.engine)?;
    write_str(out, &replay.invocation)?;
    write_option_digest(out, replay.transcript_digest)?;

    Ok(())
}
