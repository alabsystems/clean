// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

pub(super) fn write_tool_identities<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    tools: &[NativeToolIdentity],
) -> Result {
    write_sorted(tools, out, tool_cmp, |row, out| {
        write_tool_identity(out, row)
    })
}

pub(super) fn write_proof_ids<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    ids: &[ProofId],
) -> Result {
    write_sorted(
        ids,
        out,
        |a, b, out| {
            out.poll()?;
            Ok(a.cmp(b))
        },
        |id, out| write_u32(out, id.index()),
    )
}

pub(super) fn write_lineage_ids<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    ids: &[ProofLineageId],
) -> Result {
    write_sorted(
        ids,
        out,
        |a, b, out| {
            out.poll()?;
            Ok(a.cmp(b))
        },
        |id, out| write_u32(out, id.index()),
    )
}

pub(super) fn write_certificate_refs<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    rows: &[ProofCertificateRef],
) -> Result {
    write_sorted(rows, out, certificate_cmp, |row, out| {
        write_certificate_ref(out, row)
    })
}

pub(super) fn write_evidence_artifacts<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    rows: &[NativeEvidenceArtifact],
) -> Result {
    write_sorted(rows, out, artifact_cmp, |row, out| {
        write_evidence_artifact(out, row)
    })
}

pub(super) fn write_replay_context<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    context: &NativeReplayContext,
) -> Result {
    write_sorted(
        &context.atoms,
        out,
        |a, b, out| {
            out.poll()?;
            Ok(a.id.cmp(&b.id))
        },
        |row, out| write_replay_atom(out, row),
    )?;
    write_sorted(
        &context.unsupported_modes,
        out,
        unsupported_cmp,
        |row, out| write_unsupported_mode(out, row),
    )
}

pub(super) fn write_request_provenance<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    provenance: &NativeRequestProvenance,
) -> Result {
    write_verifier_suite(out, provenance.verifier_suite)?;
    write_tool_identity(out, &provenance.expected_verifier)?;
    write_tool_identities(out, &provenance.solvers)?;
    match &provenance.replay {
        None => write_u8(out, 0)?,
        Some(replay) => {
            write_u8(out, 1)?;
            write_replay_identity(out, replay)?;
        }
    }
    // Preserve the existing zero-byte empty-context trailing conditional.
    if !provenance.replay_context.is_empty() {
        write_replay_context(out, &provenance.replay_context)?;
    }
    Ok(())
}

pub(super) fn write_compiler_facts<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    facts: &NativeCompilerFacts,
) -> Result {
    write_sorted(
        &facts.adt_layouts,
        out,
        |a, b, out| {
            out.poll()?;
            Ok(a.id.cmp(&b.id))
        },
        |row, out| write_adt_layout_fact(out, row),
    )?;
    write_sorted(
        &facts.fat_pointers,
        out,
        |a, b, out| {
            out.poll()?;
            Ok(a.id.cmp(&b.id))
        },
        |row, out| write_fat_pointer_fact(out, row),
    )?;
    write_sorted(
        &facts.trait_object_metadata,
        out,
        |a, b, out| {
            out.poll()?;
            Ok(a.id.cmp(&b.id))
        },
        |row, out| write_trait_object_metadata_fact(out, row),
    )?;
    write_sorted(
        &facts.pointer_offsets,
        out,
        |a, b, out| {
            out.poll()?;
            Ok(a.id.cmp(&b.id))
        },
        |row, out| write_pointer_offset_fact(out, row),
    )?;
    write_sorted(
        &facts.casts,
        out,
        |a, b, out| {
            out.poll()?;
            Ok(a.id.cmp(&b.id))
        },
        |row, out| write_cast_fact(out, row),
    )?;
    write_sorted(
        &facts.monomorphizations,
        out,
        |a, b, out| {
            out.poll()?;
            Ok(a.id.cmp(&b.id))
        },
        |row, out| write_monomorphization_fact(out, row),
    )?;
    write_sorted(
        &facts.obligation_sources,
        out,
        |a, b, out| {
            out.poll()?;
            Ok((a.obligation, a.function, a.monomorphization).cmp(&(
                b.obligation,
                b.function,
                b.monomorphization,
            )))
        },
        |row, out| write_obligation_source(out, row),
    )
}
