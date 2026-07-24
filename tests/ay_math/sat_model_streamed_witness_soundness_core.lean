-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for streamed model-witness soundness. Large
-- SAT models can be emitted chunk-by-chunk, but public reports are justified
-- only when chunk order, digest, manifest, reconstruction, projection, and
-- audit evidence agree. Bad streams are diagnostic no-claim facts.

def AyMSWSConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMSWSDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMSWSEquisat (before : Prop) (after : Prop) :=
  AyMSWSConj (before -> after) (after -> before)

def AyMSWSAssignmentChunks
    (chunk_payloads : Prop) (chunk_order : Prop) :=
  AyMSWSConj chunk_payloads chunk_order

def AyMSWSChunkDigestEvidence
    (chunk_digests : Prop) (digest_guard : Prop) :=
  AyMSWSConj chunk_digests digest_guard

def AyMSWSStreamManifest
    (stream_id : Prop) (chunk_count : Prop) (manifest_guard : Prop) :=
  AyMSWSConj stream_id (AyMSWSConj chunk_count manifest_guard)

def AyMSWSReconstructionWitness
    (assignment_chunks : Prop) (full_assignment : Prop) :=
  assignment_chunks -> full_assignment

def AyMSWSProjectionWitness
    (full_assignment : Prop) (original_model : Prop) :=
  full_assignment -> original_model

def AyMSWSStreamEvidence
    (chunks_ok : Prop) (digests_ok : Prop)
    (manifest_ok : Prop) (projection_ok : Prop) :=
  AyMSWSConj chunks_ok
    (AyMSWSConj digests_ok
      (AyMSWSConj manifest_ok projection_ok))

def AyMSWSAuditEntry
    (stream_evidence : Prop) (audit_digest : Prop) :=
  AyMSWSConj stream_evidence audit_digest

def AyMSWSPublicSatReport
    (stream_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :=
  AyMSWSConj stream_evidence
    (AyMSWSConj audit_entry original_model)

def AyMSWSNoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMSWSConj diagnostic (public_claim -> False)

theorem ay_msws_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMSWSConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_msws_conj_left
    (left : Prop) (right : Prop) :
    AyMSWSConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_msws_conj_right
    (left : Prop) (right : Prop) :
    AyMSWSConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_msws_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMSWSDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_msws_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMSWSDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_msws_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMSWSEquisat before after := by
  intro forward
  intro backward
  exact ay_msws_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_msws_equisat_forward
    (before : Prop) (after : Prop) :
    AyMSWSEquisat before after -> before -> after := by
  intro certificate
  exact ay_msws_conj_left (before -> after) (after -> before) certificate

theorem ay_msws_equisat_backward
    (before : Prop) (after : Prop) :
    AyMSWSEquisat before after -> after -> before := by
  intro certificate
  exact ay_msws_conj_right (before -> after) (after -> before) certificate

theorem ay_msws_assignment_chunks_intro
    (chunk_payloads : Prop) (chunk_order : Prop) :
    chunk_payloads ->
    chunk_order ->
    AyMSWSAssignmentChunks chunk_payloads chunk_order := by
  intro hpayloads
  intro horder
  exact ay_msws_conj_intro chunk_payloads chunk_order
    hpayloads horder

theorem ay_msws_assignment_chunks_payloads
    (chunk_payloads : Prop) (chunk_order : Prop) :
    AyMSWSAssignmentChunks chunk_payloads chunk_order ->
    chunk_payloads := by
  intro chunks
  exact ay_msws_conj_left chunk_payloads chunk_order chunks

theorem ay_msws_assignment_chunks_order
    (chunk_payloads : Prop) (chunk_order : Prop) :
    AyMSWSAssignmentChunks chunk_payloads chunk_order ->
    chunk_order := by
  intro chunks
  exact ay_msws_conj_right chunk_payloads chunk_order chunks

theorem ay_msws_chunk_digest_intro
    (chunk_digests : Prop) (digest_guard : Prop) :
    chunk_digests ->
    digest_guard ->
    AyMSWSChunkDigestEvidence chunk_digests digest_guard := by
  intro hdigests
  intro hguard
  exact ay_msws_conj_intro chunk_digests digest_guard
    hdigests hguard

theorem ay_msws_chunk_digest_digests
    (chunk_digests : Prop) (digest_guard : Prop) :
    AyMSWSChunkDigestEvidence chunk_digests digest_guard ->
    chunk_digests := by
  intro evidence
  exact ay_msws_conj_left chunk_digests digest_guard evidence

theorem ay_msws_chunk_digest_guard
    (chunk_digests : Prop) (digest_guard : Prop) :
    AyMSWSChunkDigestEvidence chunk_digests digest_guard ->
    digest_guard := by
  intro evidence
  exact ay_msws_conj_right chunk_digests digest_guard evidence

theorem ay_msws_stream_manifest_intro
    (stream_id : Prop) (chunk_count : Prop) (manifest_guard : Prop) :
    stream_id ->
    chunk_count ->
    manifest_guard ->
    AyMSWSStreamManifest stream_id chunk_count manifest_guard := by
  intro hstream
  intro hcount
  intro hguard
  exact ay_msws_conj_intro stream_id
    (AyMSWSConj chunk_count manifest_guard)
    hstream
    (ay_msws_conj_intro chunk_count manifest_guard hcount hguard)

theorem ay_msws_stream_manifest_id
    (stream_id : Prop) (chunk_count : Prop) (manifest_guard : Prop) :
    AyMSWSStreamManifest stream_id chunk_count manifest_guard ->
    stream_id := by
  intro manifest
  exact ay_msws_conj_left stream_id
    (AyMSWSConj chunk_count manifest_guard) manifest

theorem ay_msws_stream_manifest_count
    (stream_id : Prop) (chunk_count : Prop) (manifest_guard : Prop) :
    AyMSWSStreamManifest stream_id chunk_count manifest_guard ->
    chunk_count := by
  intro manifest
  exact ay_msws_conj_left chunk_count manifest_guard
    (ay_msws_conj_right stream_id
      (AyMSWSConj chunk_count manifest_guard) manifest)

theorem ay_msws_stream_manifest_guard
    (stream_id : Prop) (chunk_count : Prop) (manifest_guard : Prop) :
    AyMSWSStreamManifest stream_id chunk_count manifest_guard ->
    manifest_guard := by
  intro manifest
  exact ay_msws_conj_right chunk_count manifest_guard
    (ay_msws_conj_right stream_id
      (AyMSWSConj chunk_count manifest_guard) manifest)

theorem ay_msws_reconstruct_apply
    (assignment_chunks : Prop) (full_assignment : Prop) :
    AyMSWSReconstructionWitness assignment_chunks full_assignment ->
    assignment_chunks ->
    full_assignment := by
  intro reconstruct
  intro hchunks
  exact reconstruct hchunks

theorem ay_msws_projection_apply
    (full_assignment : Prop) (original_model : Prop) :
    AyMSWSProjectionWitness full_assignment original_model ->
    full_assignment ->
    original_model := by
  intro project
  intro hfull
  exact project hfull

theorem ay_msws_stream_evidence_intro
    (chunks_ok : Prop) (digests_ok : Prop)
    (manifest_ok : Prop) (projection_ok : Prop) :
    chunks_ok ->
    digests_ok ->
    manifest_ok ->
    projection_ok ->
    AyMSWSStreamEvidence
      chunks_ok digests_ok manifest_ok projection_ok := by
  intro hchunks
  intro hdigests
  intro hmanifest
  intro hprojection
  exact ay_msws_conj_intro chunks_ok
    (AyMSWSConj digests_ok
      (AyMSWSConj manifest_ok projection_ok))
    hchunks
    (ay_msws_conj_intro digests_ok
      (AyMSWSConj manifest_ok projection_ok)
      hdigests
      (ay_msws_conj_intro manifest_ok projection_ok
        hmanifest hprojection))

theorem ay_msws_stream_evidence_chunks
    (chunks_ok : Prop) (digests_ok : Prop)
    (manifest_ok : Prop) (projection_ok : Prop) :
    AyMSWSStreamEvidence
      chunks_ok digests_ok manifest_ok projection_ok ->
    chunks_ok := by
  intro evidence
  exact ay_msws_conj_left chunks_ok
    (AyMSWSConj digests_ok
      (AyMSWSConj manifest_ok projection_ok)) evidence

theorem ay_msws_stream_evidence_digests
    (chunks_ok : Prop) (digests_ok : Prop)
    (manifest_ok : Prop) (projection_ok : Prop) :
    AyMSWSStreamEvidence
      chunks_ok digests_ok manifest_ok projection_ok ->
    digests_ok := by
  intro evidence
  exact ay_msws_conj_left digests_ok
    (AyMSWSConj manifest_ok projection_ok)
    (ay_msws_conj_right chunks_ok
      (AyMSWSConj digests_ok
        (AyMSWSConj manifest_ok projection_ok)) evidence)

theorem ay_msws_stream_evidence_manifest
    (chunks_ok : Prop) (digests_ok : Prop)
    (manifest_ok : Prop) (projection_ok : Prop) :
    AyMSWSStreamEvidence
      chunks_ok digests_ok manifest_ok projection_ok ->
    manifest_ok := by
  intro evidence
  exact ay_msws_conj_left manifest_ok projection_ok
    (ay_msws_conj_right digests_ok
      (AyMSWSConj manifest_ok projection_ok)
      (ay_msws_conj_right chunks_ok
        (AyMSWSConj digests_ok
          (AyMSWSConj manifest_ok projection_ok)) evidence))

theorem ay_msws_stream_evidence_projection
    (chunks_ok : Prop) (digests_ok : Prop)
    (manifest_ok : Prop) (projection_ok : Prop) :
    AyMSWSStreamEvidence
      chunks_ok digests_ok manifest_ok projection_ok ->
    projection_ok := by
  intro evidence
  exact ay_msws_conj_right manifest_ok projection_ok
    (ay_msws_conj_right digests_ok
      (AyMSWSConj manifest_ok projection_ok)
      (ay_msws_conj_right chunks_ok
        (AyMSWSConj digests_ok
          (AyMSWSConj manifest_ok projection_ok)) evidence))

theorem ay_msws_audit_entry_intro
    (stream_evidence : Prop) (audit_digest : Prop) :
    stream_evidence ->
    audit_digest ->
    AyMSWSAuditEntry stream_evidence audit_digest := by
  intro hevidence
  intro haudit
  exact ay_msws_conj_intro stream_evidence audit_digest
    hevidence haudit

theorem ay_msws_audit_entry_evidence
    (stream_evidence : Prop) (audit_digest : Prop) :
    AyMSWSAuditEntry stream_evidence audit_digest ->
    stream_evidence := by
  intro audit
  exact ay_msws_conj_left stream_evidence audit_digest audit

theorem ay_msws_audit_entry_digest
    (stream_evidence : Prop) (audit_digest : Prop) :
    AyMSWSAuditEntry stream_evidence audit_digest ->
    audit_digest := by
  intro audit
  exact ay_msws_conj_right stream_evidence audit_digest audit

theorem ay_msws_report_intro
    (stream_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    stream_evidence ->
    audit_entry ->
    original_model ->
    AyMSWSPublicSatReport
      stream_evidence audit_entry original_model := by
  intro hevidence
  intro haudit
  intro horiginal
  exact ay_msws_conj_intro stream_evidence
    (AyMSWSConj audit_entry original_model)
    hevidence
    (ay_msws_conj_intro audit_entry original_model
      haudit horiginal)

theorem ay_msws_report_evidence
    (stream_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSWSPublicSatReport stream_evidence audit_entry original_model ->
    stream_evidence := by
  intro report
  exact ay_msws_conj_left stream_evidence
    (AyMSWSConj audit_entry original_model) report

theorem ay_msws_report_audit
    (stream_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSWSPublicSatReport stream_evidence audit_entry original_model ->
    audit_entry := by
  intro report
  exact ay_msws_conj_left audit_entry original_model
    (ay_msws_conj_right stream_evidence
      (AyMSWSConj audit_entry original_model) report)

theorem ay_msws_report_original
    (stream_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSWSPublicSatReport stream_evidence audit_entry original_model ->
    original_model := by
  intro report
  exact ay_msws_conj_right audit_entry original_model
    (ay_msws_conj_right stream_evidence
      (AyMSWSConj audit_entry original_model) report)

theorem ay_msws_streamed_original_model
    (assignment_chunks : Prop) (full_assignment : Prop)
    (original_model : Prop) :
    AyMSWSReconstructionWitness assignment_chunks full_assignment ->
    AyMSWSProjectionWitness full_assignment original_model ->
    assignment_chunks ->
    original_model := by
  intro reconstruct
  intro project
  intro hchunks
  exact project (reconstruct hchunks)

theorem ay_msws_streamed_report_from_evidence
    (assignment_chunks : Prop) (full_assignment : Prop)
    (original_model : Prop) (chunks_ok : Prop)
    (digests_ok : Prop) (manifest_ok : Prop)
    (projection_ok : Prop) (audit_entry : Prop) :
    AyMSWSReconstructionWitness assignment_chunks full_assignment ->
    AyMSWSProjectionWitness full_assignment original_model ->
    assignment_chunks ->
    chunks_ok ->
    digests_ok ->
    manifest_ok ->
    projection_ok ->
    audit_entry ->
    AyMSWSPublicSatReport
      (AyMSWSStreamEvidence
        chunks_ok digests_ok manifest_ok projection_ok)
      audit_entry original_model := by
  intro reconstruct
  intro project
  intro hchunks
  intro hchunks_ok
  intro hdigests
  intro hmanifest
  intro hprojection
  intro haudit
  exact ay_msws_report_intro
    (AyMSWSStreamEvidence
      chunks_ok digests_ok manifest_ok projection_ok)
    audit_entry original_model
    (ay_msws_stream_evidence_intro
      chunks_ok digests_ok manifest_ok projection_ok
      hchunks_ok hdigests hmanifest hprojection)
    haudit
    (project (reconstruct hchunks))

theorem ay_msws_report_requires_chunks
    (chunks_ok : Prop) (digests_ok : Prop)
    (manifest_ok : Prop) (projection_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSWSPublicSatReport
      (AyMSWSStreamEvidence
        chunks_ok digests_ok manifest_ok projection_ok)
      audit_entry original_model ->
    chunks_ok := by
  intro report
  exact ay_msws_stream_evidence_chunks
    chunks_ok digests_ok manifest_ok projection_ok
    (ay_msws_report_evidence
      (AyMSWSStreamEvidence
        chunks_ok digests_ok manifest_ok projection_ok)
      audit_entry original_model report)

theorem ay_msws_report_requires_digests
    (chunks_ok : Prop) (digests_ok : Prop)
    (manifest_ok : Prop) (projection_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSWSPublicSatReport
      (AyMSWSStreamEvidence
        chunks_ok digests_ok manifest_ok projection_ok)
      audit_entry original_model ->
    digests_ok := by
  intro report
  exact ay_msws_stream_evidence_digests
    chunks_ok digests_ok manifest_ok projection_ok
    (ay_msws_report_evidence
      (AyMSWSStreamEvidence
        chunks_ok digests_ok manifest_ok projection_ok)
      audit_entry original_model report)

theorem ay_msws_report_requires_manifest
    (chunks_ok : Prop) (digests_ok : Prop)
    (manifest_ok : Prop) (projection_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSWSPublicSatReport
      (AyMSWSStreamEvidence
        chunks_ok digests_ok manifest_ok projection_ok)
      audit_entry original_model ->
    manifest_ok := by
  intro report
  exact ay_msws_stream_evidence_manifest
    chunks_ok digests_ok manifest_ok projection_ok
    (ay_msws_report_evidence
      (AyMSWSStreamEvidence
        chunks_ok digests_ok manifest_ok projection_ok)
      audit_entry original_model report)

theorem ay_msws_report_requires_projection
    (chunks_ok : Prop) (digests_ok : Prop)
    (manifest_ok : Prop) (projection_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSWSPublicSatReport
      (AyMSWSStreamEvidence
        chunks_ok digests_ok manifest_ok projection_ok)
      audit_entry original_model ->
    projection_ok := by
  intro report
  exact ay_msws_stream_evidence_projection
    chunks_ok digests_ok manifest_ok projection_ok
    (ay_msws_report_evidence
      (AyMSWSStreamEvidence
        chunks_ok digests_ok manifest_ok projection_ok)
      audit_entry original_model report)

theorem ay_msws_report_sound_exact
    (chunks_ok : Prop) (digests_ok : Prop)
    (manifest_ok : Prop) (projection_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSWSEquisat
      (AyMSWSPublicSatReport
        (AyMSWSStreamEvidence
          chunks_ok digests_ok manifest_ok projection_ok)
        audit_entry original_model)
      (AyMSWSConj chunks_ok
        (AyMSWSConj digests_ok
          (AyMSWSConj manifest_ok
            (AyMSWSConj projection_ok
              (AyMSWSConj audit_entry original_model))))) := by
  exact ay_msws_equisat_intro
    (AyMSWSPublicSatReport
      (AyMSWSStreamEvidence
        chunks_ok digests_ok manifest_ok projection_ok)
      audit_entry original_model)
    (AyMSWSConj chunks_ok
      (AyMSWSConj digests_ok
        (AyMSWSConj manifest_ok
          (AyMSWSConj projection_ok
            (AyMSWSConj audit_entry original_model)))))
    (fun report =>
      ay_msws_conj_intro chunks_ok
        (AyMSWSConj digests_ok
          (AyMSWSConj manifest_ok
            (AyMSWSConj projection_ok
              (AyMSWSConj audit_entry original_model))))
        (ay_msws_report_requires_chunks
          chunks_ok digests_ok manifest_ok projection_ok
          audit_entry original_model report)
        (ay_msws_conj_intro digests_ok
          (AyMSWSConj manifest_ok
            (AyMSWSConj projection_ok
              (AyMSWSConj audit_entry original_model)))
          (ay_msws_report_requires_digests
            chunks_ok digests_ok manifest_ok projection_ok
            audit_entry original_model report)
          (ay_msws_conj_intro manifest_ok
            (AyMSWSConj projection_ok
              (AyMSWSConj audit_entry original_model))
            (ay_msws_report_requires_manifest
              chunks_ok digests_ok manifest_ok projection_ok
              audit_entry original_model report)
            (ay_msws_conj_intro projection_ok
              (AyMSWSConj audit_entry original_model)
              (ay_msws_report_requires_projection
                chunks_ok digests_ok manifest_ok projection_ok
                audit_entry original_model report)
              (ay_msws_conj_intro audit_entry original_model
                (ay_msws_report_audit
                  (AyMSWSStreamEvidence
                    chunks_ok digests_ok manifest_ok projection_ok)
                  audit_entry original_model report)
                (ay_msws_report_original
                  (AyMSWSStreamEvidence
                    chunks_ok digests_ok manifest_ok projection_ok)
                  audit_entry original_model report))))))
    (fun bundle =>
      ay_msws_report_intro
        (AyMSWSStreamEvidence
          chunks_ok digests_ok manifest_ok projection_ok)
        audit_entry original_model
        (ay_msws_stream_evidence_intro
          chunks_ok digests_ok manifest_ok projection_ok
          (ay_msws_conj_left chunks_ok
            (AyMSWSConj digests_ok
              (AyMSWSConj manifest_ok
                (AyMSWSConj projection_ok
                  (AyMSWSConj audit_entry original_model))))
            bundle)
          (ay_msws_conj_left digests_ok
            (AyMSWSConj manifest_ok
              (AyMSWSConj projection_ok
                (AyMSWSConj audit_entry original_model)))
            (ay_msws_conj_right chunks_ok
              (AyMSWSConj digests_ok
                (AyMSWSConj manifest_ok
                  (AyMSWSConj projection_ok
                    (AyMSWSConj audit_entry original_model))))
              bundle))
          (ay_msws_conj_left manifest_ok
            (AyMSWSConj projection_ok
              (AyMSWSConj audit_entry original_model))
            (ay_msws_conj_right digests_ok
              (AyMSWSConj manifest_ok
                (AyMSWSConj projection_ok
                  (AyMSWSConj audit_entry original_model)))
              (ay_msws_conj_right chunks_ok
                (AyMSWSConj digests_ok
                  (AyMSWSConj manifest_ok
                    (AyMSWSConj projection_ok
                      (AyMSWSConj audit_entry original_model))))
                bundle)))
          (ay_msws_conj_left projection_ok
            (AyMSWSConj audit_entry original_model)
            (ay_msws_conj_right manifest_ok
              (AyMSWSConj projection_ok
                (AyMSWSConj audit_entry original_model))
              (ay_msws_conj_right digests_ok
                (AyMSWSConj manifest_ok
                  (AyMSWSConj projection_ok
                    (AyMSWSConj audit_entry original_model)))
                (ay_msws_conj_right chunks_ok
                  (AyMSWSConj digests_ok
                    (AyMSWSConj manifest_ok
                      (AyMSWSConj projection_ok
                        (AyMSWSConj audit_entry original_model))))
                  bundle)))))
        (ay_msws_conj_left audit_entry original_model
          (ay_msws_conj_right projection_ok
            (AyMSWSConj audit_entry original_model)
            (ay_msws_conj_right manifest_ok
              (AyMSWSConj projection_ok
                (AyMSWSConj audit_entry original_model))
              (ay_msws_conj_right digests_ok
                (AyMSWSConj manifest_ok
                  (AyMSWSConj projection_ok
                    (AyMSWSConj audit_entry original_model)))
                (ay_msws_conj_right chunks_ok
                  (AyMSWSConj digests_ok
                    (AyMSWSConj manifest_ok
                      (AyMSWSConj projection_ok
                        (AyMSWSConj audit_entry original_model))))
                  bundle)))))
        (ay_msws_conj_right audit_entry original_model
          (ay_msws_conj_right projection_ok
            (AyMSWSConj audit_entry original_model)
            (ay_msws_conj_right manifest_ok
              (AyMSWSConj projection_ok
                (AyMSWSConj audit_entry original_model))
              (ay_msws_conj_right digests_ok
                (AyMSWSConj manifest_ok
                  (AyMSWSConj projection_ok
                    (AyMSWSConj audit_entry original_model)))
                (ay_msws_conj_right chunks_ok
                  (AyMSWSConj digests_ok
                    (AyMSWSConj manifest_ok
                      (AyMSWSConj projection_ok
                        (AyMSWSConj audit_entry original_model))))
                  bundle))))))

theorem ay_msws_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMSWSNoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_msws_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_msws_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSWSNoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_msws_conj_left diagnostic (public_claim -> False) diag

theorem ay_msws_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSWSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_msws_conj_right diagnostic (public_claim -> False) diag

theorem ay_msws_missing_chunk_no_claim
    (missing_chunk : Prop) (public_claim : Prop) :
    missing_chunk ->
    (public_claim -> missing_chunk -> False) ->
    AyMSWSNoClaimDiagnostic missing_chunk public_claim := by
  intro hmissing
  intro blocks
  exact ay_msws_no_claim_diagnostic_intro
    missing_chunk public_claim hmissing
    (fun claim => blocks claim hmissing)

theorem ay_msws_corrupt_chunk_no_claim
    (corrupt_chunk : Prop) (public_claim : Prop) :
    corrupt_chunk ->
    (public_claim -> corrupt_chunk -> False) ->
    AyMSWSNoClaimDiagnostic corrupt_chunk public_claim := by
  intro hcorrupt
  intro blocks
  exact ay_msws_no_claim_diagnostic_intro
    corrupt_chunk public_claim hcorrupt
    (fun claim => blocks claim hcorrupt)

theorem ay_msws_out_of_order_chunk_no_claim
    (out_of_order_chunk : Prop) (public_claim : Prop) :
    out_of_order_chunk ->
    (public_claim -> out_of_order_chunk -> False) ->
    AyMSWSNoClaimDiagnostic out_of_order_chunk public_claim := by
  intro hbad_order
  intro blocks
  exact ay_msws_no_claim_diagnostic_intro
    out_of_order_chunk public_claim hbad_order
    (fun claim => blocks claim hbad_order)

theorem ay_msws_diagnostic_blocks_public_claim
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSWSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_msws_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim

theorem ay_msws_bad_stream_no_stale_claim
    (missing_chunk : Prop) (corrupt_chunk : Prop)
    (out_of_order_chunk : Prop) (public_claim : Prop) :
    AyMSWSDisj missing_chunk
      (AyMSWSDisj corrupt_chunk out_of_order_chunk) ->
    (public_claim -> missing_chunk -> False) ->
    (public_claim -> corrupt_chunk -> False) ->
    (public_claim -> out_of_order_chunk -> False) ->
    AyMSWSDisj
      (AyMSWSNoClaimDiagnostic missing_chunk public_claim)
      (AyMSWSDisj
        (AyMSWSNoClaimDiagnostic corrupt_chunk public_claim)
        (AyMSWSNoClaimDiagnostic out_of_order_chunk public_claim)) := by
  intro bad_stream
  intro missing_blocks
  intro corrupt_blocks
  intro order_blocks
  exact bad_stream
    (AyMSWSDisj
      (AyMSWSNoClaimDiagnostic missing_chunk public_claim)
      (AyMSWSDisj
        (AyMSWSNoClaimDiagnostic corrupt_chunk public_claim)
        (AyMSWSNoClaimDiagnostic out_of_order_chunk public_claim)))
    (fun hmissing =>
      ay_msws_disj_left
        (AyMSWSNoClaimDiagnostic missing_chunk public_claim)
        (AyMSWSDisj
          (AyMSWSNoClaimDiagnostic corrupt_chunk public_claim)
          (AyMSWSNoClaimDiagnostic out_of_order_chunk public_claim))
        (ay_msws_missing_chunk_no_claim
          missing_chunk public_claim hmissing missing_blocks))
    (fun other_bad =>
      ay_msws_disj_right
        (AyMSWSNoClaimDiagnostic missing_chunk public_claim)
        (AyMSWSDisj
          (AyMSWSNoClaimDiagnostic corrupt_chunk public_claim)
          (AyMSWSNoClaimDiagnostic out_of_order_chunk public_claim))
        (other_bad
          (AyMSWSDisj
            (AyMSWSNoClaimDiagnostic corrupt_chunk public_claim)
            (AyMSWSNoClaimDiagnostic out_of_order_chunk public_claim))
          (fun hcorrupt =>
            ay_msws_disj_left
              (AyMSWSNoClaimDiagnostic corrupt_chunk public_claim)
              (AyMSWSNoClaimDiagnostic out_of_order_chunk public_claim)
              (ay_msws_corrupt_chunk_no_claim
                corrupt_chunk public_claim hcorrupt corrupt_blocks))
          (fun horder =>
            ay_msws_disj_right
              (AyMSWSNoClaimDiagnostic corrupt_chunk public_claim)
              (AyMSWSNoClaimDiagnostic out_of_order_chunk public_claim)
              (ay_msws_out_of_order_chunk_no_claim
                out_of_order_chunk public_claim horder order_blocks))))

