-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for streamed model delta-merge soundness.
-- Merged streamed models justify SAT reports only when base, delta, merge,
-- projection, digest, and audit evidence all agree. Bad merge evidence is a
-- diagnostic no-claim result.

def AyMSDMSConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMSDMSDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMSDMSEquisat (before : Prop) (after : Prop) :=
  AyMSDMSConj (before -> after) (after -> before)

def AyMSDMSStreamChunks
    (chunk_payloads : Prop) (chunk_order : Prop) :=
  AyMSDMSConj chunk_payloads chunk_order

def AyMSDMSCheckpointDigestGuard
    (checkpoint_guard : Prop) (digest_guard : Prop) :=
  AyMSDMSConj checkpoint_guard digest_guard

def AyMSDMSMergeWitness
    (base_stream : Prop) (delta_stream : Prop)
    (merged_stream : Prop) :=
  base_stream -> delta_stream -> merged_stream

def AyMSDMSReconstructionWitness
    (merged_stream : Prop) (full_assignment : Prop) :=
  merged_stream -> full_assignment

def AyMSDMSProjectionWitness
    (full_assignment : Prop) (original_model : Prop) :=
  full_assignment -> original_model

def AyMSDMSMergeEvidence
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop) :=
  AyMSDMSConj base_ok
    (AyMSDMSConj delta_ok
      (AyMSDMSConj merge_ok
        (AyMSDMSConj projection_ok digest_ok)))

def AyMSDMSAuditEntry
    (merge_evidence : Prop) (audit_digest : Prop) :=
  AyMSDMSConj merge_evidence audit_digest

def AyMSDMSAcceptedSatReport
    (merge_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :=
  AyMSDMSConj merge_evidence
    (AyMSDMSConj audit_entry original_model)

def AyMSDMSNoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMSDMSConj diagnostic (public_claim -> False)

theorem ay_msdms_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMSDMSConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_msdms_conj_left
    (left : Prop) (right : Prop) :
    AyMSDMSConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_msdms_conj_right
    (left : Prop) (right : Prop) :
    AyMSDMSConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_msdms_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMSDMSDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_msdms_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMSDMSDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_msdms_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMSDMSEquisat before after := by
  intro forward
  intro backward
  exact ay_msdms_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_msdms_equisat_forward
    (before : Prop) (after : Prop) :
    AyMSDMSEquisat before after -> before -> after := by
  intro certificate
  exact ay_msdms_conj_left (before -> after) (after -> before) certificate

theorem ay_msdms_equisat_backward
    (before : Prop) (after : Prop) :
    AyMSDMSEquisat before after -> after -> before := by
  intro certificate
  exact ay_msdms_conj_right (before -> after) (after -> before) certificate

theorem ay_msdms_stream_chunks_intro
    (chunk_payloads : Prop) (chunk_order : Prop) :
    chunk_payloads ->
    chunk_order ->
    AyMSDMSStreamChunks chunk_payloads chunk_order := by
  intro hpayloads
  intro horder
  exact ay_msdms_conj_intro chunk_payloads chunk_order hpayloads horder

theorem ay_msdms_stream_chunks_payloads
    (chunk_payloads : Prop) (chunk_order : Prop) :
    AyMSDMSStreamChunks chunk_payloads chunk_order ->
    chunk_payloads := by
  intro chunks
  exact ay_msdms_conj_left chunk_payloads chunk_order chunks

theorem ay_msdms_stream_chunks_order
    (chunk_payloads : Prop) (chunk_order : Prop) :
    AyMSDMSStreamChunks chunk_payloads chunk_order ->
    chunk_order := by
  intro chunks
  exact ay_msdms_conj_right chunk_payloads chunk_order chunks

theorem ay_msdms_checkpoint_digest_guard_intro
    (checkpoint_guard : Prop) (digest_guard : Prop) :
    checkpoint_guard ->
    digest_guard ->
    AyMSDMSCheckpointDigestGuard checkpoint_guard digest_guard := by
  intro hcheckpoint
  intro hdigest
  exact ay_msdms_conj_intro checkpoint_guard digest_guard
    hcheckpoint hdigest

theorem ay_msdms_checkpoint_digest_guard_checkpoint
    (checkpoint_guard : Prop) (digest_guard : Prop) :
    AyMSDMSCheckpointDigestGuard checkpoint_guard digest_guard ->
    checkpoint_guard := by
  intro guard
  exact ay_msdms_conj_left checkpoint_guard digest_guard guard

theorem ay_msdms_checkpoint_digest_guard_digest
    (checkpoint_guard : Prop) (digest_guard : Prop) :
    AyMSDMSCheckpointDigestGuard checkpoint_guard digest_guard ->
    digest_guard := by
  intro guard
  exact ay_msdms_conj_right checkpoint_guard digest_guard guard

theorem ay_msdms_merge_apply
    (base_stream : Prop) (delta_stream : Prop)
    (merged_stream : Prop) :
    AyMSDMSMergeWitness base_stream delta_stream merged_stream ->
    base_stream ->
    delta_stream ->
    merged_stream := by
  intro combine
  intro hbase
  intro hdelta
  exact combine hbase hdelta

theorem ay_msdms_reconstruct_apply
    (merged_stream : Prop) (full_assignment : Prop) :
    AyMSDMSReconstructionWitness merged_stream full_assignment ->
    merged_stream ->
    full_assignment := by
  intro reconstruct
  intro hmerged
  exact reconstruct hmerged

theorem ay_msdms_projection_apply
    (full_assignment : Prop) (original_model : Prop) :
    AyMSDMSProjectionWitness full_assignment original_model ->
    full_assignment ->
    original_model := by
  intro project
  intro hfull
  exact project hfull

theorem ay_msdms_merge_evidence_intro
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop) :
    base_ok ->
    delta_ok ->
    merge_ok ->
    projection_ok ->
    digest_ok ->
    AyMSDMSMergeEvidence
      base_ok delta_ok merge_ok projection_ok digest_ok := by
  intro hbase
  intro hdelta
  intro hmerge
  intro hprojection
  intro hdigest
  exact ay_msdms_conj_intro base_ok
    (AyMSDMSConj delta_ok
      (AyMSDMSConj merge_ok
        (AyMSDMSConj projection_ok digest_ok)))
    hbase
    (ay_msdms_conj_intro delta_ok
      (AyMSDMSConj merge_ok
        (AyMSDMSConj projection_ok digest_ok))
      hdelta
      (ay_msdms_conj_intro merge_ok
        (AyMSDMSConj projection_ok digest_ok)
        hmerge
        (ay_msdms_conj_intro projection_ok digest_ok
          hprojection hdigest)))

theorem ay_msdms_merge_evidence_base
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop) :
    AyMSDMSMergeEvidence
      base_ok delta_ok merge_ok projection_ok digest_ok ->
    base_ok := by
  intro evidence
  exact ay_msdms_conj_left base_ok
    (AyMSDMSConj delta_ok
      (AyMSDMSConj merge_ok
        (AyMSDMSConj projection_ok digest_ok))) evidence

theorem ay_msdms_merge_evidence_delta
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop) :
    AyMSDMSMergeEvidence
      base_ok delta_ok merge_ok projection_ok digest_ok ->
    delta_ok := by
  intro evidence
  exact ay_msdms_conj_left delta_ok
    (AyMSDMSConj merge_ok
      (AyMSDMSConj projection_ok digest_ok))
    (ay_msdms_conj_right base_ok
      (AyMSDMSConj delta_ok
        (AyMSDMSConj merge_ok
          (AyMSDMSConj projection_ok digest_ok))) evidence)

theorem ay_msdms_merge_evidence_merge
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop) :
    AyMSDMSMergeEvidence
      base_ok delta_ok merge_ok projection_ok digest_ok ->
    merge_ok := by
  intro evidence
  exact ay_msdms_conj_left merge_ok
    (AyMSDMSConj projection_ok digest_ok)
    (ay_msdms_conj_right delta_ok
      (AyMSDMSConj merge_ok
        (AyMSDMSConj projection_ok digest_ok))
      (ay_msdms_conj_right base_ok
        (AyMSDMSConj delta_ok
          (AyMSDMSConj merge_ok
            (AyMSDMSConj projection_ok digest_ok))) evidence))

theorem ay_msdms_merge_evidence_projection
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop) :
    AyMSDMSMergeEvidence
      base_ok delta_ok merge_ok projection_ok digest_ok ->
    projection_ok := by
  intro evidence
  exact ay_msdms_conj_left projection_ok digest_ok
    (ay_msdms_conj_right merge_ok
      (AyMSDMSConj projection_ok digest_ok)
      (ay_msdms_conj_right delta_ok
        (AyMSDMSConj merge_ok
          (AyMSDMSConj projection_ok digest_ok))
        (ay_msdms_conj_right base_ok
          (AyMSDMSConj delta_ok
            (AyMSDMSConj merge_ok
              (AyMSDMSConj projection_ok digest_ok))) evidence)))

theorem ay_msdms_merge_evidence_digest
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop) :
    AyMSDMSMergeEvidence
      base_ok delta_ok merge_ok projection_ok digest_ok ->
    digest_ok := by
  intro evidence
  exact ay_msdms_conj_right projection_ok digest_ok
    (ay_msdms_conj_right merge_ok
      (AyMSDMSConj projection_ok digest_ok)
      (ay_msdms_conj_right delta_ok
        (AyMSDMSConj merge_ok
          (AyMSDMSConj projection_ok digest_ok))
        (ay_msdms_conj_right base_ok
          (AyMSDMSConj delta_ok
            (AyMSDMSConj merge_ok
              (AyMSDMSConj projection_ok digest_ok))) evidence)))

theorem ay_msdms_audit_entry_intro
    (merge_evidence : Prop) (audit_digest : Prop) :
    merge_evidence ->
    audit_digest ->
    AyMSDMSAuditEntry merge_evidence audit_digest := by
  intro hevidence
  intro hdigest
  exact ay_msdms_conj_intro merge_evidence audit_digest
    hevidence hdigest

theorem ay_msdms_audit_entry_evidence
    (merge_evidence : Prop) (audit_digest : Prop) :
    AyMSDMSAuditEntry merge_evidence audit_digest ->
    merge_evidence := by
  intro audit
  exact ay_msdms_conj_left merge_evidence audit_digest audit

theorem ay_msdms_audit_entry_digest
    (merge_evidence : Prop) (audit_digest : Prop) :
    AyMSDMSAuditEntry merge_evidence audit_digest ->
    audit_digest := by
  intro audit
  exact ay_msdms_conj_right merge_evidence audit_digest audit

theorem ay_msdms_report_intro
    (merge_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    merge_evidence ->
    audit_entry ->
    original_model ->
    AyMSDMSAcceptedSatReport
      merge_evidence audit_entry original_model := by
  intro hevidence
  intro haudit
  intro horiginal
  exact ay_msdms_conj_intro merge_evidence
    (AyMSDMSConj audit_entry original_model)
    hevidence
    (ay_msdms_conj_intro audit_entry original_model
      haudit horiginal)

theorem ay_msdms_report_evidence
    (merge_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSDMSAcceptedSatReport
      merge_evidence audit_entry original_model ->
    merge_evidence := by
  intro report
  exact ay_msdms_conj_left merge_evidence
    (AyMSDMSConj audit_entry original_model) report

theorem ay_msdms_report_audit
    (merge_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSDMSAcceptedSatReport
      merge_evidence audit_entry original_model ->
    audit_entry := by
  intro report
  exact ay_msdms_conj_left audit_entry original_model
    (ay_msdms_conj_right merge_evidence
      (AyMSDMSConj audit_entry original_model) report)

theorem ay_msdms_report_original
    (merge_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSDMSAcceptedSatReport
      merge_evidence audit_entry original_model ->
    original_model := by
  intro report
  exact ay_msdms_conj_right audit_entry original_model
    (ay_msdms_conj_right merge_evidence
      (AyMSDMSConj audit_entry original_model) report)

theorem ay_msdms_merged_stream_original_model
    (base_stream : Prop) (delta_stream : Prop)
    (merged_stream : Prop) (full_assignment : Prop)
    (original_model : Prop) :
    AyMSDMSMergeWitness base_stream delta_stream merged_stream ->
    AyMSDMSReconstructionWitness merged_stream full_assignment ->
    AyMSDMSProjectionWitness full_assignment original_model ->
    base_stream ->
    delta_stream ->
    original_model := by
  intro combine
  intro reconstruct
  intro project
  intro hbase
  intro hdelta
  exact project (reconstruct (combine hbase hdelta))

theorem ay_msdms_merged_report_from_evidence
    (base_stream : Prop) (delta_stream : Prop)
    (merged_stream : Prop) (full_assignment : Prop)
    (original_model : Prop) (base_ok : Prop)
    (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop)
    (audit_entry : Prop) :
    AyMSDMSMergeWitness base_stream delta_stream merged_stream ->
    AyMSDMSReconstructionWitness merged_stream full_assignment ->
    AyMSDMSProjectionWitness full_assignment original_model ->
    base_stream ->
    delta_stream ->
    base_ok ->
    delta_ok ->
    merge_ok ->
    projection_ok ->
    digest_ok ->
    audit_entry ->
    AyMSDMSAcceptedSatReport
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model := by
  intro combine
  intro reconstruct
  intro project
  intro hbase
  intro hdelta
  intro hbase_ok
  intro hdelta_ok
  intro hmerge
  intro hprojection
  intro hdigest
  intro haudit
  exact ay_msdms_report_intro
    (AyMSDMSMergeEvidence
      base_ok delta_ok merge_ok projection_ok digest_ok)
    audit_entry original_model
    (ay_msdms_merge_evidence_intro
      base_ok delta_ok merge_ok projection_ok digest_ok
      hbase_ok hdelta_ok hmerge hprojection hdigest)
    haudit
    (project (reconstruct (combine hbase hdelta)))

theorem ay_msdms_report_requires_base
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSDMSAcceptedSatReport
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model ->
    base_ok := by
  intro report
  exact ay_msdms_merge_evidence_base
    base_ok delta_ok merge_ok projection_ok digest_ok
    (ay_msdms_report_evidence
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model report)

theorem ay_msdms_report_requires_delta
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSDMSAcceptedSatReport
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model ->
    delta_ok := by
  intro report
  exact ay_msdms_merge_evidence_delta
    base_ok delta_ok merge_ok projection_ok digest_ok
    (ay_msdms_report_evidence
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model report)

theorem ay_msdms_report_requires_merge
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSDMSAcceptedSatReport
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model ->
    merge_ok := by
  intro report
  exact ay_msdms_merge_evidence_merge
    base_ok delta_ok merge_ok projection_ok digest_ok
    (ay_msdms_report_evidence
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model report)

theorem ay_msdms_report_requires_projection
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSDMSAcceptedSatReport
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model ->
    projection_ok := by
  intro report
  exact ay_msdms_merge_evidence_projection
    base_ok delta_ok merge_ok projection_ok digest_ok
    (ay_msdms_report_evidence
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model report)

theorem ay_msdms_report_requires_digest
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSDMSAcceptedSatReport
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model ->
    digest_ok := by
  intro report
  exact ay_msdms_merge_evidence_digest
    base_ok delta_ok merge_ok projection_ok digest_ok
    (ay_msdms_report_evidence
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model report)

theorem ay_msdms_report_sound_exact
    (base_ok : Prop) (delta_ok : Prop) (merge_ok : Prop)
    (projection_ok : Prop) (digest_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSDMSEquisat
      (AyMSDMSAcceptedSatReport
        (AyMSDMSMergeEvidence
          base_ok delta_ok merge_ok projection_ok digest_ok)
        audit_entry original_model)
      (AyMSDMSConj
        (AyMSDMSMergeEvidence
          base_ok delta_ok merge_ok projection_ok digest_ok)
        (AyMSDMSConj audit_entry original_model)) := by
  exact ay_msdms_equisat_intro
    (AyMSDMSAcceptedSatReport
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      audit_entry original_model)
    (AyMSDMSConj
      (AyMSDMSMergeEvidence
        base_ok delta_ok merge_ok projection_ok digest_ok)
      (AyMSDMSConj audit_entry original_model))
    (fun report =>
      ay_msdms_conj_intro
        (AyMSDMSMergeEvidence
          base_ok delta_ok merge_ok projection_ok digest_ok)
        (AyMSDMSConj audit_entry original_model)
        (ay_msdms_report_evidence
          (AyMSDMSMergeEvidence
            base_ok delta_ok merge_ok projection_ok digest_ok)
          audit_entry original_model report)
        (ay_msdms_conj_intro audit_entry original_model
          (ay_msdms_report_audit
            (AyMSDMSMergeEvidence
              base_ok delta_ok merge_ok projection_ok digest_ok)
            audit_entry original_model report)
          (ay_msdms_report_original
            (AyMSDMSMergeEvidence
              base_ok delta_ok merge_ok projection_ok digest_ok)
            audit_entry original_model report)))
    (fun bundle =>
      ay_msdms_report_intro
        (AyMSDMSMergeEvidence
          base_ok delta_ok merge_ok projection_ok digest_ok)
        audit_entry original_model
        (ay_msdms_conj_left
          (AyMSDMSMergeEvidence
            base_ok delta_ok merge_ok projection_ok digest_ok)
          (AyMSDMSConj audit_entry original_model)
          bundle)
        (ay_msdms_conj_left audit_entry original_model
          (ay_msdms_conj_right
            (AyMSDMSMergeEvidence
              base_ok delta_ok merge_ok projection_ok digest_ok)
            (AyMSDMSConj audit_entry original_model)
            bundle))
        (ay_msdms_conj_right audit_entry original_model
          (ay_msdms_conj_right
            (AyMSDMSMergeEvidence
              base_ok delta_ok merge_ok projection_ok digest_ok)
            (AyMSDMSConj audit_entry original_model)
            bundle)))

theorem ay_msdms_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMSDMSNoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_msdms_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_msdms_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSDMSNoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_msdms_conj_left diagnostic (public_claim -> False) diag

theorem ay_msdms_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSDMSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_msdms_conj_right diagnostic (public_claim -> False) diag

theorem ay_msdms_merge_conflict_no_claim
    (merge_conflict : Prop) (public_claim : Prop) :
    merge_conflict ->
    (public_claim -> merge_conflict -> False) ->
    AyMSDMSNoClaimDiagnostic merge_conflict public_claim := by
  intro hconflict
  intro blocks
  exact ay_msdms_no_claim_diagnostic_intro
    merge_conflict public_claim hconflict
    (fun claim => blocks claim hconflict)

theorem ay_msdms_missing_evidence_no_claim
    (missing_evidence : Prop) (public_claim : Prop) :
    missing_evidence ->
    (public_claim -> missing_evidence -> False) ->
    AyMSDMSNoClaimDiagnostic missing_evidence public_claim := by
  intro hmissing
  intro blocks
  exact ay_msdms_no_claim_diagnostic_intro
    missing_evidence public_claim hmissing
    (fun claim => blocks claim hmissing)

theorem ay_msdms_corrupt_chunk_no_claim
    (corrupt_chunk : Prop) (public_claim : Prop) :
    corrupt_chunk ->
    (public_claim -> corrupt_chunk -> False) ->
    AyMSDMSNoClaimDiagnostic corrupt_chunk public_claim := by
  intro hcorrupt
  intro blocks
  exact ay_msdms_no_claim_diagnostic_intro
    corrupt_chunk public_claim hcorrupt
    (fun claim => blocks claim hcorrupt)

theorem ay_msdms_diagnostic_blocks_public_claim
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSDMSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_msdms_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim

theorem ay_msdms_bad_merge_or_chunk_no_stale_claim
    (merge_conflict : Prop) (missing_evidence : Prop)
    (corrupt_chunk : Prop) (public_claim : Prop) :
    AyMSDMSDisj merge_conflict
      (AyMSDMSDisj missing_evidence corrupt_chunk) ->
    (public_claim -> merge_conflict -> False) ->
    (public_claim -> missing_evidence -> False) ->
    (public_claim -> corrupt_chunk -> False) ->
    AyMSDMSDisj
      (AyMSDMSNoClaimDiagnostic merge_conflict public_claim)
      (AyMSDMSDisj
        (AyMSDMSNoClaimDiagnostic missing_evidence public_claim)
        (AyMSDMSNoClaimDiagnostic corrupt_chunk public_claim)) := by
  intro bad
  intro conflict_blocks
  intro missing_blocks
  intro corrupt_blocks
  exact bad
    (AyMSDMSDisj
      (AyMSDMSNoClaimDiagnostic merge_conflict public_claim)
      (AyMSDMSDisj
        (AyMSDMSNoClaimDiagnostic missing_evidence public_claim)
        (AyMSDMSNoClaimDiagnostic corrupt_chunk public_claim)))
    (fun hconflict =>
      ay_msdms_disj_left
        (AyMSDMSNoClaimDiagnostic merge_conflict public_claim)
        (AyMSDMSDisj
          (AyMSDMSNoClaimDiagnostic missing_evidence public_claim)
          (AyMSDMSNoClaimDiagnostic corrupt_chunk public_claim))
        (ay_msdms_merge_conflict_no_claim
          merge_conflict public_claim hconflict conflict_blocks))
    (fun other_bad =>
      ay_msdms_disj_right
        (AyMSDMSNoClaimDiagnostic merge_conflict public_claim)
        (AyMSDMSDisj
          (AyMSDMSNoClaimDiagnostic missing_evidence public_claim)
          (AyMSDMSNoClaimDiagnostic corrupt_chunk public_claim))
        (other_bad
          (AyMSDMSDisj
            (AyMSDMSNoClaimDiagnostic missing_evidence public_claim)
            (AyMSDMSNoClaimDiagnostic corrupt_chunk public_claim))
          (fun hmissing =>
            ay_msdms_disj_left
              (AyMSDMSNoClaimDiagnostic missing_evidence public_claim)
              (AyMSDMSNoClaimDiagnostic corrupt_chunk public_claim)
              (ay_msdms_missing_evidence_no_claim
                missing_evidence public_claim hmissing missing_blocks))
          (fun hcorrupt =>
            ay_msdms_disj_right
              (AyMSDMSNoClaimDiagnostic missing_evidence public_claim)
              (AyMSDMSNoClaimDiagnostic corrupt_chunk public_claim)
              (ay_msdms_corrupt_chunk_no_claim
                corrupt_chunk public_claim hcorrupt corrupt_blocks))))
