-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for archived streamed-model soundness.
-- Public SAT claims reconstructed from archive chunks require membership,
-- ordering, digest/checkpoint guards, formula/equisat reconstruction, and
-- audit evidence. Bad archive evidence is diagnostic no-claim/recompute data.

def AyMSASConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMSASDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMSASEquisat (before : Prop) (after : Prop) :=
  AyMSASConj (before -> after) (after -> before)

def AyMSASArchiveMembership
    (archive_id : Prop) (chunk_membership : Prop) :=
  AyMSASConj archive_id chunk_membership

def AyMSASArchivedChunks
    (chunk_payloads : Prop) (chunk_order : Prop) :=
  AyMSASConj chunk_payloads chunk_order

def AyMSASDigestCheckpointGuard
    (digest_guard : Prop) (checkpoint_guard : Prop) :=
  AyMSASConj digest_guard checkpoint_guard

def AyMSASFormulaReconstruction
    (archived_chunks : Prop) (visible_model : Prop) :=
  archived_chunks -> visible_model

def AyMSASOriginalProjection
    (visible_model : Prop) (original_model : Prop) :=
  visible_model -> original_model

def AyMSASArchiveEvidence
    (membership_ok : Prop) (order_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop) :=
  AyMSASConj membership_ok
    (AyMSASConj order_ok
      (AyMSASConj guard_ok reconstruction_ok))

def AyMSASAuditEntry
    (archive_evidence : Prop) (audit_digest : Prop) :=
  AyMSASConj archive_evidence audit_digest

def AyMSASAcceptedSatReport
    (archive_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :=
  AyMSASConj archive_evidence
    (AyMSASConj audit_entry original_model)

def AyMSASNoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMSASConj diagnostic (public_claim -> False)

def AyMSASRecomputeObligation
    (reason : Prop) (recompute_request : Prop) :=
  AyMSASConj reason recompute_request

theorem ay_msas_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMSASConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_msas_conj_left
    (left : Prop) (right : Prop) :
    AyMSASConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_msas_conj_right
    (left : Prop) (right : Prop) :
    AyMSASConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_msas_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMSASDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_msas_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMSASDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_msas_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMSASEquisat before after := by
  intro forward
  intro backward
  exact ay_msas_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_msas_equisat_forward
    (before : Prop) (after : Prop) :
    AyMSASEquisat before after -> before -> after := by
  intro certificate
  exact ay_msas_conj_left (before -> after) (after -> before) certificate

theorem ay_msas_equisat_backward
    (before : Prop) (after : Prop) :
    AyMSASEquisat before after -> after -> before := by
  intro certificate
  exact ay_msas_conj_right (before -> after) (after -> before) certificate

theorem ay_msas_archive_membership_intro
    (archive_id : Prop) (chunk_membership : Prop) :
    archive_id ->
    chunk_membership ->
    AyMSASArchiveMembership archive_id chunk_membership := by
  intro harchive
  intro hmembership
  exact ay_msas_conj_intro archive_id chunk_membership
    harchive hmembership

theorem ay_msas_archive_membership_id
    (archive_id : Prop) (chunk_membership : Prop) :
    AyMSASArchiveMembership archive_id chunk_membership ->
    archive_id := by
  intro membership
  exact ay_msas_conj_left archive_id chunk_membership membership

theorem ay_msas_archive_membership_chunks
    (archive_id : Prop) (chunk_membership : Prop) :
    AyMSASArchiveMembership archive_id chunk_membership ->
    chunk_membership := by
  intro membership
  exact ay_msas_conj_right archive_id chunk_membership membership

theorem ay_msas_archived_chunks_intro
    (chunk_payloads : Prop) (chunk_order : Prop) :
    chunk_payloads ->
    chunk_order ->
    AyMSASArchivedChunks chunk_payloads chunk_order := by
  intro hpayloads
  intro horder
  exact ay_msas_conj_intro chunk_payloads chunk_order
    hpayloads horder

theorem ay_msas_archived_chunks_payloads
    (chunk_payloads : Prop) (chunk_order : Prop) :
    AyMSASArchivedChunks chunk_payloads chunk_order ->
    chunk_payloads := by
  intro chunks
  exact ay_msas_conj_left chunk_payloads chunk_order chunks

theorem ay_msas_archived_chunks_order
    (chunk_payloads : Prop) (chunk_order : Prop) :
    AyMSASArchivedChunks chunk_payloads chunk_order ->
    chunk_order := by
  intro chunks
  exact ay_msas_conj_right chunk_payloads chunk_order chunks

theorem ay_msas_digest_checkpoint_guard_intro
    (digest_guard : Prop) (checkpoint_guard : Prop) :
    digest_guard ->
    checkpoint_guard ->
    AyMSASDigestCheckpointGuard digest_guard checkpoint_guard := by
  intro hdigest
  intro hcheckpoint
  exact ay_msas_conj_intro digest_guard checkpoint_guard
    hdigest hcheckpoint

theorem ay_msas_digest_checkpoint_guard_digest
    (digest_guard : Prop) (checkpoint_guard : Prop) :
    AyMSASDigestCheckpointGuard digest_guard checkpoint_guard ->
    digest_guard := by
  intro guard
  exact ay_msas_conj_left digest_guard checkpoint_guard guard

theorem ay_msas_digest_checkpoint_guard_checkpoint
    (digest_guard : Prop) (checkpoint_guard : Prop) :
    AyMSASDigestCheckpointGuard digest_guard checkpoint_guard ->
    checkpoint_guard := by
  intro guard
  exact ay_msas_conj_right digest_guard checkpoint_guard guard

theorem ay_msas_formula_reconstruct_apply
    (archived_chunks : Prop) (visible_model : Prop) :
    AyMSASFormulaReconstruction archived_chunks visible_model ->
    archived_chunks ->
    visible_model := by
  intro reconstruct
  intro hchunks
  exact reconstruct hchunks

theorem ay_msas_original_project_apply
    (visible_model : Prop) (original_model : Prop) :
    AyMSASOriginalProjection visible_model original_model ->
    visible_model ->
    original_model := by
  intro project
  intro hvisible
  exact project hvisible

theorem ay_msas_archive_evidence_intro
    (membership_ok : Prop) (order_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop) :
    membership_ok ->
    order_ok ->
    guard_ok ->
    reconstruction_ok ->
    AyMSASArchiveEvidence
      membership_ok order_ok guard_ok reconstruction_ok := by
  intro hmembership
  intro horder
  intro hguard
  intro hreconstruct
  exact ay_msas_conj_intro membership_ok
    (AyMSASConj order_ok
      (AyMSASConj guard_ok reconstruction_ok))
    hmembership
    (ay_msas_conj_intro order_ok
      (AyMSASConj guard_ok reconstruction_ok)
      horder
      (ay_msas_conj_intro guard_ok reconstruction_ok
        hguard hreconstruct))

theorem ay_msas_archive_evidence_membership
    (membership_ok : Prop) (order_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop) :
    AyMSASArchiveEvidence
      membership_ok order_ok guard_ok reconstruction_ok ->
    membership_ok := by
  intro evidence
  exact ay_msas_conj_left membership_ok
    (AyMSASConj order_ok
      (AyMSASConj guard_ok reconstruction_ok)) evidence

theorem ay_msas_archive_evidence_order
    (membership_ok : Prop) (order_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop) :
    AyMSASArchiveEvidence
      membership_ok order_ok guard_ok reconstruction_ok ->
    order_ok := by
  intro evidence
  exact ay_msas_conj_left order_ok
    (AyMSASConj guard_ok reconstruction_ok)
    (ay_msas_conj_right membership_ok
      (AyMSASConj order_ok
        (AyMSASConj guard_ok reconstruction_ok)) evidence)

theorem ay_msas_archive_evidence_guard
    (membership_ok : Prop) (order_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop) :
    AyMSASArchiveEvidence
      membership_ok order_ok guard_ok reconstruction_ok ->
    guard_ok := by
  intro evidence
  exact ay_msas_conj_left guard_ok reconstruction_ok
    (ay_msas_conj_right order_ok
      (AyMSASConj guard_ok reconstruction_ok)
      (ay_msas_conj_right membership_ok
        (AyMSASConj order_ok
          (AyMSASConj guard_ok reconstruction_ok)) evidence))

theorem ay_msas_archive_evidence_reconstruction
    (membership_ok : Prop) (order_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop) :
    AyMSASArchiveEvidence
      membership_ok order_ok guard_ok reconstruction_ok ->
    reconstruction_ok := by
  intro evidence
  exact ay_msas_conj_right guard_ok reconstruction_ok
    (ay_msas_conj_right order_ok
      (AyMSASConj guard_ok reconstruction_ok)
      (ay_msas_conj_right membership_ok
        (AyMSASConj order_ok
          (AyMSASConj guard_ok reconstruction_ok)) evidence))

theorem ay_msas_audit_entry_intro
    (archive_evidence : Prop) (audit_digest : Prop) :
    archive_evidence ->
    audit_digest ->
    AyMSASAuditEntry archive_evidence audit_digest := by
  intro hevidence
  intro hdigest
  exact ay_msas_conj_intro archive_evidence audit_digest
    hevidence hdigest

theorem ay_msas_audit_entry_evidence
    (archive_evidence : Prop) (audit_digest : Prop) :
    AyMSASAuditEntry archive_evidence audit_digest ->
    archive_evidence := by
  intro audit
  exact ay_msas_conj_left archive_evidence audit_digest audit

theorem ay_msas_audit_entry_digest
    (archive_evidence : Prop) (audit_digest : Prop) :
    AyMSASAuditEntry archive_evidence audit_digest ->
    audit_digest := by
  intro audit
  exact ay_msas_conj_right archive_evidence audit_digest audit

theorem ay_msas_report_intro
    (archive_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    archive_evidence ->
    audit_entry ->
    original_model ->
    AyMSASAcceptedSatReport
      archive_evidence audit_entry original_model := by
  intro hevidence
  intro haudit
  intro horiginal
  exact ay_msas_conj_intro archive_evidence
    (AyMSASConj audit_entry original_model)
    hevidence
    (ay_msas_conj_intro audit_entry original_model haudit horiginal)

theorem ay_msas_report_evidence
    (archive_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSASAcceptedSatReport
      archive_evidence audit_entry original_model ->
    archive_evidence := by
  intro report
  exact ay_msas_conj_left archive_evidence
    (AyMSASConj audit_entry original_model) report

theorem ay_msas_report_audit
    (archive_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSASAcceptedSatReport
      archive_evidence audit_entry original_model ->
    audit_entry := by
  intro report
  exact ay_msas_conj_left audit_entry original_model
    (ay_msas_conj_right archive_evidence
      (AyMSASConj audit_entry original_model) report)

theorem ay_msas_report_original
    (archive_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSASAcceptedSatReport
      archive_evidence audit_entry original_model ->
    original_model := by
  intro report
  exact ay_msas_conj_right audit_entry original_model
    (ay_msas_conj_right archive_evidence
      (AyMSASConj audit_entry original_model) report)

theorem ay_msas_archived_original_model
    (archived_chunks : Prop) (visible_model : Prop)
    (original_model : Prop) :
    AyMSASFormulaReconstruction archived_chunks visible_model ->
    AyMSASOriginalProjection visible_model original_model ->
    archived_chunks ->
    original_model := by
  intro reconstruct
  intro project
  intro hchunks
  exact project (reconstruct hchunks)

theorem ay_msas_archived_report_from_evidence
    (archived_chunks : Prop) (visible_model : Prop)
    (original_model : Prop) (membership_ok : Prop)
    (order_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) (audit_entry : Prop) :
    AyMSASFormulaReconstruction archived_chunks visible_model ->
    AyMSASOriginalProjection visible_model original_model ->
    archived_chunks ->
    membership_ok ->
    order_ok ->
    guard_ok ->
    reconstruction_ok ->
    audit_entry ->
    AyMSASAcceptedSatReport
      (AyMSASArchiveEvidence
        membership_ok order_ok guard_ok reconstruction_ok)
      audit_entry original_model := by
  intro reconstruct
  intro project
  intro hchunks
  intro hmembership
  intro horder
  intro hguard
  intro hreconstruction
  intro haudit
  exact ay_msas_report_intro
    (AyMSASArchiveEvidence
      membership_ok order_ok guard_ok reconstruction_ok)
    audit_entry original_model
    (ay_msas_archive_evidence_intro
      membership_ok order_ok guard_ok reconstruction_ok
      hmembership horder hguard hreconstruction)
    haudit
    (project (reconstruct hchunks))

theorem ay_msas_report_requires_membership
    (membership_ok : Prop) (order_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSASAcceptedSatReport
      (AyMSASArchiveEvidence
        membership_ok order_ok guard_ok reconstruction_ok)
      audit_entry original_model ->
    membership_ok := by
  intro report
  exact ay_msas_archive_evidence_membership
    membership_ok order_ok guard_ok reconstruction_ok
    (ay_msas_report_evidence
      (AyMSASArchiveEvidence
        membership_ok order_ok guard_ok reconstruction_ok)
      audit_entry original_model report)

theorem ay_msas_report_requires_order
    (membership_ok : Prop) (order_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSASAcceptedSatReport
      (AyMSASArchiveEvidence
        membership_ok order_ok guard_ok reconstruction_ok)
      audit_entry original_model ->
    order_ok := by
  intro report
  exact ay_msas_archive_evidence_order
    membership_ok order_ok guard_ok reconstruction_ok
    (ay_msas_report_evidence
      (AyMSASArchiveEvidence
        membership_ok order_ok guard_ok reconstruction_ok)
      audit_entry original_model report)

theorem ay_msas_report_requires_guard
    (membership_ok : Prop) (order_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSASAcceptedSatReport
      (AyMSASArchiveEvidence
        membership_ok order_ok guard_ok reconstruction_ok)
      audit_entry original_model ->
    guard_ok := by
  intro report
  exact ay_msas_archive_evidence_guard
    membership_ok order_ok guard_ok reconstruction_ok
    (ay_msas_report_evidence
      (AyMSASArchiveEvidence
        membership_ok order_ok guard_ok reconstruction_ok)
      audit_entry original_model report)

theorem ay_msas_report_requires_reconstruction
    (membership_ok : Prop) (order_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSASAcceptedSatReport
      (AyMSASArchiveEvidence
        membership_ok order_ok guard_ok reconstruction_ok)
      audit_entry original_model ->
    reconstruction_ok := by
  intro report
  exact ay_msas_archive_evidence_reconstruction
    membership_ok order_ok guard_ok reconstruction_ok
    (ay_msas_report_evidence
      (AyMSASArchiveEvidence
        membership_ok order_ok guard_ok reconstruction_ok)
      audit_entry original_model report)

theorem ay_msas_report_sound_exact
    (membership_ok : Prop) (order_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSASEquisat
      (AyMSASAcceptedSatReport
        (AyMSASArchiveEvidence
          membership_ok order_ok guard_ok reconstruction_ok)
        audit_entry original_model)
      (AyMSASConj
        (AyMSASArchiveEvidence
          membership_ok order_ok guard_ok reconstruction_ok)
        (AyMSASConj audit_entry original_model)) := by
  exact ay_msas_equisat_intro
    (AyMSASAcceptedSatReport
      (AyMSASArchiveEvidence
        membership_ok order_ok guard_ok reconstruction_ok)
      audit_entry original_model)
    (AyMSASConj
      (AyMSASArchiveEvidence
        membership_ok order_ok guard_ok reconstruction_ok)
      (AyMSASConj audit_entry original_model))
    (fun report =>
      ay_msas_conj_intro
        (AyMSASArchiveEvidence
          membership_ok order_ok guard_ok reconstruction_ok)
        (AyMSASConj audit_entry original_model)
        (ay_msas_report_evidence
          (AyMSASArchiveEvidence
            membership_ok order_ok guard_ok reconstruction_ok)
          audit_entry original_model report)
        (ay_msas_conj_intro audit_entry original_model
          (ay_msas_report_audit
            (AyMSASArchiveEvidence
              membership_ok order_ok guard_ok reconstruction_ok)
            audit_entry original_model report)
          (ay_msas_report_original
            (AyMSASArchiveEvidence
              membership_ok order_ok guard_ok reconstruction_ok)
            audit_entry original_model report)))
    (fun bundle =>
      ay_msas_report_intro
        (AyMSASArchiveEvidence
          membership_ok order_ok guard_ok reconstruction_ok)
        audit_entry original_model
        (ay_msas_conj_left
          (AyMSASArchiveEvidence
            membership_ok order_ok guard_ok reconstruction_ok)
          (AyMSASConj audit_entry original_model)
          bundle)
        (ay_msas_conj_left audit_entry original_model
          (ay_msas_conj_right
            (AyMSASArchiveEvidence
              membership_ok order_ok guard_ok reconstruction_ok)
            (AyMSASConj audit_entry original_model)
            bundle))
        (ay_msas_conj_right audit_entry original_model
          (ay_msas_conj_right
            (AyMSASArchiveEvidence
              membership_ok order_ok guard_ok reconstruction_ok)
            (AyMSASConj audit_entry original_model)
            bundle)))

theorem ay_msas_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMSASNoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_msas_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_msas_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSASNoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_msas_conj_left diagnostic (public_claim -> False) diag

theorem ay_msas_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSASNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_msas_conj_right diagnostic (public_claim -> False) diag

theorem ay_msas_recompute_obligation_intro
    (reason : Prop) (recompute_request : Prop) :
    reason ->
    recompute_request ->
    AyMSASRecomputeObligation reason recompute_request := by
  intro hreason
  intro hrequest
  exact ay_msas_conj_intro reason recompute_request hreason hrequest

theorem ay_msas_recompute_obligation_reason
    (reason : Prop) (recompute_request : Prop) :
    AyMSASRecomputeObligation reason recompute_request ->
    reason := by
  intro obligation
  exact ay_msas_conj_left reason recompute_request obligation

theorem ay_msas_recompute_obligation_request
    (reason : Prop) (recompute_request : Prop) :
    AyMSASRecomputeObligation reason recompute_request ->
    recompute_request := by
  intro obligation
  exact ay_msas_conj_right reason recompute_request obligation

theorem ay_msas_stale_archive_no_claim
    (stale_archive : Prop) (public_claim : Prop) :
    stale_archive ->
    (public_claim -> stale_archive -> False) ->
    AyMSASNoClaimDiagnostic stale_archive public_claim := by
  intro hstale
  intro blocks
  exact ay_msas_no_claim_diagnostic_intro
    stale_archive public_claim hstale
    (fun claim => blocks claim hstale)

theorem ay_msas_missing_archive_recompute
    (missing_archive : Prop) (recompute_request : Prop) :
    missing_archive ->
    recompute_request ->
    AyMSASRecomputeObligation missing_archive recompute_request := by
  intro hmissing
  intro hrequest
  exact ay_msas_recompute_obligation_intro
    missing_archive recompute_request hmissing hrequest

theorem ay_msas_missing_archive_no_claim
    (missing_archive : Prop) (public_claim : Prop) :
    missing_archive ->
    (public_claim -> missing_archive -> False) ->
    AyMSASNoClaimDiagnostic missing_archive public_claim := by
  intro hmissing
  intro blocks
  exact ay_msas_no_claim_diagnostic_intro
    missing_archive public_claim hmissing
    (fun claim => blocks claim hmissing)

theorem ay_msas_reordered_archive_no_claim
    (reordered_archive : Prop) (public_claim : Prop) :
    reordered_archive ->
    (public_claim -> reordered_archive -> False) ->
    AyMSASNoClaimDiagnostic reordered_archive public_claim := by
  intro hreordered
  intro blocks
  exact ay_msas_no_claim_diagnostic_intro
    reordered_archive public_claim hreordered
    (fun claim => blocks claim hreordered)

theorem ay_msas_corrupt_archive_no_claim
    (corrupt_archive : Prop) (public_claim : Prop) :
    corrupt_archive ->
    (public_claim -> corrupt_archive -> False) ->
    AyMSASNoClaimDiagnostic corrupt_archive public_claim := by
  intro hcorrupt
  intro blocks
  exact ay_msas_no_claim_diagnostic_intro
    corrupt_archive public_claim hcorrupt
    (fun claim => blocks claim hcorrupt)

theorem ay_msas_diagnostic_blocks_public_claim
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSASNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_msas_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim

theorem ay_msas_bad_archive_no_stale_public_claim
    (stale_archive : Prop) (missing_archive : Prop)
    (reordered_archive : Prop) (corrupt_archive : Prop)
    (public_claim : Prop) :
    (public_claim -> stale_archive -> False) ->
    (public_claim -> missing_archive -> False) ->
    (public_claim -> reordered_archive -> False) ->
    (public_claim -> corrupt_archive -> False) ->
    AyMSASConj
      (stale_archive ->
        AyMSASNoClaimDiagnostic stale_archive public_claim)
      (AyMSASConj
        (missing_archive ->
          AyMSASNoClaimDiagnostic missing_archive public_claim)
        (AyMSASConj
          (reordered_archive ->
            AyMSASNoClaimDiagnostic reordered_archive public_claim)
          (corrupt_archive ->
            AyMSASNoClaimDiagnostic corrupt_archive public_claim))) := by
  intro stale_blocks
  intro missing_blocks
  intro reordered_blocks
  intro corrupt_blocks
  exact ay_msas_conj_intro
    (stale_archive ->
      AyMSASNoClaimDiagnostic stale_archive public_claim)
    (AyMSASConj
      (missing_archive ->
        AyMSASNoClaimDiagnostic missing_archive public_claim)
      (AyMSASConj
        (reordered_archive ->
          AyMSASNoClaimDiagnostic reordered_archive public_claim)
        (corrupt_archive ->
          AyMSASNoClaimDiagnostic corrupt_archive public_claim)))
    (fun hstale =>
      ay_msas_stale_archive_no_claim
        stale_archive public_claim hstale stale_blocks)
    (ay_msas_conj_intro
      (missing_archive ->
        AyMSASNoClaimDiagnostic missing_archive public_claim)
      (AyMSASConj
        (reordered_archive ->
          AyMSASNoClaimDiagnostic reordered_archive public_claim)
        (corrupt_archive ->
          AyMSASNoClaimDiagnostic corrupt_archive public_claim))
      (fun hmissing =>
        ay_msas_missing_archive_no_claim
          missing_archive public_claim hmissing missing_blocks)
      (ay_msas_conj_intro
        (reordered_archive ->
          AyMSASNoClaimDiagnostic reordered_archive public_claim)
        (corrupt_archive ->
          AyMSASNoClaimDiagnostic corrupt_archive public_claim)
        (fun hreordered =>
          ay_msas_reordered_archive_no_claim
            reordered_archive public_claim hreordered reordered_blocks)
        (fun hcorrupt =>
          ay_msas_corrupt_archive_no_claim
            corrupt_archive public_claim hcorrupt corrupt_blocks)))
