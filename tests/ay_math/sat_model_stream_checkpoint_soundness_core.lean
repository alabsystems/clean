-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for checkpointed streamed model witnesses.
-- A resumed model stream is public only when checkpoint digests, resume
-- manifests, reconstruction/projection witnesses, and audit evidence agree.
-- Bad checkpoints or streams are diagnostic no-claim facts.

def AyMSCSConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMSCSDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMSCSEquisat (before : Prop) (after : Prop) :=
  AyMSCSConj (before -> after) (after -> before)

def AyMSCSAssignmentStream
    (prefix_chunks : Prop) (resume_chunks : Prop) (chunk_order : Prop) :=
  AyMSCSConj prefix_chunks (AyMSCSConj resume_chunks chunk_order)

def AyMSCSCheckpointDigests
    (prefix_digest : Prop) (resume_digest : Prop) (root_digest : Prop) :=
  AyMSCSConj prefix_digest (AyMSCSConj resume_digest root_digest)

def AyMSCSResumeManifest
    (stream_id : Prop) (checkpoint_id : Prop) (manifest_guard : Prop) :=
  AyMSCSConj stream_id (AyMSCSConj checkpoint_id manifest_guard)

def AyMSCSCheckpointMatch
    (checkpoint_digests : Prop) (resume_manifest : Prop) :=
  AyMSCSConj checkpoint_digests resume_manifest

def AyMSCSReconstructionWitness
    (assignment_stream : Prop) (full_assignment : Prop) :=
  assignment_stream -> full_assignment

def AyMSCSProjectionWitness
    (full_assignment : Prop) (original_model : Prop) :=
  full_assignment -> original_model

def AyMSCSStreamEvidence
    (checkpoint_ok : Prop) (chunks_ok : Prop)
    (projection_ok : Prop) (audit_ok : Prop) :=
  AyMSCSConj checkpoint_ok
    (AyMSCSConj chunks_ok
      (AyMSCSConj projection_ok audit_ok))

def AyMSCSAuditEntry
    (stream_evidence : Prop) (audit_digest : Prop) :=
  AyMSCSConj stream_evidence audit_digest

def AyMSCSAcceptedSatReport
    (stream_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :=
  AyMSCSConj stream_evidence
    (AyMSCSConj audit_entry original_model)

def AyMSCSNoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMSCSConj diagnostic (public_claim -> False)

theorem ay_mscs_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMSCSConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mscs_conj_left
    (left : Prop) (right : Prop) :
    AyMSCSConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mscs_conj_right
    (left : Prop) (right : Prop) :
    AyMSCSConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mscs_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMSCSDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mscs_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMSCSDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mscs_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMSCSEquisat before after := by
  intro forward
  intro backward
  exact ay_mscs_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_mscs_equisat_forward
    (before : Prop) (after : Prop) :
    AyMSCSEquisat before after -> before -> after := by
  intro certificate
  exact ay_mscs_conj_left (before -> after) (after -> before) certificate

theorem ay_mscs_equisat_backward
    (before : Prop) (after : Prop) :
    AyMSCSEquisat before after -> after -> before := by
  intro certificate
  exact ay_mscs_conj_right (before -> after) (after -> before) certificate

theorem ay_mscs_assignment_stream_intro
    (prefix_chunks : Prop) (resume_chunks : Prop)
    (chunk_order : Prop) :
    prefix_chunks ->
    resume_chunks ->
    chunk_order ->
    AyMSCSAssignmentStream prefix_chunks resume_chunks chunk_order := by
  intro hprefix
  intro hresume
  intro horder
  exact ay_mscs_conj_intro prefix_chunks
    (AyMSCSConj resume_chunks chunk_order)
    hprefix
    (ay_mscs_conj_intro resume_chunks chunk_order
      hresume horder)

theorem ay_mscs_assignment_stream_prefix
    (prefix_chunks : Prop) (resume_chunks : Prop)
    (chunk_order : Prop) :
    AyMSCSAssignmentStream prefix_chunks resume_chunks chunk_order ->
    prefix_chunks := by
  intro stream
  exact ay_mscs_conj_left prefix_chunks
    (AyMSCSConj resume_chunks chunk_order) stream

theorem ay_mscs_assignment_stream_resume
    (prefix_chunks : Prop) (resume_chunks : Prop)
    (chunk_order : Prop) :
    AyMSCSAssignmentStream prefix_chunks resume_chunks chunk_order ->
    resume_chunks := by
  intro stream
  exact ay_mscs_conj_left resume_chunks chunk_order
    (ay_mscs_conj_right prefix_chunks
      (AyMSCSConj resume_chunks chunk_order) stream)

theorem ay_mscs_assignment_stream_order
    (prefix_chunks : Prop) (resume_chunks : Prop)
    (chunk_order : Prop) :
    AyMSCSAssignmentStream prefix_chunks resume_chunks chunk_order ->
    chunk_order := by
  intro stream
  exact ay_mscs_conj_right resume_chunks chunk_order
    (ay_mscs_conj_right prefix_chunks
      (AyMSCSConj resume_chunks chunk_order) stream)

theorem ay_mscs_checkpoint_digests_intro
    (prefix_digest : Prop) (resume_digest : Prop)
    (root_digest : Prop) :
    prefix_digest ->
    resume_digest ->
    root_digest ->
    AyMSCSCheckpointDigests prefix_digest resume_digest root_digest := by
  intro hprefix
  intro hresume
  intro hroot
  exact ay_mscs_conj_intro prefix_digest
    (AyMSCSConj resume_digest root_digest)
    hprefix
    (ay_mscs_conj_intro resume_digest root_digest hresume hroot)

theorem ay_mscs_checkpoint_digests_prefix
    (prefix_digest : Prop) (resume_digest : Prop)
    (root_digest : Prop) :
    AyMSCSCheckpointDigests prefix_digest resume_digest root_digest ->
    prefix_digest := by
  intro digests
  exact ay_mscs_conj_left prefix_digest
    (AyMSCSConj resume_digest root_digest) digests

theorem ay_mscs_checkpoint_digests_resume
    (prefix_digest : Prop) (resume_digest : Prop)
    (root_digest : Prop) :
    AyMSCSCheckpointDigests prefix_digest resume_digest root_digest ->
    resume_digest := by
  intro digests
  exact ay_mscs_conj_left resume_digest root_digest
    (ay_mscs_conj_right prefix_digest
      (AyMSCSConj resume_digest root_digest) digests)

theorem ay_mscs_checkpoint_digests_root
    (prefix_digest : Prop) (resume_digest : Prop)
    (root_digest : Prop) :
    AyMSCSCheckpointDigests prefix_digest resume_digest root_digest ->
    root_digest := by
  intro digests
  exact ay_mscs_conj_right resume_digest root_digest
    (ay_mscs_conj_right prefix_digest
      (AyMSCSConj resume_digest root_digest) digests)

theorem ay_mscs_resume_manifest_intro
    (stream_id : Prop) (checkpoint_id : Prop)
    (manifest_guard : Prop) :
    stream_id ->
    checkpoint_id ->
    manifest_guard ->
    AyMSCSResumeManifest stream_id checkpoint_id manifest_guard := by
  intro hstream
  intro hcheckpoint
  intro hguard
  exact ay_mscs_conj_intro stream_id
    (AyMSCSConj checkpoint_id manifest_guard)
    hstream
    (ay_mscs_conj_intro checkpoint_id manifest_guard
      hcheckpoint hguard)

theorem ay_mscs_resume_manifest_stream
    (stream_id : Prop) (checkpoint_id : Prop)
    (manifest_guard : Prop) :
    AyMSCSResumeManifest stream_id checkpoint_id manifest_guard ->
    stream_id := by
  intro manifest
  exact ay_mscs_conj_left stream_id
    (AyMSCSConj checkpoint_id manifest_guard) manifest

theorem ay_mscs_resume_manifest_checkpoint
    (stream_id : Prop) (checkpoint_id : Prop)
    (manifest_guard : Prop) :
    AyMSCSResumeManifest stream_id checkpoint_id manifest_guard ->
    checkpoint_id := by
  intro manifest
  exact ay_mscs_conj_left checkpoint_id manifest_guard
    (ay_mscs_conj_right stream_id
      (AyMSCSConj checkpoint_id manifest_guard) manifest)

theorem ay_mscs_resume_manifest_guard
    (stream_id : Prop) (checkpoint_id : Prop)
    (manifest_guard : Prop) :
    AyMSCSResumeManifest stream_id checkpoint_id manifest_guard ->
    manifest_guard := by
  intro manifest
  exact ay_mscs_conj_right checkpoint_id manifest_guard
    (ay_mscs_conj_right stream_id
      (AyMSCSConj checkpoint_id manifest_guard) manifest)

theorem ay_mscs_checkpoint_match_intro
    (checkpoint_digests : Prop) (resume_manifest : Prop) :
    checkpoint_digests ->
    resume_manifest ->
    AyMSCSCheckpointMatch checkpoint_digests resume_manifest := by
  intro hdigests
  intro hmanifest
  exact ay_mscs_conj_intro checkpoint_digests resume_manifest
    hdigests hmanifest

theorem ay_mscs_checkpoint_match_digests
    (checkpoint_digests : Prop) (resume_manifest : Prop) :
    AyMSCSCheckpointMatch checkpoint_digests resume_manifest ->
    checkpoint_digests := by
  intro hmatch
  exact ay_mscs_conj_left checkpoint_digests resume_manifest hmatch

theorem ay_mscs_checkpoint_match_manifest
    (checkpoint_digests : Prop) (resume_manifest : Prop) :
    AyMSCSCheckpointMatch checkpoint_digests resume_manifest ->
    resume_manifest := by
  intro hmatch
  exact ay_mscs_conj_right checkpoint_digests resume_manifest hmatch

theorem ay_mscs_reconstruct_apply
    (assignment_stream : Prop) (full_assignment : Prop) :
    AyMSCSReconstructionWitness assignment_stream full_assignment ->
    assignment_stream ->
    full_assignment := by
  intro reconstruct
  intro hstream
  exact reconstruct hstream

theorem ay_mscs_projection_apply
    (full_assignment : Prop) (original_model : Prop) :
    AyMSCSProjectionWitness full_assignment original_model ->
    full_assignment ->
    original_model := by
  intro project
  intro hfull
  exact project hfull

theorem ay_mscs_stream_evidence_intro
    (checkpoint_ok : Prop) (chunks_ok : Prop)
    (projection_ok : Prop) (audit_ok : Prop) :
    checkpoint_ok ->
    chunks_ok ->
    projection_ok ->
    audit_ok ->
    AyMSCSStreamEvidence
      checkpoint_ok chunks_ok projection_ok audit_ok := by
  intro hcheckpoint
  intro hchunks
  intro hprojection
  intro haudit
  exact ay_mscs_conj_intro checkpoint_ok
    (AyMSCSConj chunks_ok
      (AyMSCSConj projection_ok audit_ok))
    hcheckpoint
    (ay_mscs_conj_intro chunks_ok
      (AyMSCSConj projection_ok audit_ok)
      hchunks
      (ay_mscs_conj_intro projection_ok audit_ok
        hprojection haudit))

theorem ay_mscs_stream_evidence_checkpoint
    (checkpoint_ok : Prop) (chunks_ok : Prop)
    (projection_ok : Prop) (audit_ok : Prop) :
    AyMSCSStreamEvidence
      checkpoint_ok chunks_ok projection_ok audit_ok ->
    checkpoint_ok := by
  intro evidence
  exact ay_mscs_conj_left checkpoint_ok
    (AyMSCSConj chunks_ok
      (AyMSCSConj projection_ok audit_ok)) evidence

theorem ay_mscs_stream_evidence_chunks
    (checkpoint_ok : Prop) (chunks_ok : Prop)
    (projection_ok : Prop) (audit_ok : Prop) :
    AyMSCSStreamEvidence
      checkpoint_ok chunks_ok projection_ok audit_ok ->
    chunks_ok := by
  intro evidence
  exact ay_mscs_conj_left chunks_ok
    (AyMSCSConj projection_ok audit_ok)
    (ay_mscs_conj_right checkpoint_ok
      (AyMSCSConj chunks_ok
        (AyMSCSConj projection_ok audit_ok)) evidence)

theorem ay_mscs_stream_evidence_projection
    (checkpoint_ok : Prop) (chunks_ok : Prop)
    (projection_ok : Prop) (audit_ok : Prop) :
    AyMSCSStreamEvidence
      checkpoint_ok chunks_ok projection_ok audit_ok ->
    projection_ok := by
  intro evidence
  exact ay_mscs_conj_left projection_ok audit_ok
    (ay_mscs_conj_right chunks_ok
      (AyMSCSConj projection_ok audit_ok)
      (ay_mscs_conj_right checkpoint_ok
        (AyMSCSConj chunks_ok
          (AyMSCSConj projection_ok audit_ok)) evidence))

theorem ay_mscs_stream_evidence_audit
    (checkpoint_ok : Prop) (chunks_ok : Prop)
    (projection_ok : Prop) (audit_ok : Prop) :
    AyMSCSStreamEvidence
      checkpoint_ok chunks_ok projection_ok audit_ok ->
    audit_ok := by
  intro evidence
  exact ay_mscs_conj_right projection_ok audit_ok
    (ay_mscs_conj_right chunks_ok
      (AyMSCSConj projection_ok audit_ok)
      (ay_mscs_conj_right checkpoint_ok
        (AyMSCSConj chunks_ok
          (AyMSCSConj projection_ok audit_ok)) evidence))

theorem ay_mscs_audit_entry_intro
    (stream_evidence : Prop) (audit_digest : Prop) :
    stream_evidence ->
    audit_digest ->
    AyMSCSAuditEntry stream_evidence audit_digest := by
  intro hevidence
  intro hdigest
  exact ay_mscs_conj_intro stream_evidence audit_digest
    hevidence hdigest

theorem ay_mscs_audit_entry_evidence
    (stream_evidence : Prop) (audit_digest : Prop) :
    AyMSCSAuditEntry stream_evidence audit_digest ->
    stream_evidence := by
  intro audit
  exact ay_mscs_conj_left stream_evidence audit_digest audit

theorem ay_mscs_audit_entry_digest
    (stream_evidence : Prop) (audit_digest : Prop) :
    AyMSCSAuditEntry stream_evidence audit_digest ->
    audit_digest := by
  intro audit
  exact ay_mscs_conj_right stream_evidence audit_digest audit

theorem ay_mscs_report_intro
    (stream_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    stream_evidence ->
    audit_entry ->
    original_model ->
    AyMSCSAcceptedSatReport
      stream_evidence audit_entry original_model := by
  intro hevidence
  intro haudit
  intro horiginal
  exact ay_mscs_conj_intro stream_evidence
    (AyMSCSConj audit_entry original_model)
    hevidence
    (ay_mscs_conj_intro audit_entry original_model
      haudit horiginal)

theorem ay_mscs_report_evidence
    (stream_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSCSAcceptedSatReport stream_evidence audit_entry original_model ->
    stream_evidence := by
  intro report
  exact ay_mscs_conj_left stream_evidence
    (AyMSCSConj audit_entry original_model) report

theorem ay_mscs_report_audit
    (stream_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSCSAcceptedSatReport stream_evidence audit_entry original_model ->
    audit_entry := by
  intro report
  exact ay_mscs_conj_left audit_entry original_model
    (ay_mscs_conj_right stream_evidence
      (AyMSCSConj audit_entry original_model) report)

theorem ay_mscs_report_original
    (stream_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSCSAcceptedSatReport stream_evidence audit_entry original_model ->
    original_model := by
  intro report
  exact ay_mscs_conj_right audit_entry original_model
    (ay_mscs_conj_right stream_evidence
      (AyMSCSConj audit_entry original_model) report)

theorem ay_mscs_resumed_stream_original_model
    (assignment_stream : Prop) (full_assignment : Prop)
    (original_model : Prop) :
    AyMSCSReconstructionWitness assignment_stream full_assignment ->
    AyMSCSProjectionWitness full_assignment original_model ->
    assignment_stream ->
    original_model := by
  intro reconstruct
  intro project
  intro hstream
  exact project (reconstruct hstream)

theorem ay_mscs_resumed_report_from_evidence
    (assignment_stream : Prop) (full_assignment : Prop)
    (original_model : Prop) (checkpoint_ok : Prop)
    (chunks_ok : Prop) (projection_ok : Prop)
    (audit_ok : Prop) (audit_entry : Prop) :
    AyMSCSReconstructionWitness assignment_stream full_assignment ->
    AyMSCSProjectionWitness full_assignment original_model ->
    assignment_stream ->
    checkpoint_ok ->
    chunks_ok ->
    projection_ok ->
    audit_ok ->
    audit_entry ->
    AyMSCSAcceptedSatReport
      (AyMSCSStreamEvidence
        checkpoint_ok chunks_ok projection_ok audit_ok)
      audit_entry original_model := by
  intro reconstruct
  intro project
  intro hstream
  intro hcheckpoint
  intro hchunks
  intro hprojection
  intro haudit_ok
  intro haudit_entry
  exact ay_mscs_report_intro
    (AyMSCSStreamEvidence
      checkpoint_ok chunks_ok projection_ok audit_ok)
    audit_entry original_model
    (ay_mscs_stream_evidence_intro
      checkpoint_ok chunks_ok projection_ok audit_ok
      hcheckpoint hchunks hprojection haudit_ok)
    haudit_entry
    (project (reconstruct hstream))

theorem ay_mscs_report_requires_checkpoint
    (checkpoint_ok : Prop) (chunks_ok : Prop)
    (projection_ok : Prop) (audit_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSCSAcceptedSatReport
      (AyMSCSStreamEvidence
        checkpoint_ok chunks_ok projection_ok audit_ok)
      audit_entry original_model ->
    checkpoint_ok := by
  intro report
  exact ay_mscs_stream_evidence_checkpoint
    checkpoint_ok chunks_ok projection_ok audit_ok
    (ay_mscs_report_evidence
      (AyMSCSStreamEvidence
        checkpoint_ok chunks_ok projection_ok audit_ok)
      audit_entry original_model report)

theorem ay_mscs_report_requires_chunks
    (checkpoint_ok : Prop) (chunks_ok : Prop)
    (projection_ok : Prop) (audit_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSCSAcceptedSatReport
      (AyMSCSStreamEvidence
        checkpoint_ok chunks_ok projection_ok audit_ok)
      audit_entry original_model ->
    chunks_ok := by
  intro report
  exact ay_mscs_stream_evidence_chunks
    checkpoint_ok chunks_ok projection_ok audit_ok
    (ay_mscs_report_evidence
      (AyMSCSStreamEvidence
        checkpoint_ok chunks_ok projection_ok audit_ok)
      audit_entry original_model report)

theorem ay_mscs_report_requires_projection
    (checkpoint_ok : Prop) (chunks_ok : Prop)
    (projection_ok : Prop) (audit_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSCSAcceptedSatReport
      (AyMSCSStreamEvidence
        checkpoint_ok chunks_ok projection_ok audit_ok)
      audit_entry original_model ->
    projection_ok := by
  intro report
  exact ay_mscs_stream_evidence_projection
    checkpoint_ok chunks_ok projection_ok audit_ok
    (ay_mscs_report_evidence
      (AyMSCSStreamEvidence
        checkpoint_ok chunks_ok projection_ok audit_ok)
      audit_entry original_model report)

theorem ay_mscs_report_requires_audit
    (checkpoint_ok : Prop) (chunks_ok : Prop)
    (projection_ok : Prop) (audit_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSCSAcceptedSatReport
      (AyMSCSStreamEvidence
        checkpoint_ok chunks_ok projection_ok audit_ok)
      audit_entry original_model ->
    audit_ok := by
  intro report
  exact ay_mscs_stream_evidence_audit
    checkpoint_ok chunks_ok projection_ok audit_ok
    (ay_mscs_report_evidence
      (AyMSCSStreamEvidence
        checkpoint_ok chunks_ok projection_ok audit_ok)
      audit_entry original_model report)

theorem ay_mscs_report_sound_exact
    (checkpoint_ok : Prop) (chunks_ok : Prop)
    (projection_ok : Prop) (audit_ok : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMSCSEquisat
      (AyMSCSAcceptedSatReport
        (AyMSCSStreamEvidence
          checkpoint_ok chunks_ok projection_ok audit_ok)
        audit_entry original_model)
      (AyMSCSConj checkpoint_ok
        (AyMSCSConj chunks_ok
          (AyMSCSConj projection_ok
            (AyMSCSConj audit_ok
              (AyMSCSConj audit_entry original_model))))) := by
  exact ay_mscs_equisat_intro
    (AyMSCSAcceptedSatReport
      (AyMSCSStreamEvidence
        checkpoint_ok chunks_ok projection_ok audit_ok)
      audit_entry original_model)
    (AyMSCSConj checkpoint_ok
      (AyMSCSConj chunks_ok
        (AyMSCSConj projection_ok
          (AyMSCSConj audit_ok
            (AyMSCSConj audit_entry original_model)))))
    (fun report =>
      ay_mscs_conj_intro checkpoint_ok
        (AyMSCSConj chunks_ok
          (AyMSCSConj projection_ok
            (AyMSCSConj audit_ok
              (AyMSCSConj audit_entry original_model))))
        (ay_mscs_report_requires_checkpoint
          checkpoint_ok chunks_ok projection_ok audit_ok
          audit_entry original_model report)
        (ay_mscs_conj_intro chunks_ok
          (AyMSCSConj projection_ok
            (AyMSCSConj audit_ok
              (AyMSCSConj audit_entry original_model)))
          (ay_mscs_report_requires_chunks
            checkpoint_ok chunks_ok projection_ok audit_ok
            audit_entry original_model report)
          (ay_mscs_conj_intro projection_ok
            (AyMSCSConj audit_ok
              (AyMSCSConj audit_entry original_model))
            (ay_mscs_report_requires_projection
              checkpoint_ok chunks_ok projection_ok audit_ok
              audit_entry original_model report)
            (ay_mscs_conj_intro audit_ok
              (AyMSCSConj audit_entry original_model)
              (ay_mscs_report_requires_audit
                checkpoint_ok chunks_ok projection_ok audit_ok
                audit_entry original_model report)
              (ay_mscs_conj_intro audit_entry original_model
                (ay_mscs_report_audit
                  (AyMSCSStreamEvidence
                    checkpoint_ok chunks_ok projection_ok audit_ok)
                  audit_entry original_model report)
                (ay_mscs_report_original
                  (AyMSCSStreamEvidence
                    checkpoint_ok chunks_ok projection_ok audit_ok)
                  audit_entry original_model report))))))
    (fun bundle =>
      ay_mscs_report_intro
        (AyMSCSStreamEvidence
          checkpoint_ok chunks_ok projection_ok audit_ok)
        audit_entry original_model
        (ay_mscs_stream_evidence_intro
          checkpoint_ok chunks_ok projection_ok audit_ok
          (ay_mscs_conj_left checkpoint_ok
            (AyMSCSConj chunks_ok
              (AyMSCSConj projection_ok
                (AyMSCSConj audit_ok
                  (AyMSCSConj audit_entry original_model))))
            bundle)
          (ay_mscs_conj_left chunks_ok
            (AyMSCSConj projection_ok
              (AyMSCSConj audit_ok
                (AyMSCSConj audit_entry original_model)))
            (ay_mscs_conj_right checkpoint_ok
              (AyMSCSConj chunks_ok
                (AyMSCSConj projection_ok
                  (AyMSCSConj audit_ok
                    (AyMSCSConj audit_entry original_model))))
              bundle))
          (ay_mscs_conj_left projection_ok
            (AyMSCSConj audit_ok
              (AyMSCSConj audit_entry original_model))
            (ay_mscs_conj_right chunks_ok
              (AyMSCSConj projection_ok
                (AyMSCSConj audit_ok
                  (AyMSCSConj audit_entry original_model)))
              (ay_mscs_conj_right checkpoint_ok
                (AyMSCSConj chunks_ok
                  (AyMSCSConj projection_ok
                    (AyMSCSConj audit_ok
                      (AyMSCSConj audit_entry original_model))))
                bundle)))
          (ay_mscs_conj_left audit_ok
            (AyMSCSConj audit_entry original_model)
            (ay_mscs_conj_right projection_ok
              (AyMSCSConj audit_ok
                (AyMSCSConj audit_entry original_model))
              (ay_mscs_conj_right chunks_ok
                (AyMSCSConj projection_ok
                  (AyMSCSConj audit_ok
                    (AyMSCSConj audit_entry original_model)))
                (ay_mscs_conj_right checkpoint_ok
                  (AyMSCSConj chunks_ok
                    (AyMSCSConj projection_ok
                      (AyMSCSConj audit_ok
                        (AyMSCSConj audit_entry original_model))))
                  bundle)))))
        (ay_mscs_conj_left audit_entry original_model
          (ay_mscs_conj_right audit_ok
            (AyMSCSConj audit_entry original_model)
            (ay_mscs_conj_right projection_ok
              (AyMSCSConj audit_ok
                (AyMSCSConj audit_entry original_model))
              (ay_mscs_conj_right chunks_ok
                (AyMSCSConj projection_ok
                  (AyMSCSConj audit_ok
                    (AyMSCSConj audit_entry original_model)))
                (ay_mscs_conj_right checkpoint_ok
                  (AyMSCSConj chunks_ok
                    (AyMSCSConj projection_ok
                      (AyMSCSConj audit_ok
                        (AyMSCSConj audit_entry original_model))))
                  bundle)))))
        (ay_mscs_conj_right audit_entry original_model
          (ay_mscs_conj_right audit_ok
            (AyMSCSConj audit_entry original_model)
            (ay_mscs_conj_right projection_ok
              (AyMSCSConj audit_ok
                (AyMSCSConj audit_entry original_model))
              (ay_mscs_conj_right chunks_ok
                (AyMSCSConj projection_ok
                  (AyMSCSConj audit_ok
                    (AyMSCSConj audit_entry original_model)))
                (ay_mscs_conj_right checkpoint_ok
                  (AyMSCSConj chunks_ok
                    (AyMSCSConj projection_ok
                      (AyMSCSConj audit_ok
                        (AyMSCSConj audit_entry original_model))))
                  bundle))))))

theorem ay_mscs_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMSCSNoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_mscs_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_mscs_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSCSNoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_mscs_conj_left diagnostic (public_claim -> False) diag

theorem ay_mscs_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSCSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_mscs_conj_right diagnostic (public_claim -> False) diag

theorem ay_mscs_resume_mismatch_no_claim
    (resume_mismatch : Prop) (public_claim : Prop) :
    resume_mismatch ->
    (public_claim -> resume_mismatch -> False) ->
    AyMSCSNoClaimDiagnostic resume_mismatch public_claim := by
  intro hmismatch
  intro blocks
  exact ay_mscs_no_claim_diagnostic_intro
    resume_mismatch public_claim hmismatch
    (fun claim => blocks claim hmismatch)

theorem ay_mscs_missing_chunk_no_claim
    (missing_chunk : Prop) (public_claim : Prop) :
    missing_chunk ->
    (public_claim -> missing_chunk -> False) ->
    AyMSCSNoClaimDiagnostic missing_chunk public_claim := by
  intro hmissing
  intro blocks
  exact ay_mscs_no_claim_diagnostic_intro
    missing_chunk public_claim hmissing
    (fun claim => blocks claim hmissing)

theorem ay_mscs_corrupt_chunk_no_claim
    (corrupt_chunk : Prop) (public_claim : Prop) :
    corrupt_chunk ->
    (public_claim -> corrupt_chunk -> False) ->
    AyMSCSNoClaimDiagnostic corrupt_chunk public_claim := by
  intro hcorrupt
  intro blocks
  exact ay_mscs_no_claim_diagnostic_intro
    corrupt_chunk public_claim hcorrupt
    (fun claim => blocks claim hcorrupt)

theorem ay_mscs_bad_checkpoint_or_stream_no_stale_claim
    (resume_mismatch : Prop) (missing_chunk : Prop)
    (corrupt_chunk : Prop) (public_claim : Prop) :
    AyMSCSDisj resume_mismatch
      (AyMSCSDisj missing_chunk corrupt_chunk) ->
    (public_claim -> resume_mismatch -> False) ->
    (public_claim -> missing_chunk -> False) ->
    (public_claim -> corrupt_chunk -> False) ->
    AyMSCSDisj
      (AyMSCSNoClaimDiagnostic resume_mismatch public_claim)
      (AyMSCSDisj
        (AyMSCSNoClaimDiagnostic missing_chunk public_claim)
        (AyMSCSNoClaimDiagnostic corrupt_chunk public_claim)) := by
  intro bad
  intro resume_blocks
  intro missing_blocks
  intro corrupt_blocks
  exact bad
    (AyMSCSDisj
      (AyMSCSNoClaimDiagnostic resume_mismatch public_claim)
      (AyMSCSDisj
        (AyMSCSNoClaimDiagnostic missing_chunk public_claim)
        (AyMSCSNoClaimDiagnostic corrupt_chunk public_claim)))
    (fun hmismatch =>
      ay_mscs_disj_left
        (AyMSCSNoClaimDiagnostic resume_mismatch public_claim)
        (AyMSCSDisj
          (AyMSCSNoClaimDiagnostic missing_chunk public_claim)
          (AyMSCSNoClaimDiagnostic corrupt_chunk public_claim))
        (ay_mscs_resume_mismatch_no_claim
          resume_mismatch public_claim hmismatch resume_blocks))
    (fun chunk_bad =>
      ay_mscs_disj_right
        (AyMSCSNoClaimDiagnostic resume_mismatch public_claim)
        (AyMSCSDisj
          (AyMSCSNoClaimDiagnostic missing_chunk public_claim)
          (AyMSCSNoClaimDiagnostic corrupt_chunk public_claim))
        (chunk_bad
          (AyMSCSDisj
            (AyMSCSNoClaimDiagnostic missing_chunk public_claim)
            (AyMSCSNoClaimDiagnostic corrupt_chunk public_claim))
          (fun hmissing =>
            ay_mscs_disj_left
              (AyMSCSNoClaimDiagnostic missing_chunk public_claim)
              (AyMSCSNoClaimDiagnostic corrupt_chunk public_claim)
              (ay_mscs_missing_chunk_no_claim
                missing_chunk public_claim hmissing missing_blocks))
          (fun hcorrupt =>
            ay_mscs_disj_right
              (AyMSCSNoClaimDiagnostic missing_chunk public_claim)
              (AyMSCSNoClaimDiagnostic corrupt_chunk public_claim)
              (ay_mscs_corrupt_chunk_no_claim
                corrupt_chunk public_claim hcorrupt corrupt_blocks))))

theorem ay_mscs_diagnostic_blocks_public_claim
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSCSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_mscs_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim

