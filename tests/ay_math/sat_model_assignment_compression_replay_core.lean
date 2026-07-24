-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for compressed/delta model-assignment replay.
-- Public SAT replay requires chunk order, domain coverage, default assignment
-- semantics, digest/checkpoint guards, and formula reconstruction evidence.
-- Missing variables, reordered chunks, or corrupt deltas are no-claim or
-- recomputation facts.

def AyMACRConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMACRDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMACREquisat (before : Prop) (after : Prop) :=
  AyMACRConj (before -> after) (after -> before)

def AyMACRCompressedChunks
    (base_chunks : Prop) (delta_chunks : Prop) :=
  AyMACRConj base_chunks delta_chunks

def AyMACRReplayOrder
    (chunk_order : Prop) (delta_order : Prop) :=
  AyMACRConj chunk_order delta_order

def AyMACRDomainDefaults
    (domain_coverage : Prop) (default_assignment : Prop) :=
  AyMACRConj domain_coverage default_assignment

def AyMACRDigestCheckpointGuard
    (digest_guard : Prop) (checkpoint_guard : Prop) :=
  AyMACRConj digest_guard checkpoint_guard

def AyMACRReplayWitness
    (compressed_chunks : Prop) (full_assignment : Prop) :=
  compressed_chunks -> full_assignment

def AyMACRFormulaReconstruction
    (full_assignment : Prop) (original_model : Prop) :=
  full_assignment -> original_model

def AyMACRReplayEvidence
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) :=
  AyMACRConj order_ok
    (AyMACRConj domain_ok
      (AyMACRConj defaults_ok
        (AyMACRConj guard_ok reconstruction_ok)))

def AyMACRAuditEntry
    (replay_evidence : Prop) (audit_digest : Prop) :=
  AyMACRConj replay_evidence audit_digest

def AyMACRAcceptedSatReport
    (replay_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :=
  AyMACRConj replay_evidence
    (AyMACRConj audit_entry original_model)

def AyMACRNoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMACRConj diagnostic (public_claim -> False)

def AyMACRRecomputeObligation
    (reason : Prop) (recompute_request : Prop) :=
  AyMACRConj reason recompute_request

theorem ay_macr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMACRConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_macr_conj_left
    (left : Prop) (right : Prop) :
    AyMACRConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_macr_conj_right
    (left : Prop) (right : Prop) :
    AyMACRConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_macr_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMACRDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_macr_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMACRDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_macr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMACREquisat before after := by
  intro forward
  intro backward
  exact ay_macr_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_macr_equisat_forward
    (before : Prop) (after : Prop) :
    AyMACREquisat before after -> before -> after := by
  intro certificate
  exact ay_macr_conj_left (before -> after) (after -> before) certificate

theorem ay_macr_equisat_backward
    (before : Prop) (after : Prop) :
    AyMACREquisat before after -> after -> before := by
  intro certificate
  exact ay_macr_conj_right (before -> after) (after -> before) certificate

theorem ay_macr_compressed_chunks_intro
    (base_chunks : Prop) (delta_chunks : Prop) :
    base_chunks ->
    delta_chunks ->
    AyMACRCompressedChunks base_chunks delta_chunks := by
  intro hbase
  intro hdelta
  exact ay_macr_conj_intro base_chunks delta_chunks hbase hdelta

theorem ay_macr_compressed_chunks_base
    (base_chunks : Prop) (delta_chunks : Prop) :
    AyMACRCompressedChunks base_chunks delta_chunks ->
    base_chunks := by
  intro chunks
  exact ay_macr_conj_left base_chunks delta_chunks chunks

theorem ay_macr_compressed_chunks_delta
    (base_chunks : Prop) (delta_chunks : Prop) :
    AyMACRCompressedChunks base_chunks delta_chunks ->
    delta_chunks := by
  intro chunks
  exact ay_macr_conj_right base_chunks delta_chunks chunks

theorem ay_macr_replay_order_intro
    (chunk_order : Prop) (delta_order : Prop) :
    chunk_order ->
    delta_order ->
    AyMACRReplayOrder chunk_order delta_order := by
  intro hchunk_order
  intro hdelta_order
  exact ay_macr_conj_intro chunk_order delta_order
    hchunk_order hdelta_order

theorem ay_macr_replay_order_chunks
    (chunk_order : Prop) (delta_order : Prop) :
    AyMACRReplayOrder chunk_order delta_order ->
    chunk_order := by
  intro order
  exact ay_macr_conj_left chunk_order delta_order order

theorem ay_macr_replay_order_delta
    (chunk_order : Prop) (delta_order : Prop) :
    AyMACRReplayOrder chunk_order delta_order ->
    delta_order := by
  intro order
  exact ay_macr_conj_right chunk_order delta_order order

theorem ay_macr_domain_defaults_intro
    (domain_coverage : Prop) (default_assignment : Prop) :
    domain_coverage ->
    default_assignment ->
    AyMACRDomainDefaults domain_coverage default_assignment := by
  intro hdomain
  intro hdefault
  exact ay_macr_conj_intro domain_coverage default_assignment
    hdomain hdefault

theorem ay_macr_domain_defaults_domain
    (domain_coverage : Prop) (default_assignment : Prop) :
    AyMACRDomainDefaults domain_coverage default_assignment ->
    domain_coverage := by
  intro domain
  exact ay_macr_conj_left domain_coverage default_assignment domain

theorem ay_macr_domain_defaults_default
    (domain_coverage : Prop) (default_assignment : Prop) :
    AyMACRDomainDefaults domain_coverage default_assignment ->
    default_assignment := by
  intro domain
  exact ay_macr_conj_right domain_coverage default_assignment domain

theorem ay_macr_digest_checkpoint_guard_intro
    (digest_guard : Prop) (checkpoint_guard : Prop) :
    digest_guard ->
    checkpoint_guard ->
    AyMACRDigestCheckpointGuard digest_guard checkpoint_guard := by
  intro hdigest
  intro hcheckpoint
  exact ay_macr_conj_intro digest_guard checkpoint_guard
    hdigest hcheckpoint

theorem ay_macr_digest_checkpoint_guard_digest
    (digest_guard : Prop) (checkpoint_guard : Prop) :
    AyMACRDigestCheckpointGuard digest_guard checkpoint_guard ->
    digest_guard := by
  intro guard
  exact ay_macr_conj_left digest_guard checkpoint_guard guard

theorem ay_macr_digest_checkpoint_guard_checkpoint
    (digest_guard : Prop) (checkpoint_guard : Prop) :
    AyMACRDigestCheckpointGuard digest_guard checkpoint_guard ->
    checkpoint_guard := by
  intro guard
  exact ay_macr_conj_right digest_guard checkpoint_guard guard

theorem ay_macr_replay_apply
    (compressed_chunks : Prop) (full_assignment : Prop) :
    AyMACRReplayWitness compressed_chunks full_assignment ->
    compressed_chunks ->
    full_assignment := by
  intro replay
  intro hchunks
  exact replay hchunks

theorem ay_macr_formula_reconstruct_apply
    (full_assignment : Prop) (original_model : Prop) :
    AyMACRFormulaReconstruction full_assignment original_model ->
    full_assignment ->
    original_model := by
  intro reconstruct
  intro hfull
  exact reconstruct hfull

theorem ay_macr_replay_evidence_intro
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) :
    order_ok ->
    domain_ok ->
    defaults_ok ->
    guard_ok ->
    reconstruction_ok ->
    AyMACRReplayEvidence
      order_ok domain_ok defaults_ok guard_ok reconstruction_ok := by
  intro horder
  intro hdomain
  intro hdefaults
  intro hguard
  intro hreconstruct
  exact ay_macr_conj_intro order_ok
    (AyMACRConj domain_ok
      (AyMACRConj defaults_ok
        (AyMACRConj guard_ok reconstruction_ok)))
    horder
    (ay_macr_conj_intro domain_ok
      (AyMACRConj defaults_ok
        (AyMACRConj guard_ok reconstruction_ok))
      hdomain
      (ay_macr_conj_intro defaults_ok
        (AyMACRConj guard_ok reconstruction_ok)
        hdefaults
        (ay_macr_conj_intro guard_ok reconstruction_ok
          hguard hreconstruct)))

theorem ay_macr_replay_evidence_order
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) :
    AyMACRReplayEvidence
      order_ok domain_ok defaults_ok guard_ok reconstruction_ok ->
    order_ok := by
  intro evidence
  exact ay_macr_conj_left order_ok
    (AyMACRConj domain_ok
      (AyMACRConj defaults_ok
        (AyMACRConj guard_ok reconstruction_ok))) evidence

theorem ay_macr_replay_evidence_domain
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) :
    AyMACRReplayEvidence
      order_ok domain_ok defaults_ok guard_ok reconstruction_ok ->
    domain_ok := by
  intro evidence
  exact ay_macr_conj_left domain_ok
    (AyMACRConj defaults_ok
      (AyMACRConj guard_ok reconstruction_ok))
    (ay_macr_conj_right order_ok
      (AyMACRConj domain_ok
        (AyMACRConj defaults_ok
          (AyMACRConj guard_ok reconstruction_ok))) evidence)

theorem ay_macr_replay_evidence_defaults
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) :
    AyMACRReplayEvidence
      order_ok domain_ok defaults_ok guard_ok reconstruction_ok ->
    defaults_ok := by
  intro evidence
  exact ay_macr_conj_left defaults_ok
    (AyMACRConj guard_ok reconstruction_ok)
    (ay_macr_conj_right domain_ok
      (AyMACRConj defaults_ok
        (AyMACRConj guard_ok reconstruction_ok))
      (ay_macr_conj_right order_ok
        (AyMACRConj domain_ok
          (AyMACRConj defaults_ok
            (AyMACRConj guard_ok reconstruction_ok))) evidence))

theorem ay_macr_replay_evidence_guard
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) :
    AyMACRReplayEvidence
      order_ok domain_ok defaults_ok guard_ok reconstruction_ok ->
    guard_ok := by
  intro evidence
  exact ay_macr_conj_left guard_ok reconstruction_ok
    (ay_macr_conj_right defaults_ok
      (AyMACRConj guard_ok reconstruction_ok)
      (ay_macr_conj_right domain_ok
        (AyMACRConj defaults_ok
          (AyMACRConj guard_ok reconstruction_ok))
        (ay_macr_conj_right order_ok
          (AyMACRConj domain_ok
            (AyMACRConj defaults_ok
              (AyMACRConj guard_ok reconstruction_ok))) evidence)))

theorem ay_macr_replay_evidence_reconstruction
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) :
    AyMACRReplayEvidence
      order_ok domain_ok defaults_ok guard_ok reconstruction_ok ->
    reconstruction_ok := by
  intro evidence
  exact ay_macr_conj_right guard_ok reconstruction_ok
    (ay_macr_conj_right defaults_ok
      (AyMACRConj guard_ok reconstruction_ok)
      (ay_macr_conj_right domain_ok
        (AyMACRConj defaults_ok
          (AyMACRConj guard_ok reconstruction_ok))
        (ay_macr_conj_right order_ok
          (AyMACRConj domain_ok
            (AyMACRConj defaults_ok
              (AyMACRConj guard_ok reconstruction_ok))) evidence)))

theorem ay_macr_audit_entry_intro
    (replay_evidence : Prop) (audit_digest : Prop) :
    replay_evidence ->
    audit_digest ->
    AyMACRAuditEntry replay_evidence audit_digest := by
  intro hevidence
  intro hdigest
  exact ay_macr_conj_intro replay_evidence audit_digest
    hevidence hdigest

theorem ay_macr_audit_entry_evidence
    (replay_evidence : Prop) (audit_digest : Prop) :
    AyMACRAuditEntry replay_evidence audit_digest ->
    replay_evidence := by
  intro audit
  exact ay_macr_conj_left replay_evidence audit_digest audit

theorem ay_macr_audit_entry_digest
    (replay_evidence : Prop) (audit_digest : Prop) :
    AyMACRAuditEntry replay_evidence audit_digest ->
    audit_digest := by
  intro audit
  exact ay_macr_conj_right replay_evidence audit_digest audit

theorem ay_macr_report_intro
    (replay_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    replay_evidence ->
    audit_entry ->
    original_model ->
    AyMACRAcceptedSatReport
      replay_evidence audit_entry original_model := by
  intro hevidence
  intro haudit
  intro horiginal
  exact ay_macr_conj_intro replay_evidence
    (AyMACRConj audit_entry original_model)
    hevidence
    (ay_macr_conj_intro audit_entry original_model haudit horiginal)

theorem ay_macr_report_evidence
    (replay_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMACRAcceptedSatReport
      replay_evidence audit_entry original_model ->
    replay_evidence := by
  intro report
  exact ay_macr_conj_left replay_evidence
    (AyMACRConj audit_entry original_model) report

theorem ay_macr_report_audit
    (replay_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMACRAcceptedSatReport
      replay_evidence audit_entry original_model ->
    audit_entry := by
  intro report
  exact ay_macr_conj_left audit_entry original_model
    (ay_macr_conj_right replay_evidence
      (AyMACRConj audit_entry original_model) report)

theorem ay_macr_report_original
    (replay_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMACRAcceptedSatReport
      replay_evidence audit_entry original_model ->
    original_model := by
  intro report
  exact ay_macr_conj_right audit_entry original_model
    (ay_macr_conj_right replay_evidence
      (AyMACRConj audit_entry original_model) report)

theorem ay_macr_replayed_original_model
    (compressed_chunks : Prop) (full_assignment : Prop)
    (original_model : Prop) :
    AyMACRReplayWitness compressed_chunks full_assignment ->
    AyMACRFormulaReconstruction full_assignment original_model ->
    compressed_chunks ->
    original_model := by
  intro replay
  intro reconstruct
  intro hchunks
  exact reconstruct (replay hchunks)

theorem ay_macr_replayed_report_from_evidence
    (compressed_chunks : Prop) (full_assignment : Prop)
    (original_model : Prop) (order_ok : Prop)
    (domain_ok : Prop) (defaults_ok : Prop)
    (guard_ok : Prop) (reconstruction_ok : Prop)
    (audit_entry : Prop) :
    AyMACRReplayWitness compressed_chunks full_assignment ->
    AyMACRFormulaReconstruction full_assignment original_model ->
    compressed_chunks ->
    order_ok ->
    domain_ok ->
    defaults_ok ->
    guard_ok ->
    reconstruction_ok ->
    audit_entry ->
    AyMACRAcceptedSatReport
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model := by
  intro replay
  intro reconstruct
  intro hchunks
  intro horder
  intro hdomain
  intro hdefaults
  intro hguard
  intro hreconstruction
  intro haudit
  exact ay_macr_report_intro
    (AyMACRReplayEvidence
      order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
    audit_entry original_model
    (ay_macr_replay_evidence_intro
      order_ok domain_ok defaults_ok guard_ok reconstruction_ok
      horder hdomain hdefaults hguard hreconstruction)
    haudit
    (reconstruct (replay hchunks))

theorem ay_macr_report_requires_order
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMACRAcceptedSatReport
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model ->
    order_ok := by
  intro report
  exact ay_macr_replay_evidence_order
    order_ok domain_ok defaults_ok guard_ok reconstruction_ok
    (ay_macr_report_evidence
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model report)

theorem ay_macr_report_requires_domain
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMACRAcceptedSatReport
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model ->
    domain_ok := by
  intro report
  exact ay_macr_replay_evidence_domain
    order_ok domain_ok defaults_ok guard_ok reconstruction_ok
    (ay_macr_report_evidence
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model report)

theorem ay_macr_report_requires_defaults
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMACRAcceptedSatReport
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model ->
    defaults_ok := by
  intro report
  exact ay_macr_replay_evidence_defaults
    order_ok domain_ok defaults_ok guard_ok reconstruction_ok
    (ay_macr_report_evidence
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model report)

theorem ay_macr_report_requires_guard
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMACRAcceptedSatReport
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model ->
    guard_ok := by
  intro report
  exact ay_macr_replay_evidence_guard
    order_ok domain_ok defaults_ok guard_ok reconstruction_ok
    (ay_macr_report_evidence
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model report)

theorem ay_macr_report_requires_reconstruction
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMACRAcceptedSatReport
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model ->
    reconstruction_ok := by
  intro report
  exact ay_macr_replay_evidence_reconstruction
    order_ok domain_ok defaults_ok guard_ok reconstruction_ok
    (ay_macr_report_evidence
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model report)

theorem ay_macr_report_sound_exact
    (order_ok : Prop) (domain_ok : Prop)
    (defaults_ok : Prop) (guard_ok : Prop)
    (reconstruction_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMACREquisat
      (AyMACRAcceptedSatReport
        (AyMACRReplayEvidence
          order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
        audit_entry original_model)
      (AyMACRConj
        (AyMACRReplayEvidence
          order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
        (AyMACRConj audit_entry original_model)) := by
  exact ay_macr_equisat_intro
    (AyMACRAcceptedSatReport
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      audit_entry original_model)
    (AyMACRConj
      (AyMACRReplayEvidence
        order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
      (AyMACRConj audit_entry original_model))
    (fun report =>
      ay_macr_conj_intro
        (AyMACRReplayEvidence
          order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
        (AyMACRConj audit_entry original_model)
        (ay_macr_report_evidence
          (AyMACRReplayEvidence
            order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
          audit_entry original_model report)
        (ay_macr_conj_intro audit_entry original_model
          (ay_macr_report_audit
            (AyMACRReplayEvidence
              order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
            audit_entry original_model report)
          (ay_macr_report_original
            (AyMACRReplayEvidence
              order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
            audit_entry original_model report)))
    (fun bundle =>
      ay_macr_report_intro
        (AyMACRReplayEvidence
          order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
        audit_entry original_model
        (ay_macr_conj_left
          (AyMACRReplayEvidence
            order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
          (AyMACRConj audit_entry original_model)
          bundle)
        (ay_macr_conj_left audit_entry original_model
          (ay_macr_conj_right
            (AyMACRReplayEvidence
              order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
            (AyMACRConj audit_entry original_model)
            bundle))
        (ay_macr_conj_right audit_entry original_model
          (ay_macr_conj_right
            (AyMACRReplayEvidence
              order_ok domain_ok defaults_ok guard_ok reconstruction_ok)
            (AyMACRConj audit_entry original_model)
            bundle)))

theorem ay_macr_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMACRNoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_macr_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_macr_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMACRNoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_macr_conj_left diagnostic (public_claim -> False) diag

theorem ay_macr_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMACRNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_macr_conj_right diagnostic (public_claim -> False) diag

theorem ay_macr_recompute_obligation_intro
    (reason : Prop) (recompute_request : Prop) :
    reason ->
    recompute_request ->
    AyMACRRecomputeObligation reason recompute_request := by
  intro hreason
  intro hrequest
  exact ay_macr_conj_intro reason recompute_request hreason hrequest

theorem ay_macr_recompute_obligation_reason
    (reason : Prop) (recompute_request : Prop) :
    AyMACRRecomputeObligation reason recompute_request ->
    reason := by
  intro obligation
  exact ay_macr_conj_left reason recompute_request obligation

theorem ay_macr_recompute_obligation_request
    (reason : Prop) (recompute_request : Prop) :
    AyMACRRecomputeObligation reason recompute_request ->
    recompute_request := by
  intro obligation
  exact ay_macr_conj_right reason recompute_request obligation

theorem ay_macr_missing_variable_recompute
    (missing_variable : Prop) (recompute_request : Prop) :
    missing_variable ->
    recompute_request ->
    AyMACRRecomputeObligation missing_variable recompute_request := by
  intro hmissing
  intro hrequest
  exact ay_macr_recompute_obligation_intro
    missing_variable recompute_request hmissing hrequest

theorem ay_macr_missing_variable_no_claim
    (missing_variable : Prop) (public_claim : Prop) :
    missing_variable ->
    (public_claim -> missing_variable -> False) ->
    AyMACRNoClaimDiagnostic missing_variable public_claim := by
  intro hmissing
  intro blocks
  exact ay_macr_no_claim_diagnostic_intro
    missing_variable public_claim hmissing
    (fun claim => blocks claim hmissing)

theorem ay_macr_reordered_chunks_no_claim
    (reordered_chunks : Prop) (public_claim : Prop) :
    reordered_chunks ->
    (public_claim -> reordered_chunks -> False) ->
    AyMACRNoClaimDiagnostic reordered_chunks public_claim := by
  intro hreordered
  intro blocks
  exact ay_macr_no_claim_diagnostic_intro
    reordered_chunks public_claim hreordered
    (fun claim => blocks claim hreordered)

theorem ay_macr_corrupt_delta_no_claim
    (corrupt_delta : Prop) (public_claim : Prop) :
    corrupt_delta ->
    (public_claim -> corrupt_delta -> False) ->
    AyMACRNoClaimDiagnostic corrupt_delta public_claim := by
  intro hcorrupt
  intro blocks
  exact ay_macr_no_claim_diagnostic_intro
    corrupt_delta public_claim hcorrupt
    (fun claim => blocks claim hcorrupt)

theorem ay_macr_diagnostic_blocks_public_claim
    (diagnostic : Prop) (public_claim : Prop) :
    AyMACRNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_macr_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim

theorem ay_macr_bad_replay_no_stale_sat
    (missing_variable : Prop) (reordered_chunks : Prop)
    (corrupt_delta : Prop) (public_claim : Prop) :
    (public_claim -> missing_variable -> False) ->
    (public_claim -> reordered_chunks -> False) ->
    (public_claim -> corrupt_delta -> False) ->
    AyMACRConj
      (missing_variable ->
        AyMACRNoClaimDiagnostic missing_variable public_claim)
      (AyMACRConj
        (reordered_chunks ->
          AyMACRNoClaimDiagnostic reordered_chunks public_claim)
        (corrupt_delta ->
          AyMACRNoClaimDiagnostic corrupt_delta public_claim)) := by
  intro missing_blocks
  intro reordered_blocks
  intro corrupt_blocks
  exact ay_macr_conj_intro
    (missing_variable ->
      AyMACRNoClaimDiagnostic missing_variable public_claim)
    (AyMACRConj
      (reordered_chunks ->
        AyMACRNoClaimDiagnostic reordered_chunks public_claim)
      (corrupt_delta ->
        AyMACRNoClaimDiagnostic corrupt_delta public_claim))
    (fun hmissing =>
      ay_macr_missing_variable_no_claim
        missing_variable public_claim hmissing missing_blocks)
    (ay_macr_conj_intro
      (reordered_chunks ->
        AyMACRNoClaimDiagnostic reordered_chunks public_claim)
      (corrupt_delta ->
        AyMACRNoClaimDiagnostic corrupt_delta public_claim)
      (fun hreordered =>
        ay_macr_reordered_chunks_no_claim
          reordered_chunks public_claim hreordered reordered_blocks)
      (fun hcorrupt =>
        ay_macr_corrupt_delta_no_claim
          corrupt_delta public_claim hcorrupt corrupt_blocks))

