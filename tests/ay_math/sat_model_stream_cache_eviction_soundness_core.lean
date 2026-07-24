-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for memory-bounded streamed-model cache
-- eviction. Retained complete streams can justify SAT reports through
-- reconstruction, projection, and audit evidence. Missing, evicted, or stale
-- chunks force recomputation or diagnostic no-claim results.

def AyMSCESConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMSCESDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMSCESEquisat (before : Prop) (after : Prop) :=
  AyMSCESConj (before -> after) (after -> before)

def AyMSCESStreamChunks
    (cached_chunks : Prop) (chunk_order : Prop) :=
  AyMSCESConj cached_chunks chunk_order

def AyMSCESCheckpointState
    (checkpoint_digest : Prop) (manifest_guard : Prop) :=
  AyMSCESConj checkpoint_digest manifest_guard

def AyMSCESStreamCacheEntry
    (stream_chunks : Prop) (checkpoint_state : Prop)
    (cache_digest : Prop) :=
  AyMSCESConj stream_chunks
    (AyMSCESConj checkpoint_state cache_digest)

def AyMSCESRetainedCompleteStream
    (cache_entry : Prop) (completeness_witness : Prop) :=
  AyMSCESConj cache_entry completeness_witness

def AyMSCESEvictedChunk (eviction_record : Prop) :=
  eviction_record

def AyMSCESMissingChunk (missing_record : Prop) :=
  missing_record

def AyMSCESStaleChunk
    (stale_record : Prop) (digest_mismatch : Prop) :=
  AyMSCESConj stale_record digest_mismatch

def AyMSCESReconstructionWitness
    (stream_chunks : Prop) (full_assignment : Prop) :=
  stream_chunks -> full_assignment

def AyMSCESProjectionWitness
    (full_assignment : Prop) (original_model : Prop) :=
  full_assignment -> original_model

def AyMSCESAuditEntry
    (report_evidence : Prop) (audit_digest : Prop) :=
  AyMSCESConj report_evidence audit_digest

def AyMSCESAcceptedSatReport
    (retained_stream : Prop) (audit_entry : Prop)
    (original_model : Prop) :=
  AyMSCESConj retained_stream
    (AyMSCESConj audit_entry original_model)

def AyMSCESNoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMSCESConj diagnostic (public_claim -> False)

def AyMSCESRecomputeObligation
    (reason : Prop) (recompute_request : Prop) :=
  AyMSCESConj reason recompute_request

theorem ay_msces_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMSCESConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_msces_conj_left
    (left : Prop) (right : Prop) :
    AyMSCESConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_msces_conj_right
    (left : Prop) (right : Prop) :
    AyMSCESConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_msces_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMSCESDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_msces_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMSCESDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_msces_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMSCESEquisat before after := by
  intro forward
  intro backward
  exact ay_msces_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_msces_equisat_forward
    (before : Prop) (after : Prop) :
    AyMSCESEquisat before after -> before -> after := by
  intro certificate
  exact ay_msces_conj_left (before -> after) (after -> before) certificate

theorem ay_msces_equisat_backward
    (before : Prop) (after : Prop) :
    AyMSCESEquisat before after -> after -> before := by
  intro certificate
  exact ay_msces_conj_right (before -> after) (after -> before) certificate

theorem ay_msces_stream_chunks_intro
    (cached_chunks : Prop) (chunk_order : Prop) :
    cached_chunks ->
    chunk_order ->
    AyMSCESStreamChunks cached_chunks chunk_order := by
  intro hchunks
  intro horder
  exact ay_msces_conj_intro cached_chunks chunk_order
    hchunks horder

theorem ay_msces_stream_chunks_cached
    (cached_chunks : Prop) (chunk_order : Prop) :
    AyMSCESStreamChunks cached_chunks chunk_order ->
    cached_chunks := by
  intro chunks
  exact ay_msces_conj_left cached_chunks chunk_order chunks

theorem ay_msces_stream_chunks_order
    (cached_chunks : Prop) (chunk_order : Prop) :
    AyMSCESStreamChunks cached_chunks chunk_order ->
    chunk_order := by
  intro chunks
  exact ay_msces_conj_right cached_chunks chunk_order chunks

theorem ay_msces_checkpoint_state_intro
    (checkpoint_digest : Prop) (manifest_guard : Prop) :
    checkpoint_digest ->
    manifest_guard ->
    AyMSCESCheckpointState checkpoint_digest manifest_guard := by
  intro hdigest
  intro hguard
  exact ay_msces_conj_intro checkpoint_digest manifest_guard
    hdigest hguard

theorem ay_msces_checkpoint_state_digest
    (checkpoint_digest : Prop) (manifest_guard : Prop) :
    AyMSCESCheckpointState checkpoint_digest manifest_guard ->
    checkpoint_digest := by
  intro checkpoint
  exact ay_msces_conj_left checkpoint_digest manifest_guard checkpoint

theorem ay_msces_checkpoint_state_guard
    (checkpoint_digest : Prop) (manifest_guard : Prop) :
    AyMSCESCheckpointState checkpoint_digest manifest_guard ->
    manifest_guard := by
  intro checkpoint
  exact ay_msces_conj_right checkpoint_digest manifest_guard checkpoint

theorem ay_msces_cache_entry_intro
    (stream_chunks : Prop) (checkpoint_state : Prop)
    (cache_digest : Prop) :
    stream_chunks ->
    checkpoint_state ->
    cache_digest ->
    AyMSCESStreamCacheEntry
      stream_chunks checkpoint_state cache_digest := by
  intro hstream
  intro hcheckpoint
  intro hdigest
  exact ay_msces_conj_intro stream_chunks
    (AyMSCESConj checkpoint_state cache_digest)
    hstream
    (ay_msces_conj_intro checkpoint_state cache_digest
      hcheckpoint hdigest)

theorem ay_msces_cache_entry_stream
    (stream_chunks : Prop) (checkpoint_state : Prop)
    (cache_digest : Prop) :
    AyMSCESStreamCacheEntry
      stream_chunks checkpoint_state cache_digest ->
    stream_chunks := by
  intro entry
  exact ay_msces_conj_left stream_chunks
    (AyMSCESConj checkpoint_state cache_digest) entry

theorem ay_msces_cache_entry_checkpoint
    (stream_chunks : Prop) (checkpoint_state : Prop)
    (cache_digest : Prop) :
    AyMSCESStreamCacheEntry
      stream_chunks checkpoint_state cache_digest ->
    checkpoint_state := by
  intro entry
  exact ay_msces_conj_left checkpoint_state cache_digest
    (ay_msces_conj_right stream_chunks
      (AyMSCESConj checkpoint_state cache_digest) entry)

theorem ay_msces_cache_entry_digest
    (stream_chunks : Prop) (checkpoint_state : Prop)
    (cache_digest : Prop) :
    AyMSCESStreamCacheEntry
      stream_chunks checkpoint_state cache_digest ->
    cache_digest := by
  intro entry
  exact ay_msces_conj_right checkpoint_state cache_digest
    (ay_msces_conj_right stream_chunks
      (AyMSCESConj checkpoint_state cache_digest) entry)

theorem ay_msces_retained_stream_intro
    (cache_entry : Prop) (completeness_witness : Prop) :
    cache_entry ->
    completeness_witness ->
    AyMSCESRetainedCompleteStream
      cache_entry completeness_witness := by
  intro hentry
  intro hcomplete
  exact ay_msces_conj_intro cache_entry completeness_witness
    hentry hcomplete

theorem ay_msces_retained_stream_entry
    (cache_entry : Prop) (completeness_witness : Prop) :
    AyMSCESRetainedCompleteStream
      cache_entry completeness_witness ->
    cache_entry := by
  intro retained
  exact ay_msces_conj_left cache_entry completeness_witness retained

theorem ay_msces_retained_stream_complete
    (cache_entry : Prop) (completeness_witness : Prop) :
    AyMSCESRetainedCompleteStream
      cache_entry completeness_witness ->
    completeness_witness := by
  intro retained
  exact ay_msces_conj_right cache_entry completeness_witness retained

theorem ay_msces_reconstruct_apply
    (stream_chunks : Prop) (full_assignment : Prop) :
    AyMSCESReconstructionWitness stream_chunks full_assignment ->
    stream_chunks ->
    full_assignment := by
  intro reconstruct
  intro hstream
  exact reconstruct hstream

theorem ay_msces_projection_apply
    (full_assignment : Prop) (original_model : Prop) :
    AyMSCESProjectionWitness full_assignment original_model ->
    full_assignment ->
    original_model := by
  intro project
  intro hfull
  exact project hfull

theorem ay_msces_audit_entry_intro
    (report_evidence : Prop) (audit_digest : Prop) :
    report_evidence ->
    audit_digest ->
    AyMSCESAuditEntry report_evidence audit_digest := by
  intro hevidence
  intro hdigest
  exact ay_msces_conj_intro report_evidence audit_digest
    hevidence hdigest

theorem ay_msces_audit_entry_evidence
    (report_evidence : Prop) (audit_digest : Prop) :
    AyMSCESAuditEntry report_evidence audit_digest ->
    report_evidence := by
  intro audit
  exact ay_msces_conj_left report_evidence audit_digest audit

theorem ay_msces_audit_entry_digest
    (report_evidence : Prop) (audit_digest : Prop) :
    AyMSCESAuditEntry report_evidence audit_digest ->
    audit_digest := by
  intro audit
  exact ay_msces_conj_right report_evidence audit_digest audit

theorem ay_msces_report_intro
    (retained_stream : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    retained_stream ->
    audit_entry ->
    original_model ->
    AyMSCESAcceptedSatReport
      retained_stream audit_entry original_model := by
  intro hretained
  intro haudit
  intro horiginal
  exact ay_msces_conj_intro retained_stream
    (AyMSCESConj audit_entry original_model)
    hretained
    (ay_msces_conj_intro audit_entry original_model
      haudit horiginal)

theorem ay_msces_report_retained
    (retained_stream : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSCESAcceptedSatReport
      retained_stream audit_entry original_model ->
    retained_stream := by
  intro report
  exact ay_msces_conj_left retained_stream
    (AyMSCESConj audit_entry original_model) report

theorem ay_msces_report_audit
    (retained_stream : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSCESAcceptedSatReport
      retained_stream audit_entry original_model ->
    audit_entry := by
  intro report
  exact ay_msces_conj_left audit_entry original_model
    (ay_msces_conj_right retained_stream
      (AyMSCESConj audit_entry original_model) report)

theorem ay_msces_report_original
    (retained_stream : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSCESAcceptedSatReport
      retained_stream audit_entry original_model ->
    original_model := by
  intro report
  exact ay_msces_conj_right audit_entry original_model
    (ay_msces_conj_right retained_stream
      (AyMSCESConj audit_entry original_model) report)

theorem ay_msces_retained_stream_original_model
    (stream_chunks : Prop) (checkpoint_state : Prop)
    (cache_digest : Prop) (completeness_witness : Prop)
    (full_assignment : Prop) (original_model : Prop) :
    AyMSCESReconstructionWitness stream_chunks full_assignment ->
    AyMSCESProjectionWitness full_assignment original_model ->
    AyMSCESRetainedCompleteStream
      (AyMSCESStreamCacheEntry
        stream_chunks checkpoint_state cache_digest)
      completeness_witness ->
    original_model := by
  intro reconstruct
  intro project
  intro retained
  exact project
    (reconstruct
      (ay_msces_cache_entry_stream
        stream_chunks checkpoint_state cache_digest
        (ay_msces_retained_stream_entry
          (AyMSCESStreamCacheEntry
            stream_chunks checkpoint_state cache_digest)
          completeness_witness retained)))

theorem ay_msces_retained_stream_report
    (stream_chunks : Prop) (checkpoint_state : Prop)
    (cache_digest : Prop) (completeness_witness : Prop)
    (full_assignment : Prop) (original_model : Prop)
    (audit_entry : Prop) :
    AyMSCESReconstructionWitness stream_chunks full_assignment ->
    AyMSCESProjectionWitness full_assignment original_model ->
    AyMSCESRetainedCompleteStream
      (AyMSCESStreamCacheEntry
        stream_chunks checkpoint_state cache_digest)
      completeness_witness ->
    audit_entry ->
    AyMSCESAcceptedSatReport
      (AyMSCESRetainedCompleteStream
        (AyMSCESStreamCacheEntry
          stream_chunks checkpoint_state cache_digest)
        completeness_witness)
      audit_entry original_model := by
  intro reconstruct
  intro project
  intro retained
  intro haudit
  exact ay_msces_report_intro
    (AyMSCESRetainedCompleteStream
      (AyMSCESStreamCacheEntry
        stream_chunks checkpoint_state cache_digest)
      completeness_witness)
    audit_entry original_model
    retained
    haudit
    (ay_msces_retained_stream_original_model
      stream_chunks checkpoint_state cache_digest
      completeness_witness full_assignment original_model
      reconstruct project retained)

theorem ay_msces_report_sound_exact
    (retained_stream : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMSCESEquisat
      (AyMSCESAcceptedSatReport
        retained_stream audit_entry original_model)
      (AyMSCESConj retained_stream
        (AyMSCESConj audit_entry original_model)) := by
  exact ay_msces_equisat_intro
    (AyMSCESAcceptedSatReport
      retained_stream audit_entry original_model)
    (AyMSCESConj retained_stream
      (AyMSCESConj audit_entry original_model))
    (fun report =>
      ay_msces_conj_intro retained_stream
        (AyMSCESConj audit_entry original_model)
        (ay_msces_report_retained
          retained_stream audit_entry original_model report)
        (ay_msces_conj_intro audit_entry original_model
          (ay_msces_report_audit
            retained_stream audit_entry original_model report)
          (ay_msces_report_original
            retained_stream audit_entry original_model report)))
    (fun bundle =>
      ay_msces_report_intro retained_stream audit_entry original_model
        (ay_msces_conj_left retained_stream
          (AyMSCESConj audit_entry original_model) bundle)
        (ay_msces_conj_left audit_entry original_model
          (ay_msces_conj_right retained_stream
            (AyMSCESConj audit_entry original_model) bundle))
        (ay_msces_conj_right audit_entry original_model
          (ay_msces_conj_right retained_stream
            (AyMSCESConj audit_entry original_model) bundle)))

theorem ay_msces_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMSCESNoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_msces_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_msces_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSCESNoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_msces_conj_left diagnostic (public_claim -> False) diag

theorem ay_msces_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSCESNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_msces_conj_right diagnostic (public_claim -> False) diag

theorem ay_msces_recompute_obligation_intro
    (reason : Prop) (recompute_request : Prop) :
    reason ->
    recompute_request ->
    AyMSCESRecomputeObligation reason recompute_request := by
  intro hreason
  intro hrequest
  exact ay_msces_conj_intro reason recompute_request
    hreason hrequest

theorem ay_msces_recompute_obligation_reason
    (reason : Prop) (recompute_request : Prop) :
    AyMSCESRecomputeObligation reason recompute_request ->
    reason := by
  intro obligation
  exact ay_msces_conj_left reason recompute_request obligation

theorem ay_msces_recompute_obligation_request
    (reason : Prop) (recompute_request : Prop) :
    AyMSCESRecomputeObligation reason recompute_request ->
    recompute_request := by
  intro obligation
  exact ay_msces_conj_right reason recompute_request obligation

theorem ay_msces_evicted_chunk_no_claim
    (eviction_record : Prop) (public_claim : Prop) :
    AyMSCESEvictedChunk eviction_record ->
    (public_claim -> eviction_record -> False) ->
    AyMSCESNoClaimDiagnostic eviction_record public_claim := by
  intro hevicted
  intro blocks
  exact ay_msces_no_claim_diagnostic_intro
    eviction_record public_claim
    hevicted
    (fun claim => blocks claim hevicted)

theorem ay_msces_missing_chunk_recompute
    (missing_record : Prop) (recompute_request : Prop) :
    AyMSCESMissingChunk missing_record ->
    recompute_request ->
    AyMSCESRecomputeObligation missing_record recompute_request := by
  intro hmissing
  intro hrequest
  exact ay_msces_recompute_obligation_intro
    missing_record recompute_request hmissing hrequest

theorem ay_msces_missing_chunk_no_claim
    (missing_record : Prop) (public_claim : Prop) :
    AyMSCESMissingChunk missing_record ->
    (public_claim -> missing_record -> False) ->
    AyMSCESNoClaimDiagnostic missing_record public_claim := by
  intro hmissing
  intro blocks
  exact ay_msces_no_claim_diagnostic_intro
    missing_record public_claim
    hmissing
    (fun claim => blocks claim hmissing)

theorem ay_msces_stale_chunk_intro
    (stale_record : Prop) (digest_mismatch : Prop) :
    stale_record ->
    digest_mismatch ->
    AyMSCESStaleChunk stale_record digest_mismatch := by
  intro hstale
  intro hmismatch
  exact ay_msces_conj_intro stale_record digest_mismatch
    hstale hmismatch

theorem ay_msces_stale_chunk_record
    (stale_record : Prop) (digest_mismatch : Prop) :
    AyMSCESStaleChunk stale_record digest_mismatch ->
    stale_record := by
  intro stale
  exact ay_msces_conj_left stale_record digest_mismatch stale

theorem ay_msces_stale_chunk_mismatch
    (stale_record : Prop) (digest_mismatch : Prop) :
    AyMSCESStaleChunk stale_record digest_mismatch ->
    digest_mismatch := by
  intro stale
  exact ay_msces_conj_right stale_record digest_mismatch stale

theorem ay_msces_stale_chunk_no_claim
    (stale_record : Prop) (digest_mismatch : Prop)
    (public_claim : Prop) :
    AyMSCESStaleChunk stale_record digest_mismatch ->
    (public_claim -> digest_mismatch -> False) ->
    AyMSCESNoClaimDiagnostic digest_mismatch public_claim := by
  intro stale
  intro blocks
  exact ay_msces_no_claim_diagnostic_intro
    digest_mismatch public_claim
    (ay_msces_stale_chunk_mismatch
      stale_record digest_mismatch stale)
    (fun claim =>
      blocks claim
        (ay_msces_stale_chunk_mismatch
          stale_record digest_mismatch stale))

theorem ay_msces_evicted_or_missing_forces_recompute_or_no_claim
    (eviction_record : Prop) (missing_record : Prop)
    (public_claim : Prop) (recompute_request : Prop) :
    AyMSCESDisj
      (AyMSCESEvictedChunk eviction_record)
      (AyMSCESMissingChunk missing_record) ->
    (public_claim -> eviction_record -> False) ->
    recompute_request ->
    AyMSCESDisj
      (AyMSCESNoClaimDiagnostic eviction_record public_claim)
      (AyMSCESRecomputeObligation missing_record recompute_request) := by
  intro state
  intro evicted_blocks
  intro hrequest
  exact state
    (AyMSCESDisj
      (AyMSCESNoClaimDiagnostic eviction_record public_claim)
      (AyMSCESRecomputeObligation missing_record recompute_request))
    (fun hevicted =>
      ay_msces_disj_left
        (AyMSCESNoClaimDiagnostic eviction_record public_claim)
        (AyMSCESRecomputeObligation missing_record recompute_request)
        (ay_msces_evicted_chunk_no_claim
          eviction_record public_claim hevicted evicted_blocks))
    (fun hmissing =>
      ay_msces_disj_right
        (AyMSCESNoClaimDiagnostic eviction_record public_claim)
        (AyMSCESRecomputeObligation missing_record recompute_request)
        (ay_msces_missing_chunk_recompute
          missing_record recompute_request hmissing hrequest))

theorem ay_msces_diagnostic_blocks_stale_report
    (diagnostic : Prop) (public_claim : Prop) :
    AyMSCESNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_msces_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim

