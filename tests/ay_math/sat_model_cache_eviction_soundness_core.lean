-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for bounded model-cache eviction. Retained
-- entries can justify public SAT reports only with matching manifest, digest,
-- and projection evidence. Evicted, missing, or stale entries produce
-- diagnostics or recomputation obligations, never stale SAT claims.

def AyMCESConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMCESDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMCESEquisat (before : Prop) (after : Prop) :=
  AyMCESConj (before -> after) (after -> before)

def AyMCESManifestDigestGuard
    (manifest_ids : Prop) (digest_guard : Prop) :=
  AyMCESConj manifest_ids digest_guard

def AyMCESAssignmentProjection
    (cached_assignment : Prop) (visible_assignment : Prop) :=
  cached_assignment -> visible_assignment

def AyMCESOriginalReconstruction
    (visible_assignment : Prop) (original_model : Prop) :=
  visible_assignment -> original_model

def AyMCESModelCacheEntry
    (manifest_ids : Prop) (digest_guard : Prop)
    (cached_assignment : Prop) :=
  AyMCESConj manifest_ids
    (AyMCESConj digest_guard cached_assignment)

def AyMCESRetainedEntry
    (entry : Prop) (projection_evidence : Prop) :=
  AyMCESConj entry projection_evidence

def AyMCESEvictedEntry (eviction_record : Prop) :=
  eviction_record

def AyMCESMissingEntry (miss_record : Prop) :=
  miss_record

def AyMCESStaleEntry
    (stale_record : Prop) (guard_mismatch : Prop) :=
  AyMCESConj stale_record guard_mismatch

def AyMCESAuditMerkleOutcome
    (audit_entry : Prop) (merkle_root : Prop) :=
  AyMCESConj audit_entry merkle_root

def AyMCESPublicSatReport
    (manifest_ids : Prop) (digest_guard : Prop)
    (projection_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :=
  AyMCESConj manifest_ids
    (AyMCESConj digest_guard
      (AyMCESConj projection_evidence
        (AyMCESConj audit_merkle original_model)))

def AyMCESNoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMCESConj diagnostic (public_claim -> False)

def AyMCESRecomputeObligation
    (reason : Prop) (recompute_request : Prop) :=
  AyMCESConj reason recompute_request

theorem ay_mces_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMCESConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mces_conj_left
    (left : Prop) (right : Prop) :
    AyMCESConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mces_conj_right
    (left : Prop) (right : Prop) :
    AyMCESConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mces_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMCESDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mces_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMCESDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mces_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMCESEquisat before after := by
  intro forward
  intro backward
  exact ay_mces_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_mces_equisat_forward
    (before : Prop) (after : Prop) :
    AyMCESEquisat before after -> before -> after := by
  intro certificate
  exact ay_mces_conj_left (before -> after) (after -> before) certificate

theorem ay_mces_equisat_backward
    (before : Prop) (after : Prop) :
    AyMCESEquisat before after -> after -> before := by
  intro certificate
  exact ay_mces_conj_right (before -> after) (after -> before) certificate

theorem ay_mces_guard_intro
    (manifest_ids : Prop) (digest_guard : Prop) :
    manifest_ids ->
    digest_guard ->
    AyMCESManifestDigestGuard manifest_ids digest_guard := by
  intro hmanifest
  intro hdigest
  exact ay_mces_conj_intro manifest_ids digest_guard hmanifest hdigest

theorem ay_mces_guard_manifest
    (manifest_ids : Prop) (digest_guard : Prop) :
    AyMCESManifestDigestGuard manifest_ids digest_guard ->
    manifest_ids := by
  intro guard
  exact ay_mces_conj_left manifest_ids digest_guard guard

theorem ay_mces_guard_digest
    (manifest_ids : Prop) (digest_guard : Prop) :
    AyMCESManifestDigestGuard manifest_ids digest_guard ->
    digest_guard := by
  intro guard
  exact ay_mces_conj_right manifest_ids digest_guard guard

theorem ay_mces_projection_apply
    (cached_assignment : Prop) (visible_assignment : Prop) :
    AyMCESAssignmentProjection cached_assignment visible_assignment ->
    cached_assignment ->
    visible_assignment := by
  intro project
  intro hcached
  exact project hcached

theorem ay_mces_reconstruction_apply
    (visible_assignment : Prop) (original_model : Prop) :
    AyMCESOriginalReconstruction visible_assignment original_model ->
    visible_assignment ->
    original_model := by
  intro reconstruct
  intro hvisible
  exact reconstruct hvisible

theorem ay_mces_cache_entry_intro
    (manifest_ids : Prop) (digest_guard : Prop)
    (cached_assignment : Prop) :
    manifest_ids ->
    digest_guard ->
    cached_assignment ->
    AyMCESModelCacheEntry
      manifest_ids digest_guard cached_assignment := by
  intro hmanifest
  intro hdigest
  intro hcached
  exact ay_mces_conj_intro manifest_ids
    (AyMCESConj digest_guard cached_assignment)
    hmanifest
    (ay_mces_conj_intro digest_guard cached_assignment
      hdigest hcached)

theorem ay_mces_cache_entry_manifest
    (manifest_ids : Prop) (digest_guard : Prop)
    (cached_assignment : Prop) :
    AyMCESModelCacheEntry
      manifest_ids digest_guard cached_assignment ->
    manifest_ids := by
  intro entry
  exact ay_mces_conj_left manifest_ids
    (AyMCESConj digest_guard cached_assignment) entry

theorem ay_mces_cache_entry_digest
    (manifest_ids : Prop) (digest_guard : Prop)
    (cached_assignment : Prop) :
    AyMCESModelCacheEntry
      manifest_ids digest_guard cached_assignment ->
    digest_guard := by
  intro entry
  exact ay_mces_conj_left digest_guard cached_assignment
    (ay_mces_conj_right manifest_ids
      (AyMCESConj digest_guard cached_assignment) entry)

theorem ay_mces_cache_entry_assignment
    (manifest_ids : Prop) (digest_guard : Prop)
    (cached_assignment : Prop) :
    AyMCESModelCacheEntry
      manifest_ids digest_guard cached_assignment ->
    cached_assignment := by
  intro entry
  exact ay_mces_conj_right digest_guard cached_assignment
    (ay_mces_conj_right manifest_ids
      (AyMCESConj digest_guard cached_assignment) entry)

theorem ay_mces_retained_entry_intro
    (entry : Prop) (projection_evidence : Prop) :
    entry ->
    projection_evidence ->
    AyMCESRetainedEntry entry projection_evidence := by
  intro hentry
  intro hprojection
  exact ay_mces_conj_intro entry projection_evidence
    hentry hprojection

theorem ay_mces_retained_entry_cache
    (entry : Prop) (projection_evidence : Prop) :
    AyMCESRetainedEntry entry projection_evidence ->
    entry := by
  intro retained
  exact ay_mces_conj_left entry projection_evidence retained

theorem ay_mces_retained_entry_projection
    (entry : Prop) (projection_evidence : Prop) :
    AyMCESRetainedEntry entry projection_evidence ->
    projection_evidence := by
  intro retained
  exact ay_mces_conj_right entry projection_evidence retained

theorem ay_mces_audit_merkle_intro
    (audit_entry : Prop) (merkle_root : Prop) :
    audit_entry ->
    merkle_root ->
    AyMCESAuditMerkleOutcome audit_entry merkle_root := by
  intro haudit
  intro hroot
  exact ay_mces_conj_intro audit_entry merkle_root haudit hroot

theorem ay_mces_audit_merkle_entry
    (audit_entry : Prop) (merkle_root : Prop) :
    AyMCESAuditMerkleOutcome audit_entry merkle_root ->
    audit_entry := by
  intro outcome
  exact ay_mces_conj_left audit_entry merkle_root outcome

theorem ay_mces_audit_merkle_root
    (audit_entry : Prop) (merkle_root : Prop) :
    AyMCESAuditMerkleOutcome audit_entry merkle_root ->
    merkle_root := by
  intro outcome
  exact ay_mces_conj_right audit_entry merkle_root outcome

theorem ay_mces_public_report_intro
    (manifest_ids : Prop) (digest_guard : Prop)
    (projection_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    manifest_ids ->
    digest_guard ->
    projection_evidence ->
    audit_merkle ->
    original_model ->
    AyMCESPublicSatReport
      manifest_ids digest_guard projection_evidence
      audit_merkle original_model := by
  intro hmanifest
  intro hdigest
  intro hprojection
  intro haudit
  intro horiginal
  exact ay_mces_conj_intro manifest_ids
    (AyMCESConj digest_guard
      (AyMCESConj projection_evidence
        (AyMCESConj audit_merkle original_model)))
    hmanifest
    (ay_mces_conj_intro digest_guard
      (AyMCESConj projection_evidence
        (AyMCESConj audit_merkle original_model))
      hdigest
      (ay_mces_conj_intro projection_evidence
        (AyMCESConj audit_merkle original_model)
        hprojection
        (ay_mces_conj_intro audit_merkle original_model
          haudit horiginal)))

theorem ay_mces_public_report_manifest
    (manifest_ids : Prop) (digest_guard : Prop)
    (projection_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMCESPublicSatReport
      manifest_ids digest_guard projection_evidence
      audit_merkle original_model ->
    manifest_ids := by
  intro report
  exact ay_mces_conj_left manifest_ids
    (AyMCESConj digest_guard
      (AyMCESConj projection_evidence
        (AyMCESConj audit_merkle original_model))) report

theorem ay_mces_public_report_digest
    (manifest_ids : Prop) (digest_guard : Prop)
    (projection_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMCESPublicSatReport
      manifest_ids digest_guard projection_evidence
      audit_merkle original_model ->
    digest_guard := by
  intro report
  exact ay_mces_conj_left digest_guard
    (AyMCESConj projection_evidence
      (AyMCESConj audit_merkle original_model))
    (ay_mces_conj_right manifest_ids
      (AyMCESConj digest_guard
        (AyMCESConj projection_evidence
          (AyMCESConj audit_merkle original_model))) report)

theorem ay_mces_public_report_projection
    (manifest_ids : Prop) (digest_guard : Prop)
    (projection_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMCESPublicSatReport
      manifest_ids digest_guard projection_evidence
      audit_merkle original_model ->
    projection_evidence := by
  intro report
  exact ay_mces_conj_left projection_evidence
    (AyMCESConj audit_merkle original_model)
    (ay_mces_conj_right digest_guard
      (AyMCESConj projection_evidence
        (AyMCESConj audit_merkle original_model))
      (ay_mces_conj_right manifest_ids
        (AyMCESConj digest_guard
          (AyMCESConj projection_evidence
            (AyMCESConj audit_merkle original_model))) report))

theorem ay_mces_public_report_audit
    (manifest_ids : Prop) (digest_guard : Prop)
    (projection_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMCESPublicSatReport
      manifest_ids digest_guard projection_evidence
      audit_merkle original_model ->
    audit_merkle := by
  intro report
  exact ay_mces_conj_left audit_merkle original_model
    (ay_mces_conj_right projection_evidence
      (AyMCESConj audit_merkle original_model)
      (ay_mces_conj_right digest_guard
        (AyMCESConj projection_evidence
          (AyMCESConj audit_merkle original_model))
        (ay_mces_conj_right manifest_ids
          (AyMCESConj digest_guard
            (AyMCESConj projection_evidence
              (AyMCESConj audit_merkle original_model))) report)))

theorem ay_mces_public_report_original
    (manifest_ids : Prop) (digest_guard : Prop)
    (projection_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMCESPublicSatReport
      manifest_ids digest_guard projection_evidence
      audit_merkle original_model ->
    original_model := by
  intro report
  exact ay_mces_conj_right audit_merkle original_model
    (ay_mces_conj_right projection_evidence
      (AyMCESConj audit_merkle original_model)
      (ay_mces_conj_right digest_guard
        (AyMCESConj projection_evidence
          (AyMCESConj audit_merkle original_model))
        (ay_mces_conj_right manifest_ids
          (AyMCESConj digest_guard
            (AyMCESConj projection_evidence
              (AyMCESConj audit_merkle original_model))) report)))

theorem ay_mces_retained_entry_original_model
    (manifest_ids : Prop) (digest_guard : Prop)
    (cached_assignment : Prop) (visible_assignment : Prop)
    (original_model : Prop) (projection_evidence : Prop) :
    AyMCESAssignmentProjection cached_assignment visible_assignment ->
    AyMCESOriginalReconstruction visible_assignment original_model ->
    AyMCESRetainedEntry
      (AyMCESModelCacheEntry
        manifest_ids digest_guard cached_assignment)
      projection_evidence ->
    original_model := by
  intro project
  intro reconstruct
  intro retained
  exact reconstruct
    (project
      (ay_mces_cache_entry_assignment
        manifest_ids digest_guard cached_assignment
        (ay_mces_retained_entry_cache
          (AyMCESModelCacheEntry
            manifest_ids digest_guard cached_assignment)
          projection_evidence retained)))

theorem ay_mces_retained_entry_public_report
    (manifest_ids : Prop) (digest_guard : Prop)
    (cached_assignment : Prop) (visible_assignment : Prop)
    (original_model : Prop) (projection_evidence : Prop)
    (audit_merkle : Prop) :
    AyMCESAssignmentProjection cached_assignment visible_assignment ->
    AyMCESOriginalReconstruction visible_assignment original_model ->
    AyMCESRetainedEntry
      (AyMCESModelCacheEntry
        manifest_ids digest_guard cached_assignment)
      projection_evidence ->
    audit_merkle ->
    AyMCESPublicSatReport
      manifest_ids digest_guard projection_evidence
      audit_merkle original_model := by
  intro project
  intro reconstruct
  intro retained
  intro haudit
  let entry := ay_mces_retained_entry_cache
    (AyMCESModelCacheEntry
      manifest_ids digest_guard cached_assignment)
    projection_evidence retained
  exact ay_mces_public_report_intro
    manifest_ids digest_guard projection_evidence audit_merkle original_model
    (ay_mces_cache_entry_manifest
      manifest_ids digest_guard cached_assignment entry)
    (ay_mces_cache_entry_digest
      manifest_ids digest_guard cached_assignment entry)
    (ay_mces_retained_entry_projection
      (AyMCESModelCacheEntry
        manifest_ids digest_guard cached_assignment)
      projection_evidence retained)
    haudit
    (reconstruct
      (project
        (ay_mces_cache_entry_assignment
          manifest_ids digest_guard cached_assignment entry)))

theorem ay_mces_retained_report_requires_manifest
    (manifest_ids : Prop) (digest_guard : Prop)
    (projection_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMCESPublicSatReport
      manifest_ids digest_guard projection_evidence
      audit_merkle original_model ->
    manifest_ids := by
  exact ay_mces_public_report_manifest
    manifest_ids digest_guard projection_evidence audit_merkle original_model

theorem ay_mces_retained_report_requires_digest
    (manifest_ids : Prop) (digest_guard : Prop)
    (projection_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMCESPublicSatReport
      manifest_ids digest_guard projection_evidence
      audit_merkle original_model ->
    digest_guard := by
  exact ay_mces_public_report_digest
    manifest_ids digest_guard projection_evidence audit_merkle original_model

theorem ay_mces_retained_report_requires_projection
    (manifest_ids : Prop) (digest_guard : Prop)
    (projection_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMCESPublicSatReport
      manifest_ids digest_guard projection_evidence
      audit_merkle original_model ->
    projection_evidence := by
  exact ay_mces_public_report_projection
    manifest_ids digest_guard projection_evidence audit_merkle original_model

theorem ay_mces_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMCESNoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_mces_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_mces_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMCESNoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_mces_conj_left diagnostic (public_claim -> False) diag

theorem ay_mces_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMCESNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_mces_conj_right diagnostic (public_claim -> False) diag

theorem ay_mces_recompute_obligation_intro
    (reason : Prop) (recompute_request : Prop) :
    reason ->
    recompute_request ->
    AyMCESRecomputeObligation reason recompute_request := by
  intro hreason
  intro hrequest
  exact ay_mces_conj_intro reason recompute_request hreason hrequest

theorem ay_mces_recompute_obligation_reason
    (reason : Prop) (recompute_request : Prop) :
    AyMCESRecomputeObligation reason recompute_request ->
    reason := by
  intro obligation
  exact ay_mces_conj_left reason recompute_request obligation

theorem ay_mces_recompute_obligation_request
    (reason : Prop) (recompute_request : Prop) :
    AyMCESRecomputeObligation reason recompute_request ->
    recompute_request := by
  intro obligation
  exact ay_mces_conj_right reason recompute_request obligation

theorem ay_mces_evicted_entry_no_stale_claim
    (eviction_record : Prop) (public_claim : Prop) :
    AyMCESEvictedEntry eviction_record ->
    (public_claim -> eviction_record -> False) ->
    AyMCESNoClaimDiagnostic eviction_record public_claim := by
  intro hevicted
  intro blocks
  exact ay_mces_no_claim_diagnostic_intro
    eviction_record public_claim
    hevicted
    (fun claim => blocks claim hevicted)

theorem ay_mces_missing_entry_recompute
    (miss_record : Prop) (recompute_request : Prop) :
    AyMCESMissingEntry miss_record ->
    recompute_request ->
    AyMCESRecomputeObligation miss_record recompute_request := by
  intro hmissing
  intro hrequest
  exact ay_mces_recompute_obligation_intro
    miss_record recompute_request hmissing hrequest

theorem ay_mces_missing_entry_no_stale_claim
    (miss_record : Prop) (public_claim : Prop) :
    AyMCESMissingEntry miss_record ->
    (public_claim -> miss_record -> False) ->
    AyMCESNoClaimDiagnostic miss_record public_claim := by
  intro hmissing
  intro blocks
  exact ay_mces_no_claim_diagnostic_intro
    miss_record public_claim
    hmissing
    (fun claim => blocks claim hmissing)

theorem ay_mces_stale_entry_intro
    (stale_record : Prop) (guard_mismatch : Prop) :
    stale_record ->
    guard_mismatch ->
    AyMCESStaleEntry stale_record guard_mismatch := by
  intro hstale
  intro hmismatch
  exact ay_mces_conj_intro stale_record guard_mismatch
    hstale hmismatch

theorem ay_mces_stale_entry_record
    (stale_record : Prop) (guard_mismatch : Prop) :
    AyMCESStaleEntry stale_record guard_mismatch ->
    stale_record := by
  intro stale
  exact ay_mces_conj_left stale_record guard_mismatch stale

theorem ay_mces_stale_entry_mismatch
    (stale_record : Prop) (guard_mismatch : Prop) :
    AyMCESStaleEntry stale_record guard_mismatch ->
    guard_mismatch := by
  intro stale
  exact ay_mces_conj_right stale_record guard_mismatch stale

theorem ay_mces_stale_entry_no_stale_claim
    (stale_record : Prop) (guard_mismatch : Prop)
    (public_claim : Prop) :
    AyMCESStaleEntry stale_record guard_mismatch ->
    (public_claim -> guard_mismatch -> False) ->
    AyMCESNoClaimDiagnostic guard_mismatch public_claim := by
  intro stale
  intro blocks
  exact ay_mces_no_claim_diagnostic_intro
    guard_mismatch public_claim
    (ay_mces_stale_entry_mismatch stale_record guard_mismatch stale)
    (fun claim =>
      blocks claim
        (ay_mces_stale_entry_mismatch
          stale_record guard_mismatch stale))

theorem ay_mces_manifest_mismatch_no_claim
    (manifest_ids : Prop) (public_claim : Prop) :
    (manifest_ids -> False) ->
    (public_claim -> manifest_ids) ->
    AyMCESNoClaimDiagnostic (manifest_ids -> False) public_claim := by
  intro mismatch
  intro claim_to_manifest
  exact ay_mces_no_claim_diagnostic_intro
    (manifest_ids -> False) public_claim
    mismatch
    (fun claim => mismatch (claim_to_manifest claim))

theorem ay_mces_digest_mismatch_no_claim
    (digest_guard : Prop) (public_claim : Prop) :
    (digest_guard -> False) ->
    (public_claim -> digest_guard) ->
    AyMCESNoClaimDiagnostic (digest_guard -> False) public_claim := by
  intro mismatch
  intro claim_to_digest
  exact ay_mces_no_claim_diagnostic_intro
    (digest_guard -> False) public_claim
    mismatch
    (fun claim => mismatch (claim_to_digest claim))

theorem ay_mces_projection_mismatch_no_claim
    (projection_evidence : Prop) (public_claim : Prop) :
    (projection_evidence -> False) ->
    (public_claim -> projection_evidence) ->
    AyMCESNoClaimDiagnostic
      (projection_evidence -> False) public_claim := by
  intro mismatch
  intro claim_to_projection
  exact ay_mces_no_claim_diagnostic_intro
    (projection_evidence -> False) public_claim
    mismatch
    (fun claim => mismatch (claim_to_projection claim))

theorem ay_mces_audit_mismatch_no_claim
    (audit_merkle : Prop) (public_claim : Prop) :
    (audit_merkle -> False) ->
    (public_claim -> audit_merkle) ->
    AyMCESNoClaimDiagnostic (audit_merkle -> False) public_claim := by
  intro mismatch
  intro claim_to_audit
  exact ay_mces_no_claim_diagnostic_intro
    (audit_merkle -> False) public_claim
    mismatch
    (fun claim => mismatch (claim_to_audit claim))

theorem ay_mces_diagnostic_blocks_public_report
    (diagnostic : Prop) (public_claim : Prop) :
    AyMCESNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_mces_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim

theorem ay_mces_evicted_or_missing_requires_recompute_or_no_claim
    (eviction_record : Prop) (miss_record : Prop)
    (public_claim : Prop) (recompute_request : Prop) :
    AyMCESDisj
      (AyMCESEvictedEntry eviction_record)
      (AyMCESMissingEntry miss_record) ->
    (public_claim -> eviction_record -> False) ->
    recompute_request ->
    AyMCESDisj
      (AyMCESNoClaimDiagnostic eviction_record public_claim)
      (AyMCESRecomputeObligation miss_record recompute_request) := by
  intro state
  intro evicted_blocks
  intro hrequest
  exact state
    (AyMCESDisj
      (AyMCESNoClaimDiagnostic eviction_record public_claim)
      (AyMCESRecomputeObligation miss_record recompute_request))
    (fun hevicted =>
      ay_mces_disj_left
        (AyMCESNoClaimDiagnostic eviction_record public_claim)
        (AyMCESRecomputeObligation miss_record recompute_request)
        (ay_mces_evicted_entry_no_stale_claim
          eviction_record public_claim hevicted evicted_blocks))
    (fun hmissing =>
      ay_mces_disj_right
        (AyMCESNoClaimDiagnostic eviction_record public_claim)
        (AyMCESRecomputeObligation miss_record recompute_request)
        (ay_mces_missing_entry_recompute
          miss_record recompute_request hmissing hrequest))

