-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for incremental/preprocessed model projection.
-- Cached assignments justify original-formula SAT reports only when the
-- incremental context and preprocessing projection match the manifest/digest
-- guard. Changed clauses, assumptions, or projections force diagnostics or
-- recomputation rather than stale SAT claims.

def AyMIPSConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMIPSDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMIPSEquisat (before : Prop) (after : Prop) :=
  AyMIPSConj (before -> after) (after -> before)

def AyMIPSIncrementalContext
    (original_formula : Prop) (clause_additions : Prop)
    (assumptions : Prop) :=
  AyMIPSConj original_formula
    (AyMIPSConj clause_additions assumptions)

def AyMIPSContextMatch
    (cached_context : Prop) (current_context : Prop) :=
  AyMIPSConj cached_context current_context

def AyMIPSManifestDigestGuard
    (manifest_ids : Prop) (digest_guard : Prop) :=
  AyMIPSConj manifest_ids digest_guard

def AyMIPSPreprocessProjection
    (cached_assignment : Prop) (visible_assignment : Prop) :=
  cached_assignment -> visible_assignment

def AyMIPSOriginalReconstruction
    (visible_assignment : Prop) (original_model : Prop) :=
  visible_assignment -> original_model

def AyMIPSProjectionMapMatch
    (projection_map_id : Prop) (projection_evidence : Prop) :=
  AyMIPSConj projection_map_id projection_evidence

def AyMIPSModelCacheEntry
    (context_guard : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (cached_assignment : Prop) :=
  AyMIPSConj context_guard
    (AyMIPSConj manifest_guard
      (AyMIPSConj projection_match cached_assignment))

def AyMIPSAcceptedSatReport
    (context_match : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (original_model : Prop) :=
  AyMIPSConj context_match
    (AyMIPSConj manifest_guard
      (AyMIPSConj projection_match original_model))

def AyMIPSNoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMIPSConj diagnostic (public_claim -> False)

def AyMIPSRecomputeObligation
    (reason : Prop) (recompute_request : Prop) :=
  AyMIPSConj reason recompute_request

theorem ay_mips_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMIPSConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mips_conj_left
    (left : Prop) (right : Prop) :
    AyMIPSConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mips_conj_right
    (left : Prop) (right : Prop) :
    AyMIPSConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mips_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMIPSDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mips_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMIPSDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mips_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMIPSEquisat before after := by
  intro forward
  intro backward
  exact ay_mips_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_mips_equisat_forward
    (before : Prop) (after : Prop) :
    AyMIPSEquisat before after -> before -> after := by
  intro certificate
  exact ay_mips_conj_left (before -> after) (after -> before) certificate

theorem ay_mips_equisat_backward
    (before : Prop) (after : Prop) :
    AyMIPSEquisat before after -> after -> before := by
  intro certificate
  exact ay_mips_conj_right (before -> after) (after -> before) certificate

theorem ay_mips_context_intro
    (original_formula : Prop) (clause_additions : Prop)
    (assumptions : Prop) :
    original_formula ->
    clause_additions ->
    assumptions ->
    AyMIPSIncrementalContext
      original_formula clause_additions assumptions := by
  intro horiginal
  intro hclauses
  intro hassumptions
  exact ay_mips_conj_intro original_formula
    (AyMIPSConj clause_additions assumptions)
    horiginal
    (ay_mips_conj_intro clause_additions assumptions
      hclauses hassumptions)

theorem ay_mips_context_original
    (original_formula : Prop) (clause_additions : Prop)
    (assumptions : Prop) :
    AyMIPSIncrementalContext
      original_formula clause_additions assumptions ->
    original_formula := by
  intro context
  exact ay_mips_conj_left original_formula
    (AyMIPSConj clause_additions assumptions) context

theorem ay_mips_context_clauses
    (original_formula : Prop) (clause_additions : Prop)
    (assumptions : Prop) :
    AyMIPSIncrementalContext
      original_formula clause_additions assumptions ->
    clause_additions := by
  intro context
  exact ay_mips_conj_left clause_additions assumptions
    (ay_mips_conj_right original_formula
      (AyMIPSConj clause_additions assumptions) context)

theorem ay_mips_context_assumptions
    (original_formula : Prop) (clause_additions : Prop)
    (assumptions : Prop) :
    AyMIPSIncrementalContext
      original_formula clause_additions assumptions ->
    assumptions := by
  intro context
  exact ay_mips_conj_right clause_additions assumptions
    (ay_mips_conj_right original_formula
      (AyMIPSConj clause_additions assumptions) context)

theorem ay_mips_context_match_intro
    (cached_context : Prop) (current_context : Prop) :
    cached_context ->
    current_context ->
    AyMIPSContextMatch cached_context current_context := by
  intro hcached
  intro hcurrent
  exact ay_mips_conj_intro cached_context current_context
    hcached hcurrent

theorem ay_mips_context_match_cached
    (cached_context : Prop) (current_context : Prop) :
    AyMIPSContextMatch cached_context current_context ->
    cached_context := by
  intro hmatch
  exact ay_mips_conj_left cached_context current_context hmatch

theorem ay_mips_context_match_current
    (cached_context : Prop) (current_context : Prop) :
    AyMIPSContextMatch cached_context current_context ->
    current_context := by
  intro hmatch
  exact ay_mips_conj_right cached_context current_context hmatch

theorem ay_mips_manifest_digest_guard_intro
    (manifest_ids : Prop) (digest_guard : Prop) :
    manifest_ids ->
    digest_guard ->
    AyMIPSManifestDigestGuard manifest_ids digest_guard := by
  intro hmanifest
  intro hdigest
  exact ay_mips_conj_intro manifest_ids digest_guard
    hmanifest hdigest

theorem ay_mips_manifest_digest_guard_manifest
    (manifest_ids : Prop) (digest_guard : Prop) :
    AyMIPSManifestDigestGuard manifest_ids digest_guard ->
    manifest_ids := by
  intro guard
  exact ay_mips_conj_left manifest_ids digest_guard guard

theorem ay_mips_manifest_digest_guard_digest
    (manifest_ids : Prop) (digest_guard : Prop) :
    AyMIPSManifestDigestGuard manifest_ids digest_guard ->
    digest_guard := by
  intro guard
  exact ay_mips_conj_right manifest_ids digest_guard guard

theorem ay_mips_projection_apply
    (cached_assignment : Prop) (visible_assignment : Prop) :
    AyMIPSPreprocessProjection cached_assignment visible_assignment ->
    cached_assignment ->
    visible_assignment := by
  intro project
  intro hcached
  exact project hcached

theorem ay_mips_reconstruction_apply
    (visible_assignment : Prop) (original_model : Prop) :
    AyMIPSOriginalReconstruction visible_assignment original_model ->
    visible_assignment ->
    original_model := by
  intro reconstruct
  intro hvisible
  exact reconstruct hvisible

theorem ay_mips_projection_map_match_intro
    (projection_map_id : Prop) (projection_evidence : Prop) :
    projection_map_id ->
    projection_evidence ->
    AyMIPSProjectionMapMatch
      projection_map_id projection_evidence := by
  intro hmap
  intro hevidence
  exact ay_mips_conj_intro projection_map_id projection_evidence
    hmap hevidence

theorem ay_mips_projection_map_match_id
    (projection_map_id : Prop) (projection_evidence : Prop) :
    AyMIPSProjectionMapMatch
      projection_map_id projection_evidence ->
    projection_map_id := by
  intro hmatch
  exact ay_mips_conj_left projection_map_id projection_evidence hmatch

theorem ay_mips_projection_map_match_evidence
    (projection_map_id : Prop) (projection_evidence : Prop) :
    AyMIPSProjectionMapMatch
      projection_map_id projection_evidence ->
    projection_evidence := by
  intro hmatch
  exact ay_mips_conj_right projection_map_id projection_evidence hmatch

theorem ay_mips_cache_entry_intro
    (context_guard : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (cached_assignment : Prop) :
    context_guard ->
    manifest_guard ->
    projection_match ->
    cached_assignment ->
    AyMIPSModelCacheEntry
      context_guard manifest_guard projection_match
      cached_assignment := by
  intro hcontext
  intro hmanifest
  intro hprojection
  intro hcached
  exact ay_mips_conj_intro context_guard
    (AyMIPSConj manifest_guard
      (AyMIPSConj projection_match cached_assignment))
    hcontext
    (ay_mips_conj_intro manifest_guard
      (AyMIPSConj projection_match cached_assignment)
      hmanifest
      (ay_mips_conj_intro projection_match cached_assignment
        hprojection hcached))

theorem ay_mips_cache_entry_context
    (context_guard : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (cached_assignment : Prop) :
    AyMIPSModelCacheEntry
      context_guard manifest_guard projection_match
      cached_assignment ->
    context_guard := by
  intro entry
  exact ay_mips_conj_left context_guard
    (AyMIPSConj manifest_guard
      (AyMIPSConj projection_match cached_assignment)) entry

theorem ay_mips_cache_entry_manifest
    (context_guard : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (cached_assignment : Prop) :
    AyMIPSModelCacheEntry
      context_guard manifest_guard projection_match
      cached_assignment ->
    manifest_guard := by
  intro entry
  exact ay_mips_conj_left manifest_guard
    (AyMIPSConj projection_match cached_assignment)
    (ay_mips_conj_right context_guard
      (AyMIPSConj manifest_guard
        (AyMIPSConj projection_match cached_assignment)) entry)

theorem ay_mips_cache_entry_projection
    (context_guard : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (cached_assignment : Prop) :
    AyMIPSModelCacheEntry
      context_guard manifest_guard projection_match
      cached_assignment ->
    projection_match := by
  intro entry
  exact ay_mips_conj_left projection_match cached_assignment
    (ay_mips_conj_right manifest_guard
      (AyMIPSConj projection_match cached_assignment)
      (ay_mips_conj_right context_guard
        (AyMIPSConj manifest_guard
          (AyMIPSConj projection_match cached_assignment)) entry))

theorem ay_mips_cache_entry_assignment
    (context_guard : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (cached_assignment : Prop) :
    AyMIPSModelCacheEntry
      context_guard manifest_guard projection_match
      cached_assignment ->
    cached_assignment := by
  intro entry
  exact ay_mips_conj_right projection_match cached_assignment
    (ay_mips_conj_right manifest_guard
      (AyMIPSConj projection_match cached_assignment)
      (ay_mips_conj_right context_guard
        (AyMIPSConj manifest_guard
          (AyMIPSConj projection_match cached_assignment)) entry))

theorem ay_mips_sat_report_intro
    (context_match : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (original_model : Prop) :
    context_match ->
    manifest_guard ->
    projection_match ->
    original_model ->
    AyMIPSAcceptedSatReport
      context_match manifest_guard projection_match original_model := by
  intro hcontext
  intro hmanifest
  intro hprojection
  intro horiginal
  exact ay_mips_conj_intro context_match
    (AyMIPSConj manifest_guard
      (AyMIPSConj projection_match original_model))
    hcontext
    (ay_mips_conj_intro manifest_guard
      (AyMIPSConj projection_match original_model)
      hmanifest
      (ay_mips_conj_intro projection_match original_model
        hprojection horiginal))

theorem ay_mips_sat_report_context
    (context_match : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (original_model : Prop) :
    AyMIPSAcceptedSatReport
      context_match manifest_guard projection_match original_model ->
    context_match := by
  intro report
  exact ay_mips_conj_left context_match
    (AyMIPSConj manifest_guard
      (AyMIPSConj projection_match original_model)) report

theorem ay_mips_sat_report_manifest
    (context_match : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (original_model : Prop) :
    AyMIPSAcceptedSatReport
      context_match manifest_guard projection_match original_model ->
    manifest_guard := by
  intro report
  exact ay_mips_conj_left manifest_guard
    (AyMIPSConj projection_match original_model)
    (ay_mips_conj_right context_match
      (AyMIPSConj manifest_guard
        (AyMIPSConj projection_match original_model)) report)

theorem ay_mips_sat_report_projection
    (context_match : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (original_model : Prop) :
    AyMIPSAcceptedSatReport
      context_match manifest_guard projection_match original_model ->
    projection_match := by
  intro report
  exact ay_mips_conj_left projection_match original_model
    (ay_mips_conj_right manifest_guard
      (AyMIPSConj projection_match original_model)
      (ay_mips_conj_right context_match
        (AyMIPSConj manifest_guard
          (AyMIPSConj projection_match original_model)) report))

theorem ay_mips_sat_report_original
    (context_match : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (original_model : Prop) :
    AyMIPSAcceptedSatReport
      context_match manifest_guard projection_match original_model ->
    original_model := by
  intro report
  exact ay_mips_conj_right projection_match original_model
    (ay_mips_conj_right manifest_guard
      (AyMIPSConj projection_match original_model)
      (ay_mips_conj_right context_match
        (AyMIPSConj manifest_guard
          (AyMIPSConj projection_match original_model)) report))

theorem ay_mips_cached_projection_original_model
    (context_match : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (cached_assignment : Prop)
    (visible_assignment : Prop) (original_model : Prop) :
    AyMIPSPreprocessProjection cached_assignment visible_assignment ->
    AyMIPSOriginalReconstruction visible_assignment original_model ->
    AyMIPSModelCacheEntry
      context_match manifest_guard projection_match cached_assignment ->
    original_model := by
  intro project
  intro reconstruct
  intro entry
  exact reconstruct
    (project
      (ay_mips_cache_entry_assignment
        context_match manifest_guard projection_match
        cached_assignment entry))

theorem ay_mips_cached_projection_sat_report
    (context_match : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (cached_assignment : Prop)
    (visible_assignment : Prop) (original_model : Prop) :
    AyMIPSPreprocessProjection cached_assignment visible_assignment ->
    AyMIPSOriginalReconstruction visible_assignment original_model ->
    AyMIPSModelCacheEntry
      context_match manifest_guard projection_match cached_assignment ->
    AyMIPSAcceptedSatReport
      context_match manifest_guard projection_match original_model := by
  intro project
  intro reconstruct
  intro entry
  exact ay_mips_sat_report_intro
    context_match manifest_guard projection_match original_model
    (ay_mips_cache_entry_context
      context_match manifest_guard projection_match cached_assignment entry)
    (ay_mips_cache_entry_manifest
      context_match manifest_guard projection_match cached_assignment entry)
    (ay_mips_cache_entry_projection
      context_match manifest_guard projection_match cached_assignment entry)
    (reconstruct
      (project
        (ay_mips_cache_entry_assignment
          context_match manifest_guard projection_match
          cached_assignment entry)))

theorem ay_mips_cached_report_requires_context_match
    (context_match : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (original_model : Prop) :
    AyMIPSAcceptedSatReport
      context_match manifest_guard projection_match original_model ->
    context_match := by
  exact ay_mips_sat_report_context
    context_match manifest_guard projection_match original_model

theorem ay_mips_cached_report_requires_projection_match
    (context_match : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (original_model : Prop) :
    AyMIPSAcceptedSatReport
      context_match manifest_guard projection_match original_model ->
    projection_match := by
  exact ay_mips_sat_report_projection
    context_match manifest_guard projection_match original_model

theorem ay_mips_cached_report_sound_original
    (context_match : Prop) (manifest_guard : Prop)
    (projection_match : Prop) (original_model : Prop) :
    AyMIPSAcceptedSatReport
      context_match manifest_guard projection_match original_model ->
    original_model := by
  exact ay_mips_sat_report_original
    context_match manifest_guard projection_match original_model

theorem ay_mips_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMIPSNoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_mips_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_mips_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMIPSNoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_mips_conj_left diagnostic (public_claim -> False) diag

theorem ay_mips_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMIPSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_mips_conj_right diagnostic (public_claim -> False) diag

theorem ay_mips_recompute_obligation_intro
    (reason : Prop) (recompute_request : Prop) :
    reason ->
    recompute_request ->
    AyMIPSRecomputeObligation reason recompute_request := by
  intro hreason
  intro hrequest
  exact ay_mips_conj_intro reason recompute_request
    hreason hrequest

theorem ay_mips_recompute_obligation_reason
    (reason : Prop) (recompute_request : Prop) :
    AyMIPSRecomputeObligation reason recompute_request ->
    reason := by
  intro obligation
  exact ay_mips_conj_left reason recompute_request obligation

theorem ay_mips_recompute_obligation_request
    (reason : Prop) (recompute_request : Prop) :
    AyMIPSRecomputeObligation reason recompute_request ->
    recompute_request := by
  intro obligation
  exact ay_mips_conj_right reason recompute_request obligation

theorem ay_mips_changed_clauses_no_claim
    (changed_clauses : Prop) (public_claim : Prop) :
    changed_clauses ->
    (public_claim -> changed_clauses -> False) ->
    AyMIPSNoClaimDiagnostic changed_clauses public_claim := by
  intro hchanged
  intro blocks
  exact ay_mips_no_claim_diagnostic_intro
    changed_clauses public_claim
    hchanged
    (fun claim => blocks claim hchanged)

theorem ay_mips_changed_assumptions_no_claim
    (changed_assumptions : Prop) (public_claim : Prop) :
    changed_assumptions ->
    (public_claim -> changed_assumptions -> False) ->
    AyMIPSNoClaimDiagnostic changed_assumptions public_claim := by
  intro hchanged
  intro blocks
  exact ay_mips_no_claim_diagnostic_intro
    changed_assumptions public_claim
    hchanged
    (fun claim => blocks claim hchanged)

theorem ay_mips_projection_mismatch_no_claim
    (projection_mismatch : Prop) (public_claim : Prop) :
    projection_mismatch ->
    (public_claim -> projection_mismatch -> False) ->
    AyMIPSNoClaimDiagnostic projection_mismatch public_claim := by
  intro hmismatch
  intro blocks
  exact ay_mips_no_claim_diagnostic_intro
    projection_mismatch public_claim
    hmismatch
    (fun claim => blocks claim hmismatch)

theorem ay_mips_manifest_digest_mismatch_no_claim
    (manifest_or_digest_mismatch : Prop) (public_claim : Prop) :
    manifest_or_digest_mismatch ->
    (public_claim -> manifest_or_digest_mismatch -> False) ->
    AyMIPSNoClaimDiagnostic
      manifest_or_digest_mismatch public_claim := by
  intro hmismatch
  intro blocks
  exact ay_mips_no_claim_diagnostic_intro
    manifest_or_digest_mismatch public_claim
    hmismatch
    (fun claim => blocks claim hmismatch)

theorem ay_mips_changed_clauses_recompute
    (changed_clauses : Prop) (recompute_request : Prop) :
    changed_clauses ->
    recompute_request ->
    AyMIPSRecomputeObligation
      changed_clauses recompute_request := by
  intro hchanged
  intro hrequest
  exact ay_mips_recompute_obligation_intro
    changed_clauses recompute_request hchanged hrequest

theorem ay_mips_changed_assumptions_recompute
    (changed_assumptions : Prop) (recompute_request : Prop) :
    changed_assumptions ->
    recompute_request ->
    AyMIPSRecomputeObligation
      changed_assumptions recompute_request := by
  intro hchanged
  intro hrequest
  exact ay_mips_recompute_obligation_intro
    changed_assumptions recompute_request hchanged hrequest

theorem ay_mips_projection_mismatch_recompute
    (projection_mismatch : Prop) (recompute_request : Prop) :
    projection_mismatch ->
    recompute_request ->
    AyMIPSRecomputeObligation
      projection_mismatch recompute_request := by
  intro hmismatch
  intro hrequest
  exact ay_mips_recompute_obligation_intro
    projection_mismatch recompute_request hmismatch hrequest

theorem ay_mips_context_change_no_stale_sat
    (changed_clauses : Prop) (changed_assumptions : Prop)
    (public_claim : Prop) :
    AyMIPSDisj changed_clauses changed_assumptions ->
    (public_claim -> changed_clauses -> False) ->
    (public_claim -> changed_assumptions -> False) ->
    AyMIPSDisj
      (AyMIPSNoClaimDiagnostic changed_clauses public_claim)
      (AyMIPSNoClaimDiagnostic changed_assumptions public_claim) := by
  intro changed
  intro clauses_block
  intro assumptions_block
  exact changed
    (AyMIPSDisj
      (AyMIPSNoClaimDiagnostic changed_clauses public_claim)
      (AyMIPSNoClaimDiagnostic changed_assumptions public_claim))
    (fun hclauses =>
      ay_mips_disj_left
        (AyMIPSNoClaimDiagnostic changed_clauses public_claim)
        (AyMIPSNoClaimDiagnostic changed_assumptions public_claim)
        (ay_mips_changed_clauses_no_claim
          changed_clauses public_claim hclauses clauses_block))
    (fun hassumptions =>
      ay_mips_disj_right
        (AyMIPSNoClaimDiagnostic changed_clauses public_claim)
        (AyMIPSNoClaimDiagnostic changed_assumptions public_claim)
        (ay_mips_changed_assumptions_no_claim
          changed_assumptions public_claim
          hassumptions assumptions_block))

theorem ay_mips_invalidated_cache_requires_recompute_or_no_claim
    (changed_context : Prop) (projection_mismatch : Prop)
    (public_claim : Prop) (recompute_request : Prop) :
    AyMIPSDisj changed_context projection_mismatch ->
    (public_claim -> changed_context -> False) ->
    recompute_request ->
    AyMIPSDisj
      (AyMIPSNoClaimDiagnostic changed_context public_claim)
      (AyMIPSRecomputeObligation
        projection_mismatch recompute_request) := by
  intro invalidated
  intro context_blocks
  intro hrequest
  exact invalidated
    (AyMIPSDisj
      (AyMIPSNoClaimDiagnostic changed_context public_claim)
      (AyMIPSRecomputeObligation
        projection_mismatch recompute_request))
    (fun hchanged =>
      ay_mips_disj_left
        (AyMIPSNoClaimDiagnostic changed_context public_claim)
        (AyMIPSRecomputeObligation
          projection_mismatch recompute_request)
        (ay_mips_no_claim_diagnostic_intro
          changed_context public_claim
          hchanged
          (fun claim => context_blocks claim hchanged)))
    (fun hmismatch =>
      ay_mips_disj_right
        (AyMIPSNoClaimDiagnostic changed_context public_claim)
        (AyMIPSRecomputeObligation
          projection_mismatch recompute_request)
        (ay_mips_projection_mismatch_recompute
          projection_mismatch recompute_request hmismatch hrequest))

theorem ay_mips_diagnostic_blocks_stale_report
    (diagnostic : Prop) (public_claim : Prop) :
    AyMIPSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_mips_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim
