-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for refining model-cache guards. Coarse CNF
-- digests are strengthened by refined witness and partition digests; only
-- accepted refinement evidence permits cache reuse and public SAT claims.

def AyMCDRConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMCDRDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMCDREquisat (before : Prop) (after : Prop) :=
  AyMCDRConj (before -> after) (after -> before)

def AyMCDRCoarseGuard (coarse_cnf_digest : Prop) :=
  coarse_cnf_digest

def AyMCDRRefinedGuard
    (coarse_cnf_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :=
  AyMCDRConj coarse_cnf_digest
    (AyMCDRConj witness_digest partition_digest)

def AyMCDRAcceptedRefinement
    (requested_guard : Prop) (stored_guard : Prop) :=
  requested_guard -> stored_guard

def AyMCDRRefinementMismatch
    (requested_guard : Prop) (stored_guard : Prop) :=
  requested_guard -> stored_guard -> False

def AyMCDRInvalidation (stored_guard : Prop) :=
  stored_guard -> False

def AyMCDRCacheEntry (stored_guard : Prop) (partition : Prop) :=
  stored_guard -> partition

def AyMCDRProjection
    (compressed_witness : Prop) (visible_assignment : Prop) :=
  compressed_witness -> visible_assignment

def AyMCDRPreprocessReconstruction
    (visible_assignment : Prop) (original_assignment : Prop) :=
  visible_assignment -> original_assignment

def AyMCDRCachedPublicClaim
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :=
  AyMCDRConj requested_guard
    (AyMCDRConj stored_guard original_assignment)

def AyMCDRNoClaim (claim : Prop) :=
  claim -> False

def AyMCDRPublicSatAnswer (original_assignment : Prop) :=
  original_assignment

theorem ay_mcdr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMCDRConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mcdr_conj_left
    (left : Prop) (right : Prop) :
    AyMCDRConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mcdr_conj_right
    (left : Prop) (right : Prop) :
    AyMCDRConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mcdr_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMCDRDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mcdr_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMCDRDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mcdr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMCDREquisat before after := by
  intro forward
  intro backward
  exact ay_mcdr_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_mcdr_equisat_forward
    (before : Prop) (after : Prop) :
    AyMCDREquisat before after -> before -> after := by
  intro certificate
  exact ay_mcdr_conj_left (before -> after) (after -> before) certificate

theorem ay_mcdr_equisat_backward
    (before : Prop) (after : Prop) :
    AyMCDREquisat before after -> after -> before := by
  intro certificate
  exact ay_mcdr_conj_right (before -> after) (after -> before) certificate

theorem ay_mcdr_refined_guard_intro
    (coarse_cnf_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    coarse_cnf_digest ->
    witness_digest ->
    partition_digest ->
    AyMCDRRefinedGuard
      coarse_cnf_digest witness_digest partition_digest := by
  intro hcoarse
  intro hwitness
  intro hpartition
  exact ay_mcdr_conj_intro coarse_cnf_digest
    (AyMCDRConj witness_digest partition_digest)
    hcoarse
    (ay_mcdr_conj_intro witness_digest partition_digest
      hwitness hpartition)

theorem ay_mcdr_refined_guard_coarse
    (coarse_cnf_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    AyMCDRRefinedGuard
      coarse_cnf_digest witness_digest partition_digest ->
    coarse_cnf_digest := by
  intro guard
  exact ay_mcdr_conj_left coarse_cnf_digest
    (AyMCDRConj witness_digest partition_digest)
    guard

theorem ay_mcdr_refined_guard_witness
    (coarse_cnf_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    AyMCDRRefinedGuard
      coarse_cnf_digest witness_digest partition_digest ->
    witness_digest := by
  intro guard
  exact ay_mcdr_conj_left witness_digest partition_digest
    (ay_mcdr_conj_right coarse_cnf_digest
      (AyMCDRConj witness_digest partition_digest)
      guard)

theorem ay_mcdr_refined_guard_partition
    (coarse_cnf_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    AyMCDRRefinedGuard
      coarse_cnf_digest witness_digest partition_digest ->
    partition_digest := by
  intro guard
  exact ay_mcdr_conj_right witness_digest partition_digest
    (ay_mcdr_conj_right coarse_cnf_digest
      (AyMCDRConj witness_digest partition_digest)
      guard)

theorem ay_mcdr_accept_refinement
    (requested_guard : Prop) (stored_guard : Prop) :
    AyMCDRAcceptedRefinement requested_guard stored_guard ->
    requested_guard ->
    stored_guard := by
  intro accepted
  intro hrequested
  exact accepted hrequested

theorem ay_mcdr_cache_entry_lookup
    (stored_guard : Prop) (partition : Prop) :
    AyMCDRCacheEntry stored_guard partition ->
    stored_guard ->
    partition := by
  intro entry
  intro hstored
  exact entry hstored

theorem ay_mcdr_safe_reuse_partition
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) :
    AyMCDRAcceptedRefinement requested_guard stored_guard ->
    AyMCDRCacheEntry stored_guard partition ->
    requested_guard ->
    partition := by
  intro accepted
  intro entry
  intro hrequested
  exact entry (accepted hrequested)

theorem ay_mcdr_project_visible
    (compressed_witness : Prop) (visible_assignment : Prop) :
    AyMCDRProjection compressed_witness visible_assignment ->
    compressed_witness ->
    visible_assignment := by
  intro project
  intro hcompressed
  exact project hcompressed

theorem ay_mcdr_reconstruct_original
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyMCDRPreprocessReconstruction
      visible_assignment original_assignment ->
    visible_assignment ->
    original_assignment := by
  intro reconstruct
  intro hvisible
  exact reconstruct hvisible

theorem ay_mcdr_cached_claim_intro
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    requested_guard ->
    stored_guard ->
    original_assignment ->
    AyMCDRCachedPublicClaim
      requested_guard stored_guard original_assignment := by
  intro hrequested
  intro hstored
  intro horiginal
  exact ay_mcdr_conj_intro requested_guard
    (AyMCDRConj stored_guard original_assignment)
    hrequested
    (ay_mcdr_conj_intro stored_guard original_assignment
      hstored horiginal)

theorem ay_mcdr_cached_claim_requested
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    AyMCDRCachedPublicClaim
      requested_guard stored_guard original_assignment ->
    requested_guard := by
  intro claim
  exact ay_mcdr_conj_left requested_guard
    (AyMCDRConj stored_guard original_assignment)
    claim

theorem ay_mcdr_cached_claim_stored
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    AyMCDRCachedPublicClaim
      requested_guard stored_guard original_assignment ->
    stored_guard := by
  intro claim
  exact ay_mcdr_conj_left stored_guard original_assignment
    (ay_mcdr_conj_right requested_guard
      (AyMCDRConj stored_guard original_assignment)
      claim)

theorem ay_mcdr_cached_claim_original
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    AyMCDRCachedPublicClaim
      requested_guard stored_guard original_assignment ->
    original_assignment := by
  intro claim
  exact ay_mcdr_conj_right stored_guard original_assignment
    (ay_mcdr_conj_right requested_guard
      (AyMCDRConj stored_guard original_assignment)
      claim)

theorem ay_mcdr_mismatch_no_sat_claim
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    AyMCDRRefinementMismatch requested_guard stored_guard ->
    AyMCDRNoClaim
      (AyMCDRCachedPublicClaim
        requested_guard stored_guard original_assignment) := by
  intro mismatch
  intro claim
  exact mismatch
    (ay_mcdr_cached_claim_requested
      requested_guard stored_guard original_assignment claim)
    (ay_mcdr_cached_claim_stored
      requested_guard stored_guard original_assignment claim)

theorem ay_mcdr_invalidated_no_sat_claim
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    AyMCDRInvalidation stored_guard ->
    AyMCDRNoClaim
      (AyMCDRCachedPublicClaim
        requested_guard stored_guard original_assignment) := by
  intro invalidated
  intro claim
  exact invalidated
    (ay_mcdr_cached_claim_stored
      requested_guard stored_guard original_assignment claim)

theorem ay_mcdr_refined_matching_public_sat
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) (visible_cnf : Prop)
    (compressed_witness : Prop) (visible_assignment : Prop)
    (original_assignment : Prop) :
    AyMCDRAcceptedRefinement requested_guard stored_guard ->
    AyMCDRCacheEntry stored_guard partition ->
    (partition -> visible_cnf) ->
    AyMCDRProjection compressed_witness visible_assignment ->
    AyMCDRPreprocessReconstruction
      visible_assignment original_assignment ->
    requested_guard ->
    compressed_witness ->
    AyMCDRPublicSatAnswer original_assignment := by
  intro _accepted
  intro _entry
  intro _assemble
  intro project
  intro reconstruct
  intro _hrequested
  intro hcompressed
  exact reconstruct (project hcompressed)

theorem ay_mcdr_refined_matching_soundness_certificate
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) (visible_cnf : Prop)
    (compressed_witness : Prop) (visible_assignment : Prop)
    (original_assignment : Prop) :
    AyMCDRAcceptedRefinement requested_guard stored_guard ->
    AyMCDRCacheEntry stored_guard partition ->
    (partition -> visible_cnf) ->
    AyMCDRProjection compressed_witness visible_assignment ->
    AyMCDRPreprocessReconstruction
      visible_assignment original_assignment ->
    requested_guard ->
    compressed_witness ->
    AyMCDRConj visible_cnf original_assignment := by
  intro accepted
  intro entry
  intro assemble
  intro project
  intro reconstruct
  intro hrequested
  intro hcompressed
  exact ay_mcdr_conj_intro visible_cnf original_assignment
    (assemble
      (ay_mcdr_safe_reuse_partition
        requested_guard stored_guard partition accepted entry hrequested))
    (reconstruct (project hcompressed))

theorem ay_mcdr_refined_matching_cached_claim
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) (visible_cnf : Prop)
    (compressed_witness : Prop) (visible_assignment : Prop)
    (original_assignment : Prop) :
    AyMCDRAcceptedRefinement requested_guard stored_guard ->
    AyMCDRCacheEntry stored_guard partition ->
    (partition -> visible_cnf) ->
    AyMCDRProjection compressed_witness visible_assignment ->
    AyMCDRPreprocessReconstruction
      visible_assignment original_assignment ->
    requested_guard ->
    compressed_witness ->
    AyMCDRCachedPublicClaim
      requested_guard stored_guard original_assignment := by
  intro accepted
  intro _entry
  intro _assemble
  intro project
  intro reconstruct
  intro hrequested
  intro hcompressed
  exact ay_mcdr_cached_claim_intro
    requested_guard stored_guard original_assignment
    hrequested
    (accepted hrequested)
    (reconstruct (project hcompressed))
