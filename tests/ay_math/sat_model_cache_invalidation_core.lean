-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for invalidating cached model/partition
-- checks. A cached public SAT claim carries the requested guard, the stored
-- guard, and the reconstructed original assignment; invalidation or guard
-- mismatch prevents that claim, while matched accepted reuse preserves SAT.

def AyMCIConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMCIDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMCIEquisat (before : Prop) (after : Prop) :=
  AyMCIConj (before -> after) (after -> before)

def AyMCIWitnessExpansion
    (compressed_witness : Prop) (full_assignment : Prop) :=
  compressed_witness -> full_assignment

def AyMCIProjection
    (full_assignment : Prop) (visible_assignment : Prop) :=
  full_assignment -> visible_assignment

def AyMCIGuard (witness_key : Prop) (cnf_digest : Prop) :=
  AyMCIConj witness_key cnf_digest

def AyMCIGuardMatch (requested_guard : Prop) (stored_guard : Prop) :=
  requested_guard -> stored_guard

def AyMCIGuardMismatch (requested_guard : Prop) (stored_guard : Prop) :=
  requested_guard -> stored_guard -> False

def AyMCIInvalidation (stored_guard : Prop) :=
  stored_guard -> False

def AyMCIPartitionCacheEntry (stored_guard : Prop) (partition : Prop) :=
  stored_guard -> partition

def AyMCIAcceptedReuse (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) :=
  AyMCIConj requested_guard (AyMCIConj stored_guard partition)

def AyMCIPreprocessReconstruction
    (visible_assignment : Prop) (original_assignment : Prop) :=
  visible_assignment -> original_assignment

def AyMCICachedPublicClaim
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :=
  AyMCIConj requested_guard
    (AyMCIConj stored_guard original_assignment)

def AyMCINoClaim (claim : Prop) :=
  claim -> False

def AyMCIPublicSatAnswer (original_assignment : Prop) :=
  original_assignment

theorem ay_mci_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMCIConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mci_conj_left
    (left : Prop) (right : Prop) :
    AyMCIConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mci_conj_right
    (left : Prop) (right : Prop) :
    AyMCIConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mci_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMCIDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mci_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMCIDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mci_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMCIEquisat before after := by
  intro forward
  intro backward
  exact ay_mci_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_mci_equisat_forward
    (before : Prop) (after : Prop) :
    AyMCIEquisat before after -> before -> after := by
  intro certificate
  exact ay_mci_conj_left (before -> after) (after -> before) certificate

theorem ay_mci_equisat_backward
    (before : Prop) (after : Prop) :
    AyMCIEquisat before after -> after -> before := by
  intro certificate
  exact ay_mci_conj_right (before -> after) (after -> before) certificate

theorem ay_mci_expand_witness
    (compressed_witness : Prop) (full_assignment : Prop) :
    AyMCIWitnessExpansion compressed_witness full_assignment ->
    compressed_witness ->
    full_assignment := by
  intro expand
  intro hcompressed
  exact expand hcompressed

theorem ay_mci_project_visible
    (full_assignment : Prop) (visible_assignment : Prop) :
    AyMCIProjection full_assignment visible_assignment ->
    full_assignment ->
    visible_assignment := by
  intro project
  intro hfull
  exact project hfull

theorem ay_mci_guard_intro
    (witness_key : Prop) (cnf_digest : Prop) :
    witness_key -> cnf_digest -> AyMCIGuard witness_key cnf_digest := by
  intro hwitness
  intro hdigest
  exact ay_mci_conj_intro witness_key cnf_digest hwitness hdigest

theorem ay_mci_guard_witness
    (witness_key : Prop) (cnf_digest : Prop) :
    AyMCIGuard witness_key cnf_digest -> witness_key := by
  intro guard
  exact ay_mci_conj_left witness_key cnf_digest guard

theorem ay_mci_guard_digest
    (witness_key : Prop) (cnf_digest : Prop) :
    AyMCIGuard witness_key cnf_digest -> cnf_digest := by
  intro guard
  exact ay_mci_conj_right witness_key cnf_digest guard

theorem ay_mci_cache_entry_lookup
    (stored_guard : Prop) (partition : Prop) :
    AyMCIPartitionCacheEntry stored_guard partition ->
    stored_guard ->
    partition := by
  intro entry
  intro hstored
  exact entry hstored

theorem ay_mci_match_reuse_partition
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) :
    AyMCIGuardMatch requested_guard stored_guard ->
    AyMCIPartitionCacheEntry stored_guard partition ->
    requested_guard ->
    partition := by
  intro guard_match
  intro entry
  intro hrequested
  exact entry (guard_match hrequested)

theorem ay_mci_accepted_reuse_intro
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) :
    requested_guard ->
    stored_guard ->
    partition ->
    AyMCIAcceptedReuse requested_guard stored_guard partition := by
  intro hrequested
  intro hstored
  intro hpartition
  exact ay_mci_conj_intro requested_guard
    (AyMCIConj stored_guard partition)
    hrequested
    (ay_mci_conj_intro stored_guard partition hstored hpartition)

theorem ay_mci_accepted_reuse_requested
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) :
    AyMCIAcceptedReuse requested_guard stored_guard partition ->
    requested_guard := by
  intro reuse
  exact ay_mci_conj_left requested_guard
    (AyMCIConj stored_guard partition)
    reuse

theorem ay_mci_accepted_reuse_stored
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) :
    AyMCIAcceptedReuse requested_guard stored_guard partition ->
    stored_guard := by
  intro reuse
  exact ay_mci_conj_left stored_guard partition
    (ay_mci_conj_right requested_guard
      (AyMCIConj stored_guard partition)
      reuse)

theorem ay_mci_accepted_reuse_partition
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) :
    AyMCIAcceptedReuse requested_guard stored_guard partition ->
    partition := by
  intro reuse
  exact ay_mci_conj_right stored_guard partition
    (ay_mci_conj_right requested_guard
      (AyMCIConj stored_guard partition)
      reuse)

theorem ay_mci_cached_claim_intro
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    requested_guard ->
    stored_guard ->
    original_assignment ->
    AyMCICachedPublicClaim
      requested_guard stored_guard original_assignment := by
  intro hrequested
  intro hstored
  intro horiginal
  exact ay_mci_conj_intro requested_guard
    (AyMCIConj stored_guard original_assignment)
    hrequested
    (ay_mci_conj_intro stored_guard original_assignment
      hstored horiginal)

theorem ay_mci_cached_claim_requested
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    AyMCICachedPublicClaim
      requested_guard stored_guard original_assignment ->
    requested_guard := by
  intro claim
  exact ay_mci_conj_left requested_guard
    (AyMCIConj stored_guard original_assignment)
    claim

theorem ay_mci_cached_claim_stored
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    AyMCICachedPublicClaim
      requested_guard stored_guard original_assignment ->
    stored_guard := by
  intro claim
  exact ay_mci_conj_left stored_guard original_assignment
    (ay_mci_conj_right requested_guard
      (AyMCIConj stored_guard original_assignment)
      claim)

theorem ay_mci_cached_claim_original
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    AyMCICachedPublicClaim
      requested_guard stored_guard original_assignment ->
    original_assignment := by
  intro claim
  exact ay_mci_conj_right stored_guard original_assignment
    (ay_mci_conj_right requested_guard
      (AyMCIConj stored_guard original_assignment)
      claim)

theorem ay_mci_invalidated_no_cached_claim
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    AyMCIInvalidation stored_guard ->
    AyMCINoClaim
      (AyMCICachedPublicClaim
        requested_guard stored_guard original_assignment) := by
  intro invalidated
  intro claim
  exact invalidated
    (ay_mci_cached_claim_stored
      requested_guard stored_guard original_assignment claim)

theorem ay_mci_mismatch_no_cached_claim
    (requested_guard : Prop) (stored_guard : Prop)
    (original_assignment : Prop) :
    AyMCIGuardMismatch requested_guard stored_guard ->
    AyMCINoClaim
      (AyMCICachedPublicClaim
        requested_guard stored_guard original_assignment) := by
  intro mismatch
  intro claim
  exact mismatch
    (ay_mci_cached_claim_requested
      requested_guard stored_guard original_assignment claim)
    (ay_mci_cached_claim_stored
      requested_guard stored_guard original_assignment claim)

theorem ay_mci_compressed_witness_visible
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) :
    AyMCIWitnessExpansion compressed_witness full_assignment ->
    AyMCIProjection full_assignment visible_assignment ->
    compressed_witness ->
    visible_assignment := by
  intro expand
  intro project
  intro hcompressed
  exact project (expand hcompressed)

theorem ay_mci_reconstruct_original
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyMCIPreprocessReconstruction
      visible_assignment original_assignment ->
    visible_assignment ->
    original_assignment := by
  intro reconstruct
  intro hvisible
  exact reconstruct hvisible

theorem ay_mci_matched_reuse_public_sat_sound
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) (visible_cnf : Prop)
    (original_assignment : Prop) :
    AyMCIWitnessExpansion compressed_witness full_assignment ->
    AyMCIProjection full_assignment visible_assignment ->
    AyMCIGuardMatch requested_guard stored_guard ->
    AyMCIPartitionCacheEntry stored_guard partition ->
    (partition -> visible_cnf) ->
    AyMCIPreprocessReconstruction
      visible_assignment original_assignment ->
    compressed_witness ->
    requested_guard ->
    AyMCIPublicSatAnswer original_assignment := by
  intro expand
  intro project
  intro _guard_match
  intro _entry
  intro _assemble
  intro reconstruct
  intro hcompressed
  intro _hrequested
  exact reconstruct
    (ay_mci_compressed_witness_visible
      compressed_witness full_assignment visible_assignment
      expand project hcompressed)

theorem ay_mci_matched_reuse_soundness_certificate
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) (visible_cnf : Prop)
    (original_assignment : Prop) :
    AyMCIWitnessExpansion compressed_witness full_assignment ->
    AyMCIProjection full_assignment visible_assignment ->
    AyMCIGuardMatch requested_guard stored_guard ->
    AyMCIPartitionCacheEntry stored_guard partition ->
    (partition -> visible_cnf) ->
    AyMCIPreprocessReconstruction
      visible_assignment original_assignment ->
    compressed_witness ->
    requested_guard ->
    AyMCIConj visible_cnf original_assignment := by
  intro expand
  intro project
  intro guard_match
  intro entry
  intro assemble
  intro reconstruct
  intro hcompressed
  intro hrequested
  have hvisible : visible_assignment :=
    ay_mci_compressed_witness_visible
      compressed_witness full_assignment visible_assignment
      expand project hcompressed
  exact ay_mci_conj_intro visible_cnf original_assignment
    (assemble
      (ay_mci_match_reuse_partition
        requested_guard stored_guard partition
        guard_match entry hrequested))
    (reconstruct hvisible)

theorem ay_mci_matched_reuse_cached_claim
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (partition : Prop) (visible_cnf : Prop)
    (original_assignment : Prop) :
    AyMCIWitnessExpansion compressed_witness full_assignment ->
    AyMCIProjection full_assignment visible_assignment ->
    AyMCIGuardMatch requested_guard stored_guard ->
    AyMCIPartitionCacheEntry stored_guard partition ->
    (partition -> visible_cnf) ->
    AyMCIPreprocessReconstruction
      visible_assignment original_assignment ->
    compressed_witness ->
    requested_guard ->
    AyMCICachedPublicClaim
      requested_guard stored_guard original_assignment := by
  intro expand
  intro project
  intro guard_match
  intro _entry
  intro _assemble
  intro reconstruct
  intro hcompressed
  intro hrequested
  exact ay_mci_cached_claim_intro
    requested_guard stored_guard original_assignment
    hrequested
    (guard_match hrequested)
    (reconstruct
      (ay_mci_compressed_witness_visible
        compressed_witness full_assignment visible_assignment
        expand project hcompressed))
