-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Cache invalidation for accepted preprocessing schedules. The propositions
-- stand for CNF digest keys, cache entries, validation guards, fallback
-- decisions, model pullback payloads, replay certificates, and public output.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AySat (cnf : Prop) (model : Prop) :=
  AyConj cnf model

def AyReplay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def AyDigestMatch (cachedDigest : Prop) (currentDigest : Prop) :=
  AyConj (cachedDigest -> currentDigest) (currentDigest -> cachedDigest)

def AyCnfGuard (cachedCnf : Prop) (currentCnf : Prop) :=
  AyEquisat cachedCnf currentCnf

def AyCanonicalArtifact (cnf : Prop) (visibleCnf : Prop) :=
  AyEquisat cnf visibleCnf

def AyCacheEntry
    (cachedDigest : Prop) (cachedCnf : Prop) (visibleCnf : Prop) :=
  AyConj cachedDigest (AyCanonicalArtifact cachedCnf visibleCnf)

def AyAcceptedReuse
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :=
  AyConj
    (AyCacheEntry cachedDigest cachedCnf visibleCnf)
    (AyConj
      (AyDigestMatch cachedDigest currentDigest)
      (AyCnfGuard cachedCnf currentCnf))

def AyInvalidationReason (invalidated : Prop) (guardMismatch : Prop) :=
  AyDisj invalidated guardMismatch

def AyNoSemanticClaim (fallback : Prop) :=
  fallback

def AyCacheDecision
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (invalidated : Prop) (guardMismatch : Prop) (fallback : Prop) :=
  AyDisj
    (AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyInvalidationReason invalidated guardMismatch)
      (AyNoSemanticClaim fallback))

def AySatPullback (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyUnsatPushback
    (currentCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj (currentCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)

def AyCacheContract
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj
    (AyCanonicalArtifact currentCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))

def AyPublicOutcome
    (currentCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyDisj
    (AySat currentCnf originalModel)
    (certificate -> currentCnf -> conflict)

theorem ay_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyEquisat before after := by
  intro forward
  intro backward
  exact ay_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_conj_left (before -> after) (after -> before) eq

theorem ay_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_conj_right (before -> after) (after -> before) eq

theorem ay_equisat_trans
    (first : Prop) (middle : Prop) (last : Prop) :
    AyEquisat first middle ->
    AyEquisat middle last ->
    AyEquisat first last := by
  intro first_middle
  intro middle_last
  exact ay_equisat_intro first last
    (fun hfirst =>
      ay_equisat_forward middle last middle_last
        (ay_equisat_forward first middle first_middle hfirst))
    (fun hlast =>
      ay_equisat_backward first middle first_middle
        (ay_equisat_backward middle last middle_last hlast))

theorem ay_equisat_symm
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    AyEquisat after before := by
  intro eq
  exact ay_equisat_intro after before
    (ay_equisat_backward before after eq)
    (ay_equisat_forward before after eq)

theorem ay_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_conj_left cnf model sat

theorem ay_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_conj_right cnf model sat

theorem ay_digest_cached_to_current
    (cachedDigest : Prop) (currentDigest : Prop) :
    AyDigestMatch cachedDigest currentDigest ->
    cachedDigest ->
    currentDigest := by
  intro hmatch
  intro hcached
  exact ay_conj_left
    (cachedDigest -> currentDigest)
    (currentDigest -> cachedDigest)
    hmatch
    hcached

theorem ay_digest_current_to_cached
    (cachedDigest : Prop) (currentDigest : Prop) :
    AyDigestMatch cachedDigest currentDigest ->
    currentDigest ->
    cachedDigest := by
  intro hmatch
  intro hcurrent
  exact ay_conj_right
    (cachedDigest -> currentDigest)
    (currentDigest -> cachedDigest)
    hmatch
    hcurrent

theorem ay_cache_entry_digest
    (cachedDigest : Prop) (cachedCnf : Prop) (visibleCnf : Prop) :
    AyCacheEntry cachedDigest cachedCnf visibleCnf ->
    cachedDigest := by
  intro entry
  exact ay_conj_left cachedDigest
    (AyCanonicalArtifact cachedCnf visibleCnf)
    entry

theorem ay_cache_entry_artifact
    (cachedDigest : Prop) (cachedCnf : Prop) (visibleCnf : Prop) :
    AyCacheEntry cachedDigest cachedCnf visibleCnf ->
    AyCanonicalArtifact cachedCnf visibleCnf := by
  intro entry
  exact ay_conj_right cachedDigest
    (AyCanonicalArtifact cachedCnf visibleCnf)
    entry

theorem ay_reuse_entry
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AyCacheEntry cachedDigest cachedCnf visibleCnf := by
  intro reuse
  exact ay_conj_left
    (AyCacheEntry cachedDigest cachedCnf visibleCnf)
    (AyConj
      (AyDigestMatch cachedDigest currentDigest)
      (AyCnfGuard cachedCnf currentCnf))
    reuse

theorem ay_reuse_digest_match
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AyDigestMatch cachedDigest currentDigest := by
  intro reuse
  exact ay_conj_left
    (AyDigestMatch cachedDigest currentDigest)
    (AyCnfGuard cachedCnf currentCnf)
    (ay_conj_right
      (AyCacheEntry cachedDigest cachedCnf visibleCnf)
      (AyConj
        (AyDigestMatch cachedDigest currentDigest)
        (AyCnfGuard cachedCnf currentCnf))
      reuse)

theorem ay_reuse_cnf_guard
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AyCnfGuard cachedCnf currentCnf := by
  intro reuse
  exact ay_conj_right
    (AyDigestMatch cachedDigest currentDigest)
    (AyCnfGuard cachedCnf currentCnf)
    (ay_conj_right
      (AyCacheEntry cachedDigest cachedCnf visibleCnf)
      (AyConj
        (AyDigestMatch cachedDigest currentDigest)
        (AyCnfGuard cachedCnf currentCnf))
      reuse)

theorem ay_reuse_current_digest
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    currentDigest := by
  intro reuse
  exact ay_digest_cached_to_current cachedDigest currentDigest
    (ay_reuse_digest_match cachedDigest currentDigest cachedCnf currentCnf
      visibleCnf reuse)
    (ay_cache_entry_digest cachedDigest cachedCnf visibleCnf
      (ay_reuse_entry cachedDigest currentDigest cachedCnf currentCnf
        visibleCnf reuse))

theorem ay_reuse_cached_artifact
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AyCanonicalArtifact cachedCnf visibleCnf := by
  intro reuse
  exact ay_cache_entry_artifact cachedDigest cachedCnf visibleCnf
    (ay_reuse_entry cachedDigest currentDigest cachedCnf currentCnf
      visibleCnf reuse)

theorem ay_reuse_current_canonical
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AyCanonicalArtifact currentCnf visibleCnf := by
  intro reuse
  exact ay_equisat_trans currentCnf cachedCnf visibleCnf
    (ay_equisat_symm cachedCnf currentCnf
      (ay_reuse_cnf_guard cachedDigest currentDigest cachedCnf currentCnf
        visibleCnf reuse))
    (ay_reuse_cached_artifact cachedDigest currentDigest cachedCnf currentCnf
      visibleCnf reuse)

theorem ay_invalidation_left
    (invalidated : Prop) (guardMismatch : Prop) :
    invalidated ->
    AyInvalidationReason invalidated guardMismatch := by
  exact ay_disj_left invalidated guardMismatch

theorem ay_invalidation_right
    (invalidated : Prop) (guardMismatch : Prop) :
    guardMismatch ->
    AyInvalidationReason invalidated guardMismatch := by
  exact ay_disj_right invalidated guardMismatch

theorem ay_invalidated_no_semantic_claim
    (invalidated : Prop) (guardMismatch : Prop) (fallback : Prop) :
    invalidated ->
    fallback ->
    AyConj
      (AyInvalidationReason invalidated guardMismatch)
      (AyNoSemanticClaim fallback) := by
  intro hinvalidated
  intro hfallback
  exact ay_conj_intro
    (AyInvalidationReason invalidated guardMismatch)
    (AyNoSemanticClaim fallback)
    (ay_invalidation_left invalidated guardMismatch hinvalidated)
    hfallback

theorem ay_guard_mismatch_no_semantic_claim
    (invalidated : Prop) (guardMismatch : Prop) (fallback : Prop) :
    guardMismatch ->
    fallback ->
    AyConj
      (AyInvalidationReason invalidated guardMismatch)
      (AyNoSemanticClaim fallback) := by
  intro hmismatch
  intro hfallback
  exact ay_conj_intro
    (AyInvalidationReason invalidated guardMismatch)
    (AyNoSemanticClaim fallback)
    (ay_invalidation_right invalidated guardMismatch hmismatch)
    hfallback

theorem ay_no_claim_reason
    (invalidated : Prop) (guardMismatch : Prop) (fallback : Prop) :
    AyConj
      (AyInvalidationReason invalidated guardMismatch)
      (AyNoSemanticClaim fallback) ->
    AyInvalidationReason invalidated guardMismatch := by
  intro no_claim
  exact ay_conj_left
    (AyInvalidationReason invalidated guardMismatch)
    (AyNoSemanticClaim fallback)
    no_claim

theorem ay_no_claim_fallback
    (invalidated : Prop) (guardMismatch : Prop) (fallback : Prop) :
    AyConj
      (AyInvalidationReason invalidated guardMismatch)
      (AyNoSemanticClaim fallback) ->
    fallback := by
  intro no_claim
  exact ay_conj_right
    (AyInvalidationReason invalidated guardMismatch)
    (AyNoSemanticClaim fallback)
    no_claim

theorem ay_decision_from_invalidated
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (invalidated : Prop) (guardMismatch : Prop) (fallback : Prop) :
    invalidated ->
    fallback ->
    AyCacheDecision
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf
      invalidated guardMismatch fallback := by
  intro hinvalidated
  intro hfallback
  exact ay_disj_right
    (AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyInvalidationReason invalidated guardMismatch)
      (AyNoSemanticClaim fallback))
    (ay_invalidated_no_semantic_claim
      invalidated guardMismatch fallback hinvalidated hfallback)

theorem ay_decision_from_guard_mismatch
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (invalidated : Prop) (guardMismatch : Prop) (fallback : Prop) :
    guardMismatch ->
    fallback ->
    AyCacheDecision
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf
      invalidated guardMismatch fallback := by
  intro hmismatch
  intro hfallback
  exact ay_disj_right
    (AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyInvalidationReason invalidated guardMismatch)
      (AyNoSemanticClaim fallback))
    (ay_guard_mismatch_no_semantic_claim
      invalidated guardMismatch fallback hmismatch hfallback)

theorem ay_decision_from_reuse
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (invalidated : Prop) (guardMismatch : Prop) (fallback : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AyCacheDecision
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf
      invalidated guardMismatch fallback := by
  intro reuse
  exact ay_disj_left
    (AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyInvalidationReason invalidated guardMismatch)
      (AyNoSemanticClaim fallback))
    reuse

theorem ay_decision_elim
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (invalidated : Prop) (guardMismatch : Prop) (fallback : Prop)
    (result : Prop) :
    (AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
      result) ->
    (AyConj
      (AyInvalidationReason invalidated guardMismatch)
      (AyNoSemanticClaim fallback) ->
      result) ->
    AyCacheDecision
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf
      invalidated guardMismatch fallback ->
    result := by
  intro reuse_case
  intro fallback_case
  intro decision
  exact decision result reuse_case fallback_case

theorem ay_reuse_forward_map
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    currentCnf ->
    visibleCnf := by
  intro reuse
  exact ay_equisat_forward currentCnf visibleCnf
    (ay_reuse_current_canonical cachedDigest currentDigest cachedCnf
      currentCnf visibleCnf reuse)

theorem ay_reuse_backward_map
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    visibleCnf ->
    currentCnf := by
  intro reuse
  exact ay_equisat_backward currentCnf visibleCnf
    (ay_reuse_current_canonical cachedDigest currentDigest cachedCnf
      currentCnf visibleCnf reuse)

theorem ay_reuse_visible_sat_pullback
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat currentCnf originalModel := by
  intro reuse
  intro pullback
  intro sat
  exact ay_conj_intro currentCnf originalModel
    (ay_reuse_backward_map cachedDigest currentDigest cachedCnf currentCnf
      visibleCnf reuse
      (ay_sat_cnf visibleCnf visibleModel sat))
    (pullback (ay_sat_model visibleCnf visibleModel sat))

theorem ay_reuse_unsat_pushback
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    currentCnf ->
    conflict := by
  intro reuse
  intro replay
  intro hcertificate
  intro hcurrent
  exact replay
    (ay_reuse_forward_map cachedDigest currentDigest cachedCnf currentCnf
      visibleCnf reuse hcurrent)
    hcertificate

theorem ay_reuse_unsat_pushback_artifact
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    AyUnsatPushback currentCnf visibleCnf certificate conflict := by
  intro reuse
  intro replay
  exact ay_conj_intro
    (currentCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)
    (ay_reuse_forward_map cachedDigest currentDigest cachedCnf currentCnf
      visibleCnf reuse)
    replay

theorem ay_cache_contract_from_reuse
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AyReplay visibleCnf certificate conflict ->
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict := by
  intro reuse
  intro pullback
  intro replay
  exact ay_conj_intro
    (AyCanonicalArtifact currentCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))
    (ay_reuse_current_canonical cachedDigest currentDigest cachedCnf
      currentCnf visibleCnf reuse)
    (ay_conj_intro
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict)
      pullback
      replay)

theorem ay_contract_canonical
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyCanonicalArtifact currentCnf visibleCnf := by
  intro contract
  exact ay_conj_left
    (AyCanonicalArtifact currentCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))
    contract

theorem ay_contract_pullback
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySatPullback visibleModel originalModel := by
  intro contract
  exact ay_conj_left
    (AySatPullback visibleModel originalModel)
    (AyReplay visibleCnf certificate conflict)
    (ay_conj_right
      (AyCanonicalArtifact currentCnf visibleCnf)
      (AyConj
        (AySatPullback visibleModel originalModel)
        (AyReplay visibleCnf certificate conflict))
      contract)

theorem ay_contract_replay
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyReplay visibleCnf certificate conflict := by
  intro contract
  exact ay_conj_right
    (AySatPullback visibleModel originalModel)
    (AyReplay visibleCnf certificate conflict)
    (ay_conj_right
      (AyCanonicalArtifact currentCnf visibleCnf)
      (AyConj
        (AySatPullback visibleModel originalModel)
        (AyReplay visibleCnf certificate conflict))
      contract)

theorem ay_contract_sat_obligation
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySat visibleCnf visibleModel ->
    AySat currentCnf originalModel := by
  intro contract
  intro sat
  exact ay_conj_intro currentCnf originalModel
    (ay_equisat_backward currentCnf visibleCnf
      (ay_contract_canonical
        currentCnf visibleCnf visibleModel originalModel
        certificate conflict contract)
      (ay_sat_cnf visibleCnf visibleModel sat))
    (ay_contract_pullback
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict contract
      (ay_sat_model visibleCnf visibleModel sat))

theorem ay_contract_unsat_obligation
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    certificate ->
    currentCnf ->
    conflict := by
  intro contract
  intro hcertificate
  intro hcurrent
  exact ay_contract_replay
    currentCnf visibleCnf visibleModel originalModel
    certificate conflict contract
    (ay_equisat_forward currentCnf visibleCnf
      (ay_contract_canonical
        currentCnf visibleCnf visibleModel originalModel
        certificate conflict contract)
      hcurrent)
    hcertificate

theorem ay_public_outcome_sat
    (currentCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AySat currentCnf originalModel ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  exact ay_disj_left
    (AySat currentCnf originalModel)
    (certificate -> currentCnf -> conflict)

theorem ay_public_outcome_unsat
    (currentCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    (certificate -> currentCnf -> conflict) ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  exact ay_disj_right
    (AySat currentCnf originalModel)
    (certificate -> currentCnf -> conflict)

theorem ay_reuse_sat_public_sound
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  intro reuse
  intro pullback
  intro sat
  exact ay_public_outcome_sat
    currentCnf originalModel certificate conflict
    (ay_reuse_visible_sat_pullback
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf
      visibleModel originalModel reuse pullback sat)

theorem ay_reuse_unsat_public_sound
    (cachedDigest : Prop) (currentDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReuse
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  intro reuse
  intro replay
  exact ay_public_outcome_unsat
    currentCnf originalModel certificate conflict
    (ay_reuse_unsat_pushback
      cachedDigest currentDigest cachedCnf currentCnf visibleCnf
      certificate conflict reuse replay)

theorem ay_contract_sat_public_sound
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySat visibleCnf visibleModel ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  intro contract
  intro sat
  exact ay_public_outcome_sat
    currentCnf originalModel certificate conflict
    (ay_contract_sat_obligation
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict contract sat)

theorem ay_contract_unsat_public_sound
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  intro contract
  exact ay_public_outcome_unsat
    currentCnf originalModel certificate conflict
    (ay_contract_unsat_obligation
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict contract)
