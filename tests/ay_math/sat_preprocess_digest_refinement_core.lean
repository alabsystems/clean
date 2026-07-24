-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Refinement of preprocessing cache digests. The propositions stand for coarse
-- CNF digests, refined schedule/artifact digests, cache entries, canonical
-- preprocessing artifacts, model pullbacks, replay certificates, and public
-- SAT/UNSAT outcome claims.

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

def AyDigestRefinement
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop) :=
  AyConj
    (AyDigestMatch coarseCached coarseCurrent)
    (AyDigestMatch refinedCached refinedCurrent)

def AyRefinedMismatch (coarseMatched : Prop) (refinedMismatch : Prop) :=
  AyConj coarseMatched refinedMismatch

def AyNoSemanticClaim (fallback : Prop) :=
  fallback

def AyCanonicalArtifact (cnf : Prop) (visibleCnf : Prop) :=
  AyEquisat cnf visibleCnf

def AyCacheEntry
    (coarseDigest : Prop) (refinedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :=
  AyConj coarseDigest
    (AyConj refinedDigest (AyCanonicalArtifact cachedCnf visibleCnf))

def AyCnfGuard (cachedCnf : Prop) (currentCnf : Prop) :=
  AyEquisat cachedCnf currentCnf

def AyAcceptedRefinedReuse
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :=
  AyConj
    (AyCacheEntry coarseCached refinedCached cachedCnf visibleCnf)
    (AyConj
      (AyDigestRefinement
        coarseCached coarseCurrent refinedCached refinedCurrent)
      (AyCnfGuard cachedCnf currentCnf))

def AyRefinementDecision
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (coarseMatched : Prop) (refinedMismatch : Prop) (fallback : Prop) :=
  AyDisj
    (AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyRefinedMismatch coarseMatched refinedMismatch)
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

theorem ay_digest_match_forward
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

theorem ay_digest_match_backward
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

theorem ay_refinement_coarse_match
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop) :
    AyDigestRefinement
      coarseCached coarseCurrent refinedCached refinedCurrent ->
    AyDigestMatch coarseCached coarseCurrent := by
  intro refinement
  exact ay_conj_left
    (AyDigestMatch coarseCached coarseCurrent)
    (AyDigestMatch refinedCached refinedCurrent)
    refinement

theorem ay_refinement_refined_match
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop) :
    AyDigestRefinement
      coarseCached coarseCurrent refinedCached refinedCurrent ->
    AyDigestMatch refinedCached refinedCurrent := by
  intro refinement
  exact ay_conj_right
    (AyDigestMatch coarseCached coarseCurrent)
    (AyDigestMatch refinedCached refinedCurrent)
    refinement

theorem ay_cache_entry_coarse
    (coarseDigest : Prop) (refinedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :
    AyCacheEntry coarseDigest refinedDigest cachedCnf visibleCnf ->
    coarseDigest := by
  intro entry
  exact ay_conj_left coarseDigest
    (AyConj refinedDigest (AyCanonicalArtifact cachedCnf visibleCnf))
    entry

theorem ay_cache_entry_refined
    (coarseDigest : Prop) (refinedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :
    AyCacheEntry coarseDigest refinedDigest cachedCnf visibleCnf ->
    refinedDigest := by
  intro entry
  exact ay_conj_left refinedDigest
    (AyCanonicalArtifact cachedCnf visibleCnf)
    (ay_conj_right coarseDigest
      (AyConj refinedDigest (AyCanonicalArtifact cachedCnf visibleCnf))
      entry)

theorem ay_cache_entry_artifact
    (coarseDigest : Prop) (refinedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :
    AyCacheEntry coarseDigest refinedDigest cachedCnf visibleCnf ->
    AyCanonicalArtifact cachedCnf visibleCnf := by
  intro entry
  exact ay_conj_right refinedDigest
    (AyCanonicalArtifact cachedCnf visibleCnf)
    (ay_conj_right coarseDigest
      (AyConj refinedDigest (AyCanonicalArtifact cachedCnf visibleCnf))
      entry)

theorem ay_reuse_entry
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    AyCacheEntry coarseCached refinedCached cachedCnf visibleCnf := by
  intro reuse
  exact ay_conj_left
    (AyCacheEntry coarseCached refinedCached cachedCnf visibleCnf)
    (AyConj
      (AyDigestRefinement
        coarseCached coarseCurrent refinedCached refinedCurrent)
      (AyCnfGuard cachedCnf currentCnf))
    reuse

theorem ay_reuse_refinement
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    AyDigestRefinement
      coarseCached coarseCurrent refinedCached refinedCurrent := by
  intro reuse
  exact ay_conj_left
    (AyDigestRefinement
      coarseCached coarseCurrent refinedCached refinedCurrent)
    (AyCnfGuard cachedCnf currentCnf)
    (ay_conj_right
      (AyCacheEntry coarseCached refinedCached cachedCnf visibleCnf)
      (AyConj
        (AyDigestRefinement
          coarseCached coarseCurrent refinedCached refinedCurrent)
        (AyCnfGuard cachedCnf currentCnf))
      reuse)

theorem ay_reuse_cnf_guard
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    AyCnfGuard cachedCnf currentCnf := by
  intro reuse
  exact ay_conj_right
    (AyDigestRefinement
      coarseCached coarseCurrent refinedCached refinedCurrent)
    (AyCnfGuard cachedCnf currentCnf)
    (ay_conj_right
      (AyCacheEntry coarseCached refinedCached cachedCnf visibleCnf)
      (AyConj
        (AyDigestRefinement
          coarseCached coarseCurrent refinedCached refinedCurrent)
        (AyCnfGuard cachedCnf currentCnf))
      reuse)

theorem ay_reuse_current_refined_digest
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    refinedCurrent := by
  intro reuse
  exact ay_digest_match_forward refinedCached refinedCurrent
    (ay_refinement_refined_match coarseCached coarseCurrent
      refinedCached refinedCurrent
      (ay_reuse_refinement
        coarseCached coarseCurrent refinedCached refinedCurrent
        cachedCnf currentCnf visibleCnf reuse))
    (ay_cache_entry_refined coarseCached refinedCached cachedCnf visibleCnf
      (ay_reuse_entry coarseCached coarseCurrent refinedCached refinedCurrent
        cachedCnf currentCnf visibleCnf reuse))

theorem ay_reuse_current_canonical
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    AyCanonicalArtifact currentCnf visibleCnf := by
  intro reuse
  exact ay_equisat_trans currentCnf cachedCnf visibleCnf
    (ay_equisat_symm cachedCnf currentCnf
      (ay_reuse_cnf_guard
        coarseCached coarseCurrent refinedCached refinedCurrent
        cachedCnf currentCnf visibleCnf reuse))
    (ay_cache_entry_artifact coarseCached refinedCached cachedCnf visibleCnf
      (ay_reuse_entry coarseCached coarseCurrent refinedCached refinedCurrent
        cachedCnf currentCnf visibleCnf reuse))

theorem ay_refined_mismatch_no_claim
    (coarseMatched : Prop) (refinedMismatch : Prop) (fallback : Prop) :
    coarseMatched ->
    refinedMismatch ->
    fallback ->
    AyConj
      (AyRefinedMismatch coarseMatched refinedMismatch)
      (AyNoSemanticClaim fallback) := by
  intro hcoarse
  intro hrefined
  intro hfallback
  exact ay_conj_intro
    (AyRefinedMismatch coarseMatched refinedMismatch)
    (AyNoSemanticClaim fallback)
    (ay_conj_intro coarseMatched refinedMismatch hcoarse hrefined)
    hfallback

theorem ay_no_claim_mismatch
    (coarseMatched : Prop) (refinedMismatch : Prop) (fallback : Prop) :
    AyConj
      (AyRefinedMismatch coarseMatched refinedMismatch)
      (AyNoSemanticClaim fallback) ->
    AyRefinedMismatch coarseMatched refinedMismatch := by
  intro no_claim
  exact ay_conj_left
    (AyRefinedMismatch coarseMatched refinedMismatch)
    (AyNoSemanticClaim fallback)
    no_claim

theorem ay_no_claim_fallback
    (coarseMatched : Prop) (refinedMismatch : Prop) (fallback : Prop) :
    AyConj
      (AyRefinedMismatch coarseMatched refinedMismatch)
      (AyNoSemanticClaim fallback) ->
    fallback := by
  intro no_claim
  exact ay_conj_right
    (AyRefinedMismatch coarseMatched refinedMismatch)
    (AyNoSemanticClaim fallback)
    no_claim

theorem ay_decision_from_refined_match
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (coarseMatched : Prop) (refinedMismatch : Prop) (fallback : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    AyRefinementDecision
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf
      coarseMatched refinedMismatch fallback := by
  intro reuse
  exact ay_disj_left
    (AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyRefinedMismatch coarseMatched refinedMismatch)
      (AyNoSemanticClaim fallback))
    reuse

theorem ay_decision_from_refined_mismatch
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (coarseMatched : Prop) (refinedMismatch : Prop) (fallback : Prop) :
    coarseMatched ->
    refinedMismatch ->
    fallback ->
    AyRefinementDecision
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf
      coarseMatched refinedMismatch fallback := by
  intro hcoarse
  intro hrefined
  intro hfallback
  exact ay_disj_right
    (AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyRefinedMismatch coarseMatched refinedMismatch)
      (AyNoSemanticClaim fallback))
    (ay_refined_mismatch_no_claim
      coarseMatched refinedMismatch fallback hcoarse hrefined hfallback)

theorem ay_refinement_decision_elim
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (coarseMatched : Prop) (refinedMismatch : Prop) (fallback : Prop)
    (result : Prop) :
    (AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf -> result) ->
    (AyConj
      (AyRefinedMismatch coarseMatched refinedMismatch)
      (AyNoSemanticClaim fallback) -> result) ->
    AyRefinementDecision
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf
      coarseMatched refinedMismatch fallback ->
    result := by
  intro reuse_case
  intro mismatch_case
  intro decision
  exact decision result reuse_case mismatch_case

theorem ay_reuse_forward_map
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    currentCnf ->
    visibleCnf := by
  intro reuse
  exact ay_equisat_forward currentCnf visibleCnf
    (ay_reuse_current_canonical
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf reuse)

theorem ay_reuse_backward_map
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    visibleCnf ->
    currentCnf := by
  intro reuse
  exact ay_equisat_backward currentCnf visibleCnf
    (ay_reuse_current_canonical
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf reuse)

theorem ay_reuse_visible_sat_pullback
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat currentCnf originalModel := by
  intro reuse
  intro pullback
  intro sat
  exact ay_conj_intro currentCnf originalModel
    (ay_reuse_backward_map
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf reuse
      (ay_sat_cnf visibleCnf visibleModel sat))
    (pullback (ay_sat_model visibleCnf visibleModel sat))

theorem ay_reuse_unsat_pushback
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    currentCnf ->
    conflict := by
  intro reuse
  intro replay
  intro hcertificate
  intro hcurrent
  exact replay
    (ay_reuse_forward_map
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf reuse hcurrent)
    hcertificate

theorem ay_reuse_unsat_pushback_artifact
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    AyUnsatPushback currentCnf visibleCnf certificate conflict := by
  intro reuse
  intro replay
  exact ay_conj_intro
    (currentCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)
    (ay_reuse_forward_map
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf reuse)
    replay

theorem ay_cache_contract_from_reuse
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
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
    (ay_reuse_current_canonical
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf reuse)
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
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  intro reuse
  intro pullback
  intro sat
  exact ay_public_outcome_sat
    currentCnf originalModel certificate conflict
    (ay_reuse_visible_sat_pullback
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf
      visibleModel originalModel reuse pullback sat)

theorem ay_reuse_unsat_public_sound
    (coarseCached : Prop) (coarseCurrent : Prop)
    (refinedCached : Prop) (refinedCurrent : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedRefinedReuse
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  intro reuse
  intro replay
  exact ay_public_outcome_unsat
    currentCnf originalModel certificate conflict
    (ay_reuse_unsat_pushback
      coarseCached coarseCurrent refinedCached refinedCurrent
      cachedCnf currentCnf visibleCnf certificate conflict reuse replay)

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
