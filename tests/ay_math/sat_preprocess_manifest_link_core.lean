-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Linking preprocessing digest refinement/cache reuse to run manifests. The
-- propositions stand for manifest artifact IDs, coarse/refined digests, cache
-- entries, canonical preprocessing artifacts, model pullbacks, replay
-- certificates, no-claim branches, and public SAT/UNSAT reports.

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

def AyIdMatch (cachedId : Prop) (manifestId : Prop) :=
  AyConj (cachedId -> manifestId) (manifestId -> cachedId)

def AyDigestMatch (cachedDigest : Prop) (manifestDigest : Prop) :=
  AyConj (cachedDigest -> manifestDigest) (manifestDigest -> cachedDigest)

def AyDigestRefinement
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop) :=
  AyConj
    (AyDigestMatch coarseCached coarseManifest)
    (AyDigestMatch refinedCached refinedManifest)

def AyCanonicalArtifact (cnf : Prop) (visibleCnf : Prop) :=
  AyEquisat cnf visibleCnf

def AyManifestCacheEntry
    (artifactId : Prop) (coarseDigest : Prop) (refinedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :=
  AyConj artifactId
    (AyConj coarseDigest
      (AyConj refinedDigest (AyCanonicalArtifact cachedCnf visibleCnf)))

def AyManifestLink
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop) :=
  AyConj
    (AyIdMatch cachedId manifestId)
    (AyDigestRefinement
      coarseCached coarseManifest refinedCached refinedManifest)

def AyCnfGuard (cachedCnf : Prop) (currentCnf : Prop) :=
  AyEquisat cachedCnf currentCnf

def AyAcceptedManifestReuse
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :=
  AyConj
    (AyManifestCacheEntry
      cachedId coarseCached refinedCached cachedCnf visibleCnf)
    (AyConj
      (AyManifestLink
        cachedId manifestId
        coarseCached coarseManifest refinedCached refinedManifest)
      (AyCnfGuard cachedCnf currentCnf))

def AyManifestMismatch (idMismatch : Prop) (refinedMismatch : Prop) :=
  AyDisj idMismatch refinedMismatch

def AyNoSemanticClaim (fallback : Prop) :=
  fallback

def AyManifestDecision
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (idMismatch : Prop) (refinedMismatch : Prop) (fallback : Prop) :=
  AyDisj
    (AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyManifestMismatch idMismatch refinedMismatch)
      (AyNoSemanticClaim fallback))

def AySatPullback (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyManifestContract
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj
    (AyCanonicalArtifact currentCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))

def AyPublicReport
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

theorem ay_id_match_forward
    (cachedId : Prop) (manifestId : Prop) :
    AyIdMatch cachedId manifestId ->
    cachedId ->
    manifestId := by
  intro hmatch
  intro hcached
  exact ay_conj_left (cachedId -> manifestId) (manifestId -> cachedId)
    hmatch hcached

theorem ay_id_match_backward
    (cachedId : Prop) (manifestId : Prop) :
    AyIdMatch cachedId manifestId ->
    manifestId ->
    cachedId := by
  intro hmatch
  intro hmanifest
  exact ay_conj_right (cachedId -> manifestId) (manifestId -> cachedId)
    hmatch hmanifest

theorem ay_digest_match_forward
    (cachedDigest : Prop) (manifestDigest : Prop) :
    AyDigestMatch cachedDigest manifestDigest ->
    cachedDigest ->
    manifestDigest := by
  intro hmatch
  intro hcached
  exact ay_conj_left
    (cachedDigest -> manifestDigest)
    (manifestDigest -> cachedDigest)
    hmatch
    hcached

theorem ay_digest_refinement_coarse
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop) :
    AyDigestRefinement
      coarseCached coarseManifest refinedCached refinedManifest ->
    AyDigestMatch coarseCached coarseManifest := by
  intro refinement
  exact ay_conj_left
    (AyDigestMatch coarseCached coarseManifest)
    (AyDigestMatch refinedCached refinedManifest)
    refinement

theorem ay_digest_refinement_refined
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop) :
    AyDigestRefinement
      coarseCached coarseManifest refinedCached refinedManifest ->
    AyDigestMatch refinedCached refinedManifest := by
  intro refinement
  exact ay_conj_right
    (AyDigestMatch coarseCached coarseManifest)
    (AyDigestMatch refinedCached refinedManifest)
    refinement

theorem ay_entry_id
    (artifactId : Prop) (coarseDigest : Prop) (refinedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :
    AyManifestCacheEntry
      artifactId coarseDigest refinedDigest cachedCnf visibleCnf ->
    artifactId := by
  intro entry
  exact ay_conj_left artifactId
    (AyConj coarseDigest
      (AyConj refinedDigest (AyCanonicalArtifact cachedCnf visibleCnf)))
    entry

theorem ay_entry_refined_digest
    (artifactId : Prop) (coarseDigest : Prop) (refinedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :
    AyManifestCacheEntry
      artifactId coarseDigest refinedDigest cachedCnf visibleCnf ->
    refinedDigest := by
  intro entry
  exact ay_conj_left refinedDigest
    (AyCanonicalArtifact cachedCnf visibleCnf)
    (ay_conj_right coarseDigest
      (AyConj refinedDigest (AyCanonicalArtifact cachedCnf visibleCnf))
      (ay_conj_right artifactId
        (AyConj coarseDigest
          (AyConj refinedDigest
            (AyCanonicalArtifact cachedCnf visibleCnf)))
        entry))

theorem ay_entry_artifact
    (artifactId : Prop) (coarseDigest : Prop) (refinedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :
    AyManifestCacheEntry
      artifactId coarseDigest refinedDigest cachedCnf visibleCnf ->
    AyCanonicalArtifact cachedCnf visibleCnf := by
  intro entry
  exact ay_conj_right refinedDigest
    (AyCanonicalArtifact cachedCnf visibleCnf)
    (ay_conj_right coarseDigest
      (AyConj refinedDigest (AyCanonicalArtifact cachedCnf visibleCnf))
      (ay_conj_right artifactId
        (AyConj coarseDigest
          (AyConj refinedDigest
            (AyCanonicalArtifact cachedCnf visibleCnf)))
        entry))

theorem ay_link_id_match
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop) :
    AyManifestLink
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest ->
    AyIdMatch cachedId manifestId := by
  intro link
  exact ay_conj_left
    (AyIdMatch cachedId manifestId)
    (AyDigestRefinement
      coarseCached coarseManifest refinedCached refinedManifest)
    link

theorem ay_link_digest_refinement
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop) :
    AyManifestLink
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest ->
    AyDigestRefinement
      coarseCached coarseManifest refinedCached refinedManifest := by
  intro link
  exact ay_conj_right
    (AyIdMatch cachedId manifestId)
    (AyDigestRefinement
      coarseCached coarseManifest refinedCached refinedManifest)
    link

theorem ay_reuse_entry
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    AyManifestCacheEntry
      cachedId coarseCached refinedCached cachedCnf visibleCnf := by
  intro reuse
  exact ay_conj_left
    (AyManifestCacheEntry
      cachedId coarseCached refinedCached cachedCnf visibleCnf)
    (AyConj
      (AyManifestLink
        cachedId manifestId
        coarseCached coarseManifest refinedCached refinedManifest)
      (AyCnfGuard cachedCnf currentCnf))
    reuse

theorem ay_reuse_link
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    AyManifestLink
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest := by
  intro reuse
  exact ay_conj_left
    (AyManifestLink
      cachedId manifestId
      coarseCached coarseManifest refinedCached refinedManifest)
    (AyCnfGuard cachedCnf currentCnf)
    (ay_conj_right
      (AyManifestCacheEntry
        cachedId coarseCached refinedCached cachedCnf visibleCnf)
      (AyConj
        (AyManifestLink
          cachedId manifestId
          coarseCached coarseManifest refinedCached refinedManifest)
        (AyCnfGuard cachedCnf currentCnf))
      reuse)

theorem ay_reuse_guard
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    AyCnfGuard cachedCnf currentCnf := by
  intro reuse
  exact ay_conj_right
    (AyManifestLink
      cachedId manifestId
      coarseCached coarseManifest refinedCached refinedManifest)
    (AyCnfGuard cachedCnf currentCnf)
    (ay_conj_right
      (AyManifestCacheEntry
        cachedId coarseCached refinedCached cachedCnf visibleCnf)
      (AyConj
        (AyManifestLink
          cachedId manifestId
          coarseCached coarseManifest refinedCached refinedManifest)
        (AyCnfGuard cachedCnf currentCnf))
      reuse)

theorem ay_reuse_manifest_id
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    manifestId := by
  intro reuse
  exact ay_id_match_forward cachedId manifestId
    (ay_link_id_match cachedId manifestId
      coarseCached coarseManifest refinedCached refinedManifest
      (ay_reuse_link cachedId manifestId coarseCached coarseManifest
        refinedCached refinedManifest cachedCnf currentCnf visibleCnf reuse))
    (ay_entry_id cachedId coarseCached refinedCached cachedCnf visibleCnf
      (ay_reuse_entry cachedId manifestId coarseCached coarseManifest
        refinedCached refinedManifest cachedCnf currentCnf visibleCnf reuse))

theorem ay_reuse_refined_manifest_digest
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    refinedManifest := by
  intro reuse
  exact ay_digest_match_forward refinedCached refinedManifest
    (ay_digest_refinement_refined coarseCached coarseManifest
      refinedCached refinedManifest
      (ay_link_digest_refinement cachedId manifestId
        coarseCached coarseManifest refinedCached refinedManifest
        (ay_reuse_link cachedId manifestId coarseCached coarseManifest
          refinedCached refinedManifest cachedCnf currentCnf visibleCnf reuse)))
    (ay_entry_refined_digest cachedId coarseCached refinedCached
      cachedCnf visibleCnf
      (ay_reuse_entry cachedId manifestId coarseCached coarseManifest
        refinedCached refinedManifest cachedCnf currentCnf visibleCnf reuse))

theorem ay_reuse_current_canonical
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    AyCanonicalArtifact currentCnf visibleCnf := by
  intro reuse
  exact ay_equisat_trans currentCnf cachedCnf visibleCnf
    (ay_equisat_symm cachedCnf currentCnf
      (ay_reuse_guard cachedId manifestId coarseCached coarseManifest
        refinedCached refinedManifest cachedCnf currentCnf visibleCnf reuse))
    (ay_entry_artifact cachedId coarseCached refinedCached cachedCnf visibleCnf
      (ay_reuse_entry cachedId manifestId coarseCached coarseManifest
        refinedCached refinedManifest cachedCnf currentCnf visibleCnf reuse))

theorem ay_manifest_mismatch_id
    (idMismatch : Prop) (refinedMismatch : Prop) :
    idMismatch ->
    AyManifestMismatch idMismatch refinedMismatch := by
  exact ay_disj_left idMismatch refinedMismatch

theorem ay_manifest_mismatch_refined
    (idMismatch : Prop) (refinedMismatch : Prop) :
    refinedMismatch ->
    AyManifestMismatch idMismatch refinedMismatch := by
  exact ay_disj_right idMismatch refinedMismatch

theorem ay_manifest_no_claim
    (idMismatch : Prop) (refinedMismatch : Prop) (fallback : Prop) :
    AyManifestMismatch idMismatch refinedMismatch ->
    fallback ->
    AyConj
      (AyManifestMismatch idMismatch refinedMismatch)
      (AyNoSemanticClaim fallback) := by
  intro mismatch
  intro hfallback
  exact ay_conj_intro
    (AyManifestMismatch idMismatch refinedMismatch)
    (AyNoSemanticClaim fallback)
    mismatch
    hfallback

theorem ay_no_claim_mismatch
    (idMismatch : Prop) (refinedMismatch : Prop) (fallback : Prop) :
    AyConj
      (AyManifestMismatch idMismatch refinedMismatch)
      (AyNoSemanticClaim fallback) ->
    AyManifestMismatch idMismatch refinedMismatch := by
  intro no_claim
  exact ay_conj_left
    (AyManifestMismatch idMismatch refinedMismatch)
    (AyNoSemanticClaim fallback)
    no_claim

theorem ay_no_claim_fallback
    (idMismatch : Prop) (refinedMismatch : Prop) (fallback : Prop) :
    AyConj
      (AyManifestMismatch idMismatch refinedMismatch)
      (AyNoSemanticClaim fallback) ->
    fallback := by
  intro no_claim
  exact ay_conj_right
    (AyManifestMismatch idMismatch refinedMismatch)
    (AyNoSemanticClaim fallback)
    no_claim

theorem ay_decision_from_reuse
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (idMismatch : Prop) (refinedMismatch : Prop) (fallback : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    AyManifestDecision
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf
      idMismatch refinedMismatch fallback := by
  intro reuse
  exact ay_disj_left
    (AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyManifestMismatch idMismatch refinedMismatch)
      (AyNoSemanticClaim fallback))
    reuse

theorem ay_decision_from_id_mismatch
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (idMismatch : Prop) (refinedMismatch : Prop) (fallback : Prop) :
    idMismatch ->
    fallback ->
    AyManifestDecision
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf
      idMismatch refinedMismatch fallback := by
  intro hid
  intro hfallback
  exact ay_disj_right
    (AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyManifestMismatch idMismatch refinedMismatch)
      (AyNoSemanticClaim fallback))
    (ay_manifest_no_claim idMismatch refinedMismatch fallback
      (ay_manifest_mismatch_id idMismatch refinedMismatch hid)
      hfallback)

theorem ay_decision_from_refined_mismatch
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (idMismatch : Prop) (refinedMismatch : Prop) (fallback : Prop) :
    refinedMismatch ->
    fallback ->
    AyManifestDecision
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf
      idMismatch refinedMismatch fallback := by
  intro hrefined
  intro hfallback
  exact ay_disj_right
    (AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyManifestMismatch idMismatch refinedMismatch)
      (AyNoSemanticClaim fallback))
    (ay_manifest_no_claim idMismatch refinedMismatch fallback
      (ay_manifest_mismatch_refined idMismatch refinedMismatch hrefined)
      hfallback)

theorem ay_reuse_forward_map
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    currentCnf ->
    visibleCnf := by
  intro reuse
  exact ay_equisat_forward currentCnf visibleCnf
    (ay_reuse_current_canonical cachedId manifestId
      coarseCached coarseManifest refinedCached refinedManifest
      cachedCnf currentCnf visibleCnf reuse)

theorem ay_reuse_backward_map
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    visibleCnf ->
    currentCnf := by
  intro reuse
  exact ay_equisat_backward currentCnf visibleCnf
    (ay_reuse_current_canonical cachedId manifestId
      coarseCached coarseManifest refinedCached refinedManifest
      cachedCnf currentCnf visibleCnf reuse)

theorem ay_reuse_visible_sat_pullback
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat currentCnf originalModel := by
  intro reuse
  intro pullback
  intro sat
  exact ay_conj_intro currentCnf originalModel
    (ay_reuse_backward_map cachedId manifestId
      coarseCached coarseManifest refinedCached refinedManifest
      cachedCnf currentCnf visibleCnf reuse
      (ay_sat_cnf visibleCnf visibleModel sat))
    (pullback (ay_sat_model visibleCnf visibleModel sat))

theorem ay_reuse_unsat_pushback
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    currentCnf ->
    conflict := by
  intro reuse
  intro replay
  intro hcertificate
  intro hcurrent
  exact replay
    (ay_reuse_forward_map cachedId manifestId
      coarseCached coarseManifest refinedCached refinedManifest
      cachedCnf currentCnf visibleCnf reuse hcurrent)
    hcertificate

theorem ay_manifest_contract_from_reuse
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AyReplay visibleCnf certificate conflict ->
    AyManifestContract
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
    (ay_reuse_current_canonical cachedId manifestId
      coarseCached coarseManifest refinedCached refinedManifest
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
    AyManifestContract
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
    AyManifestContract
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
    AyManifestContract
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

theorem ay_contract_sat_report
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyManifestContract
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

theorem ay_contract_unsat_report
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyManifestContract
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

theorem ay_public_report_sat
    (currentCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AySat currentCnf originalModel ->
    AyPublicReport currentCnf originalModel certificate conflict := by
  exact ay_disj_left
    (AySat currentCnf originalModel)
    (certificate -> currentCnf -> conflict)

theorem ay_public_report_unsat
    (currentCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    (certificate -> currentCnf -> conflict) ->
    AyPublicReport currentCnf originalModel certificate conflict := by
  exact ay_disj_right
    (AySat currentCnf originalModel)
    (certificate -> currentCnf -> conflict)

theorem ay_manifest_reuse_sat_public_sound
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AyPublicReport currentCnf originalModel certificate conflict := by
  intro reuse
  intro pullback
  intro sat
  exact ay_public_report_sat
    currentCnf originalModel certificate conflict
    (ay_reuse_visible_sat_pullback cachedId manifestId
      coarseCached coarseManifest refinedCached refinedManifest
      cachedCnf currentCnf visibleCnf visibleModel originalModel
      reuse pullback sat)

theorem ay_manifest_reuse_unsat_public_sound
    (cachedId : Prop) (manifestId : Prop)
    (coarseCached : Prop) (coarseManifest : Prop)
    (refinedCached : Prop) (refinedManifest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedManifestReuse
      cachedId manifestId coarseCached coarseManifest
      refinedCached refinedManifest cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    AyPublicReport currentCnf originalModel certificate conflict := by
  intro reuse
  intro replay
  exact ay_public_report_unsat
    currentCnf originalModel certificate conflict
    (ay_reuse_unsat_pushback cachedId manifestId
      coarseCached coarseManifest refinedCached refinedManifest
      cachedCnf currentCnf visibleCnf certificate conflict reuse replay)

theorem ay_contract_sat_public_sound
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyManifestContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySat visibleCnf visibleModel ->
    AyPublicReport currentCnf originalModel certificate conflict := by
  intro contract
  intro sat
  exact ay_public_report_sat
    currentCnf originalModel certificate conflict
    (ay_contract_sat_report currentCnf visibleCnf
      visibleModel originalModel certificate conflict contract sat)

theorem ay_contract_unsat_public_sound
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyManifestContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyPublicReport currentCnf originalModel certificate conflict := by
  intro contract
  exact ay_public_report_unsat
    currentCnf originalModel certificate conflict
    (ay_contract_unsat_report currentCnf visibleCnf
      visibleModel originalModel certificate conflict contract)
