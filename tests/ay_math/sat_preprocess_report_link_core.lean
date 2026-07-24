-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Linking preprocessing manifest/cache artifacts to validator reports. The
-- propositions stand for report artifact IDs, manifest artifact IDs, refined
-- digests, cache entries, SAT/UNSAT reports, no-claim branches, and exit codes.

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

def AyIdMatch (leftId : Prop) (rightId : Prop) :=
  AyConj (leftId -> rightId) (rightId -> leftId)

def AyDigestMatch (cachedDigest : Prop) (reportDigest : Prop) :=
  AyConj (cachedDigest -> reportDigest) (reportDigest -> cachedDigest)

def AyReportManifestLink
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop) :=
  AyConj
    (AyIdMatch reportId manifestId)
    (AyConj
      (AyIdMatch cachedId manifestId)
      (AyDigestMatch cachedDigest reportDigest))

def AyCanonicalArtifact (cnf : Prop) (visibleCnf : Prop) :=
  AyEquisat cnf visibleCnf

def AyReportCacheEntry
    (cachedId : Prop) (cachedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :=
  AyConj cachedId
    (AyConj cachedDigest (AyCanonicalArtifact cachedCnf visibleCnf))

def AyCnfGuard (cachedCnf : Prop) (currentCnf : Prop) :=
  AyEquisat cachedCnf currentCnf

def AyAcceptedReportReuse
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :=
  AyConj
    (AyReportCacheEntry cachedId cachedDigest cachedCnf visibleCnf)
    (AyConj
      (AyReportManifestLink
        reportId manifestId cachedId cachedDigest reportDigest)
      (AyCnfGuard cachedCnf currentCnf))

def AyReportMismatch (idMismatch : Prop) (digestMismatch : Prop) :=
  AyDisj idMismatch digestMismatch

def AyNoSemanticClaim (fallback : Prop) :=
  fallback

def AyReportDecision
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (idMismatch : Prop) (digestMismatch : Prop) (fallback : Prop) :=
  AyDisj
    (AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyReportMismatch idMismatch digestMismatch)
      (AyNoSemanticClaim fallback))

def AySatPullback (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyReportContract
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj
    (AyCanonicalArtifact currentCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))

def AyExitCodeSound (exitCode : Prop) (claim : Prop) :=
  AyConj exitCode claim

def AyPublicReport
    (currentCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  AyDisj
    (AyExitCodeSound exitCode (AySat currentCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> currentCnf -> conflict))

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
    (leftId : Prop) (rightId : Prop) :
    AyIdMatch leftId rightId ->
    leftId ->
    rightId := by
  intro hmatch
  intro hleft
  exact ay_conj_left (leftId -> rightId) (rightId -> leftId)
    hmatch hleft

theorem ay_digest_match_forward
    (cachedDigest : Prop) (reportDigest : Prop) :
    AyDigestMatch cachedDigest reportDigest ->
    cachedDigest ->
    reportDigest := by
  intro hmatch
  intro hcached
  exact ay_conj_left
    (cachedDigest -> reportDigest)
    (reportDigest -> cachedDigest)
    hmatch
    hcached

theorem ay_entry_id
    (cachedId : Prop) (cachedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :
    AyReportCacheEntry cachedId cachedDigest cachedCnf visibleCnf ->
    cachedId := by
  intro entry
  exact ay_conj_left cachedId
    (AyConj cachedDigest (AyCanonicalArtifact cachedCnf visibleCnf))
    entry

theorem ay_entry_digest
    (cachedId : Prop) (cachedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :
    AyReportCacheEntry cachedId cachedDigest cachedCnf visibleCnf ->
    cachedDigest := by
  intro entry
  exact ay_conj_left cachedDigest
    (AyCanonicalArtifact cachedCnf visibleCnf)
    (ay_conj_right cachedId
      (AyConj cachedDigest (AyCanonicalArtifact cachedCnf visibleCnf))
      entry)

theorem ay_entry_artifact
    (cachedId : Prop) (cachedDigest : Prop)
    (cachedCnf : Prop) (visibleCnf : Prop) :
    AyReportCacheEntry cachedId cachedDigest cachedCnf visibleCnf ->
    AyCanonicalArtifact cachedCnf visibleCnf := by
  intro entry
  exact ay_conj_right cachedDigest
    (AyCanonicalArtifact cachedCnf visibleCnf)
    (ay_conj_right cachedId
      (AyConj cachedDigest (AyCanonicalArtifact cachedCnf visibleCnf))
      entry)

theorem ay_link_report_manifest_id
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop) :
    AyReportManifestLink
      reportId manifestId cachedId cachedDigest reportDigest ->
    AyIdMatch reportId manifestId := by
  intro link
  exact ay_conj_left
    (AyIdMatch reportId manifestId)
    (AyConj
      (AyIdMatch cachedId manifestId)
      (AyDigestMatch cachedDigest reportDigest))
    link

theorem ay_link_cached_manifest_id
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop) :
    AyReportManifestLink
      reportId manifestId cachedId cachedDigest reportDigest ->
    AyIdMatch cachedId manifestId := by
  intro link
  exact ay_conj_left
    (AyIdMatch cachedId manifestId)
    (AyDigestMatch cachedDigest reportDigest)
    (ay_conj_right
      (AyIdMatch reportId manifestId)
      (AyConj
        (AyIdMatch cachedId manifestId)
        (AyDigestMatch cachedDigest reportDigest))
      link)

theorem ay_link_refined_digest
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop) :
    AyReportManifestLink
      reportId manifestId cachedId cachedDigest reportDigest ->
    AyDigestMatch cachedDigest reportDigest := by
  intro link
  exact ay_conj_right
    (AyIdMatch cachedId manifestId)
    (AyDigestMatch cachedDigest reportDigest)
    (ay_conj_right
      (AyIdMatch reportId manifestId)
      (AyConj
        (AyIdMatch cachedId manifestId)
        (AyDigestMatch cachedDigest reportDigest))
      link)

theorem ay_reuse_entry
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    AyReportCacheEntry cachedId cachedDigest cachedCnf visibleCnf := by
  intro reuse
  exact ay_conj_left
    (AyReportCacheEntry cachedId cachedDigest cachedCnf visibleCnf)
    (AyConj
      (AyReportManifestLink
        reportId manifestId cachedId cachedDigest reportDigest)
      (AyCnfGuard cachedCnf currentCnf))
    reuse

theorem ay_reuse_link
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    AyReportManifestLink
      reportId manifestId cachedId cachedDigest reportDigest := by
  intro reuse
  exact ay_conj_left
    (AyReportManifestLink
      reportId manifestId cachedId cachedDigest reportDigest)
    (AyCnfGuard cachedCnf currentCnf)
    (ay_conj_right
      (AyReportCacheEntry cachedId cachedDigest cachedCnf visibleCnf)
      (AyConj
        (AyReportManifestLink
          reportId manifestId cachedId cachedDigest reportDigest)
        (AyCnfGuard cachedCnf currentCnf))
      reuse)

theorem ay_reuse_guard
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    AyCnfGuard cachedCnf currentCnf := by
  intro reuse
  exact ay_conj_right
    (AyReportManifestLink
      reportId manifestId cachedId cachedDigest reportDigest)
    (AyCnfGuard cachedCnf currentCnf)
    (ay_conj_right
      (AyReportCacheEntry cachedId cachedDigest cachedCnf visibleCnf)
      (AyConj
        (AyReportManifestLink
          reportId manifestId cachedId cachedDigest reportDigest)
        (AyCnfGuard cachedCnf currentCnf))
      reuse)

theorem ay_reuse_manifest_id
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    manifestId := by
  intro reuse
  exact ay_id_match_forward cachedId manifestId
    (ay_link_cached_manifest_id reportId manifestId cachedId
      cachedDigest reportDigest
      (ay_reuse_link reportId manifestId cachedId cachedDigest
        reportDigest cachedCnf currentCnf visibleCnf reuse))
    (ay_entry_id cachedId cachedDigest cachedCnf visibleCnf
      (ay_reuse_entry reportId manifestId cachedId cachedDigest
        reportDigest cachedCnf currentCnf visibleCnf reuse))

theorem ay_reuse_report_id
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    reportId ->
    manifestId := by
  intro reuse
  exact ay_id_match_forward reportId manifestId
    (ay_link_report_manifest_id reportId manifestId cachedId
      cachedDigest reportDigest
      (ay_reuse_link reportId manifestId cachedId cachedDigest
        reportDigest cachedCnf currentCnf visibleCnf reuse))

theorem ay_reuse_report_digest
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    reportDigest := by
  intro reuse
  exact ay_digest_match_forward cachedDigest reportDigest
    (ay_link_refined_digest reportId manifestId cachedId
      cachedDigest reportDigest
      (ay_reuse_link reportId manifestId cachedId cachedDigest
        reportDigest cachedCnf currentCnf visibleCnf reuse))
    (ay_entry_digest cachedId cachedDigest cachedCnf visibleCnf
      (ay_reuse_entry reportId manifestId cachedId cachedDigest
        reportDigest cachedCnf currentCnf visibleCnf reuse))

theorem ay_reuse_current_canonical
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    AyCanonicalArtifact currentCnf visibleCnf := by
  intro reuse
  exact ay_equisat_trans currentCnf cachedCnf visibleCnf
    (ay_equisat_symm cachedCnf currentCnf
      (ay_reuse_guard reportId manifestId cachedId cachedDigest
        reportDigest cachedCnf currentCnf visibleCnf reuse))
    (ay_entry_artifact cachedId cachedDigest cachedCnf visibleCnf
      (ay_reuse_entry reportId manifestId cachedId cachedDigest
        reportDigest cachedCnf currentCnf visibleCnf reuse))

theorem ay_report_mismatch_id
    (idMismatch : Prop) (digestMismatch : Prop) :
    idMismatch ->
    AyReportMismatch idMismatch digestMismatch := by
  exact ay_disj_left idMismatch digestMismatch

theorem ay_report_mismatch_digest
    (idMismatch : Prop) (digestMismatch : Prop) :
    digestMismatch ->
    AyReportMismatch idMismatch digestMismatch := by
  exact ay_disj_right idMismatch digestMismatch

theorem ay_report_no_claim
    (idMismatch : Prop) (digestMismatch : Prop) (fallback : Prop) :
    AyReportMismatch idMismatch digestMismatch ->
    fallback ->
    AyConj
      (AyReportMismatch idMismatch digestMismatch)
      (AyNoSemanticClaim fallback) := by
  intro mismatch
  intro hfallback
  exact ay_conj_intro
    (AyReportMismatch idMismatch digestMismatch)
    (AyNoSemanticClaim fallback)
    mismatch
    hfallback

theorem ay_no_claim_mismatch
    (idMismatch : Prop) (digestMismatch : Prop) (fallback : Prop) :
    AyConj
      (AyReportMismatch idMismatch digestMismatch)
      (AyNoSemanticClaim fallback) ->
    AyReportMismatch idMismatch digestMismatch := by
  intro no_claim
  exact ay_conj_left
    (AyReportMismatch idMismatch digestMismatch)
    (AyNoSemanticClaim fallback)
    no_claim

theorem ay_no_claim_fallback
    (idMismatch : Prop) (digestMismatch : Prop) (fallback : Prop) :
    AyConj
      (AyReportMismatch idMismatch digestMismatch)
      (AyNoSemanticClaim fallback) ->
    fallback := by
  intro no_claim
  exact ay_conj_right
    (AyReportMismatch idMismatch digestMismatch)
    (AyNoSemanticClaim fallback)
    no_claim

theorem ay_decision_from_reuse
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (idMismatch : Prop) (digestMismatch : Prop) (fallback : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    AyReportDecision
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf
      idMismatch digestMismatch fallback := by
  intro reuse
  exact ay_disj_left
    (AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyReportMismatch idMismatch digestMismatch)
      (AyNoSemanticClaim fallback))
    reuse

theorem ay_decision_from_id_mismatch
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (idMismatch : Prop) (digestMismatch : Prop) (fallback : Prop) :
    idMismatch ->
    fallback ->
    AyReportDecision
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf
      idMismatch digestMismatch fallback := by
  intro hid
  intro hfallback
  exact ay_disj_right
    (AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyReportMismatch idMismatch digestMismatch)
      (AyNoSemanticClaim fallback))
    (ay_report_no_claim idMismatch digestMismatch fallback
      (ay_report_mismatch_id idMismatch digestMismatch hid)
      hfallback)

theorem ay_decision_from_digest_mismatch
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (idMismatch : Prop) (digestMismatch : Prop) (fallback : Prop) :
    digestMismatch ->
    fallback ->
    AyReportDecision
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf
      idMismatch digestMismatch fallback := by
  intro hdigest
  intro hfallback
  exact ay_disj_right
    (AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf)
    (AyConj
      (AyReportMismatch idMismatch digestMismatch)
      (AyNoSemanticClaim fallback))
    (ay_report_no_claim idMismatch digestMismatch fallback
      (ay_report_mismatch_digest idMismatch digestMismatch hdigest)
      hfallback)

theorem ay_reuse_forward_map
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    currentCnf ->
    visibleCnf := by
  intro reuse
  exact ay_equisat_forward currentCnf visibleCnf
    (ay_reuse_current_canonical reportId manifestId cachedId
      cachedDigest reportDigest cachedCnf currentCnf visibleCnf reuse)

theorem ay_reuse_backward_map
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    visibleCnf ->
    currentCnf := by
  intro reuse
  exact ay_equisat_backward currentCnf visibleCnf
    (ay_reuse_current_canonical reportId manifestId cachedId
      cachedDigest reportDigest cachedCnf currentCnf visibleCnf reuse)

theorem ay_reuse_visible_sat_pullback
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat currentCnf originalModel := by
  intro reuse
  intro pullback
  intro sat
  exact ay_conj_intro currentCnf originalModel
    (ay_reuse_backward_map reportId manifestId cachedId
      cachedDigest reportDigest cachedCnf currentCnf visibleCnf reuse
      (ay_sat_cnf visibleCnf visibleModel sat))
    (pullback (ay_sat_model visibleCnf visibleModel sat))

theorem ay_reuse_unsat_pushback
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
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
    (ay_reuse_forward_map reportId manifestId cachedId
      cachedDigest reportDigest cachedCnf currentCnf visibleCnf reuse
      hcurrent)
    hcertificate

theorem ay_report_contract_from_reuse
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AyReplay visibleCnf certificate conflict ->
    AyReportContract
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
    (ay_reuse_current_canonical reportId manifestId cachedId
      cachedDigest reportDigest cachedCnf currentCnf visibleCnf reuse)
    (ay_conj_intro
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict)
      pullback
      replay)

theorem ay_contract_canonical
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyReportContract
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
    AyReportContract
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
    AyReportContract
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
    AyReportContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySat visibleCnf visibleModel ->
    AySat currentCnf originalModel := by
  intro contract
  intro sat
  exact ay_conj_intro currentCnf originalModel
    (ay_equisat_backward currentCnf visibleCnf
      (ay_contract_canonical currentCnf visibleCnf
        visibleModel originalModel certificate conflict contract)
      (ay_sat_cnf visibleCnf visibleModel sat))
    (ay_contract_pullback currentCnf visibleCnf
      visibleModel originalModel certificate conflict contract
      (ay_sat_model visibleCnf visibleModel sat))

theorem ay_contract_unsat_report
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyReportContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    certificate ->
    currentCnf ->
    conflict := by
  intro contract
  intro hcertificate
  intro hcurrent
  exact ay_contract_replay currentCnf visibleCnf
    visibleModel originalModel certificate conflict contract
    (ay_equisat_forward currentCnf visibleCnf
      (ay_contract_canonical currentCnf visibleCnf
        visibleModel originalModel certificate conflict contract)
      hcurrent)
    hcertificate

theorem ay_exit_code_sound_intro
    (exitCode : Prop) (claim : Prop) :
    exitCode ->
    claim ->
    AyExitCodeSound exitCode claim := by
  exact ay_conj_intro exitCode claim

theorem ay_public_report_sat
    (currentCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    AySat currentCnf originalModel ->
    AyPublicReport currentCnf originalModel certificate conflict exitCode := by
  intro hexit
  intro sat
  exact ay_disj_left
    (AyExitCodeSound exitCode (AySat currentCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> currentCnf -> conflict))
    (ay_exit_code_sound_intro exitCode
      (AySat currentCnf originalModel) hexit sat)

theorem ay_public_report_unsat
    (currentCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> currentCnf -> conflict) ->
    AyPublicReport currentCnf originalModel certificate conflict exitCode := by
  intro hexit
  intro unsat
  exact ay_disj_right
    (AyExitCodeSound exitCode (AySat currentCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> currentCnf -> conflict))
    (ay_exit_code_sound_intro exitCode
      (certificate -> currentCnf -> conflict) hexit unsat)

theorem ay_reuse_sat_public_report
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    exitCode ->
    AyPublicReport currentCnf originalModel certificate conflict exitCode := by
  intro reuse
  intro pullback
  intro sat
  intro hexit
  exact ay_public_report_sat
    currentCnf originalModel certificate conflict exitCode
    hexit
    (ay_reuse_visible_sat_pullback reportId manifestId cachedId
      cachedDigest reportDigest cachedCnf currentCnf visibleCnf
      visibleModel originalModel reuse pullback sat)

theorem ay_reuse_unsat_public_report
    (reportId : Prop) (manifestId : Prop)
    (cachedId : Prop) (cachedDigest : Prop) (reportDigest : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedReportReuse
      reportId manifestId cachedId cachedDigest reportDigest
      cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    exitCode ->
    AyPublicReport currentCnf originalModel certificate conflict exitCode := by
  intro reuse
  intro replay
  intro hexit
  exact ay_public_report_unsat
    currentCnf originalModel certificate conflict exitCode
    hexit
    (ay_reuse_unsat_pushback reportId manifestId cachedId
      cachedDigest reportDigest cachedCnf currentCnf visibleCnf
      certificate conflict reuse replay)

theorem ay_contract_sat_public_report
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyReportContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySat visibleCnf visibleModel ->
    exitCode ->
    AyPublicReport currentCnf originalModel certificate conflict exitCode := by
  intro contract
  intro sat
  intro hexit
  exact ay_public_report_sat
    currentCnf originalModel certificate conflict exitCode
    hexit
    (ay_contract_sat_report currentCnf visibleCnf
      visibleModel originalModel certificate conflict contract sat)

theorem ay_contract_unsat_public_report
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyReportContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    exitCode ->
    AyPublicReport currentCnf originalModel certificate conflict exitCode := by
  intro contract
  intro hexit
  exact ay_public_report_unsat
    currentCnf originalModel certificate conflict exitCode
    hexit
    (ay_contract_unsat_report currentCnf visibleCnf
      visibleModel originalModel certificate conflict contract)
