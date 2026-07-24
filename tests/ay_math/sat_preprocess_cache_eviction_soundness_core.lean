-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Preprocessing cache eviction soundness for bounded ay SAT-COMP caches. The
-- propositions stand for cache entries, epoch/manifest/digest agreement,
-- retained reuse reports, eviction/missing-entry fallbacks, append-only audit
-- diagnostics, and public SAT/UNSAT results.

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

def AyDigestMatch (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj (cachedDigest -> runDigest) (runDigest -> cachedDigest)

def AyCanonicalPreprocessArtifact (originalCnf : Prop) (visibleCnf : Prop) :=
  AyEquisat originalCnf visibleCnf

def AyCacheAgreement
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyPreprocessCacheEntry
    (cachedEpoch : Prop) (cachedManifest : Prop) (cachedDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :=
  AyConj cachedEpoch
    (AyConj cachedManifest
      (AyConj cachedDigest
        (AyCanonicalPreprocessArtifact originalCnf visibleCnf)))

def AyRetainedPreprocessReuse
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :=
  AyConj
    (AyPreprocessCacheEntry
      cachedEpoch cachedManifest cachedDigest originalCnf visibleCnf)
    (AyCacheAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)

def AyEvictionReason (evicted : Prop) (missing : Prop) :=
  AyDisj evicted missing

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyRetainedReuseLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf)
    nextLog

def AyEvictionDiagnosticLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (evicted : Prop) (missing : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyEvictionReason evicted missing)
      (AyConj recompute (AyNoSemanticClaim diagnostic)))
    nextLog

def AySatPullback (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyExitCodeSound (exitCode : Prop) (claim : Prop) :=
  AyConj exitCode claim

def AyPublicResult
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  AyDisj
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pcev_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_pcev_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pcev_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pcev_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_pcev_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_pcev_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pcev_conj_left (before -> after) (after -> before) eq

theorem ay_pcev_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pcev_conj_right (before -> after) (after -> before) eq

theorem ay_pcev_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_pcev_conj_left cnf model sat

theorem ay_pcev_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_pcev_conj_right cnf model sat

theorem ay_pcev_id_match_forward
    (leftId : Prop) (rightId : Prop) :
    AyIdMatch leftId rightId ->
    leftId ->
    rightId := by
  intro hmatch
  intro hleft
  exact ay_pcev_conj_left (leftId -> rightId) (rightId -> leftId)
    hmatch hleft

theorem ay_pcev_digest_match_forward
    (cachedDigest : Prop) (runDigest : Prop) :
    AyDigestMatch cachedDigest runDigest ->
    cachedDigest ->
    runDigest := by
  intro hmatch
  intro hcached
  exact ay_pcev_conj_left
    (cachedDigest -> runDigest)
    (runDigest -> cachedDigest)
    hmatch
    hcached

theorem ay_pcev_entry_epoch
    (cachedEpoch : Prop) (cachedManifest : Prop) (cachedDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyPreprocessCacheEntry
      cachedEpoch cachedManifest cachedDigest originalCnf visibleCnf ->
    cachedEpoch := by
  intro entry
  exact ay_pcev_conj_left cachedEpoch
    (AyConj cachedManifest
      (AyConj cachedDigest
        (AyCanonicalPreprocessArtifact originalCnf visibleCnf)))
    entry

theorem ay_pcev_entry_manifest
    (cachedEpoch : Prop) (cachedManifest : Prop) (cachedDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyPreprocessCacheEntry
      cachedEpoch cachedManifest cachedDigest originalCnf visibleCnf ->
    cachedManifest := by
  intro entry
  exact ay_pcev_conj_left cachedManifest
    (AyConj cachedDigest
      (AyCanonicalPreprocessArtifact originalCnf visibleCnf))
    (ay_pcev_conj_right cachedEpoch
      (AyConj cachedManifest
        (AyConj cachedDigest
          (AyCanonicalPreprocessArtifact originalCnf visibleCnf)))
      entry)

theorem ay_pcev_entry_digest
    (cachedEpoch : Prop) (cachedManifest : Prop) (cachedDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyPreprocessCacheEntry
      cachedEpoch cachedManifest cachedDigest originalCnf visibleCnf ->
    cachedDigest := by
  intro entry
  exact ay_pcev_conj_left cachedDigest
    (AyCanonicalPreprocessArtifact originalCnf visibleCnf)
    (ay_pcev_conj_right cachedManifest
      (AyConj cachedDigest
        (AyCanonicalPreprocessArtifact originalCnf visibleCnf))
      (ay_pcev_conj_right cachedEpoch
        (AyConj cachedManifest
          (AyConj cachedDigest
            (AyCanonicalPreprocessArtifact originalCnf visibleCnf)))
        entry))

theorem ay_pcev_entry_artifact
    (cachedEpoch : Prop) (cachedManifest : Prop) (cachedDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyPreprocessCacheEntry
      cachedEpoch cachedManifest cachedDigest originalCnf visibleCnf ->
    AyCanonicalPreprocessArtifact originalCnf visibleCnf := by
  intro entry
  exact ay_pcev_conj_right cachedDigest
    (AyCanonicalPreprocessArtifact originalCnf visibleCnf)
    (ay_pcev_conj_right cachedManifest
      (AyConj cachedDigest
        (AyCanonicalPreprocessArtifact originalCnf visibleCnf))
      (ay_pcev_conj_right cachedEpoch
        (AyConj cachedManifest
          (AyConj cachedDigest
            (AyCanonicalPreprocessArtifact originalCnf visibleCnf)))
        entry))

theorem ay_pcev_agreement_epoch
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyCacheAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyIdMatch cachedEpoch currentEpoch := by
  intro agreement
  exact ay_pcev_conj_left
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))
    agreement

theorem ay_pcev_agreement_manifest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyCacheAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyIdMatch cachedManifest runManifest := by
  intro agreement
  exact ay_pcev_conj_left
    (AyIdMatch cachedManifest runManifest)
    (AyDigestMatch cachedDigest runDigest)
    (ay_pcev_conj_right
      (AyIdMatch cachedEpoch currentEpoch)
      (AyConj
        (AyIdMatch cachedManifest runManifest)
        (AyDigestMatch cachedDigest runDigest))
      agreement)

theorem ay_pcev_agreement_digest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyCacheAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyDigestMatch cachedDigest runDigest := by
  intro agreement
  exact ay_pcev_conj_right
    (AyIdMatch cachedManifest runManifest)
    (AyDigestMatch cachedDigest runDigest)
    (ay_pcev_conj_right
      (AyIdMatch cachedEpoch currentEpoch)
      (AyConj
        (AyIdMatch cachedManifest runManifest)
        (AyDigestMatch cachedDigest runDigest))
      agreement)

theorem ay_pcev_reuse_entry
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    AyPreprocessCacheEntry
      cachedEpoch cachedManifest cachedDigest originalCnf visibleCnf := by
  intro reuse
  exact ay_pcev_conj_left
    (AyPreprocessCacheEntry
      cachedEpoch cachedManifest cachedDigest originalCnf visibleCnf)
    (AyCacheAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    reuse

theorem ay_pcev_reuse_agreement
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    AyCacheAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest := by
  intro reuse
  exact ay_pcev_conj_right
    (AyPreprocessCacheEntry
      cachedEpoch cachedManifest cachedDigest originalCnf visibleCnf)
    (AyCacheAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    reuse

theorem ay_pcev_reuse_artifact
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    AyCanonicalPreprocessArtifact originalCnf visibleCnf := by
  intro reuse
  exact ay_pcev_entry_artifact cachedEpoch cachedManifest cachedDigest
    originalCnf visibleCnf
    (ay_pcev_reuse_entry cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf reuse)

theorem ay_pcev_reuse_current_epoch
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    currentEpoch := by
  intro reuse
  exact ay_pcev_id_match_forward cachedEpoch currentEpoch
    (ay_pcev_agreement_epoch cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      (ay_pcev_reuse_agreement cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        originalCnf visibleCnf reuse))
    (ay_pcev_entry_epoch cachedEpoch cachedManifest cachedDigest
      originalCnf visibleCnf
      (ay_pcev_reuse_entry cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        originalCnf visibleCnf reuse))

theorem ay_pcev_reuse_run_manifest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    runManifest := by
  intro reuse
  exact ay_pcev_id_match_forward cachedManifest runManifest
    (ay_pcev_agreement_manifest cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      (ay_pcev_reuse_agreement cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        originalCnf visibleCnf reuse))
    (ay_pcev_entry_manifest cachedEpoch cachedManifest cachedDigest
      originalCnf visibleCnf
      (ay_pcev_reuse_entry cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        originalCnf visibleCnf reuse))

theorem ay_pcev_reuse_run_digest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    runDigest := by
  intro reuse
  exact ay_pcev_digest_match_forward cachedDigest runDigest
    (ay_pcev_agreement_digest cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      (ay_pcev_reuse_agreement cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        originalCnf visibleCnf reuse))
    (ay_pcev_entry_digest cachedEpoch cachedManifest cachedDigest
      originalCnf visibleCnf
      (ay_pcev_reuse_entry cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        originalCnf visibleCnf reuse))

theorem ay_pcev_reuse_forward
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    originalCnf ->
    visibleCnf := by
  intro reuse
  exact ay_pcev_equisat_forward originalCnf visibleCnf
    (ay_pcev_reuse_artifact cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest originalCnf visibleCnf reuse)

theorem ay_pcev_reuse_backward
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    visibleCnf ->
    originalCnf := by
  intro reuse
  exact ay_pcev_equisat_backward originalCnf visibleCnf
    (ay_pcev_reuse_artifact cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest originalCnf visibleCnf reuse)

theorem ay_pcev_append_previous
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :
    AyAppendOnlyEntry previousLog entry nextLog ->
    previousLog := by
  intro log_entry
  exact ay_pcev_conj_left previousLog (AyConj entry nextLog) log_entry

theorem ay_pcev_append_entry
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :
    AyAppendOnlyEntry previousLog entry nextLog ->
    entry := by
  intro log_entry
  exact ay_pcev_conj_left entry nextLog
    (ay_pcev_conj_right previousLog (AyConj entry nextLog) log_entry)

theorem ay_pcev_append_next
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :
    AyAppendOnlyEntry previousLog entry nextLog ->
    nextLog := by
  intro log_entry
  exact ay_pcev_conj_right entry nextLog
    (ay_pcev_conj_right previousLog (AyConj entry nextLog) log_entry)

theorem ay_pcev_retained_log_reuse
    (previousLog : Prop) (nextLog : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyRetainedReuseLogEntry
      previousLog nextLog cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf ->
    AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf := by
  intro log_entry
  exact ay_pcev_append_entry previousLog
    (AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf)
    nextLog
    log_entry

theorem ay_pcev_retained_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyRetainedReuseLogEntry
      previousLog nextLog cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf ->
    AyConj previousLog nextLog := by
  intro log_entry
  exact ay_pcev_conj_intro previousLog nextLog
    (ay_pcev_append_previous previousLog
      (AyRetainedPreprocessReuse
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest originalCnf visibleCnf)
      nextLog log_entry)
    (ay_pcev_append_next previousLog
      (AyRetainedPreprocessReuse
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest originalCnf visibleCnf)
      nextLog log_entry)

theorem ay_pcev_reason_evicted
    (evicted : Prop) (missing : Prop) :
    evicted ->
    AyEvictionReason evicted missing := by
  exact ay_pcev_disj_left evicted missing

theorem ay_pcev_reason_missing
    (evicted : Prop) (missing : Prop) :
    missing ->
    AyEvictionReason evicted missing := by
  exact ay_pcev_disj_right evicted missing

theorem ay_pcev_diagnostic_entry
    (evicted : Prop) (missing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyEvictionReason evicted missing ->
    recompute ->
    diagnostic ->
    AyConj
      (AyEvictionReason evicted missing)
      (AyConj recompute (AyNoSemanticClaim diagnostic)) := by
  intro reason
  intro hrecompute
  intro hdiagnostic
  exact ay_pcev_conj_intro
    (AyEvictionReason evicted missing)
    (AyConj recompute (AyNoSemanticClaim diagnostic))
    reason
    (ay_pcev_conj_intro recompute
      (AyNoSemanticClaim diagnostic)
      hrecompute
      hdiagnostic)

theorem ay_pcev_diagnostic_log_reason
    (previousLog : Prop) (nextLog : Prop)
    (evicted : Prop) (missing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyEvictionDiagnosticLogEntry
      previousLog nextLog evicted missing recompute diagnostic ->
    AyEvictionReason evicted missing := by
  intro log_entry
  exact ay_pcev_conj_left
    (AyEvictionReason evicted missing)
    (AyConj recompute (AyNoSemanticClaim diagnostic))
    (ay_pcev_append_entry previousLog
      (AyConj
        (AyEvictionReason evicted missing)
        (AyConj recompute (AyNoSemanticClaim diagnostic)))
      nextLog
      log_entry)

theorem ay_pcev_diagnostic_log_recompute
    (previousLog : Prop) (nextLog : Prop)
    (evicted : Prop) (missing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyEvictionDiagnosticLogEntry
      previousLog nextLog evicted missing recompute diagnostic ->
    recompute := by
  intro log_entry
  exact ay_pcev_conj_left recompute
    (AyNoSemanticClaim diagnostic)
    (ay_pcev_conj_right
      (AyEvictionReason evicted missing)
      (AyConj recompute (AyNoSemanticClaim diagnostic))
      (ay_pcev_append_entry previousLog
        (AyConj
          (AyEvictionReason evicted missing)
          (AyConj recompute (AyNoSemanticClaim diagnostic)))
        nextLog
        log_entry))

theorem ay_pcev_diagnostic_log_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (evicted : Prop) (missing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyEvictionDiagnosticLogEntry
      previousLog nextLog evicted missing recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro log_entry
  exact ay_pcev_conj_right recompute
    (AyNoSemanticClaim diagnostic)
    (ay_pcev_conj_right
      (AyEvictionReason evicted missing)
      (AyConj recompute (AyNoSemanticClaim diagnostic))
      (ay_pcev_append_entry previousLog
        (AyConj
          (AyEvictionReason evicted missing)
          (AyConj recompute (AyNoSemanticClaim diagnostic)))
        nextLog
        log_entry))

theorem ay_pcev_diagnostic_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (evicted : Prop) (missing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyEvictionDiagnosticLogEntry
      previousLog nextLog evicted missing recompute diagnostic ->
    AyConj previousLog nextLog := by
  intro log_entry
  exact ay_pcev_conj_intro previousLog nextLog
    (ay_pcev_append_previous previousLog
      (AyConj
        (AyEvictionReason evicted missing)
        (AyConj recompute (AyNoSemanticClaim diagnostic)))
      nextLog log_entry)
    (ay_pcev_append_next previousLog
      (AyConj
        (AyEvictionReason evicted missing)
        (AyConj recompute (AyNoSemanticClaim diagnostic)))
      nextLog log_entry)

theorem ay_pcev_retained_sat_pullback_sound
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat originalCnf originalModel := by
  intro reuse
  intro pullback
  intro sat
  exact ay_pcev_conj_intro originalCnf originalModel
    (ay_pcev_reuse_backward cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf reuse
      (ay_pcev_sat_cnf visibleCnf visibleModel sat))
    (pullback (ay_pcev_sat_model visibleCnf visibleModel sat))

theorem ay_pcev_retained_unsat_pushforward_sound
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyRetainedPreprocessReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reuse
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_pcev_reuse_forward cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf reuse horiginal)
    hcertificate

theorem ay_pcev_exit_code_sound_intro
    (exitCode : Prop) (claim : Prop) :
    exitCode ->
    claim ->
    AyExitCodeSound exitCode claim := by
  exact ay_pcev_conj_intro exitCode claim

theorem ay_pcev_public_sat_result
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    AySat originalCnf originalModel ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro hexit
  intro sat
  exact ay_pcev_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pcev_exit_code_sound_intro exitCode
      (AySat originalCnf originalModel)
      hexit
      sat)

theorem ay_pcev_public_unsat_result
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro hexit
  intro unsat
  exact ay_pcev_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pcev_exit_code_sound_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      unsat)

theorem ay_preprocess_cache_eviction_sat_public_sound
    (previousLog : Prop) (nextLog : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyRetainedReuseLogEntry
      previousLog nextLog cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro log_entry
  intro pullback
  intro sat
  intro hexit
  exact ay_pcev_public_sat_result
    originalCnf originalModel certificate conflict exitCode
    hexit
    (ay_pcev_retained_sat_pullback_sound cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf visibleModel originalModel
      (ay_pcev_retained_log_reuse previousLog nextLog
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest originalCnf visibleCnf log_entry)
      pullback
      sat)

theorem ay_preprocess_cache_eviction_unsat_public_sound
    (previousLog : Prop) (nextLog : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyRetainedReuseLogEntry
      previousLog nextLog cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro log_entry
  intro replay
  intro hexit
  exact ay_pcev_public_unsat_result
    originalCnf originalModel certificate conflict exitCode
    hexit
    (ay_pcev_retained_unsat_pushforward_sound cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf certificate conflict
      (ay_pcev_retained_log_reuse previousLog nextLog
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest originalCnf visibleCnf log_entry)
      replay)

theorem ay_preprocess_cache_eviction_no_stale_public_result
    (previousLog : Prop) (nextLog : Prop)
    (evicted : Prop) (missing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyEvictionDiagnosticLogEntry
      previousLog nextLog evicted missing recompute diagnostic ->
    AyConj
      (AyEvictionReason evicted missing)
      (AyConj recompute (AyNoSemanticClaim diagnostic)) := by
  intro log_entry
  exact ay_pcev_append_entry previousLog
    (AyConj
      (AyEvictionReason evicted missing)
      (AyConj recompute (AyNoSemanticClaim diagnostic)))
    nextLog
    log_entry
