-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Cache-epoch invalidation for preprocessing reuse. The propositions stand
-- for cache epoch IDs, manifest IDs, digest agreement, canonical preprocessing
-- artifacts, accepted reuse audit entries, stale/mismatch diagnostics, and
-- public SAT/UNSAT competition results.

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

def AyCanonicalPreprocessArtifact (originalCnf : Prop) (visibleCnf : Prop) :=
  AyEquisat originalCnf visibleCnf

def AyEpochManifestDigestAgreement
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedEpochReuse
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :=
  AyConj
    (AyEpochManifestDigestAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (AyCanonicalPreprocessArtifact originalCnf visibleCnf)

def AyEpochMismatch
    (staleEpoch : Prop) (manifestMismatch : Prop) (digestMismatch : Prop) :=
  AyDisj staleEpoch (AyDisj manifestMismatch digestMismatch)

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedEpochLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedEpochReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf)
    nextLog

def AyDiagnosticEpochLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (staleEpoch : Prop) (manifestMismatch : Prop)
    (digestMismatch : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyEpochMismatch staleEpoch manifestMismatch digestMismatch)
      (AyNoSemanticClaim diagnostic))
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

theorem ay_pce_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_pce_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pce_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pce_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_pce_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_pce_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pce_conj_left (before -> after) (after -> before) eq

theorem ay_pce_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pce_conj_right (before -> after) (after -> before) eq

theorem ay_pce_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_pce_conj_left cnf model sat

theorem ay_pce_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_pce_conj_right cnf model sat

theorem ay_pce_id_match_forward
    (leftId : Prop) (rightId : Prop) :
    AyIdMatch leftId rightId ->
    leftId ->
    rightId := by
  intro hmatch
  intro hleft
  exact ay_pce_conj_left (leftId -> rightId) (rightId -> leftId)
    hmatch hleft

theorem ay_pce_digest_match_forward
    (cachedDigest : Prop) (runDigest : Prop) :
    AyDigestMatch cachedDigest runDigest ->
    cachedDigest ->
    runDigest := by
  intro hmatch
  intro hcached
  exact ay_pce_conj_left
    (cachedDigest -> runDigest)
    (runDigest -> cachedDigest)
    hmatch
    hcached

theorem ay_pce_agreement_epoch
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyEpochManifestDigestAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyIdMatch cachedEpoch currentEpoch := by
  intro agreement
  exact ay_pce_conj_left
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))
    agreement

theorem ay_pce_agreement_manifest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyEpochManifestDigestAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyIdMatch cachedManifest runManifest := by
  intro agreement
  exact ay_pce_conj_left
    (AyIdMatch cachedManifest runManifest)
    (AyDigestMatch cachedDigest runDigest)
    (ay_pce_conj_right
      (AyIdMatch cachedEpoch currentEpoch)
      (AyConj
        (AyIdMatch cachedManifest runManifest)
        (AyDigestMatch cachedDigest runDigest))
      agreement)

theorem ay_pce_agreement_digest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyEpochManifestDigestAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyDigestMatch cachedDigest runDigest := by
  intro agreement
  exact ay_pce_conj_right
    (AyIdMatch cachedManifest runManifest)
    (AyDigestMatch cachedDigest runDigest)
    (ay_pce_conj_right
      (AyIdMatch cachedEpoch currentEpoch)
      (AyConj
        (AyIdMatch cachedManifest runManifest)
        (AyDigestMatch cachedDigest runDigest))
      agreement)

theorem ay_pce_reuse_agreement
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedEpochReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    AyEpochManifestDigestAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest := by
  intro reuse
  exact ay_pce_conj_left
    (AyEpochManifestDigestAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (AyCanonicalPreprocessArtifact originalCnf visibleCnf)
    reuse

theorem ay_pce_reuse_artifact
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedEpochReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    AyCanonicalPreprocessArtifact originalCnf visibleCnf := by
  intro reuse
  exact ay_pce_conj_right
    (AyEpochManifestDigestAgreement
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (AyCanonicalPreprocessArtifact originalCnf visibleCnf)
    reuse

theorem ay_pce_reuse_current_epoch
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedEpochReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    cachedEpoch ->
    currentEpoch := by
  intro reuse
  exact ay_pce_id_match_forward cachedEpoch currentEpoch
    (ay_pce_agreement_epoch cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      (ay_pce_reuse_agreement cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        originalCnf visibleCnf reuse))

theorem ay_pce_reuse_run_manifest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedEpochReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    cachedManifest ->
    runManifest := by
  intro reuse
  exact ay_pce_id_match_forward cachedManifest runManifest
    (ay_pce_agreement_manifest cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      (ay_pce_reuse_agreement cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        originalCnf visibleCnf reuse))

theorem ay_pce_reuse_run_digest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedEpochReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    cachedDigest ->
    runDigest := by
  intro reuse
  exact ay_pce_digest_match_forward cachedDigest runDigest
    (ay_pce_agreement_digest cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      (ay_pce_reuse_agreement cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        originalCnf visibleCnf reuse))

theorem ay_pce_reuse_forward
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedEpochReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    originalCnf ->
    visibleCnf := by
  intro reuse
  exact ay_pce_equisat_forward originalCnf visibleCnf
    (ay_pce_reuse_artifact cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf reuse)

theorem ay_pce_reuse_backward
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedEpochReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    visibleCnf ->
    originalCnf := by
  intro reuse
  exact ay_pce_equisat_backward originalCnf visibleCnf
    (ay_pce_reuse_artifact cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf reuse)

theorem ay_pce_append_previous
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :
    AyAppendOnlyEntry previousLog entry nextLog ->
    previousLog := by
  intro log_entry
  exact ay_pce_conj_left previousLog (AyConj entry nextLog) log_entry

theorem ay_pce_append_entry
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :
    AyAppendOnlyEntry previousLog entry nextLog ->
    entry := by
  intro log_entry
  exact ay_pce_conj_left entry nextLog
    (ay_pce_conj_right previousLog (AyConj entry nextLog) log_entry)

theorem ay_pce_append_next
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :
    AyAppendOnlyEntry previousLog entry nextLog ->
    nextLog := by
  intro log_entry
  exact ay_pce_conj_right entry nextLog
    (ay_pce_conj_right previousLog (AyConj entry nextLog) log_entry)

theorem ay_pce_accepted_log_reuse
    (previousLog : Prop) (nextLog : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedEpochLogEntry
      previousLog nextLog cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf ->
    AyAcceptedEpochReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf := by
  intro log_entry
  exact ay_pce_append_entry previousLog
    (AyAcceptedEpochReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf)
    nextLog
    log_entry

theorem ay_pce_accepted_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedEpochLogEntry
      previousLog nextLog cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf ->
    AyConj previousLog nextLog := by
  intro log_entry
  exact ay_pce_conj_intro previousLog nextLog
    (ay_pce_append_previous previousLog
      (AyAcceptedEpochReuse
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest originalCnf visibleCnf)
      nextLog log_entry)
    (ay_pce_append_next previousLog
      (AyAcceptedEpochReuse
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest originalCnf visibleCnf)
      nextLog log_entry)

theorem ay_pce_mismatch_stale_epoch
    (staleEpoch : Prop) (manifestMismatch : Prop) (digestMismatch : Prop) :
    staleEpoch ->
    AyEpochMismatch staleEpoch manifestMismatch digestMismatch := by
  intro hstale
  exact ay_pce_disj_left staleEpoch (AyDisj manifestMismatch digestMismatch)
    hstale

theorem ay_pce_mismatch_manifest
    (staleEpoch : Prop) (manifestMismatch : Prop) (digestMismatch : Prop) :
    manifestMismatch ->
    AyEpochMismatch staleEpoch manifestMismatch digestMismatch := by
  intro hmanifest
  exact ay_pce_disj_right staleEpoch (AyDisj manifestMismatch digestMismatch)
    (ay_pce_disj_left manifestMismatch digestMismatch hmanifest)

theorem ay_pce_mismatch_digest
    (staleEpoch : Prop) (manifestMismatch : Prop) (digestMismatch : Prop) :
    digestMismatch ->
    AyEpochMismatch staleEpoch manifestMismatch digestMismatch := by
  intro hdigest
  exact ay_pce_disj_right staleEpoch (AyDisj manifestMismatch digestMismatch)
    (ay_pce_disj_right manifestMismatch digestMismatch hdigest)

theorem ay_pce_diagnostic_no_claim
    (staleEpoch : Prop) (manifestMismatch : Prop)
    (digestMismatch : Prop) (diagnostic : Prop) :
    AyEpochMismatch staleEpoch manifestMismatch digestMismatch ->
    diagnostic ->
    AyConj
      (AyEpochMismatch staleEpoch manifestMismatch digestMismatch)
      (AyNoSemanticClaim diagnostic) := by
  intro mismatch
  intro hdiagnostic
  exact ay_pce_conj_intro
    (AyEpochMismatch staleEpoch manifestMismatch digestMismatch)
    (AyNoSemanticClaim diagnostic)
    mismatch
    hdiagnostic

theorem ay_pce_diagnostic_log_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (staleEpoch : Prop) (manifestMismatch : Prop)
    (digestMismatch : Prop) (diagnostic : Prop) :
    AyDiagnosticEpochLogEntry
      previousLog nextLog staleEpoch manifestMismatch
      digestMismatch diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro log_entry
  exact ay_pce_conj_right
    (AyEpochMismatch staleEpoch manifestMismatch digestMismatch)
    (AyNoSemanticClaim diagnostic)
    (ay_pce_append_entry previousLog
      (AyConj
        (AyEpochMismatch staleEpoch manifestMismatch digestMismatch)
        (AyNoSemanticClaim diagnostic))
      nextLog
      log_entry)

theorem ay_pce_diagnostic_log_mismatch
    (previousLog : Prop) (nextLog : Prop)
    (staleEpoch : Prop) (manifestMismatch : Prop)
    (digestMismatch : Prop) (diagnostic : Prop) :
    AyDiagnosticEpochLogEntry
      previousLog nextLog staleEpoch manifestMismatch
      digestMismatch diagnostic ->
    AyEpochMismatch staleEpoch manifestMismatch digestMismatch := by
  intro log_entry
  exact ay_pce_conj_left
    (AyEpochMismatch staleEpoch manifestMismatch digestMismatch)
    (AyNoSemanticClaim diagnostic)
    (ay_pce_append_entry previousLog
      (AyConj
        (AyEpochMismatch staleEpoch manifestMismatch digestMismatch)
        (AyNoSemanticClaim diagnostic))
      nextLog
      log_entry)

theorem ay_pce_diagnostic_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (staleEpoch : Prop) (manifestMismatch : Prop)
    (digestMismatch : Prop) (diagnostic : Prop) :
    AyDiagnosticEpochLogEntry
      previousLog nextLog staleEpoch manifestMismatch
      digestMismatch diagnostic ->
    AyConj previousLog nextLog := by
  intro log_entry
  exact ay_pce_conj_intro previousLog nextLog
    (ay_pce_append_previous previousLog
      (AyConj
        (AyEpochMismatch staleEpoch manifestMismatch digestMismatch)
        (AyNoSemanticClaim diagnostic))
      nextLog log_entry)
    (ay_pce_append_next previousLog
      (AyConj
        (AyEpochMismatch staleEpoch manifestMismatch digestMismatch)
        (AyNoSemanticClaim diagnostic))
      nextLog log_entry)

theorem ay_pce_sat_pullback_sound
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyAcceptedEpochReuse
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest originalCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat originalCnf originalModel := by
  intro reuse
  intro pullback
  intro sat
  exact ay_pce_conj_intro originalCnf originalModel
    (ay_pce_reuse_backward cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf reuse
      (ay_pce_sat_cnf visibleCnf visibleModel sat))
    (pullback (ay_pce_sat_model visibleCnf visibleModel sat))

theorem ay_pce_unsat_pushforward_sound
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedEpochReuse
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
    (ay_pce_reuse_forward cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf reuse horiginal)
    hcertificate

theorem ay_pce_exit_code_sound_intro
    (exitCode : Prop) (claim : Prop) :
    exitCode ->
    claim ->
    AyExitCodeSound exitCode claim := by
  exact ay_pce_conj_intro exitCode claim

theorem ay_pce_public_sat_result
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    AySat originalCnf originalModel ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro hexit
  intro sat
  exact ay_pce_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pce_exit_code_sound_intro exitCode
      (AySat originalCnf originalModel)
      hexit
      sat)

theorem ay_pce_public_unsat_result
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro hexit
  intro unsat
  exact ay_pce_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pce_exit_code_sound_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      unsat)

theorem ay_preprocess_cache_epoch_sat_public_sound
    (previousLog : Prop) (nextLog : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedEpochLogEntry
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
  exact ay_pce_public_sat_result
    originalCnf originalModel certificate conflict exitCode
    hexit
    (ay_pce_sat_pullback_sound cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf visibleModel originalModel
      (ay_pce_accepted_log_reuse previousLog nextLog
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest originalCnf visibleCnf log_entry)
      pullback
      sat)

theorem ay_preprocess_cache_epoch_unsat_public_sound
    (previousLog : Prop) (nextLog : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedEpochLogEntry
      previousLog nextLog cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro log_entry
  intro replay
  intro hexit
  exact ay_pce_public_unsat_result
    originalCnf originalModel certificate conflict exitCode
    hexit
    (ay_pce_unsat_pushforward_sound cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      originalCnf visibleCnf certificate conflict
      (ay_pce_accepted_log_reuse previousLog nextLog
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest originalCnf visibleCnf log_entry)
      replay)

theorem ay_preprocess_cache_epoch_diagnostic_no_public_result
    (previousLog : Prop) (nextLog : Prop)
    (staleEpoch : Prop) (manifestMismatch : Prop)
    (digestMismatch : Prop) (diagnostic : Prop) :
    AyDiagnosticEpochLogEntry
      previousLog nextLog staleEpoch manifestMismatch
      digestMismatch diagnostic ->
    AyConj
      (AyEpochMismatch staleEpoch manifestMismatch digestMismatch)
      (AyNoSemanticClaim diagnostic) := by
  intro log_entry
  exact ay_pce_append_entry previousLog
    (AyConj
      (AyEpochMismatch staleEpoch manifestMismatch digestMismatch)
      (AyNoSemanticClaim diagnostic))
    nextLog
    log_entry
