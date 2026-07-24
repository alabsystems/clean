-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Append-only validator audit log bridge for preprocessing report reuse. The
-- propositions stand for canonical preprocessing artifacts, manifest/digest
-- agreement, accepted reuse reports, mismatch diagnostics, public SAT/UNSAT
-- result exposure, and append-only log evidence.

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

def AyPreprocessManifestLink
    (reportId : Prop) (manifestId : Prop)
    (artifactId : Prop) (cachedDigest : Prop) (reportDigest : Prop) :=
  AyConj
    (AyIdMatch reportId manifestId)
    (AyConj
      (AyIdMatch artifactId manifestId)
      (AyDigestMatch cachedDigest reportDigest))

def AyAcceptedPreprocessReuse
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :=
  AyConj
    (AyPreprocessManifestLink
      reportId manifestId artifactId cachedDigest reportDigest)
    (AyCanonicalPreprocessArtifact originalCnf visibleCnf)

def AyMismatchDiagnostic (idMismatch : Prop) (digestMismatch : Prop) :=
  AyDisj idMismatch digestMismatch

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedReuseLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedPreprocessReuse
      reportId manifestId artifactId cachedDigest reportDigest
      originalCnf visibleCnf)
    nextLog

def AyDiagnosticLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (idMismatch : Prop) (digestMismatch : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyMismatchDiagnostic idMismatch digestMismatch)
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

theorem ay_pal_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_pal_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pal_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pal_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_pal_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_pal_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyEquisat before after := by
  intro forward
  intro backward
  exact ay_pal_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_pal_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pal_conj_left (before -> after) (after -> before) eq

theorem ay_pal_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pal_conj_right (before -> after) (after -> before) eq

theorem ay_pal_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_pal_conj_left cnf model sat

theorem ay_pal_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_pal_conj_right cnf model sat

theorem ay_pal_id_match_forward
    (leftId : Prop) (rightId : Prop) :
    AyIdMatch leftId rightId ->
    leftId ->
    rightId := by
  intro hmatch
  intro hleft
  exact ay_pal_conj_left (leftId -> rightId) (rightId -> leftId)
    hmatch hleft

theorem ay_pal_digest_match_forward
    (cachedDigest : Prop) (reportDigest : Prop) :
    AyDigestMatch cachedDigest reportDigest ->
    cachedDigest ->
    reportDigest := by
  intro hmatch
  intro hcached
  exact ay_pal_conj_left
    (cachedDigest -> reportDigest)
    (reportDigest -> cachedDigest)
    hmatch
    hcached

theorem ay_pal_link_report_manifest
    (reportId : Prop) (manifestId : Prop)
    (artifactId : Prop) (cachedDigest : Prop) (reportDigest : Prop) :
    AyPreprocessManifestLink
      reportId manifestId artifactId cachedDigest reportDigest ->
    AyIdMatch reportId manifestId := by
  intro link
  exact ay_pal_conj_left
    (AyIdMatch reportId manifestId)
    (AyConj
      (AyIdMatch artifactId manifestId)
      (AyDigestMatch cachedDigest reportDigest))
    link

theorem ay_pal_link_artifact_manifest
    (reportId : Prop) (manifestId : Prop)
    (artifactId : Prop) (cachedDigest : Prop) (reportDigest : Prop) :
    AyPreprocessManifestLink
      reportId manifestId artifactId cachedDigest reportDigest ->
    AyIdMatch artifactId manifestId := by
  intro link
  exact ay_pal_conj_left
    (AyIdMatch artifactId manifestId)
    (AyDigestMatch cachedDigest reportDigest)
    (ay_pal_conj_right
      (AyIdMatch reportId manifestId)
      (AyConj
        (AyIdMatch artifactId manifestId)
        (AyDigestMatch cachedDigest reportDigest))
      link)

theorem ay_pal_link_digest
    (reportId : Prop) (manifestId : Prop)
    (artifactId : Prop) (cachedDigest : Prop) (reportDigest : Prop) :
    AyPreprocessManifestLink
      reportId manifestId artifactId cachedDigest reportDigest ->
    AyDigestMatch cachedDigest reportDigest := by
  intro link
  exact ay_pal_conj_right
    (AyIdMatch artifactId manifestId)
    (AyDigestMatch cachedDigest reportDigest)
    (ay_pal_conj_right
      (AyIdMatch reportId manifestId)
      (AyConj
        (AyIdMatch artifactId manifestId)
        (AyDigestMatch cachedDigest reportDigest))
      link)

theorem ay_pal_reuse_link
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedPreprocessReuse
      reportId manifestId artifactId cachedDigest reportDigest
      originalCnf visibleCnf ->
    AyPreprocessManifestLink
      reportId manifestId artifactId cachedDigest reportDigest := by
  intro reuse
  exact ay_pal_conj_left
    (AyPreprocessManifestLink
      reportId manifestId artifactId cachedDigest reportDigest)
    (AyCanonicalPreprocessArtifact originalCnf visibleCnf)
    reuse

theorem ay_pal_reuse_artifact
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedPreprocessReuse
      reportId manifestId artifactId cachedDigest reportDigest
      originalCnf visibleCnf ->
    AyCanonicalPreprocessArtifact originalCnf visibleCnf := by
  intro reuse
  exact ay_pal_conj_right
    (AyPreprocessManifestLink
      reportId manifestId artifactId cachedDigest reportDigest)
    (AyCanonicalPreprocessArtifact originalCnf visibleCnf)
    reuse

theorem ay_pal_reuse_manifest_id
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedPreprocessReuse
      reportId manifestId artifactId cachedDigest reportDigest
      originalCnf visibleCnf ->
    artifactId ->
    manifestId := by
  intro reuse
  exact ay_pal_id_match_forward artifactId manifestId
    (ay_pal_link_artifact_manifest reportId manifestId artifactId
      cachedDigest reportDigest
      (ay_pal_reuse_link reportId manifestId artifactId
        cachedDigest reportDigest originalCnf visibleCnf reuse))

theorem ay_pal_reuse_report_digest
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedPreprocessReuse
      reportId manifestId artifactId cachedDigest reportDigest
      originalCnf visibleCnf ->
    cachedDigest ->
    reportDigest := by
  intro reuse
  exact ay_pal_digest_match_forward cachedDigest reportDigest
    (ay_pal_link_digest reportId manifestId artifactId
      cachedDigest reportDigest
      (ay_pal_reuse_link reportId manifestId artifactId
        cachedDigest reportDigest originalCnf visibleCnf reuse))

theorem ay_pal_reuse_forward
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedPreprocessReuse
      reportId manifestId artifactId cachedDigest reportDigest
      originalCnf visibleCnf ->
    originalCnf ->
    visibleCnf := by
  intro reuse
  exact ay_pal_equisat_forward originalCnf visibleCnf
    (ay_pal_reuse_artifact reportId manifestId artifactId
      cachedDigest reportDigest originalCnf visibleCnf reuse)

theorem ay_pal_reuse_backward
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedPreprocessReuse
      reportId manifestId artifactId cachedDigest reportDigest
      originalCnf visibleCnf ->
    visibleCnf ->
    originalCnf := by
  intro reuse
  exact ay_pal_equisat_backward originalCnf visibleCnf
    (ay_pal_reuse_artifact reportId manifestId artifactId
      cachedDigest reportDigest originalCnf visibleCnf reuse)

theorem ay_pal_append_previous
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :
    AyAppendOnlyEntry previousLog entry nextLog ->
    previousLog := by
  intro log_entry
  exact ay_pal_conj_left previousLog (AyConj entry nextLog) log_entry

theorem ay_pal_append_entry
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :
    AyAppendOnlyEntry previousLog entry nextLog ->
    entry := by
  intro log_entry
  exact ay_pal_conj_left entry nextLog
    (ay_pal_conj_right previousLog (AyConj entry nextLog) log_entry)

theorem ay_pal_append_next
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :
    AyAppendOnlyEntry previousLog entry nextLog ->
    nextLog := by
  intro log_entry
  exact ay_pal_conj_right entry nextLog
    (ay_pal_conj_right previousLog (AyConj entry nextLog) log_entry)

theorem ay_pal_accepted_log_reuse
    (previousLog : Prop) (nextLog : Prop)
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuseLogEntry
      previousLog nextLog reportId manifestId artifactId
      cachedDigest reportDigest originalCnf visibleCnf ->
    AyAcceptedPreprocessReuse
      reportId manifestId artifactId cachedDigest reportDigest
      originalCnf visibleCnf := by
  intro log_entry
  exact ay_pal_append_entry previousLog
    (AyAcceptedPreprocessReuse
      reportId manifestId artifactId cachedDigest reportDigest
      originalCnf visibleCnf)
    nextLog
    log_entry

theorem ay_pal_accepted_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuseLogEntry
      previousLog nextLog reportId manifestId artifactId
      cachedDigest reportDigest originalCnf visibleCnf ->
    AyConj previousLog nextLog := by
  intro log_entry
  exact ay_pal_conj_intro previousLog nextLog
    (ay_pal_append_previous previousLog
      (AyAcceptedPreprocessReuse
        reportId manifestId artifactId cachedDigest reportDigest
        originalCnf visibleCnf)
      nextLog log_entry)
    (ay_pal_append_next previousLog
      (AyAcceptedPreprocessReuse
        reportId manifestId artifactId cachedDigest reportDigest
        originalCnf visibleCnf)
      nextLog log_entry)

theorem ay_pal_mismatch_id
    (idMismatch : Prop) (digestMismatch : Prop) :
    idMismatch ->
    AyMismatchDiagnostic idMismatch digestMismatch := by
  exact ay_pal_disj_left idMismatch digestMismatch

theorem ay_pal_mismatch_digest
    (idMismatch : Prop) (digestMismatch : Prop) :
    digestMismatch ->
    AyMismatchDiagnostic idMismatch digestMismatch := by
  exact ay_pal_disj_right idMismatch digestMismatch

theorem ay_pal_diagnostic_no_claim
    (idMismatch : Prop) (digestMismatch : Prop) (diagnostic : Prop) :
    AyMismatchDiagnostic idMismatch digestMismatch ->
    diagnostic ->
    AyConj
      (AyMismatchDiagnostic idMismatch digestMismatch)
      (AyNoSemanticClaim diagnostic) := by
  intro mismatch
  intro hdiagnostic
  exact ay_pal_conj_intro
    (AyMismatchDiagnostic idMismatch digestMismatch)
    (AyNoSemanticClaim diagnostic)
    mismatch
    hdiagnostic

theorem ay_pal_diagnostic_log_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (idMismatch : Prop) (digestMismatch : Prop) (diagnostic : Prop) :
    AyDiagnosticLogEntry
      previousLog nextLog idMismatch digestMismatch diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro log_entry
  exact ay_pal_conj_right
    (AyMismatchDiagnostic idMismatch digestMismatch)
    (AyNoSemanticClaim diagnostic)
    (ay_pal_append_entry previousLog
      (AyConj
        (AyMismatchDiagnostic idMismatch digestMismatch)
        (AyNoSemanticClaim diagnostic))
      nextLog
      log_entry)

theorem ay_pal_diagnostic_log_mismatch
    (previousLog : Prop) (nextLog : Prop)
    (idMismatch : Prop) (digestMismatch : Prop) (diagnostic : Prop) :
    AyDiagnosticLogEntry
      previousLog nextLog idMismatch digestMismatch diagnostic ->
    AyMismatchDiagnostic idMismatch digestMismatch := by
  intro log_entry
  exact ay_pal_conj_left
    (AyMismatchDiagnostic idMismatch digestMismatch)
    (AyNoSemanticClaim diagnostic)
    (ay_pal_append_entry previousLog
      (AyConj
        (AyMismatchDiagnostic idMismatch digestMismatch)
        (AyNoSemanticClaim diagnostic))
      nextLog
      log_entry)

theorem ay_pal_diagnostic_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (idMismatch : Prop) (digestMismatch : Prop) (diagnostic : Prop) :
    AyDiagnosticLogEntry
      previousLog nextLog idMismatch digestMismatch diagnostic ->
    AyConj previousLog nextLog := by
  intro log_entry
  exact ay_pal_conj_intro previousLog nextLog
    (ay_pal_append_previous previousLog
      (AyConj
        (AyMismatchDiagnostic idMismatch digestMismatch)
        (AyNoSemanticClaim diagnostic))
      nextLog
      log_entry)
    (ay_pal_append_next previousLog
      (AyConj
        (AyMismatchDiagnostic idMismatch digestMismatch)
        (AyNoSemanticClaim diagnostic))
      nextLog
      log_entry)

theorem ay_pal_sat_pullback_sound
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyAcceptedPreprocessReuse
      reportId manifestId artifactId cachedDigest reportDigest
      originalCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat originalCnf originalModel := by
  intro reuse
  intro pullback
  intro sat
  exact ay_pal_conj_intro originalCnf originalModel
    (ay_pal_reuse_backward reportId manifestId artifactId
      cachedDigest reportDigest originalCnf visibleCnf reuse
      (ay_pal_sat_cnf visibleCnf visibleModel sat))
    (pullback (ay_pal_sat_model visibleCnf visibleModel sat))

theorem ay_pal_unsat_pushforward_sound
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedPreprocessReuse
      reportId manifestId artifactId cachedDigest reportDigest
      originalCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reuse
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_pal_reuse_forward reportId manifestId artifactId
      cachedDigest reportDigest originalCnf visibleCnf reuse horiginal)
    hcertificate

theorem ay_pal_exit_code_sound_intro
    (exitCode : Prop) (claim : Prop) :
    exitCode ->
    claim ->
    AyExitCodeSound exitCode claim := by
  exact ay_pal_conj_intro exitCode claim

theorem ay_pal_public_sat_result
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    AySat originalCnf originalModel ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro hexit
  intro sat
  exact ay_pal_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pal_exit_code_sound_intro exitCode
      (AySat originalCnf originalModel)
      hexit
      sat)

theorem ay_pal_public_unsat_result
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro hexit
  intro unsat
  exact ay_pal_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pal_exit_code_sound_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      unsat)

theorem ay_preprocess_audit_sat_public_sound
    (previousLog : Prop) (nextLog : Prop)
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedReuseLogEntry
      previousLog nextLog reportId manifestId artifactId
      cachedDigest reportDigest originalCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro log_entry
  intro pullback
  intro sat
  intro hexit
  exact ay_pal_public_sat_result
    originalCnf originalModel certificate conflict exitCode
    hexit
    (ay_pal_sat_pullback_sound reportId manifestId artifactId
      cachedDigest reportDigest originalCnf visibleCnf
      visibleModel originalModel
      (ay_pal_accepted_log_reuse previousLog nextLog
        reportId manifestId artifactId cachedDigest reportDigest
        originalCnf visibleCnf log_entry)
      pullback
      sat)

theorem ay_preprocess_audit_unsat_public_sound
    (previousLog : Prop) (nextLog : Prop)
    (reportId : Prop) (manifestId : Prop) (artifactId : Prop)
    (cachedDigest : Prop) (reportDigest : Prop)
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedReuseLogEntry
      previousLog nextLog reportId manifestId artifactId
      cachedDigest reportDigest originalCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro log_entry
  intro replay
  intro hexit
  exact ay_pal_public_unsat_result
    originalCnf originalModel certificate conflict exitCode
    hexit
    (ay_pal_unsat_pushforward_sound reportId manifestId artifactId
      cachedDigest reportDigest originalCnf visibleCnf
      certificate conflict
      (ay_pal_accepted_log_reuse previousLog nextLog
        reportId manifestId artifactId cachedDigest reportDigest
        originalCnf visibleCnf log_entry)
      replay)

theorem ay_preprocess_audit_diagnostic_no_public_result
    (previousLog : Prop) (nextLog : Prop)
    (idMismatch : Prop) (digestMismatch : Prop) (diagnostic : Prop) :
    AyDiagnosticLogEntry
      previousLog nextLog idMismatch digestMismatch diagnostic ->
    AyConj
      (AyMismatchDiagnostic idMismatch digestMismatch)
      (AyNoSemanticClaim diagnostic) := by
  intro log_entry
  exact ay_pal_append_entry previousLog
    (AyConj
      (AyMismatchDiagnostic idMismatch digestMismatch)
      (AyNoSemanticClaim diagnostic))
    nextLog
    log_entry
