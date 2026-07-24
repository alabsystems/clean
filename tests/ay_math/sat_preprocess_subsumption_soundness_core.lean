-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Subsumption and self-subsuming-resolution soundness for preprocessing.
-- The propositions stand for original clauses, subsumed/strengthened clauses,
-- preprocessing maps, replay witnesses, guard evidence, accepted reports,
-- diagnostics, and public SAT/UNSAT competition outcomes.

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

def AySubsumptionStep
    (originalClauses : Prop)
    (subsumedClauses : Prop)
    (strengthenedClauses : Prop) :=
  AyConj
    (originalClauses -> subsumedClauses)
    (strengthenedClauses -> subsumedClauses)

def AyPreprocessMap (originalCnf : Prop) (preprocessedCnf : Prop) :=
  AyEquisat originalCnf preprocessedCnf

def AySubsumptionGuards
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedSubsumptionReport
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyPreprocessMap originalCnf preprocessedCnf)
    (AyConj
      (AySubsumptionStep
        originalClauses subsumedClauses strengthenedClauses)
      (AySubsumptionGuards
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))

def AySubsumptionFailure
    (badDroppedLiteral : Prop)
    (staleReplay : Prop)
    (digestMismatch : Prop) :=
  AyDisj badDroppedLiteral (AyDisj staleReplay digestMismatch)

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  AyConj currentCnf recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedSubsumptionLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedSubsumptionReport
      originalCnf preprocessedCnf originalClauses subsumedClauses
      strengthenedClauses cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest)
    nextLog

def AyDiagnosticSubsumptionLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (badDroppedLiteral : Prop)
    (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AySubsumptionFailure
        badDroppedLiteral staleReplay digestMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog

def AyExitCodeSound (exitCode : Prop) (claim : Prop) :=
  AyConj exitCode claim

def AyPublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  AyDisj
    (AyExitCodeSound exitCode (AySat originalCnf model))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pss_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_pss_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pss_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pss_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_pss_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_pss_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pss_conj_left (before -> after) (after -> before) eq

theorem ay_pss_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pss_conj_right (before -> after) (after -> before) eq

theorem ay_pss_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_pss_conj_left cnf model sat

theorem ay_pss_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_pss_conj_right cnf model sat

theorem ay_pss_report_map
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedSubsumptionReport
      originalCnf preprocessedCnf originalClauses subsumedClauses
      strengthenedClauses cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyPreprocessMap originalCnf preprocessedCnf := by
  intro accepted
  exact ay_pss_conj_left
    (AyPreprocessMap originalCnf preprocessedCnf)
    (AyConj
      (AySubsumptionStep
        originalClauses subsumedClauses strengthenedClauses)
      (AySubsumptionGuards
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))
    accepted

theorem ay_pss_report_step
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedSubsumptionReport
      originalCnf preprocessedCnf originalClauses subsumedClauses
      strengthenedClauses cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AySubsumptionStep
      originalClauses subsumedClauses strengthenedClauses := by
  intro accepted
  exact ay_pss_conj_left
    (AySubsumptionStep
      originalClauses subsumedClauses strengthenedClauses)
    (AySubsumptionGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pss_conj_right
      (AyPreprocessMap originalCnf preprocessedCnf)
      (AyConj
        (AySubsumptionStep
          originalClauses subsumedClauses strengthenedClauses)
        (AySubsumptionGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      accepted)

theorem ay_pss_report_guards
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedSubsumptionReport
      originalCnf preprocessedCnf originalClauses subsumedClauses
      strengthenedClauses cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AySubsumptionGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest := by
  intro accepted
  exact ay_pss_conj_right
    (AySubsumptionStep
      originalClauses subsumedClauses strengthenedClauses)
    (AySubsumptionGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pss_conj_right
      (AyPreprocessMap originalCnf preprocessedCnf)
      (AyConj
        (AySubsumptionStep
          originalClauses subsumedClauses strengthenedClauses)
        (AySubsumptionGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      accepted)

theorem ay_pss_step_original_subsumed
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) :
    AySubsumptionStep
      originalClauses subsumedClauses strengthenedClauses ->
    originalClauses ->
    subsumedClauses := by
  intro step
  exact ay_pss_conj_left
    (originalClauses -> subsumedClauses)
    (strengthenedClauses -> subsumedClauses)
    step

theorem ay_pss_step_strengthened_subsumed
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) :
    AySubsumptionStep
      originalClauses subsumedClauses strengthenedClauses ->
    strengthenedClauses ->
    subsumedClauses := by
  intro step
  exact ay_pss_conj_right
    (originalClauses -> subsumedClauses)
    (strengthenedClauses -> subsumedClauses)
    step

theorem ay_pss_accepted_semantics
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedSubsumptionReport
      originalCnf preprocessedCnf originalClauses subsumedClauses
      strengthenedClauses cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyEquisat originalCnf preprocessedCnf := by
  intro accepted
  exact ay_pss_report_map originalCnf preprocessedCnf
    originalClauses subsumedClauses strengthenedClauses cachedEpoch
    currentEpoch cachedManifest runManifest cachedDigest runDigest accepted

theorem ay_pss_sat_forward
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (model : Prop) :
    AyAcceptedSubsumptionReport
      originalCnf preprocessedCnf originalClauses subsumedClauses
      strengthenedClauses cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AySat originalCnf model ->
    AySat preprocessedCnf model := by
  intro accepted
  intro sat
  exact ay_pss_conj_intro preprocessedCnf model
    (ay_pss_equisat_forward originalCnf preprocessedCnf
      (ay_pss_accepted_semantics originalCnf preprocessedCnf
        originalClauses subsumedClauses strengthenedClauses cachedEpoch
        currentEpoch cachedManifest runManifest cachedDigest runDigest
        accepted)
      (ay_pss_sat_cnf originalCnf model sat))
    (ay_pss_sat_model originalCnf model sat)

theorem ay_pss_sat_backward
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (model : Prop) :
    AyAcceptedSubsumptionReport
      originalCnf preprocessedCnf originalClauses subsumedClauses
      strengthenedClauses cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AySat preprocessedCnf model ->
    AySat originalCnf model := by
  intro accepted
  intro sat
  exact ay_pss_conj_intro originalCnf model
    (ay_pss_equisat_backward originalCnf preprocessedCnf
      (ay_pss_accepted_semantics originalCnf preprocessedCnf
        originalClauses subsumedClauses strengthenedClauses cachedEpoch
        currentEpoch cachedManifest runManifest cachedDigest runDigest
        accepted)
      (ay_pss_sat_cnf preprocessedCnf model sat))
    (ay_pss_sat_model preprocessedCnf model sat)

theorem ay_pss_unsat_pushback
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedSubsumptionReport
      originalCnf preprocessedCnf originalClauses subsumedClauses
      strengthenedClauses cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyReplay preprocessedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_pss_equisat_forward originalCnf preprocessedCnf
      (ay_pss_accepted_semantics originalCnf preprocessedCnf
        originalClauses subsumedClauses strengthenedClauses cachedEpoch
        currentEpoch cachedManifest runManifest cachedDigest runDigest
        accepted)
      horiginal)
    hcertificate

theorem ay_pss_accepted_log_report
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedSubsumptionLogEntry
      previousLog nextLog originalCnf preprocessedCnf
      originalClauses subsumedClauses strengthenedClauses cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyAcceptedSubsumptionReport
      originalCnf preprocessedCnf originalClauses subsumedClauses
      strengthenedClauses cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest := by
  intro entry
  exact ay_pss_conj_left
    (AyAcceptedSubsumptionReport
      originalCnf preprocessedCnf originalClauses subsumedClauses
      strengthenedClauses cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest)
    nextLog
    (ay_pss_conj_right previousLog
      (AyConj
        (AyAcceptedSubsumptionReport
          originalCnf preprocessedCnf originalClauses subsumedClauses
          strengthenedClauses cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest)
        nextLog)
      entry)

theorem ay_pss_accepted_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedSubsumptionLogEntry
      previousLog nextLog originalCnf preprocessedCnf
      originalClauses subsumedClauses strengthenedClauses cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyConj previousLog nextLog := by
  intro entry
  exact ay_pss_conj_intro previousLog nextLog
    (ay_pss_conj_left previousLog
      (AyConj
        (AyAcceptedSubsumptionReport
          originalCnf preprocessedCnf originalClauses subsumedClauses
          strengthenedClauses cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest)
        nextLog)
      entry)
    (ay_pss_conj_right
      (AyAcceptedSubsumptionReport
        originalCnf preprocessedCnf originalClauses subsumedClauses
        strengthenedClauses cachedEpoch currentEpoch cachedManifest
        runManifest cachedDigest runDigest)
      nextLog
      (ay_pss_conj_right previousLog
        (AyConj
          (AyAcceptedSubsumptionReport
            originalCnf preprocessedCnf originalClauses subsumedClauses
            strengthenedClauses cachedEpoch currentEpoch cachedManifest
            runManifest cachedDigest runDigest)
          nextLog)
        entry))

theorem ay_pss_public_sat_from_preprocessed
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (model : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    AyAcceptedSubsumptionLogEntry
      previousLog nextLog originalCnf preprocessedCnf
      originalClauses subsumedClauses strengthenedClauses cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AySat preprocessedCnf model ->
    exitCode ->
    AyPublicResult originalCnf model certificate conflict exitCode := by
  intro entry
  intro sat
  intro hexit
  exact ay_pss_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf model))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pss_conj_intro exitCode (AySat originalCnf model)
      hexit
      (ay_pss_sat_backward originalCnf preprocessedCnf
        originalClauses subsumedClauses strengthenedClauses cachedEpoch
        currentEpoch cachedManifest runManifest cachedDigest runDigest
        model
        (ay_pss_accepted_log_report previousLog nextLog
          originalCnf preprocessedCnf originalClauses subsumedClauses
          strengthenedClauses cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest entry)
        sat))

theorem ay_pss_public_unsat_from_preprocessed
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (model : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    AyAcceptedSubsumptionLogEntry
      previousLog nextLog originalCnf preprocessedCnf
      originalClauses subsumedClauses strengthenedClauses cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyReplay preprocessedCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf model certificate conflict exitCode := by
  intro entry
  intro replay
  intro hexit
  exact ay_pss_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf model))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pss_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (ay_pss_unsat_pushback originalCnf preprocessedCnf
        originalClauses subsumedClauses strengthenedClauses cachedEpoch
        currentEpoch cachedManifest runManifest cachedDigest runDigest
        certificate conflict
        (ay_pss_accepted_log_report previousLog nextLog
          originalCnf preprocessedCnf originalClauses subsumedClauses
          strengthenedClauses cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest entry)
        replay))

theorem ay_pss_failure_bad_dropped_literal
    (badDroppedLiteral : Prop) (staleReplay : Prop)
    (digestMismatch : Prop) :
    badDroppedLiteral ->
    AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch := by
  intro hbad
  exact ay_pss_disj_left badDroppedLiteral
    (AyDisj staleReplay digestMismatch)
    hbad

theorem ay_pss_failure_stale_replay
    (badDroppedLiteral : Prop) (staleReplay : Prop)
    (digestMismatch : Prop) :
    staleReplay ->
    AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch := by
  intro hstale
  exact ay_pss_disj_right badDroppedLiteral
    (AyDisj staleReplay digestMismatch)
    (ay_pss_disj_left staleReplay digestMismatch hstale)

theorem ay_pss_failure_digest_mismatch
    (badDroppedLiteral : Prop) (staleReplay : Prop)
    (digestMismatch : Prop) :
    digestMismatch ->
    AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch := by
  intro hdigest
  exact ay_pss_disj_right badDroppedLiteral
    (AyDisj staleReplay digestMismatch)
    (ay_pss_disj_right staleReplay digestMismatch hdigest)

theorem ay_pss_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (badDroppedLiteral : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticSubsumptionLogEntry
      previousLog nextLog currentCnf badDroppedLiteral staleReplay
      digestMismatch recompute diagnostic ->
    AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch := by
  intro entry
  exact ay_pss_conj_left
    (AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pss_conj_left
      (AyConj
        (AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch)
        (AyConj
          (AyRecomputeObligation currentCnf recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pss_conj_right previousLog
        (AyConj
          (AyConj
            (AySubsumptionFailure
              badDroppedLiteral staleReplay digestMismatch)
            (AyConj
              (AyRecomputeObligation currentCnf recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pss_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (badDroppedLiteral : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticSubsumptionLogEntry
      previousLog nextLog currentCnf badDroppedLiteral staleReplay
      digestMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pss_conj_right
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pss_conj_right
      (AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pss_conj_left
        (AyConj
          (AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pss_conj_right previousLog
          (AyConj
            (AyConj
              (AySubsumptionFailure
                badDroppedLiteral staleReplay digestMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pss_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (badDroppedLiteral : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticSubsumptionLogEntry
      previousLog nextLog currentCnf badDroppedLiteral staleReplay
      digestMismatch recompute diagnostic ->
    AyRecomputeObligation currentCnf recompute := by
  intro entry
  exact ay_pss_conj_left
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pss_conj_right
      (AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pss_conj_left
        (AyConj
          (AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pss_conj_right previousLog
          (AyConj
            (AyConj
              (AySubsumptionFailure
                badDroppedLiteral staleReplay digestMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_preprocess_subsumption_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (badDroppedLiteral : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticSubsumptionLogEntry
      previousLog nextLog currentCnf badDroppedLiteral staleReplay
      digestMismatch recompute diagnostic ->
    AyConj
      (AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pss_conj_intro
    (AySubsumptionFailure badDroppedLiteral staleReplay digestMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pss_diagnostic_failure previousLog nextLog currentCnf
      badDroppedLiteral staleReplay digestMismatch recompute diagnostic entry)
    (ay_pss_conj_intro
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pss_diagnostic_recompute previousLog nextLog currentCnf
        badDroppedLiteral staleReplay digestMismatch recompute diagnostic entry)
      (ay_pss_diagnostic_no_claim previousLog nextLog currentCnf
        badDroppedLiteral staleReplay digestMismatch recompute diagnostic entry))
