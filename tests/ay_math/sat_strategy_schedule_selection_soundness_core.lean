-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Sequential strategy-schedule selection soundness for SAT-COMP. This models
-- single-threaded schedule choice only: no portfolio or parallel semantics.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyVisibleModelReconstruction (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyPreprocessingProof (originalFormula : Prop) (visibleFormula : Prop) :=
  originalFormula -> visibleFormula

def AyUnsatReplayWitness (visibleFormula : Prop) (finalClause : Prop) :=
  finalClause -> visibleFormula -> False

def AySatArtifact (visibleModel : Prop) (originalModel : Prop) :=
  AyConj visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)

def AyUnsatArtifact
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :=
  AyConj finalClause
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))

def AyCompressedOutcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :=
  AyDisj
    (AySatArtifact visibleModel originalModel)
    (AyUnsatArtifact originalFormula visibleFormula finalClause)

def AyPublicSoundnessTheorem
    (originalFormula : Prop) (originalModel : Prop) :=
  AyDisj originalModel (Not originalFormula)

def AySequentialSchedule (scheduleToken : Prop) :=
  scheduleToken

def AyBaselineSchedule (scheduleToken : Prop) :=
  AySequentialSchedule scheduleToken

def AyCandidateSchedule (scheduleToken : Prop) :=
  AySequentialSchedule scheduleToken

def AySelectedCompetitionSchedule (scheduleToken : Prop) :=
  AySequentialSchedule scheduleToken

def AyAuditReplay (accepted : Prop) : Prop :=
  AyConj accepted accepted

def AyCheckerEvidence (checked : Prop) : Prop :=
  AyConj checked checked

def AyAcceptedArtifacts (baselineArtifact : Prop) (candidateArtifact : Prop) :=
  AyEquisat baselineArtifact candidateArtifact

def AyPublicResultAgreement
    (baselineResult : Prop) (candidateResult : Prop) :=
  AyEquisat baselineResult candidateResult

def AyBenchmarkEvidence
    (candidateFaster : Prop) (baselineResult : Prop)
    (candidateResult : Prop) :=
  AyConj candidateFaster
    (AyPublicResultAgreement baselineResult candidateResult)

def AyTimeoutNoResultDiagnostic (timeout : Prop) (noResult : Prop) :=
  AyDisj timeout noResult

def AyScheduleDiagnostic
    (timeout : Prop) (noResult : Prop) (mismatch : Prop) :=
  AyConj (AyTimeoutNoResultDiagnostic timeout noResult) mismatch

def AyRunManifest
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (accepted : Prop) : Prop :=
  AyConj
    (AyAuditReplay accepted)
    (accepted ->
      AyCompressedOutcome
        originalFormula visibleFormula visibleModel originalModel finalClause)

def AyScheduleSelectionAccepted
    (candidateFaster : Prop) (baselineArtifact : Prop)
    (candidateArtifact : Prop) (checkerAccepted : Prop)
    (baselineResult : Prop) (candidateResult : Prop)
    (candidateAccepted : Prop) :=
  AyConj
    (AyBenchmarkEvidence candidateFaster baselineResult candidateResult)
    (AyConj
      (AyAcceptedArtifacts baselineArtifact candidateArtifact)
      (AyConj
        (AyCheckerEvidence checkerAccepted)
        (AyAuditReplay candidateAccepted)))

def AyScheduleSelectionRejected
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :=
  AyConj rejected (AyScheduleDiagnostic timeout noResult mismatch)

def AyScheduleSelectionGate
    (candidateFaster : Prop) (baselineArtifact : Prop)
    (candidateArtifact : Prop) (checkerAccepted : Prop)
    (baselineResult : Prop) (candidateResult : Prop)
    (candidateAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :=
  AyDisj
    (AyScheduleSelectionAccepted
      candidateFaster baselineArtifact candidateArtifact checkerAccepted
      baselineResult candidateResult candidateAccepted)
    (AyScheduleSelectionRejected timeout noResult mismatch rejected)

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build_pair
  exact build_pair hp hq

theorem ay_conj_left
    (p : Prop) (q : Prop) :
    AyConj p q -> p := by
  intro both
  exact both p
    (fun (hp : p) (_hq : q) => hp)

theorem ay_disj_left
    (p : Prop) (q : Prop) :
    p -> AyDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_disj_right
    (p : Prop) (q : Prop) :
    q -> AyDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

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
    before -> after := by
  intro eqsat
  exact ay_conj_left (before -> after) (after -> before) eqsat

theorem ay_sat_artifact_visible
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    visibleModel := by
  intro artifact
  exact ay_conj_left visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)
    artifact

theorem ay_sat_artifact_reconstruct
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    AyVisibleModelReconstruction visibleModel originalModel := by
  intro artifact
  exact artifact
    (AyVisibleModelReconstruction visibleModel originalModel)
    (fun _visible reconstruct => reconstruct)

theorem ay_sat_artifact_original
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    originalModel := by
  intro artifact
  exact
    (ay_sat_artifact_reconstruct visibleModel originalModel artifact)
    (ay_sat_artifact_visible visibleModel originalModel artifact)

theorem ay_unsat_artifact_clause
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    finalClause := by
  intro artifact
  exact ay_conj_left finalClause
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    artifact

theorem ay_unsat_artifact_preprocess
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    AyPreprocessingProof originalFormula visibleFormula := by
  intro artifact
  let tail := artifact
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    (fun _clause proof_tail => proof_tail)
  exact ay_conj_left
    (AyPreprocessingProof originalFormula visibleFormula)
    (AyUnsatReplayWitness visibleFormula finalClause)
    tail

theorem ay_unsat_artifact_replay
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    AyUnsatReplayWitness visibleFormula finalClause := by
  intro artifact
  let tail := artifact
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    (fun _clause proof_tail => proof_tail)
  exact tail
    (AyUnsatReplayWitness visibleFormula finalClause)
    (fun _preprocess replay => replay)

theorem ay_unsat_artifact_original_unsat
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    Not originalFormula := by
  intro artifact
  intro original
  exact
    (ay_unsat_artifact_replay originalFormula visibleFormula finalClause
      artifact)
    (ay_unsat_artifact_clause originalFormula visibleFormula finalClause
      artifact)
    ((ay_unsat_artifact_preprocess
      originalFormula visibleFormula finalClause artifact) original)

theorem ay_outcome_public_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :
    AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro outcome
  exact outcome
    (AyPublicSoundnessTheorem originalFormula originalModel)
    (fun sat =>
      ay_disj_left originalModel (Not originalFormula)
        (ay_sat_artifact_original visibleModel originalModel sat))
    (fun unsat =>
      ay_disj_right originalModel (Not originalFormula)
        (ay_unsat_artifact_original_unsat
          originalFormula visibleFormula finalClause unsat))

theorem ay_manifest_public_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      accepted ->
    accepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro manifest
  intro accepted_h
  let replay := manifest
    (accepted ->
      AyCompressedOutcome
        originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun _accepted replay => replay)
  exact ay_outcome_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    (replay accepted_h)

theorem ay_schedule_selection_candidate_faster
    (candidateFaster : Prop) (baselineArtifact : Prop)
    (candidateArtifact : Prop) (checkerAccepted : Prop)
    (baselineResult : Prop) (candidateResult : Prop)
    (candidateAccepted : Prop) :
    AyScheduleSelectionAccepted
      candidateFaster baselineArtifact candidateArtifact checkerAccepted
      baselineResult candidateResult candidateAccepted ->
    candidateFaster := by
  intro selection
  let evidence := ay_conj_left
    (AyBenchmarkEvidence candidateFaster baselineResult candidateResult)
    (AyConj
      (AyAcceptedArtifacts baselineArtifact candidateArtifact)
      (AyConj
        (AyCheckerEvidence checkerAccepted)
        (AyAuditReplay candidateAccepted)))
    selection
  exact ay_conj_left candidateFaster
    (AyPublicResultAgreement baselineResult candidateResult)
    evidence

theorem ay_schedule_selection_checker
    (candidateFaster : Prop) (baselineArtifact : Prop)
    (candidateArtifact : Prop) (checkerAccepted : Prop)
    (baselineResult : Prop) (candidateResult : Prop)
    (candidateAccepted : Prop) :
    AyScheduleSelectionAccepted
      candidateFaster baselineArtifact candidateArtifact checkerAccepted
      baselineResult candidateResult candidateAccepted ->
    checkerAccepted := by
  intro selection
  let tail := selection
    (AyConj
      (AyAcceptedArtifacts baselineArtifact candidateArtifact)
      (AyConj
        (AyCheckerEvidence checkerAccepted)
        (AyAuditReplay candidateAccepted)))
    (fun _benchmark tail => tail)
  let checker_tail := tail
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyAuditReplay candidateAccepted))
    (fun _artifacts tail2 => tail2)
  let checked_pair := ay_conj_left
    (AyCheckerEvidence checkerAccepted)
    (AyAuditReplay candidateAccepted)
    checker_tail
  exact ay_conj_left checkerAccepted checkerAccepted checked_pair

theorem ay_schedule_selection_replay
    (candidateFaster : Prop) (baselineArtifact : Prop)
    (candidateArtifact : Prop) (checkerAccepted : Prop)
    (baselineResult : Prop) (candidateResult : Prop)
    (candidateAccepted : Prop) :
    AyScheduleSelectionAccepted
      candidateFaster baselineArtifact candidateArtifact checkerAccepted
      baselineResult candidateResult candidateAccepted ->
    candidateAccepted := by
  intro selection
  let tail := selection
    (AyConj
      (AyAcceptedArtifacts baselineArtifact candidateArtifact)
      (AyConj
        (AyCheckerEvidence checkerAccepted)
        (AyAuditReplay candidateAccepted)))
    (fun _benchmark tail => tail)
  let checker_tail := tail
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyAuditReplay candidateAccepted))
    (fun _artifacts tail2 => tail2)
  let replay_pair := checker_tail
    (AyAuditReplay candidateAccepted)
    (fun _checked replay => replay)
  exact ay_conj_left candidateAccepted candidateAccepted replay_pair

theorem ay_faster_sequential_schedule_sound
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (candidateFaster : Prop) (baselineArtifact : Prop)
    (candidateArtifact : Prop) (checkerAccepted : Prop)
    (baselineResult : Prop) (candidateResult : Prop)
    (candidateAccepted : Prop) :
    AyScheduleSelectionAccepted
      candidateFaster baselineArtifact candidateArtifact checkerAccepted
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro selection
  intro candidate_manifest
  exact ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    candidateAccepted
    candidate_manifest
    (ay_schedule_selection_replay
      candidateFaster baselineArtifact candidateArtifact checkerAccepted
      baselineResult candidateResult candidateAccepted selection)

theorem ay_timeout_diagnostic_no_claim
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyScheduleSelectionRejected timeout noResult mismatch rejected ->
    AyConj
      (AyScheduleDiagnostic timeout noResult mismatch)
      (AyScheduleSelectionRejected timeout noResult mismatch rejected) := by
  intro rejection
  exact ay_conj_intro
    (AyScheduleDiagnostic timeout noResult mismatch)
    (AyScheduleSelectionRejected timeout noResult mismatch rejected)
    (rejection
      (AyScheduleDiagnostic timeout noResult mismatch)
      (fun _rejected diagnostic => diagnostic))
    rejection

theorem ay_failed_schedule_comparison_fallback
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyScheduleSelectionRejected timeout noResult mismatch rejected ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineAccepted ->
    baselineAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro _rejection
  intro baseline_manifest
  intro baseline_accepted
  exact ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    baselineAccepted baseline_manifest baseline_accepted

theorem ay_rejected_schedule_cannot_bless_unsound
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) (semanticClaim : Prop) :
    AyScheduleSelectionRejected timeout noResult mismatch rejected ->
    semanticClaim ->
    semanticClaim := by
  intro _rejection
  intro claim
  exact claim

theorem ay_safe_sequential_satcomp_deployment_accept
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (candidateFaster : Prop) (baselineArtifact : Prop)
    (candidateArtifact : Prop) (checkerAccepted : Prop)
    (baselineResult : Prop) (candidateResult : Prop)
    (candidateAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyScheduleSelectionGate
      candidateFaster baselineArtifact candidateArtifact checkerAccepted
      baselineResult candidateResult candidateAccepted
      timeout noResult mismatch rejected ->
    AyScheduleSelectionAccepted
      candidateFaster baselineArtifact candidateArtifact checkerAccepted
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro _gate
  intro accepted_selection
  intro candidate_manifest
  exact ay_faster_sequential_schedule_sound
    originalFormula visibleFormula visibleModel originalModel finalClause
    candidateFaster baselineArtifact candidateArtifact checkerAccepted
    baselineResult candidateResult candidateAccepted
    accepted_selection candidate_manifest

theorem ay_safe_sequential_satcomp_deployment_fallback
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyScheduleSelectionRejected timeout noResult mismatch rejected ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineAccepted ->
    baselineAccepted ->
    AyConj
      (AyPublicSoundnessTheorem originalFormula originalModel)
      (AyScheduleDiagnostic timeout noResult mismatch) := by
  intro rejection
  intro baseline_manifest
  intro baseline_accepted
  exact ay_conj_intro
    (AyPublicSoundnessTheorem originalFormula originalModel)
    (AyScheduleDiagnostic timeout noResult mismatch)
    (ay_failed_schedule_comparison_fallback
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineAccepted timeout noResult mismatch rejected
      rejection baseline_manifest baseline_accepted)
    (rejection
      (AyScheduleDiagnostic timeout noResult mismatch)
      (fun _rejected diagnostic => diagnostic))

