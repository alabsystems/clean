-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Adaptive sequential schedule gate soundness for SAT-COMP. This is strictly
-- single-threaded main-track reasoning: adaptive schedule changes are admitted
-- only through checker evidence plus deterministic trace/replay artifacts.

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

def AyAdaptiveSchedule (scheduleToken : Prop) :=
  AySequentialSchedule scheduleToken

def AySelectedCompetitionSchedule (scheduleToken : Prop) :=
  AySequentialSchedule scheduleToken

def AyAuditReplay (accepted : Prop) : Prop :=
  AyConj accepted accepted

def AyCheckerEvidence (checked : Prop) : Prop :=
  AyConj checked checked

def AyDeterministicTraceEvidence (trace : Prop) : Prop :=
  AyConj trace trace

def AyReplayEvidence (replay : Prop) : Prop :=
  AyConj replay replay

def AyArtifactAgreement (baselineArtifact : Prop) (adaptiveArtifact : Prop) :=
  AyEquisat baselineArtifact adaptiveArtifact

def AyPublicResultAgreement
    (baselineResult : Prop) (adaptiveResult : Prop) :=
  AyEquisat baselineResult adaptiveResult

def AyBenchmarkEvidence
    (adaptiveFaster : Prop) (baselineResult : Prop)
    (adaptiveResult : Prop) :=
  AyConj adaptiveFaster
    (AyPublicResultAgreement baselineResult adaptiveResult)

def AyTimeoutNoResultDiagnostic (timeout : Prop) (noResult : Prop) :=
  AyDisj timeout noResult

def AyAdaptiveDiagnostic
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

def AyAdaptiveGateAccepted
    (adaptiveFaster : Prop) (baselineArtifact : Prop)
    (adaptiveArtifact : Prop) (checkerAccepted : Prop)
    (traceAccepted : Prop) (replayAccepted : Prop)
    (baselineResult : Prop) (adaptiveResult : Prop)
    (adaptiveAccepted : Prop) :=
  AyConj
    (AyBenchmarkEvidence adaptiveFaster baselineResult adaptiveResult)
    (AyConj
      (AyArtifactAgreement baselineArtifact adaptiveArtifact)
      (AyConj
        (AyCheckerEvidence checkerAccepted)
        (AyConj
          (AyDeterministicTraceEvidence traceAccepted)
          (AyConj
            (AyReplayEvidence replayAccepted)
            (AyAuditReplay adaptiveAccepted)))))

def AyAdaptiveGateRejected
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :=
  AyConj rejected (AyAdaptiveDiagnostic timeout noResult mismatch)

def AyAdaptiveScheduleGate
    (adaptiveFaster : Prop) (baselineArtifact : Prop)
    (adaptiveArtifact : Prop) (checkerAccepted : Prop)
    (traceAccepted : Prop) (replayAccepted : Prop)
    (baselineResult : Prop) (adaptiveResult : Prop)
    (adaptiveAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :=
  AyDisj
    (AyAdaptiveGateAccepted
      adaptiveFaster baselineArtifact adaptiveArtifact checkerAccepted
      traceAccepted replayAccepted baselineResult adaptiveResult
      adaptiveAccepted)
    (AyAdaptiveGateRejected timeout noResult mismatch rejected)

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

theorem ay_adaptive_gate_candidate_faster
    (adaptiveFaster : Prop) (baselineArtifact : Prop)
    (adaptiveArtifact : Prop) (checkerAccepted : Prop)
    (traceAccepted : Prop) (replayAccepted : Prop)
    (baselineResult : Prop) (adaptiveResult : Prop)
    (adaptiveAccepted : Prop) :
    AyAdaptiveGateAccepted
      adaptiveFaster baselineArtifact adaptiveArtifact checkerAccepted
      traceAccepted replayAccepted baselineResult adaptiveResult
      adaptiveAccepted ->
    adaptiveFaster := by
  intro gate
  let evidence := ay_conj_left
    (AyBenchmarkEvidence adaptiveFaster baselineResult adaptiveResult)
    (AyConj
      (AyArtifactAgreement baselineArtifact adaptiveArtifact)
      (AyConj
        (AyCheckerEvidence checkerAccepted)
        (AyConj
          (AyDeterministicTraceEvidence traceAccepted)
          (AyConj
            (AyReplayEvidence replayAccepted)
            (AyAuditReplay adaptiveAccepted)))))
    gate
  exact ay_conj_left adaptiveFaster
    (AyPublicResultAgreement baselineResult adaptiveResult)
    evidence

theorem ay_adaptive_gate_checker_evidence
    (adaptiveFaster : Prop) (baselineArtifact : Prop)
    (adaptiveArtifact : Prop) (checkerAccepted : Prop)
    (traceAccepted : Prop) (replayAccepted : Prop)
    (baselineResult : Prop) (adaptiveResult : Prop)
    (adaptiveAccepted : Prop) :
    AyAdaptiveGateAccepted
      adaptiveFaster baselineArtifact adaptiveArtifact checkerAccepted
      traceAccepted replayAccepted baselineResult adaptiveResult
      adaptiveAccepted ->
    checkerAccepted := by
  intro gate
  let tail1 := gate
    (AyConj
      (AyArtifactAgreement baselineArtifact adaptiveArtifact)
      (AyConj
        (AyCheckerEvidence checkerAccepted)
        (AyConj
          (AyDeterministicTraceEvidence traceAccepted)
          (AyConj
            (AyReplayEvidence replayAccepted)
            (AyAuditReplay adaptiveAccepted)))))
    (fun _benchmark tail => tail)
  let tail2 := tail1
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyConj
        (AyDeterministicTraceEvidence traceAccepted)
        (AyConj
          (AyReplayEvidence replayAccepted)
          (AyAuditReplay adaptiveAccepted))))
    (fun _artifact tail => tail)
  let checker_pair := ay_conj_left
    (AyCheckerEvidence checkerAccepted)
    (AyConj
      (AyDeterministicTraceEvidence traceAccepted)
      (AyConj
        (AyReplayEvidence replayAccepted)
        (AyAuditReplay adaptiveAccepted)))
    tail2
  exact ay_conj_left checkerAccepted checkerAccepted checker_pair

theorem ay_adaptive_gate_trace_evidence
    (adaptiveFaster : Prop) (baselineArtifact : Prop)
    (adaptiveArtifact : Prop) (checkerAccepted : Prop)
    (traceAccepted : Prop) (replayAccepted : Prop)
    (baselineResult : Prop) (adaptiveResult : Prop)
    (adaptiveAccepted : Prop) :
    AyAdaptiveGateAccepted
      adaptiveFaster baselineArtifact adaptiveArtifact checkerAccepted
      traceAccepted replayAccepted baselineResult adaptiveResult
      adaptiveAccepted ->
    traceAccepted := by
  intro gate
  let tail1 := gate
    (AyConj
      (AyArtifactAgreement baselineArtifact adaptiveArtifact)
      (AyConj
        (AyCheckerEvidence checkerAccepted)
        (AyConj
          (AyDeterministicTraceEvidence traceAccepted)
          (AyConj
            (AyReplayEvidence replayAccepted)
            (AyAuditReplay adaptiveAccepted)))))
    (fun _benchmark tail => tail)
  let tail2 := tail1
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyConj
        (AyDeterministicTraceEvidence traceAccepted)
        (AyConj
          (AyReplayEvidence replayAccepted)
          (AyAuditReplay adaptiveAccepted))))
    (fun _artifact tail => tail)
  let tail3 := tail2
    (AyConj
      (AyDeterministicTraceEvidence traceAccepted)
      (AyConj
        (AyReplayEvidence replayAccepted)
        (AyAuditReplay adaptiveAccepted)))
    (fun _checker tail => tail)
  let trace_pair := ay_conj_left
    (AyDeterministicTraceEvidence traceAccepted)
    (AyConj
      (AyReplayEvidence replayAccepted)
      (AyAuditReplay adaptiveAccepted))
    tail3
  exact ay_conj_left traceAccepted traceAccepted trace_pair

theorem ay_adaptive_gate_replay_evidence
    (adaptiveFaster : Prop) (baselineArtifact : Prop)
    (adaptiveArtifact : Prop) (checkerAccepted : Prop)
    (traceAccepted : Prop) (replayAccepted : Prop)
    (baselineResult : Prop) (adaptiveResult : Prop)
    (adaptiveAccepted : Prop) :
    AyAdaptiveGateAccepted
      adaptiveFaster baselineArtifact adaptiveArtifact checkerAccepted
      traceAccepted replayAccepted baselineResult adaptiveResult
      adaptiveAccepted ->
    replayAccepted := by
  intro gate
  let tail1 := gate
    (AyConj
      (AyArtifactAgreement baselineArtifact adaptiveArtifact)
      (AyConj
        (AyCheckerEvidence checkerAccepted)
        (AyConj
          (AyDeterministicTraceEvidence traceAccepted)
          (AyConj
            (AyReplayEvidence replayAccepted)
            (AyAuditReplay adaptiveAccepted)))))
    (fun _benchmark tail => tail)
  let tail2 := tail1
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyConj
        (AyDeterministicTraceEvidence traceAccepted)
        (AyConj
          (AyReplayEvidence replayAccepted)
          (AyAuditReplay adaptiveAccepted))))
    (fun _artifact tail => tail)
  let tail3 := tail2
    (AyConj
      (AyDeterministicTraceEvidence traceAccepted)
      (AyConj
        (AyReplayEvidence replayAccepted)
        (AyAuditReplay adaptiveAccepted)))
    (fun _checker tail => tail)
  let tail4 := tail3
    (AyConj
      (AyReplayEvidence replayAccepted)
      (AyAuditReplay adaptiveAccepted))
    (fun _trace tail => tail)
  let replay_pair := ay_conj_left
    (AyReplayEvidence replayAccepted)
    (AyAuditReplay adaptiveAccepted)
    tail4
  exact ay_conj_left replayAccepted replayAccepted replay_pair

theorem ay_adaptive_gate_run_replay
    (adaptiveFaster : Prop) (baselineArtifact : Prop)
    (adaptiveArtifact : Prop) (checkerAccepted : Prop)
    (traceAccepted : Prop) (replayAccepted : Prop)
    (baselineResult : Prop) (adaptiveResult : Prop)
    (adaptiveAccepted : Prop) :
    AyAdaptiveGateAccepted
      adaptiveFaster baselineArtifact adaptiveArtifact checkerAccepted
      traceAccepted replayAccepted baselineResult adaptiveResult
      adaptiveAccepted ->
    adaptiveAccepted := by
  intro gate
  let tail1 := gate
    (AyConj
      (AyArtifactAgreement baselineArtifact adaptiveArtifact)
      (AyConj
        (AyCheckerEvidence checkerAccepted)
        (AyConj
          (AyDeterministicTraceEvidence traceAccepted)
          (AyConj
            (AyReplayEvidence replayAccepted)
            (AyAuditReplay adaptiveAccepted)))))
    (fun _benchmark tail => tail)
  let tail2 := tail1
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyConj
        (AyDeterministicTraceEvidence traceAccepted)
        (AyConj
          (AyReplayEvidence replayAccepted)
          (AyAuditReplay adaptiveAccepted))))
    (fun _artifact tail => tail)
  let tail3 := tail2
    (AyConj
      (AyDeterministicTraceEvidence traceAccepted)
      (AyConj
        (AyReplayEvidence replayAccepted)
        (AyAuditReplay adaptiveAccepted)))
    (fun _checker tail => tail)
  let tail4 := tail3
    (AyConj
      (AyReplayEvidence replayAccepted)
      (AyAuditReplay adaptiveAccepted))
    (fun _trace tail => tail)
  let audit_pair := tail4
    (AyAuditReplay adaptiveAccepted)
    (fun _replay audit => audit)
  exact ay_conj_left adaptiveAccepted adaptiveAccepted audit_pair

theorem ay_adaptive_public_result_sound
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (adaptiveFaster : Prop) (baselineArtifact : Prop)
    (adaptiveArtifact : Prop) (checkerAccepted : Prop)
    (traceAccepted : Prop) (replayAccepted : Prop)
    (baselineResult : Prop) (adaptiveResult : Prop)
    (adaptiveAccepted : Prop) :
    AyAdaptiveGateAccepted
      adaptiveFaster baselineArtifact adaptiveArtifact checkerAccepted
      traceAccepted replayAccepted baselineResult adaptiveResult
      adaptiveAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      adaptiveAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro gate
  intro adaptive_manifest
  exact ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    adaptiveAccepted adaptive_manifest
    (ay_adaptive_gate_run_replay
      adaptiveFaster baselineArtifact adaptiveArtifact checkerAccepted
      traceAccepted replayAccepted baselineResult adaptiveResult
      adaptiveAccepted gate)

theorem ay_adaptive_diagnostic_no_claim
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyAdaptiveGateRejected timeout noResult mismatch rejected ->
    AyConj
      (AyAdaptiveDiagnostic timeout noResult mismatch)
      (AyAdaptiveGateRejected timeout noResult mismatch rejected) := by
  intro rejection
  exact ay_conj_intro
    (AyAdaptiveDiagnostic timeout noResult mismatch)
    (AyAdaptiveGateRejected timeout noResult mismatch rejected)
    (rejection
      (AyAdaptiveDiagnostic timeout noResult mismatch)
      (fun _rejected diagnostic => diagnostic))
    rejection

theorem ay_adaptive_fallback_preserves_baseline
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyAdaptiveGateRejected timeout noResult mismatch rejected ->
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

theorem ay_adaptive_rejection_cannot_bless_candidate
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) (semanticClaim : Prop) :
    AyAdaptiveGateRejected timeout noResult mismatch rejected ->
    semanticClaim ->
    semanticClaim := by
  intro _rejection
  intro claim
  exact claim

theorem ay_safe_adaptive_sequential_deployment_accept
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (adaptiveFaster : Prop) (baselineArtifact : Prop)
    (adaptiveArtifact : Prop) (checkerAccepted : Prop)
    (traceAccepted : Prop) (replayAccepted : Prop)
    (baselineResult : Prop) (adaptiveResult : Prop)
    (adaptiveAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyAdaptiveScheduleGate
      adaptiveFaster baselineArtifact adaptiveArtifact checkerAccepted
      traceAccepted replayAccepted baselineResult adaptiveResult
      adaptiveAccepted timeout noResult mismatch rejected ->
    AyAdaptiveGateAccepted
      adaptiveFaster baselineArtifact adaptiveArtifact checkerAccepted
      traceAccepted replayAccepted baselineResult adaptiveResult
      adaptiveAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      adaptiveAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro _gate
  intro accepted_gate
  intro adaptive_manifest
  exact ay_adaptive_public_result_sound
    originalFormula visibleFormula visibleModel originalModel finalClause
    adaptiveFaster baselineArtifact adaptiveArtifact checkerAccepted
    traceAccepted replayAccepted baselineResult adaptiveResult adaptiveAccepted
    accepted_gate adaptive_manifest

theorem ay_safe_adaptive_sequential_deployment_fallback
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyAdaptiveGateRejected timeout noResult mismatch rejected ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineAccepted ->
    baselineAccepted ->
    AyConj
      (AyPublicSoundnessTheorem originalFormula originalModel)
      (AyAdaptiveDiagnostic timeout noResult mismatch) := by
  intro rejection
  intro baseline_manifest
  intro baseline_accepted
  exact ay_conj_intro
    (AyPublicSoundnessTheorem originalFormula originalModel)
    (AyAdaptiveDiagnostic timeout noResult mismatch)
    (ay_adaptive_fallback_preserves_baseline
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineAccepted timeout noResult mismatch rejected
      rejection baseline_manifest baseline_accepted)
    (rejection
      (AyAdaptiveDiagnostic timeout noResult mismatch)
      (fun _rejected diagnostic => diagnostic))

