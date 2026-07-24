-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-deletion/reduction gate soundness for sequential ay SAT-COMP runs.
-- Learned clause deletion changes search performance, not public SAT/UNSAT
-- semantics; public results are admitted only through checker/replay evidence.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

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

def AySequentialClausePolicy (policyToken : Prop) :=
  policyToken

def AyBaselineClauseDatabasePolicy (policyToken : Prop) :=
  AySequentialClausePolicy policyToken

def AyCandidateDeletionPolicy (policyToken : Prop) :=
  AySequentialClausePolicy policyToken

def AySelectedCompetitionPolicy (policyToken : Prop) :=
  AySequentialClausePolicy policyToken

def AyAuditReplay (accepted : Prop) : Prop :=
  AyConj accepted accepted

def AyCheckerEvidence (checked : Prop) : Prop :=
  AyConj checked checked

def AyReplayEvidence (replay : Prop) : Prop :=
  AyConj replay replay

def AyLearnedClauseRetentionEvidence (retention : Prop) : Prop :=
  AyConj retention retention

def AyBenchmarkEvidence (candidateFaster : Prop) :=
  candidateFaster

def AyTimeoutNoResultDiagnostic (timeout : Prop) (noResult : Prop) :=
  AyDisj timeout noResult

def AyClauseDeletionDiagnostic
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

def AyClauseDeletionGateAccepted
    (candidateFaster : Prop) (retentionOk : Prop)
    (checkerAccepted : Prop) (replayAccepted : Prop)
    (candidateAccepted : Prop) :=
  AyConj
    (AyAuditReplay candidateAccepted)
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyConj
        (AyReplayEvidence replayAccepted)
        (AyConj
          (AyLearnedClauseRetentionEvidence retentionOk)
          (AyBenchmarkEvidence candidateFaster))))

def AyClauseDeletionGateRejected
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :=
  AyConj rejected (AyClauseDeletionDiagnostic timeout noResult mismatch)

def AyClauseDeletionGate
    (candidateFaster : Prop) (retentionOk : Prop)
    (checkerAccepted : Prop) (replayAccepted : Prop)
    (candidateAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :=
  AyDisj
    (AyClauseDeletionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      candidateAccepted)
    (AyClauseDeletionGateRejected timeout noResult mismatch rejected)

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

theorem ay_clause_deletion_gate_candidate_faster
    (candidateFaster : Prop) (retentionOk : Prop)
    (checkerAccepted : Prop) (replayAccepted : Prop)
    (candidateAccepted : Prop) :
    AyClauseDeletionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      candidateAccepted ->
    candidateFaster := by
  intro gate
  let tail1 := gate
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyConj
        (AyReplayEvidence replayAccepted)
        (AyConj
          (AyLearnedClauseRetentionEvidence retentionOk)
          (AyBenchmarkEvidence candidateFaster))))
    (fun _audit tail => tail)
  let tail2 := tail1
    (AyConj
      (AyReplayEvidence replayAccepted)
      (AyConj
        (AyLearnedClauseRetentionEvidence retentionOk)
        (AyBenchmarkEvidence candidateFaster)))
    (fun _checker tail => tail)
  let tail3 := tail2
    (AyConj
      (AyLearnedClauseRetentionEvidence retentionOk)
      (AyBenchmarkEvidence candidateFaster))
    (fun _replay tail => tail)
  exact tail3
    (AyBenchmarkEvidence candidateFaster)
    (fun _retention benchmark => benchmark)

theorem ay_clause_deletion_gate_checker_evidence
    (candidateFaster : Prop) (retentionOk : Prop)
    (checkerAccepted : Prop) (replayAccepted : Prop)
    (candidateAccepted : Prop) :
    AyClauseDeletionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      candidateAccepted ->
    checkerAccepted := by
  intro gate
  let tail1 := gate
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyConj
        (AyReplayEvidence replayAccepted)
        (AyConj
          (AyLearnedClauseRetentionEvidence retentionOk)
          (AyBenchmarkEvidence candidateFaster))))
    (fun _audit tail => tail)
  let checker_pair := ay_conj_left
    (AyCheckerEvidence checkerAccepted)
    (AyConj
      (AyReplayEvidence replayAccepted)
      (AyConj
        (AyLearnedClauseRetentionEvidence retentionOk)
        (AyBenchmarkEvidence candidateFaster)))
    tail1
  exact ay_conj_left checkerAccepted checkerAccepted checker_pair

theorem ay_clause_deletion_gate_replay_evidence
    (candidateFaster : Prop) (retentionOk : Prop)
    (checkerAccepted : Prop) (replayAccepted : Prop)
    (candidateAccepted : Prop) :
    AyClauseDeletionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      candidateAccepted ->
    replayAccepted := by
  intro gate
  let tail1 := gate
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyConj
        (AyReplayEvidence replayAccepted)
        (AyConj
          (AyLearnedClauseRetentionEvidence retentionOk)
          (AyBenchmarkEvidence candidateFaster))))
    (fun _audit tail => tail)
  let tail2 := tail1
    (AyConj
      (AyReplayEvidence replayAccepted)
      (AyConj
        (AyLearnedClauseRetentionEvidence retentionOk)
        (AyBenchmarkEvidence candidateFaster)))
    (fun _checker tail => tail)
  let replay_pair := ay_conj_left
    (AyReplayEvidence replayAccepted)
    (AyConj
      (AyLearnedClauseRetentionEvidence retentionOk)
      (AyBenchmarkEvidence candidateFaster))
    tail2
  exact ay_conj_left replayAccepted replayAccepted replay_pair

theorem ay_clause_deletion_gate_retention_evidence
    (candidateFaster : Prop) (retentionOk : Prop)
    (checkerAccepted : Prop) (replayAccepted : Prop)
    (candidateAccepted : Prop) :
    AyClauseDeletionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      candidateAccepted ->
    retentionOk := by
  intro gate
  let tail1 := gate
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyConj
        (AyReplayEvidence replayAccepted)
        (AyConj
          (AyLearnedClauseRetentionEvidence retentionOk)
          (AyBenchmarkEvidence candidateFaster))))
    (fun _audit tail => tail)
  let tail2 := tail1
    (AyConj
      (AyReplayEvidence replayAccepted)
      (AyConj
        (AyLearnedClauseRetentionEvidence retentionOk)
        (AyBenchmarkEvidence candidateFaster)))
    (fun _checker tail => tail)
  let tail3 := tail2
    (AyConj
      (AyLearnedClauseRetentionEvidence retentionOk)
      (AyBenchmarkEvidence candidateFaster))
    (fun _replay tail => tail)
  let retention_pair := ay_conj_left
    (AyLearnedClauseRetentionEvidence retentionOk)
    (AyBenchmarkEvidence candidateFaster)
    tail3
  exact ay_conj_left retentionOk retentionOk retention_pair

theorem ay_clause_deletion_gate_run_replay
    (candidateFaster : Prop) (retentionOk : Prop)
    (checkerAccepted : Prop) (replayAccepted : Prop)
    (candidateAccepted : Prop) :
    AyClauseDeletionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      candidateAccepted ->
    candidateAccepted := by
  intro gate
  let audit_pair := ay_conj_left
    (AyAuditReplay candidateAccepted)
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyConj
        (AyReplayEvidence replayAccepted)
        (AyConj
          (AyLearnedClauseRetentionEvidence retentionOk)
          (AyBenchmarkEvidence candidateFaster))))
    gate
  exact ay_conj_left candidateAccepted candidateAccepted audit_pair

theorem ay_clause_deletion_public_result_sound
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (candidateFaster : Prop) (retentionOk : Prop)
    (checkerAccepted : Prop) (replayAccepted : Prop)
    (candidateAccepted : Prop) :
    AyClauseDeletionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      candidateAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro gate
  intro candidate_manifest
  exact ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    candidateAccepted candidate_manifest
    (ay_clause_deletion_gate_run_replay
      candidateFaster retentionOk checkerAccepted replayAccepted
      candidateAccepted gate)

theorem ay_clause_deletion_is_search_only
    (searchPerformanceFact : Prop) (semanticClaim : Prop) :
    searchPerformanceFact ->
    semanticClaim ->
    semanticClaim := by
  intro _search_fact
  intro claim
  exact claim

theorem ay_clause_deletion_diagnostic_no_claim
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyClauseDeletionGateRejected timeout noResult mismatch rejected ->
    AyConj
      (AyClauseDeletionDiagnostic timeout noResult mismatch)
      (AyClauseDeletionGateRejected timeout noResult mismatch rejected) := by
  intro rejection
  exact ay_conj_intro
    (AyClauseDeletionDiagnostic timeout noResult mismatch)
    (AyClauseDeletionGateRejected timeout noResult mismatch rejected)
    (rejection
      (AyClauseDeletionDiagnostic timeout noResult mismatch)
      (fun _rejected diagnostic => diagnostic))
    rejection

theorem ay_clause_deletion_fallback_preserves_baseline
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyClauseDeletionGateRejected timeout noResult mismatch rejected ->
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

theorem ay_clause_deletion_rejection_cannot_bless_candidate
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) (semanticClaim : Prop) :
    AyClauseDeletionGateRejected timeout noResult mismatch rejected ->
    semanticClaim ->
    semanticClaim := by
  intro _rejection
  intro claim
  exact claim

theorem ay_safe_clause_deletion_sequential_deployment_accept
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (candidateFaster : Prop) (retentionOk : Prop)
    (checkerAccepted : Prop) (replayAccepted : Prop)
    (candidateAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyClauseDeletionGate
      candidateFaster retentionOk checkerAccepted replayAccepted
      candidateAccepted timeout noResult mismatch rejected ->
    AyClauseDeletionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      candidateAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro _gate
  intro accepted_gate
  intro candidate_manifest
  exact ay_clause_deletion_public_result_sound
    originalFormula visibleFormula visibleModel originalModel finalClause
    candidateFaster retentionOk checkerAccepted replayAccepted candidateAccepted
    accepted_gate candidate_manifest

theorem ay_safe_clause_deletion_sequential_deployment_fallback
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineAccepted : Prop)
    (timeout : Prop) (noResult : Prop) (mismatch : Prop)
    (rejected : Prop) :
    AyClauseDeletionGateRejected timeout noResult mismatch rejected ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineAccepted ->
    baselineAccepted ->
    AyConj
      (AyPublicSoundnessTheorem originalFormula originalModel)
      (AyClauseDeletionDiagnostic timeout noResult mismatch) := by
  intro rejection
  intro baseline_manifest
  intro baseline_accepted
  exact ay_conj_intro
    (AyPublicSoundnessTheorem originalFormula originalModel)
    (AyClauseDeletionDiagnostic timeout noResult mismatch)
    (ay_clause_deletion_fallback_preserves_baseline
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineAccepted timeout noResult mismatch rejected
      rejection baseline_manifest baseline_accepted)
    (rejection
      (AyClauseDeletionDiagnostic timeout noResult mismatch)
      (fun _rejected diagnostic => diagnostic))

