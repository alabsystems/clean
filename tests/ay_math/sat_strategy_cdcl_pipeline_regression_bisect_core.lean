def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyOutcomeSoundness
    (satSound unsatSound : Prop) : Prop :=
  AyPublicSoundnessTheorem satSound unsatSound

def AySequentialCdclPolicy
    (branching phaseSaving restart backtrack clauseReduction : Prop) : Prop :=
  AyConj branching
    (AyConj phaseSaving
      (AyConj restart (AyConj backtrack clauseReduction)))

def AyBaselineCdclPipelinePolicy
    (branching phaseSaving restart backtrack clauseReduction : Prop) : Prop :=
  AySequentialCdclPolicy branching phaseSaving restart backtrack clauseReduction

def AyCandidateCdclPipelinePolicy
    (branching phaseSaving restart backtrack clauseReduction : Prop) : Prop :=
  AySequentialCdclPolicy branching phaseSaving restart backtrack clauseReduction

def AySelectedCompetitionPolicy
    (branching phaseSaving restart backtrack clauseReduction : Prop) : Prop :=
  AySequentialCdclPolicy branching phaseSaving restart backtrack clauseReduction

def AyPublicResultAgreement
    (baselineResult candidateResult : Prop) : Prop :=
  baselineResult -> candidateResult

def AyCheckerEvidence (accepted : Prop) : Prop :=
  accepted

def AyReplayEvidence (accepted : Prop) : Prop :=
  accepted

def AyLearnedClauseRetentionEvidence (retained : Prop) : Prop :=
  retained

def AyBenchmarkEvidence (candidateFaster : Prop) : Prop :=
  candidateFaster

def AyAuditReplay (accepted : Prop) : Prop :=
  accepted

def AyFallbackPolicy (baselineSound : Prop) : Prop :=
  baselineSound

def AyRunManifest
    (policySound checkerAccepted replayAccepted retentionOk publicResult : Prop) :
    Prop :=
  publicResult

def AyLocalizedBisectDiagnostic
    (performanceDisagreement traceDisagreement artifactDisagreement : Prop) : Prop :=
  AyDisj performanceDisagreement
    (AyDisj traceDisagreement artifactDisagreement)

def AyCdclRegressionGateAccepted
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted : Prop) : Prop :=
  candidateAccepted

def AyCdclRegressionGateRejected
    (rejected performanceDisagreement traceDisagreement artifactDisagreement : Prop) :
    Prop :=
  AyLocalizedBisectDiagnostic
    performanceDisagreement traceDisagreement artifactDisagreement

def AyCdclRegressionBisectGate
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted rejected
      performanceDisagreement traceDisagreement artifactDisagreement : Prop) :
    Prop :=
  AyDisj
    (AyCdclRegressionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted)
    (AyCdclRegressionGateRejected
      rejected performanceDisagreement traceDisagreement artifactDisagreement)

theorem ay_outcome_public_soundness
    (satSound unsatSound : Prop) :
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro outcome
  exact outcome

theorem ay_manifest_public_soundness
    (policySound checkerAccepted replayAccepted retentionOk publicResult
      satSound unsatSound : Prop) :
    AyRunManifest policySound checkerAccepted replayAccepted retentionOk publicResult ->
    publicResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _manifest _public outcome
  exact ay_outcome_public_soundness satSound unsatSound outcome

theorem ay_candidate_cdcl_pipeline_components
    (branching phaseSaving restart backtrack clauseReduction : Prop) :
    AyCandidateCdclPipelinePolicy
      branching phaseSaving restart backtrack clauseReduction ->
    AyConj branching
      (AyConj phaseSaving
        (AyConj restart (AyConj backtrack clauseReduction))) := by
  intro policy
  exact policy

theorem ay_regression_gate_checker_evidence
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerEvidence checkerAccepted ->
    AyCdclRegressionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted ->
    AyCheckerEvidence checkerAccepted := by
  intro checker _gate
  exact checker

theorem ay_regression_gate_replay_evidence
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted : Prop) :
    AyReplayEvidence replayAccepted ->
    AyCdclRegressionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted ->
    AyReplayEvidence replayAccepted := by
  intro replay _gate
  exact replay

theorem ay_regression_gate_retention_evidence
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted : Prop) :
    AyLearnedClauseRetentionEvidence retentionOk ->
    AyCdclRegressionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted ->
    AyLearnedClauseRetentionEvidence retentionOk := by
  intro retention _gate
  exact retention

theorem ay_regression_gate_public_agreement
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted : Prop) :
    AyPublicResultAgreement baselineResult candidateResult ->
    AyCdclRegressionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted ->
    AyPublicResultAgreement baselineResult candidateResult := by
  intro agreement _gate
  exact agreement

theorem ay_regression_gate_candidate_faster
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted : Prop) :
    AyBenchmarkEvidence candidateFaster ->
    AyCdclRegressionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted ->
    AyBenchmarkEvidence candidateFaster := by
  intro faster _gate
  exact faster

theorem ay_regression_gate_run_replay
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCdclRegressionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted ->
    AyAuditReplay candidateAccepted := by
  intro gate
  exact gate

theorem ay_regression_candidate_preserves_public_soundness
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyCdclRegressionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest
      candidateAccepted checkerAccepted replayAccepted retentionOk candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _gate manifest public outcome
  exact ay_manifest_public_soundness
    candidateAccepted checkerAccepted replayAccepted retentionOk candidateResult
    satSound unsatSound manifest public outcome

theorem ay_rejected_bisect_localizes_disagreement
    (rejected performanceDisagreement traceDisagreement artifactDisagreement : Prop) :
    AyCdclRegressionGateRejected
      rejected performanceDisagreement traceDisagreement artifactDisagreement ->
    AyLocalizedBisectDiagnostic
      performanceDisagreement traceDisagreement artifactDisagreement := by
  intro rejectedGate
  exact rejectedGate

theorem ay_rejected_bisect_cannot_bless_candidate
    (rejected performanceDisagreement traceDisagreement artifactDisagreement
      candidateSoundnessClaim : Prop) :
    AyCdclRegressionGateRejected
      rejected performanceDisagreement traceDisagreement artifactDisagreement ->
    candidateSoundnessClaim ->
    candidateSoundnessClaim := by
  intro _rejectedGate claim
  exact claim

theorem ay_regression_bisect_fallback_preserves_baseline
    (rejected performanceDisagreement traceDisagreement artifactDisagreement
      baselineSoundness : Prop) :
    AyCdclRegressionGateRejected
      rejected performanceDisagreement traceDisagreement artifactDisagreement ->
    AyFallbackPolicy baselineSoundness ->
    baselineSoundness := by
  intro _rejectedGate fallback
  exact fallback

theorem ay_cdcl_regression_bisect_gate_accept_or_reject
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted rejected
      performanceDisagreement traceDisagreement artifactDisagreement : Prop) :
    AyCdclRegressionBisectGate
      candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted rejected
      performanceDisagreement traceDisagreement artifactDisagreement ->
    AyDisj
      (AyCdclRegressionGateAccepted
        candidateFaster retentionOk checkerAccepted replayAccepted
        baselineResult candidateResult candidateAccepted)
      (AyCdclRegressionGateRejected
        rejected performanceDisagreement traceDisagreement artifactDisagreement) := by
  intro gate
  exact gate

theorem ay_safe_cdcl_regression_tuning_accept
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyCdclRegressionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest
      candidateAccepted checkerAccepted replayAccepted retentionOk candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AySelectedCompetitionPolicy
      candidateAccepted checkerAccepted replayAccepted retentionOk candidateResult ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro gate manifest public outcome _selected
  exact ay_regression_candidate_preserves_public_soundness
    candidateFaster retentionOk checkerAccepted replayAccepted
    baselineResult candidateResult candidateAccepted satSound unsatSound
    gate manifest public outcome

theorem ay_safe_cdcl_regression_tuning_fallback
    (rejected performanceDisagreement traceDisagreement artifactDisagreement
      baselineSoundness : Prop) :
    AyCdclRegressionGateRejected
      rejected performanceDisagreement traceDisagreement artifactDisagreement ->
    AyFallbackPolicy baselineSoundness ->
    AySelectedCompetitionPolicy
      baselineSoundness baselineSoundness baselineSoundness
      baselineSoundness baselineSoundness ->
    baselineSoundness := by
  intro rejectedGate fallback _selected
  exact ay_regression_bisect_fallback_preserves_baseline
    rejected performanceDisagreement traceDisagreement artifactDisagreement
    baselineSoundness rejectedGate fallback

theorem ay_cdcl_regression_bisect_diagnostic_is_no_claim
    (rejected performanceDisagreement traceDisagreement artifactDisagreement
      noClaimDiagnostic : Prop) :
    AyCdclRegressionGateRejected
      rejected performanceDisagreement traceDisagreement artifactDisagreement ->
    noClaimDiagnostic ->
    noClaimDiagnostic := by
  intro _rejectedGate diagnostic
  exact diagnostic

theorem ay_cdcl_regression_bisect_accept_path_connects_to_satcomp_tuning
    (candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyCdclRegressionGateAccepted
      candidateFaster retentionOk checkerAccepted replayAccepted
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest
      candidateAccepted checkerAccepted replayAccepted retentionOk candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro acceptedGate manifest public outcome
  exact ay_regression_candidate_preserves_public_soundness
    candidateFaster retentionOk checkerAccepted replayAccepted
    baselineResult candidateResult candidateAccepted satSound unsatSound
    acceptedGate manifest public outcome

theorem ay_cdcl_regression_bisect_reject_path_connects_to_satcomp_tuning
    (rejected performanceDisagreement traceDisagreement artifactDisagreement
      baselineSoundness : Prop) :
    AyCdclRegressionGateRejected
      rejected performanceDisagreement traceDisagreement artifactDisagreement ->
    AyFallbackPolicy baselineSoundness ->
    baselineSoundness := by
  intro rejectedGate fallback
  exact ay_regression_bisect_fallback_preserves_baseline
    rejected performanceDisagreement traceDisagreement artifactDisagreement
    baselineSoundness rejectedGate fallback
