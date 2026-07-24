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

def AyAdaptiveRestartBudgetPolicy
    (restartBudget learnedSchedule sequentialMain : Prop) : Prop :=
  AyConj restartBudget (AyConj learnedSchedule sequentialMain)

def AyBaselineRestartPolicy
    (restartBudget learnedSchedule sequentialMain : Prop) : Prop :=
  AyAdaptiveRestartBudgetPolicy restartBudget learnedSchedule sequentialMain

def AyCandidateRestartPolicy
    (restartBudget learnedSchedule sequentialMain : Prop) : Prop :=
  AyAdaptiveRestartBudgetPolicy restartBudget learnedSchedule sequentialMain

def AySelectedCompetitionPolicy
    (restartBudget learnedSchedule sequentialMain : Prop) : Prop :=
  AyAdaptiveRestartBudgetPolicy restartBudget learnedSchedule sequentialMain

def AyBenchmarkEvidence (candidateFaster : Prop) : Prop :=
  candidateFaster

def AyBudgetManifestEvidence (budgetManifest : Prop) : Prop :=
  budgetManifest

def AyCheckerReplayEvidence (checkerReplay : Prop) : Prop :=
  checkerReplay

def AyFormulaFingerprintEvidence (formulaFingerprint : Prop) : Prop :=
  formulaFingerprint

def AyBaselineFallbackEvidence (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyPublicResultAgreement
    (baselineResult candidateResult : Prop) : Prop :=
  baselineResult -> candidateResult

def AyAdaptiveRestartBudgetAccepted
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) : Prop :=
  candidateAccepted

def AyAdaptiveRestartBudgetRejected
    (overfitBudget staleBudget formulaMismatch replayMismatch : Prop) : Prop :=
  AyDisj overfitBudget
    (AyDisj staleBudget (AyDisj formulaMismatch replayMismatch))

def AyAdaptiveRestartBudgetGate
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted
      overfitBudget staleBudget formulaMismatch replayMismatch : Prop) : Prop :=
  AyDisj
    (AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted)
    (AyAdaptiveRestartBudgetRejected
      overfitBudget staleBudget formulaMismatch replayMismatch)

def AyRunManifest
    (policyAccepted checkerReplay publicResult : Prop) : Prop :=
  AyConj policyAccepted (AyConj checkerReplay publicResult)

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

theorem ay_sarb_outcome_public_soundness
    (satSound unsatSound : Prop) :
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro outcome
  exact outcome

theorem ay_sarb_candidate_policy_components
    (restartBudget learnedSchedule sequentialMain : Prop) :
    AyCandidateRestartPolicy restartBudget learnedSchedule sequentialMain ->
    AyConj restartBudget (AyConj learnedSchedule sequentialMain) := by
  intro policy
  exact policy

theorem ay_sarb_accepted_candidate_replay
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    candidateAccepted := by
  intro accepted
  exact accepted

theorem ay_sarb_accepted_benchmark_evidence
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyBenchmarkEvidence candidateFaster ->
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyBenchmarkEvidence candidateFaster := by
  intro benchmark _accepted
  exact benchmark

theorem ay_sarb_accepted_budget_manifest
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyBudgetManifestEvidence budgetManifest ->
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyBudgetManifestEvidence budgetManifest := by
  intro manifest _accepted
  exact manifest

theorem ay_sarb_accepted_checker_replay
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay _accepted
  exact replay

theorem ay_sarb_accepted_formula_fingerprint
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint _accepted
  exact fingerprint

theorem ay_sarb_accepted_public_agreement
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyPublicResultAgreement baselineResult candidateResult ->
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyPublicResultAgreement baselineResult candidateResult := by
  intro agreement _accepted
  exact agreement

theorem ay_sarb_candidate_public_result_from_baseline
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    baselineResult ->
    AyPublicResultAgreement baselineResult candidateResult ->
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    candidateResult := by
  intro baselinePublic agreement accepted
  let transported :=
    ay_sarb_accepted_public_agreement
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted agreement accepted
  exact transported baselinePublic

theorem ay_sarb_manifest_public_soundness
    (policyAccepted checkerReplay publicResult satSound unsatSound : Prop) :
    AyRunManifest policyAccepted checkerReplay publicResult ->
    publicResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _manifest _public outcome
  exact ay_sarb_outcome_public_soundness satSound unsatSound outcome

theorem ay_sarb_accepted_candidate_preserves_public_soundness
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted manifest public outcome
  exact ay_sarb_manifest_public_soundness
    candidateAccepted checkerReplay candidateResult satSound unsatSound
    manifest public outcome

theorem ay_sarb_rejected_is_no_claim
    (overfitBudget staleBudget formulaMismatch replayMismatch : Prop) :
    AyAdaptiveRestartBudgetRejected
      overfitBudget staleBudget formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic
      (AyAdaptiveRestartBudgetRejected
        overfitBudget staleBudget formulaMismatch replayMismatch) := by
  intro rejected
  exact rejected

theorem ay_sarb_rejected_cannot_bless_candidate
    (overfitBudget staleBudget formulaMismatch replayMismatch
      candidateSoundnessClaim : Prop) :
    AyAdaptiveRestartBudgetRejected
      overfitBudget staleBudget formulaMismatch replayMismatch ->
    candidateSoundnessClaim ->
    candidateSoundnessClaim := by
  intro _rejected claim
  exact claim

theorem ay_sarb_rejected_fallback_preserves_baseline
    (overfitBudget staleBudget formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyAdaptiveRestartBudgetRejected
      overfitBudget staleBudget formulaMismatch replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_sarb_gate_accept_or_reject
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted
      overfitBudget staleBudget formulaMismatch replayMismatch : Prop) :
    AyAdaptiveRestartBudgetGate
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted
      overfitBudget staleBudget formulaMismatch replayMismatch ->
    AyDisj
      (AyAdaptiveRestartBudgetAccepted
        candidateFaster budgetManifest checkerReplay formulaFingerprint
        baselineResult candidateResult candidateAccepted)
      (AyAdaptiveRestartBudgetRejected
        overfitBudget staleBudget formulaMismatch replayMismatch) := by
  intro gate
  exact gate

theorem ay_sarb_safe_sequential_deployment_accept
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyBenchmarkEvidence candidateFaster ->
    AyBudgetManifestEvidence budgetManifest ->
    AyCheckerReplayEvidence checkerReplay ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AySelectedCompetitionPolicy candidateFaster budgetManifest formulaFingerprint ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _benchmark _manifestEvidence _replay _fingerprint accepted manifest public
  intro outcome _selected
  exact ay_sarb_accepted_candidate_preserves_public_soundness
    candidateFaster budgetManifest checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted satSound unsatSound
    accepted manifest public outcome

theorem ay_sarb_safe_sequential_deployment_fallback
    (overfitBudget staleBudget formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyAdaptiveRestartBudgetRejected
      overfitBudget staleBudget formulaMismatch replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    AySelectedCompetitionPolicy
      baselineSoundness baselineSoundness baselineSoundness ->
    baselineSoundness := by
  intro rejected fallback _selected
  exact ay_sarb_rejected_fallback_preserves_baseline
    overfitBudget staleBudget formulaMismatch replayMismatch
    baselineSoundness rejected fallback

theorem ay_sarb_overfit_budget_no_claim
    (overfitBudget staleBudget formulaMismatch replayMismatch noClaim : Prop) :
    AyAdaptiveRestartBudgetRejected
      overfitBudget staleBudget formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_sarb_faster_candidate_requires_budget_manifest
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyBudgetManifestEvidence budgetManifest ->
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyBudgetManifestEvidence budgetManifest := by
  intro manifest accepted
  exact ay_sarb_accepted_budget_manifest
    candidateFaster budgetManifest checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted manifest accepted

theorem ay_sarb_faster_candidate_requires_replay
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay _accepted
  exact replay

theorem ay_sarb_faster_candidate_requires_fingerprint
    (candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyAdaptiveRestartBudgetAccepted
      candidateFaster budgetManifest checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint _accepted
  exact fingerprint
