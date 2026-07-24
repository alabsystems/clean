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

def AyClauseLearningPolicy
    (minimization aggressiveness sequentialMain : Prop) : Prop :=
  AyConj minimization (AyConj aggressiveness sequentialMain)

def AyBaselineClauseLearningPolicy
    (minimization aggressiveness sequentialMain : Prop) : Prop :=
  AyClauseLearningPolicy minimization aggressiveness sequentialMain

def AyCandidateClauseLearningPolicy
    (minimization aggressiveness sequentialMain : Prop) : Prop :=
  AyClauseLearningPolicy minimization aggressiveness sequentialMain

def AySelectedCompetitionPolicy
    (minimization aggressiveness sequentialMain : Prop) : Prop :=
  AyClauseLearningPolicy minimization aggressiveness sequentialMain

def AyPolicyManifestEvidence (policyManifest : Prop) : Prop :=
  policyManifest

def AyBenchmarkEvidence (candidateFaster : Prop) : Prop :=
  candidateFaster

def AyCheckerReplayEvidence (checkerReplay : Prop) : Prop :=
  checkerReplay

def AyFormulaFingerprintEvidence (formulaFingerprint : Prop) : Prop :=
  formulaFingerprint

def AyBaselineFallbackEvidence (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyPublicResultAgreement
    (baselineResult candidateResult : Prop) : Prop :=
  baselineResult -> candidateResult

def AyClauseLearningPolicyAccepted
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) : Prop :=
  candidateAccepted

def AyClauseLearningPolicyRejected
    (stalePolicy overfitPolicy formulaMismatch replayMismatch : Prop) : Prop :=
  AyDisj stalePolicy
    (AyDisj overfitPolicy (AyDisj formulaMismatch replayMismatch))

def AyClauseLearningPolicyGate
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted
      stalePolicy overfitPolicy formulaMismatch replayMismatch : Prop) : Prop :=
  AyDisj
    (AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted)
    (AyClauseLearningPolicyRejected
      stalePolicy overfitPolicy formulaMismatch replayMismatch)

def AyRunManifest
    (policyAccepted checkerReplay publicResult : Prop) : Prop :=
  AyConj policyAccepted (AyConj checkerReplay publicResult)

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

theorem ay_sclp_outcome_public_soundness
    (satSound unsatSound : Prop) :
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro outcome
  exact outcome

theorem ay_sclp_candidate_policy_components
    (minimization aggressiveness sequentialMain : Prop) :
    AyCandidateClauseLearningPolicy minimization aggressiveness sequentialMain ->
    AyConj minimization (AyConj aggressiveness sequentialMain) := by
  intro policy
  exact policy

theorem ay_sclp_accepted_candidate_replay
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    candidateAccepted := by
  intro accepted
  exact accepted

theorem ay_sclp_accepted_policy_manifest
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyPolicyManifestEvidence policyManifest ->
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyPolicyManifestEvidence policyManifest := by
  intro manifest _accepted
  exact manifest

theorem ay_sclp_accepted_benchmark_evidence
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyBenchmarkEvidence candidateFaster ->
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyBenchmarkEvidence candidateFaster := by
  intro benchmark _accepted
  exact benchmark

theorem ay_sclp_accepted_checker_replay
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay _accepted
  exact replay

theorem ay_sclp_accepted_formula_fingerprint
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint _accepted
  exact fingerprint

theorem ay_sclp_accepted_public_agreement
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyPublicResultAgreement baselineResult candidateResult ->
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyPublicResultAgreement baselineResult candidateResult := by
  intro agreement _accepted
  exact agreement

theorem ay_sclp_candidate_public_result_from_baseline
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    baselineResult ->
    AyPublicResultAgreement baselineResult candidateResult ->
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    candidateResult := by
  intro baselinePublic agreement accepted
  let transported :=
    ay_sclp_accepted_public_agreement
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted agreement accepted
  exact transported baselinePublic

theorem ay_sclp_manifest_public_soundness
    (policyAccepted checkerReplay publicResult satSound unsatSound : Prop) :
    AyRunManifest policyAccepted checkerReplay publicResult ->
    publicResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _manifest _public outcome
  exact ay_sclp_outcome_public_soundness satSound unsatSound outcome

theorem ay_sclp_accepted_candidate_preserves_public_soundness
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted manifest public outcome
  exact ay_sclp_manifest_public_soundness
    candidateAccepted checkerReplay candidateResult satSound unsatSound
    manifest public outcome

theorem ay_sclp_rejected_is_no_claim
    (stalePolicy overfitPolicy formulaMismatch replayMismatch : Prop) :
    AyClauseLearningPolicyRejected
      stalePolicy overfitPolicy formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic
      (AyClauseLearningPolicyRejected
        stalePolicy overfitPolicy formulaMismatch replayMismatch) := by
  intro rejected
  exact rejected

theorem ay_sclp_rejected_cannot_bless_candidate
    (stalePolicy overfitPolicy formulaMismatch replayMismatch
      candidateSoundnessClaim : Prop) :
    AyClauseLearningPolicyRejected
      stalePolicy overfitPolicy formulaMismatch replayMismatch ->
    candidateSoundnessClaim ->
    candidateSoundnessClaim := by
  intro _rejected claim
  exact claim

theorem ay_sclp_rejected_fallback_preserves_baseline
    (stalePolicy overfitPolicy formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyClauseLearningPolicyRejected
      stalePolicy overfitPolicy formulaMismatch replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_sclp_gate_accept_or_reject
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted
      stalePolicy overfitPolicy formulaMismatch replayMismatch : Prop) :
    AyClauseLearningPolicyGate
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted
      stalePolicy overfitPolicy formulaMismatch replayMismatch ->
    AyDisj
      (AyClauseLearningPolicyAccepted
        policyManifest candidateFaster checkerReplay formulaFingerprint
        baselineResult candidateResult candidateAccepted)
      (AyClauseLearningPolicyRejected
        stalePolicy overfitPolicy formulaMismatch replayMismatch) := by
  intro gate
  exact gate

theorem ay_sclp_safe_sequential_deployment_accept
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyPolicyManifestEvidence policyManifest ->
    AyBenchmarkEvidence candidateFaster ->
    AyCheckerReplayEvidence checkerReplay ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AySelectedCompetitionPolicy
      policyManifest candidateFaster formulaFingerprint ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _manifestEvidence _benchmark _replay _fingerprint accepted manifest
  intro public outcome _selected
  exact ay_sclp_accepted_candidate_preserves_public_soundness
    policyManifest candidateFaster checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted satSound unsatSound
    accepted manifest public outcome

theorem ay_sclp_safe_sequential_deployment_fallback
    (stalePolicy overfitPolicy formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyClauseLearningPolicyRejected
      stalePolicy overfitPolicy formulaMismatch replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    AySelectedCompetitionPolicy
      baselineSoundness baselineSoundness baselineSoundness ->
    baselineSoundness := by
  intro rejected fallback _selected
  exact ay_sclp_rejected_fallback_preserves_baseline
    stalePolicy overfitPolicy formulaMismatch replayMismatch
    baselineSoundness rejected fallback

theorem ay_sclp_stale_or_overfit_no_claim
    (stalePolicy overfitPolicy formulaMismatch replayMismatch noClaim : Prop) :
    AyClauseLearningPolicyRejected
      stalePolicy overfitPolicy formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_sclp_faster_candidate_requires_policy_manifest
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyPolicyManifestEvidence policyManifest ->
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyPolicyManifestEvidence policyManifest := by
  intro manifest accepted
  exact ay_sclp_accepted_policy_manifest
    policyManifest candidateFaster checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted manifest accepted

theorem ay_sclp_faster_candidate_requires_replay
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay accepted
  exact ay_sclp_accepted_checker_replay
    policyManifest candidateFaster checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted replay accepted

theorem ay_sclp_faster_candidate_requires_fingerprint
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint accepted
  exact ay_sclp_accepted_formula_fingerprint
    policyManifest candidateFaster checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted fingerprint accepted

theorem ay_sclp_faster_candidate_requires_benchmark
    (policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyBenchmarkEvidence candidateFaster ->
    AyClauseLearningPolicyAccepted
      policyManifest candidateFaster checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyBenchmarkEvidence candidateFaster := by
  intro benchmark accepted
  exact ay_sclp_accepted_benchmark_evidence
    policyManifest candidateFaster checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted benchmark accepted
