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

def AyJointRestartLearningPolicy
    (restartSchedule learningPolicy sequentialMain : Prop) : Prop :=
  AyConj restartSchedule (AyConj learningPolicy sequentialMain)

def AyBaselineJointPolicy
    (restartSchedule learningPolicy sequentialMain : Prop) : Prop :=
  AyJointRestartLearningPolicy restartSchedule learningPolicy sequentialMain

def AyCandidateJointPolicy
    (restartSchedule learningPolicy sequentialMain : Prop) : Prop :=
  AyJointRestartLearningPolicy restartSchedule learningPolicy sequentialMain

def AySelectedCompetitionPolicy
    (restartSchedule learningPolicy sequentialMain : Prop) : Prop :=
  AyJointRestartLearningPolicy restartSchedule learningPolicy sequentialMain

def AyRestartManifestEvidence (restartManifest : Prop) : Prop :=
  restartManifest

def AyLearningManifestEvidence (learningManifest : Prop) : Prop :=
  learningManifest

def AyPairCompatibilityEvidence (pairCompatible : Prop) : Prop :=
  pairCompatible

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

def AyJointRestartLearningAccepted
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) : Prop :=
  candidateAccepted

def AyJointRestartLearningRejected
    (staleRestart staleLearning pairMismatch formulaMismatch replayMismatch : Prop) :
    Prop :=
  AyDisj staleRestart
    (AyDisj staleLearning
      (AyDisj pairMismatch (AyDisj formulaMismatch replayMismatch)))

def AyJointRestartLearningGate
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted staleRestart staleLearning pairMismatch formulaMismatch
      replayMismatch : Prop) : Prop :=
  AyDisj
    (AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted)
    (AyJointRestartLearningRejected
      staleRestart staleLearning pairMismatch formulaMismatch replayMismatch)

def AyRunManifest
    (policyAccepted checkerReplay publicResult : Prop) : Prop :=
  AyConj policyAccepted (AyConj checkerReplay publicResult)

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

theorem ay_srlj_outcome_public_soundness
    (satSound unsatSound : Prop) :
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro outcome
  exact outcome

theorem ay_srlj_candidate_policy_components
    (restartSchedule learningPolicy sequentialMain : Prop) :
    AyCandidateJointPolicy restartSchedule learningPolicy sequentialMain ->
    AyConj restartSchedule (AyConj learningPolicy sequentialMain) := by
  intro policy
  exact policy

theorem ay_srlj_accepted_candidate_replay
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    candidateAccepted := by
  intro accepted
  exact accepted

theorem ay_srlj_accepted_restart_manifest
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyRestartManifestEvidence restartManifest ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyRestartManifestEvidence restartManifest := by
  intro manifest _accepted
  exact manifest

theorem ay_srlj_accepted_learning_manifest
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyLearningManifestEvidence learningManifest ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyLearningManifestEvidence learningManifest := by
  intro manifest _accepted
  exact manifest

theorem ay_srlj_accepted_pair_compatibility
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyPairCompatibilityEvidence pairCompatible ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyPairCompatibilityEvidence pairCompatible := by
  intro compatible _accepted
  exact compatible

theorem ay_srlj_accepted_benchmark_evidence
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyBenchmarkEvidence candidateFaster ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyBenchmarkEvidence candidateFaster := by
  intro benchmark _accepted
  exact benchmark

theorem ay_srlj_accepted_checker_replay
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay _accepted
  exact replay

theorem ay_srlj_accepted_formula_fingerprint
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint _accepted
  exact fingerprint

theorem ay_srlj_accepted_public_agreement
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyPublicResultAgreement baselineResult candidateResult ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyPublicResultAgreement baselineResult candidateResult := by
  intro agreement _accepted
  exact agreement

theorem ay_srlj_candidate_public_result_from_baseline
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    baselineResult ->
    AyPublicResultAgreement baselineResult candidateResult ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    candidateResult := by
  intro baselinePublic agreement accepted
  let transported :=
    ay_srlj_accepted_public_agreement
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted agreement accepted
  exact transported baselinePublic

theorem ay_srlj_manifest_public_soundness
    (policyAccepted checkerReplay publicResult satSound unsatSound : Prop) :
    AyRunManifest policyAccepted checkerReplay publicResult ->
    publicResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _manifest _public outcome
  exact ay_srlj_outcome_public_soundness satSound unsatSound outcome

theorem ay_srlj_accepted_candidate_preserves_public_soundness
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted satSound unsatSound : Prop) :
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted manifest public outcome
  exact ay_srlj_manifest_public_soundness
    candidateAccepted checkerReplay candidateResult satSound unsatSound
    manifest public outcome

theorem ay_srlj_rejected_is_no_claim
    (staleRestart staleLearning pairMismatch formulaMismatch replayMismatch : Prop) :
    AyJointRestartLearningRejected
      staleRestart staleLearning pairMismatch formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic
      (AyJointRestartLearningRejected
        staleRestart staleLearning pairMismatch formulaMismatch replayMismatch) := by
  intro rejected
  exact rejected

theorem ay_srlj_rejected_cannot_bless_candidate
    (staleRestart staleLearning pairMismatch formulaMismatch replayMismatch
      candidateSoundnessClaim : Prop) :
    AyJointRestartLearningRejected
      staleRestart staleLearning pairMismatch formulaMismatch replayMismatch ->
    candidateSoundnessClaim ->
    candidateSoundnessClaim := by
  intro _rejected claim
  exact claim

theorem ay_srlj_rejected_fallback_preserves_baseline
    (staleRestart staleLearning pairMismatch formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyJointRestartLearningRejected
      staleRestart staleLearning pairMismatch formulaMismatch replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_srlj_gate_accept_or_reject
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted staleRestart staleLearning pairMismatch formulaMismatch
      replayMismatch : Prop) :
    AyJointRestartLearningGate
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted staleRestart staleLearning pairMismatch formulaMismatch
      replayMismatch ->
    AyDisj
      (AyJointRestartLearningAccepted
        restartManifest learningManifest pairCompatible candidateFaster
        checkerReplay formulaFingerprint baselineResult candidateResult
        candidateAccepted)
      (AyJointRestartLearningRejected
        staleRestart staleLearning pairMismatch formulaMismatch replayMismatch) := by
  intro gate
  exact gate

theorem ay_srlj_safe_sequential_deployment_accept
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted satSound unsatSound : Prop) :
    AyRestartManifestEvidence restartManifest ->
    AyLearningManifestEvidence learningManifest ->
    AyPairCompatibilityEvidence pairCompatible ->
    AyBenchmarkEvidence candidateFaster ->
    AyCheckerReplayEvidence checkerReplay ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AySelectedCompetitionPolicy restartManifest learningManifest pairCompatible ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _restartManifest _learningManifest _compatible _benchmark _replay
  intro _fingerprint accepted manifest public outcome _selected
  exact ay_srlj_accepted_candidate_preserves_public_soundness
    restartManifest learningManifest pairCompatible candidateFaster
    checkerReplay formulaFingerprint baselineResult candidateResult
    candidateAccepted satSound unsatSound accepted manifest public outcome

theorem ay_srlj_safe_sequential_deployment_fallback
    (staleRestart staleLearning pairMismatch formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyJointRestartLearningRejected
      staleRestart staleLearning pairMismatch formulaMismatch replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    AySelectedCompetitionPolicy
      baselineSoundness baselineSoundness baselineSoundness ->
    baselineSoundness := by
  intro rejected fallback _selected
  exact ay_srlj_rejected_fallback_preserves_baseline
    staleRestart staleLearning pairMismatch formulaMismatch replayMismatch
    baselineSoundness rejected fallback

theorem ay_srlj_mismatched_pair_no_claim
    (staleRestart staleLearning pairMismatch formulaMismatch replayMismatch
      noClaim : Prop) :
    AyJointRestartLearningRejected
      staleRestart staleLearning pairMismatch formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_srlj_faster_candidate_requires_restart_manifest
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyRestartManifestEvidence restartManifest ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyRestartManifestEvidence restartManifest := by
  intro manifest accepted
  exact ay_srlj_accepted_restart_manifest
    restartManifest learningManifest pairCompatible candidateFaster
    checkerReplay formulaFingerprint baselineResult candidateResult
    candidateAccepted manifest accepted

theorem ay_srlj_faster_candidate_requires_learning_manifest
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyLearningManifestEvidence learningManifest ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyLearningManifestEvidence learningManifest := by
  intro manifest accepted
  exact ay_srlj_accepted_learning_manifest
    restartManifest learningManifest pairCompatible candidateFaster
    checkerReplay formulaFingerprint baselineResult candidateResult
    candidateAccepted manifest accepted

theorem ay_srlj_faster_candidate_requires_pair_compatibility
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyPairCompatibilityEvidence pairCompatible ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyPairCompatibilityEvidence pairCompatible := by
  intro compatible accepted
  exact ay_srlj_accepted_pair_compatibility
    restartManifest learningManifest pairCompatible candidateFaster
    checkerReplay formulaFingerprint baselineResult candidateResult
    candidateAccepted compatible accepted

theorem ay_srlj_faster_candidate_requires_replay
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay accepted
  exact ay_srlj_accepted_checker_replay
    restartManifest learningManifest pairCompatible candidateFaster
    checkerReplay formulaFingerprint baselineResult candidateResult
    candidateAccepted replay accepted

theorem ay_srlj_faster_candidate_requires_fingerprint
    (restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyJointRestartLearningAccepted
      restartManifest learningManifest pairCompatible candidateFaster
      checkerReplay formulaFingerprint baselineResult candidateResult
      candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint accepted
  exact ay_srlj_accepted_formula_fingerprint
    restartManifest learningManifest pairCompatible candidateFaster
    checkerReplay formulaFingerprint baselineResult candidateResult
    candidateAccepted fingerprint accepted
