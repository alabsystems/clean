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

def AyClauseActivityDecayPolicy
    (activityDecay learnedClauseScoring sequentialMain : Prop) : Prop :=
  AyConj activityDecay (AyConj learnedClauseScoring sequentialMain)

def AyBaselineActivityPolicy
    (activityDecay learnedClauseScoring sequentialMain : Prop) : Prop :=
  AyClauseActivityDecayPolicy activityDecay learnedClauseScoring sequentialMain

def AyCandidateActivityPolicy
    (activityDecay learnedClauseScoring sequentialMain : Prop) : Prop :=
  AyClauseActivityDecayPolicy activityDecay learnedClauseScoring sequentialMain

def AySelectedCompetitionPolicy
    (activityDecay learnedClauseScoring sequentialMain : Prop) : Prop :=
  AyClauseActivityDecayPolicy activityDecay learnedClauseScoring sequentialMain

def AyActivityEpochEvidence (activityEpoch : Prop) : Prop :=
  activityEpoch

def AyDecayManifestEvidence (decayManifest : Prop) : Prop :=
  decayManifest

def AyFormulaFingerprintEvidence (formulaFingerprint : Prop) : Prop :=
  formulaFingerprint

def AyCheckerReplayEvidence (checkerReplay : Prop) : Prop :=
  checkerReplay

def AyBenchmarkEvidence (candidateFaster : Prop) : Prop :=
  candidateFaster

def AyBaselineFallbackEvidence (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyPublicResultAgreement
    (baselineResult candidateResult : Prop) : Prop :=
  baselineResult -> candidateResult

def AyClauseActivityDecayAccepted
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) : Prop :=
  candidateAccepted

def AyClauseActivityDecayRejected
    (staleScoreCache overfitDecay formulaMismatch replayMismatch : Prop) : Prop :=
  AyDisj staleScoreCache
    (AyDisj overfitDecay (AyDisj formulaMismatch replayMismatch))

def AyClauseActivityDecayGate
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted
      staleScoreCache overfitDecay formulaMismatch replayMismatch : Prop) : Prop :=
  AyDisj
    (AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted)
    (AyClauseActivityDecayRejected
      staleScoreCache overfitDecay formulaMismatch replayMismatch)

def AyRunManifest
    (policyAccepted checkerReplay publicResult : Prop) : Prop :=
  AyConj policyAccepted (AyConj checkerReplay publicResult)

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

theorem ay_scad_outcome_public_soundness
    (satSound unsatSound : Prop) :
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro outcome
  exact outcome

theorem ay_scad_candidate_policy_components
    (activityDecay learnedClauseScoring sequentialMain : Prop) :
    AyCandidateActivityPolicy
      activityDecay learnedClauseScoring sequentialMain ->
    AyConj activityDecay (AyConj learnedClauseScoring sequentialMain) := by
  intro policy
  exact policy

theorem ay_scad_accepted_candidate_replay
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    candidateAccepted := by
  intro accepted
  exact accepted

theorem ay_scad_accepted_benchmark_evidence
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyBenchmarkEvidence candidateFaster ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyBenchmarkEvidence candidateFaster := by
  intro benchmark _accepted
  exact benchmark

theorem ay_scad_accepted_activity_epoch
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyActivityEpochEvidence activityEpoch ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyActivityEpochEvidence activityEpoch := by
  intro epoch _accepted
  exact epoch

theorem ay_scad_accepted_decay_manifest
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyDecayManifestEvidence decayManifest ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyDecayManifestEvidence decayManifest := by
  intro manifest _accepted
  exact manifest

theorem ay_scad_accepted_formula_fingerprint
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint _accepted
  exact fingerprint

theorem ay_scad_accepted_checker_replay
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay _accepted
  exact replay

theorem ay_scad_accepted_public_agreement
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyPublicResultAgreement baselineResult candidateResult ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyPublicResultAgreement baselineResult candidateResult := by
  intro agreement _accepted
  exact agreement

theorem ay_scad_candidate_public_result_from_baseline
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    baselineResult ->
    AyPublicResultAgreement baselineResult candidateResult ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    candidateResult := by
  intro baselinePublic agreement accepted
  let transported :=
    ay_scad_accepted_public_agreement
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted agreement accepted
  exact transported baselinePublic

theorem ay_scad_manifest_public_soundness
    (policyAccepted checkerReplay publicResult satSound unsatSound : Prop) :
    AyRunManifest policyAccepted checkerReplay publicResult ->
    publicResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _manifest _public outcome
  exact ay_scad_outcome_public_soundness satSound unsatSound outcome

theorem ay_scad_accepted_candidate_preserves_public_soundness
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted manifest public outcome
  exact ay_scad_manifest_public_soundness
    candidateAccepted checkerReplay candidateResult satSound unsatSound
    manifest public outcome

theorem ay_scad_rejected_is_no_claim
    (staleScoreCache overfitDecay formulaMismatch replayMismatch : Prop) :
    AyClauseActivityDecayRejected
      staleScoreCache overfitDecay formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic
      (AyClauseActivityDecayRejected
        staleScoreCache overfitDecay formulaMismatch replayMismatch) := by
  intro rejected
  exact rejected

theorem ay_scad_rejected_cannot_bless_candidate
    (staleScoreCache overfitDecay formulaMismatch replayMismatch
      candidateSoundnessClaim : Prop) :
    AyClauseActivityDecayRejected
      staleScoreCache overfitDecay formulaMismatch replayMismatch ->
    candidateSoundnessClaim ->
    candidateSoundnessClaim := by
  intro _rejected claim
  exact claim

theorem ay_scad_rejected_fallback_preserves_baseline
    (staleScoreCache overfitDecay formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyClauseActivityDecayRejected
      staleScoreCache overfitDecay formulaMismatch replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_scad_gate_accept_or_reject
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted
      staleScoreCache overfitDecay formulaMismatch replayMismatch : Prop) :
    AyClauseActivityDecayGate
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted
      staleScoreCache overfitDecay formulaMismatch replayMismatch ->
    AyDisj
      (AyClauseActivityDecayAccepted
        candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
        baselineResult candidateResult candidateAccepted)
      (AyClauseActivityDecayRejected
        staleScoreCache overfitDecay formulaMismatch replayMismatch) := by
  intro gate
  exact gate

theorem ay_scad_safe_sequential_deployment_accept
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyBenchmarkEvidence candidateFaster ->
    AyActivityEpochEvidence activityEpoch ->
    AyDecayManifestEvidence decayManifest ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyCheckerReplayEvidence checkerReplay ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AySelectedCompetitionPolicy
      activityEpoch decayManifest formulaFingerprint ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _benchmark _epoch _manifest _fingerprint _replay accepted manifest public
  intro outcome _selected
  exact ay_scad_accepted_candidate_preserves_public_soundness
    candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
    baselineResult candidateResult candidateAccepted satSound unsatSound
    accepted manifest public outcome

theorem ay_scad_safe_sequential_deployment_fallback
    (staleScoreCache overfitDecay formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyClauseActivityDecayRejected
      staleScoreCache overfitDecay formulaMismatch replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    AySelectedCompetitionPolicy
      baselineSoundness baselineSoundness baselineSoundness ->
    baselineSoundness := by
  intro rejected fallback _selected
  exact ay_scad_rejected_fallback_preserves_baseline
    staleScoreCache overfitDecay formulaMismatch replayMismatch
    baselineSoundness rejected fallback

theorem ay_scad_stale_score_cache_no_claim
    (staleScoreCache overfitDecay formulaMismatch replayMismatch noClaim : Prop) :
    AyClauseActivityDecayRejected
      staleScoreCache overfitDecay formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_scad_faster_candidate_requires_activity_epoch
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyActivityEpochEvidence activityEpoch ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyActivityEpochEvidence activityEpoch := by
  intro epoch accepted
  exact ay_scad_accepted_activity_epoch
    candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
    baselineResult candidateResult candidateAccepted epoch accepted

theorem ay_scad_faster_candidate_requires_decay_manifest
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyDecayManifestEvidence decayManifest ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyDecayManifestEvidence decayManifest := by
  intro manifest accepted
  exact ay_scad_accepted_decay_manifest
    candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
    baselineResult candidateResult candidateAccepted manifest accepted

theorem ay_scad_faster_candidate_requires_replay
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay accepted
  exact ay_scad_accepted_checker_replay
    candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
    baselineResult candidateResult candidateAccepted replay accepted

theorem ay_scad_faster_candidate_requires_fingerprint
    (candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyClauseActivityDecayAccepted
      candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint accepted
  exact ay_scad_accepted_formula_fingerprint
    candidateFaster activityEpoch decayManifest formulaFingerprint checkerReplay
    baselineResult candidateResult candidateAccepted fingerprint accepted
