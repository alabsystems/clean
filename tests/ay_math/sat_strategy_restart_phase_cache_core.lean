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

def AyRestartPhaseCachePolicy
    (restartSchedule phaseCache branchingCache : Prop) : Prop :=
  AyConj restartSchedule (AyConj phaseCache branchingCache)

def AyBaselinePolicy
    (restartSchedule phaseCache branchingCache : Prop) : Prop :=
  AyRestartPhaseCachePolicy restartSchedule phaseCache branchingCache

def AyCandidatePolicy
    (restartSchedule phaseCache branchingCache : Prop) : Prop :=
  AyRestartPhaseCachePolicy restartSchedule phaseCache branchingCache

def AySelectedCompetitionPolicy
    (restartSchedule phaseCache branchingCache : Prop) : Prop :=
  AyRestartPhaseCachePolicy restartSchedule phaseCache branchingCache

def AyScheduleDigestAgreement (baselineDigest candidateDigest : Prop) : Prop :=
  AyConj baselineDigest candidateDigest

def AyPhaseCacheEpochAgreement (baselineEpoch candidateEpoch : Prop) : Prop :=
  AyConj baselineEpoch candidateEpoch

def AyFormulaFingerprintAgreement
    (baselineFingerprint candidateFingerprint : Prop) : Prop :=
  AyConj baselineFingerprint candidateFingerprint

def AyCheckerReplayEvidence (checkerReplay : Prop) : Prop :=
  checkerReplay

def AyPublicResultAgreement
    (baselineResult candidateResult : Prop) : Prop :=
  baselineResult -> candidateResult

def AyBaselinePublicEvidence
    (baselineResult baselineSoundness : Prop) : Prop :=
  AyConj baselineResult baselineSoundness

def AyCacheFreshnessEvidence
    (scheduleDigest phaseEpoch formulaFingerprint : Prop) : Prop :=
  AyConj scheduleDigest (AyConj phaseEpoch formulaFingerprint)

def AyRestartPhaseCacheAccepted
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) : Prop :=
  candidateAccepted

def AyRestartPhaseCacheRejected
    (staleSchedule stalePhaseEpoch formulaMismatch replayMismatch : Prop) :
    Prop :=
  AyDisj staleSchedule
    (AyDisj stalePhaseEpoch (AyDisj formulaMismatch replayMismatch))

def AyRestartPhaseCacheGate
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted
      staleSchedule stalePhaseEpoch formulaMismatch replayMismatch : Prop) :
    Prop :=
  AyDisj
    (AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted)
    (AyRestartPhaseCacheRejected
      staleSchedule stalePhaseEpoch formulaMismatch replayMismatch)

def AyRunManifest
    (policyAccepted checkerReplay publicResult : Prop) : Prop :=
  AyConj policyAccepted (AyConj checkerReplay publicResult)

def AyFallbackPolicy (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

theorem ay_srpc_outcome_public_soundness
    (satSound unsatSound : Prop) :
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro outcome
  exact outcome

theorem ay_srpc_policy_components
    (restartSchedule phaseCache branchingCache : Prop) :
    AyCandidatePolicy restartSchedule phaseCache branchingCache ->
    AyConj restartSchedule (AyConj phaseCache branchingCache) := by
  intro policy
  exact policy

theorem ay_srpc_accepted_candidate_replay
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    candidateAccepted := by
  intro accepted
  exact accepted

theorem ay_srpc_accepted_fresh_cache
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCacheFreshnessEvidence scheduleDigest phaseEpoch formulaFingerprint ->
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyCacheFreshnessEvidence scheduleDigest phaseEpoch formulaFingerprint := by
  intro fresh _accepted
  exact fresh

theorem ay_srpc_accepted_schedule_digest
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    scheduleDigest ->
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    scheduleDigest := by
  intro digest _accepted
  exact digest

theorem ay_srpc_accepted_phase_epoch
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    phaseEpoch ->
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    phaseEpoch := by
  intro epoch _accepted
  exact epoch

theorem ay_srpc_accepted_formula_fingerprint
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    formulaFingerprint ->
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    formulaFingerprint := by
  intro fingerprint _accepted
  exact fingerprint

theorem ay_srpc_accepted_checker_replay
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay _accepted
  exact replay

theorem ay_srpc_accepted_public_result_agreement
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyPublicResultAgreement baselineResult candidateResult ->
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyPublicResultAgreement baselineResult candidateResult := by
  intro agreement _accepted
  exact agreement

theorem ay_srpc_baseline_public_result
    (baselineResult baselineSoundness : Prop) :
    baselineResult ->
    AyBaselinePublicEvidence baselineResult baselineSoundness ->
    baselineResult := by
  intro public _evidence
  exact public

theorem ay_srpc_baseline_public_soundness
    (baselineResult baselineSoundness : Prop) :
    baselineSoundness ->
    AyBaselinePublicEvidence baselineResult baselineSoundness ->
    baselineSoundness := by
  intro sound _evidence
  exact sound

theorem ay_srpc_candidate_public_result_from_baseline
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted baselineSoundness : Prop) :
    baselineResult ->
    AyPublicResultAgreement baselineResult candidateResult ->
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyBaselinePublicEvidence baselineResult baselineSoundness ->
    candidateResult := by
  intro baselinePublic agreement accepted _baselineEvidence
  let transported :=
    ay_srpc_accepted_public_result_agreement
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted agreement accepted
  exact transported baselinePublic

theorem ay_srpc_manifest_public_soundness
    (policyAccepted checkerReplay publicResult satSound unsatSound : Prop) :
    AyRunManifest policyAccepted checkerReplay publicResult ->
    publicResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _manifest _public outcome
  exact ay_srpc_outcome_public_soundness satSound unsatSound outcome

theorem ay_srpc_accepted_candidate_preserves_public_soundness
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted manifest public outcome
  exact ay_srpc_manifest_public_soundness
    candidateAccepted checkerReplay candidateResult satSound unsatSound
    manifest public outcome

theorem ay_srpc_rejected_is_diagnostic
    (staleSchedule stalePhaseEpoch formulaMismatch replayMismatch : Prop) :
    AyRestartPhaseCacheRejected
      staleSchedule stalePhaseEpoch formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic
      (AyRestartPhaseCacheRejected
        staleSchedule stalePhaseEpoch formulaMismatch replayMismatch) := by
  intro rejected
  exact rejected

theorem ay_srpc_rejected_cannot_bless_candidate
    (staleSchedule stalePhaseEpoch formulaMismatch replayMismatch
      candidateSoundnessClaim : Prop) :
    AyRestartPhaseCacheRejected
      staleSchedule stalePhaseEpoch formulaMismatch replayMismatch ->
    candidateSoundnessClaim ->
    candidateSoundnessClaim := by
  intro _rejected claim
  exact claim

theorem ay_srpc_rejected_fallback_preserves_baseline
    (staleSchedule stalePhaseEpoch formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyRestartPhaseCacheRejected
      staleSchedule stalePhaseEpoch formulaMismatch replayMismatch ->
    AyFallbackPolicy baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_srpc_gate_accept_or_reject
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted
      staleSchedule stalePhaseEpoch formulaMismatch replayMismatch : Prop) :
    AyRestartPhaseCacheGate
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted
      staleSchedule stalePhaseEpoch formulaMismatch replayMismatch ->
    AyDisj
      (AyRestartPhaseCacheAccepted
        scheduleDigest phaseEpoch formulaFingerprint checkerReplay
        baselineResult candidateResult candidateAccepted)
      (AyRestartPhaseCacheRejected
        staleSchedule stalePhaseEpoch formulaMismatch replayMismatch) := by
  intro gate
  exact gate

theorem ay_srpc_safe_deployment_accept
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AySelectedCompetitionPolicy
      scheduleDigest phaseEpoch formulaFingerprint ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro accepted manifest public outcome _selected
  exact ay_srpc_accepted_candidate_preserves_public_soundness
    scheduleDigest phaseEpoch formulaFingerprint checkerReplay
    baselineResult candidateResult candidateAccepted satSound unsatSound
    accepted manifest public outcome

theorem ay_srpc_safe_deployment_fallback
    (staleSchedule stalePhaseEpoch formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyRestartPhaseCacheRejected
      staleSchedule stalePhaseEpoch formulaMismatch replayMismatch ->
    AyFallbackPolicy baselineSoundness ->
    AySelectedCompetitionPolicy
      baselineSoundness baselineSoundness baselineSoundness ->
    baselineSoundness := by
  intro rejected fallback _selected
  exact ay_srpc_rejected_fallback_preserves_baseline
    staleSchedule stalePhaseEpoch formulaMismatch replayMismatch
    baselineSoundness rejected fallback

theorem ay_srpc_stale_cache_no_claim
    (staleSchedule stalePhaseEpoch formulaMismatch replayMismatch
      noClaim : Prop) :
    AyRestartPhaseCacheRejected
      staleSchedule stalePhaseEpoch formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_srpc_faster_candidate_requires_cache_and_replay
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCacheFreshnessEvidence scheduleDigest phaseEpoch formulaFingerprint ->
    AyCheckerReplayEvidence checkerReplay ->
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyCacheFreshnessEvidence scheduleDigest phaseEpoch formulaFingerprint := by
  intro fresh _replay accepted
  exact ay_srpc_accepted_fresh_cache
    scheduleDigest phaseEpoch formulaFingerprint checkerReplay
    baselineResult candidateResult candidateAccepted fresh accepted

theorem ay_srpc_faster_candidate_requires_replay
    (scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyRestartPhaseCacheAccepted
      scheduleDigest phaseEpoch formulaFingerprint checkerReplay
      baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay accepted
  exact ay_srpc_accepted_checker_replay
    scheduleDigest phaseEpoch formulaFingerprint checkerReplay
    baselineResult candidateResult candidateAccepted replay accepted
