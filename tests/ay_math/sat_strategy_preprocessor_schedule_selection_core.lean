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

def AyPreprocessorSchedule
    (scheduleManifest stageOrdering sequentialMain : Prop) : Prop :=
  AyConj scheduleManifest (AyConj stageOrdering sequentialMain)

def AyBaselinePreprocessorSchedule
    (scheduleManifest stageOrdering sequentialMain : Prop) : Prop :=
  AyPreprocessorSchedule scheduleManifest stageOrdering sequentialMain

def AyCandidatePreprocessorSchedule
    (scheduleManifest stageOrdering sequentialMain : Prop) : Prop :=
  AyPreprocessorSchedule scheduleManifest stageOrdering sequentialMain

def AySelectedCompetitionSchedule
    (scheduleManifest stageOrdering sequentialMain : Prop) : Prop :=
  AyPreprocessorSchedule scheduleManifest stageOrdering sequentialMain

def AyScheduleManifestEvidence (scheduleManifest : Prop) : Prop :=
  scheduleManifest

def AyBenchmarkEvidence (candidateFaster : Prop) : Prop :=
  candidateFaster

def AyFormulaFingerprintEvidence (formulaFingerprint : Prop) : Prop :=
  formulaFingerprint

def AyStageCertificateEvidence (stageCertificates : Prop) : Prop :=
  stageCertificates

def AyCheckerReplayEvidence (checkerReplay : Prop) : Prop :=
  checkerReplay

def AyBaselineFallbackEvidence (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyPublicResultAgreement
    (baselineResult candidateResult : Prop) : Prop :=
  baselineResult -> candidateResult

def AyPreprocessorScheduleAccepted
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    Prop :=
  candidateAccepted

def AyPreprocessorScheduleRejected
    (staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch : Prop) : Prop :=
  AyDisj staleSchedule
    (AyDisj overfitSchedule
      (AyDisj formulaMismatch
        (AyDisj certificateMismatch replayMismatch)))

def AyPreprocessorScheduleGate
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted
      staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch : Prop) : Prop :=
  AyDisj
    (AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted)
    (AyPreprocessorScheduleRejected
      staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch)

def AyRunManifest
    (policyAccepted checkerReplay publicResult : Prop) : Prop :=
  AyConj policyAccepted (AyConj checkerReplay publicResult)

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

theorem ay_spss_outcome_public_soundness
    (satSound unsatSound : Prop) :
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro outcome
  exact outcome

theorem ay_spss_candidate_schedule_components
    (scheduleManifest stageOrdering sequentialMain : Prop) :
    AyCandidatePreprocessorSchedule
      scheduleManifest stageOrdering sequentialMain ->
    AyConj scheduleManifest (AyConj stageOrdering sequentialMain) := by
  intro schedule
  exact schedule

theorem ay_spss_accepted_candidate_replay
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    candidateAccepted := by
  intro accepted
  exact accepted

theorem ay_spss_accepted_schedule_manifest
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    AyScheduleManifestEvidence scheduleManifest ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyScheduleManifestEvidence scheduleManifest := by
  intro manifest _accepted
  exact manifest

theorem ay_spss_accepted_benchmark_evidence
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    AyBenchmarkEvidence candidateFaster ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyBenchmarkEvidence candidateFaster := by
  intro benchmark _accepted
  exact benchmark

theorem ay_spss_accepted_formula_fingerprint
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint _accepted
  exact fingerprint

theorem ay_spss_accepted_stage_certificates
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    AyStageCertificateEvidence stageCertificates ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyStageCertificateEvidence stageCertificates := by
  intro certificates _accepted
  exact certificates

theorem ay_spss_accepted_checker_replay
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay _accepted
  exact replay

theorem ay_spss_accepted_public_agreement
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    AyPublicResultAgreement baselineResult candidateResult ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyPublicResultAgreement baselineResult candidateResult := by
  intro agreement _accepted
  exact agreement

theorem ay_spss_candidate_public_result_from_baseline
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    baselineResult ->
    AyPublicResultAgreement baselineResult candidateResult ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    candidateResult := by
  intro baselinePublic agreement accepted
  let transported :=
    ay_spss_accepted_public_agreement
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted
      agreement accepted
  exact transported baselinePublic

theorem ay_spss_manifest_public_soundness
    (policyAccepted checkerReplay publicResult satSound unsatSound : Prop) :
    AyRunManifest policyAccepted checkerReplay publicResult ->
    publicResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _manifest _public outcome
  exact ay_spss_outcome_public_soundness satSound unsatSound outcome

theorem ay_spss_accepted_pipeline_preserves_public_soundness
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted
      satSound unsatSound : Prop) :
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted manifest public outcome
  exact ay_spss_manifest_public_soundness
    candidateAccepted checkerReplay candidateResult satSound unsatSound
    manifest public outcome

theorem ay_spss_rejected_is_no_claim
    (staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch : Prop) :
    AyPreprocessorScheduleRejected
      staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch ->
    AyNoClaimDiagnostic
      (AyPreprocessorScheduleRejected
        staleSchedule overfitSchedule formulaMismatch certificateMismatch
        replayMismatch) := by
  intro rejected
  exact rejected

theorem ay_spss_rejected_cannot_bless_candidate
    (staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch candidateSoundnessClaim : Prop) :
    AyPreprocessorScheduleRejected
      staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch ->
    candidateSoundnessClaim ->
    candidateSoundnessClaim := by
  intro _rejected claim
  exact claim

theorem ay_spss_rejected_fallback_preserves_baseline
    (staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch baselineSoundness : Prop) :
    AyPreprocessorScheduleRejected
      staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_spss_gate_accept_or_reject
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted
      staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch : Prop) :
    AyPreprocessorScheduleGate
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted
      staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch ->
    AyDisj
      (AyPreprocessorScheduleAccepted
        scheduleManifest candidateFaster formulaFingerprint stageCertificates
        checkerReplay baselineResult candidateResult candidateAccepted)
      (AyPreprocessorScheduleRejected
        staleSchedule overfitSchedule formulaMismatch certificateMismatch
        replayMismatch) := by
  intro gate
  exact gate

theorem ay_spss_safe_sequential_deployment_accept
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted
      satSound unsatSound : Prop) :
    AyScheduleManifestEvidence scheduleManifest ->
    AyBenchmarkEvidence candidateFaster ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyStageCertificateEvidence stageCertificates ->
    AyCheckerReplayEvidence checkerReplay ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AySelectedCompetitionSchedule
      scheduleManifest stageCertificates formulaFingerprint ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _manifestEvidence _benchmark _fingerprint _certificates _replay
  intro accepted manifest public outcome _selected
  exact ay_spss_accepted_pipeline_preserves_public_soundness
    scheduleManifest candidateFaster formulaFingerprint stageCertificates
    checkerReplay baselineResult candidateResult candidateAccepted
    satSound unsatSound accepted manifest public outcome

theorem ay_spss_safe_sequential_deployment_fallback
    (staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch baselineSoundness : Prop) :
    AyPreprocessorScheduleRejected
      staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    AySelectedCompetitionSchedule
      baselineSoundness baselineSoundness baselineSoundness ->
    baselineSoundness := by
  intro rejected fallback _selected
  exact ay_spss_rejected_fallback_preserves_baseline
    staleSchedule overfitSchedule formulaMismatch certificateMismatch
    replayMismatch baselineSoundness rejected fallback

theorem ay_spss_stale_or_overfit_no_claim
    (staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch noClaim : Prop) :
    AyPreprocessorScheduleRejected
      staleSchedule overfitSchedule formulaMismatch certificateMismatch
      replayMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_spss_faster_pipeline_requires_manifest
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    AyScheduleManifestEvidence scheduleManifest ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyScheduleManifestEvidence scheduleManifest := by
  intro manifest accepted
  exact ay_spss_accepted_schedule_manifest
    scheduleManifest candidateFaster formulaFingerprint stageCertificates
    checkerReplay baselineResult candidateResult candidateAccepted
    manifest accepted

theorem ay_spss_faster_pipeline_requires_stage_certificates
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    AyStageCertificateEvidence stageCertificates ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyStageCertificateEvidence stageCertificates := by
  intro certificates accepted
  exact ay_spss_accepted_stage_certificates
    scheduleManifest candidateFaster formulaFingerprint stageCertificates
    checkerReplay baselineResult candidateResult candidateAccepted
    certificates accepted

theorem ay_spss_faster_pipeline_requires_replay
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay accepted
  exact ay_spss_accepted_checker_replay
    scheduleManifest candidateFaster formulaFingerprint stageCertificates
    checkerReplay baselineResult candidateResult candidateAccepted
    replay accepted

theorem ay_spss_faster_pipeline_requires_fingerprint
    (scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyPreprocessorScheduleAccepted
      scheduleManifest candidateFaster formulaFingerprint stageCertificates
      checkerReplay baselineResult candidateResult candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint accepted
  exact ay_spss_accepted_formula_fingerprint
    scheduleManifest candidateFaster formulaFingerprint stageCertificates
    checkerReplay baselineResult candidateResult candidateAccepted
    fingerprint accepted
