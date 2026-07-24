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

def AyOfflineSequentialProfile
    (profileManifest benchmarkClass sequentialMain : Prop) : Prop :=
  AyConj profileManifest (AyConj benchmarkClass sequentialMain)

def AyBaselineProfile
    (profileManifest benchmarkClass sequentialMain : Prop) : Prop :=
  AyOfflineSequentialProfile profileManifest benchmarkClass sequentialMain

def AyCandidateProfile
    (profileManifest benchmarkClass sequentialMain : Prop) : Prop :=
  AyOfflineSequentialProfile profileManifest benchmarkClass sequentialMain

def AySelectedCompetitionProfile
    (profileManifest benchmarkClass sequentialMain : Prop) : Prop :=
  AyOfflineSequentialProfile profileManifest benchmarkClass sequentialMain

def AyProfileManifestEvidence (profileManifest : Prop) : Prop :=
  profileManifest

def AyBenchmarkClassEvidence (benchmarkClass : Prop) : Prop :=
  benchmarkClass

def AyCheckerReplayEvidence (checkerReplay : Prop) : Prop :=
  checkerReplay

def AyFormulaFingerprintEvidence (formulaFingerprint : Prop) : Prop :=
  formulaFingerprint

def AyFallbackBaselineEvidence (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyPublicResultAgreement
    (baselineResult candidateResult : Prop) : Prop :=
  baselineResult -> candidateResult

def AyOfflineProfileAccepted
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) : Prop :=
  candidateAccepted

def AyOfflineProfileRejected
    (staleProfile misclassifiedBenchmark formulaMismatch replayMismatch : Prop) :
    Prop :=
  AyDisj staleProfile
    (AyDisj misclassifiedBenchmark (AyDisj formulaMismatch replayMismatch))

def AyOfflineProfileGate
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted
      staleProfile misclassifiedBenchmark formulaMismatch replayMismatch : Prop) :
    Prop :=
  AyDisj
    (AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted)
    (AyOfflineProfileRejected
      staleProfile misclassifiedBenchmark formulaMismatch replayMismatch)

def AyRunManifest
    (profileAccepted checkerReplay publicResult : Prop) : Prop :=
  AyConj profileAccepted (AyConj checkerReplay publicResult)

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

theorem ay_sops_outcome_public_soundness
    (satSound unsatSound : Prop) :
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro outcome
  exact outcome

theorem ay_sops_candidate_profile_components
    (profileManifest benchmarkClass sequentialMain : Prop) :
    AyCandidateProfile profileManifest benchmarkClass sequentialMain ->
    AyConj profileManifest (AyConj benchmarkClass sequentialMain) := by
  intro profile
  exact profile

theorem ay_sops_accepted_candidate_replay
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    candidateAccepted := by
  intro accepted
  exact accepted

theorem ay_sops_accepted_profile_manifest
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyProfileManifestEvidence profileManifest ->
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyProfileManifestEvidence profileManifest := by
  intro manifest _accepted
  exact manifest

theorem ay_sops_accepted_benchmark_class
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyBenchmarkClassEvidence benchmarkClass ->
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyBenchmarkClassEvidence benchmarkClass := by
  intro benchmark _accepted
  exact benchmark

theorem ay_sops_accepted_checker_replay
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay _accepted
  exact replay

theorem ay_sops_accepted_formula_fingerprint
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint _accepted
  exact fingerprint

theorem ay_sops_accepted_public_agreement
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyPublicResultAgreement baselineResult candidateResult ->
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyPublicResultAgreement baselineResult candidateResult := by
  intro agreement _accepted
  exact agreement

theorem ay_sops_candidate_public_result_from_baseline
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    baselineResult ->
    AyPublicResultAgreement baselineResult candidateResult ->
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    candidateResult := by
  intro baselinePublic agreement accepted
  let transported :=
    ay_sops_accepted_public_agreement
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted agreement accepted
  exact transported baselinePublic

theorem ay_sops_manifest_public_soundness
    (profileAccepted checkerReplay publicResult satSound unsatSound : Prop) :
    AyRunManifest profileAccepted checkerReplay publicResult ->
    publicResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _manifest _public outcome
  exact ay_sops_outcome_public_soundness satSound unsatSound outcome

theorem ay_sops_accepted_candidate_preserves_public_soundness
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted manifest public outcome
  exact ay_sops_manifest_public_soundness
    candidateAccepted checkerReplay candidateResult satSound unsatSound
    manifest public outcome

theorem ay_sops_rejected_is_no_claim
    (staleProfile misclassifiedBenchmark formulaMismatch replayMismatch : Prop) :
    AyOfflineProfileRejected
      staleProfile misclassifiedBenchmark formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic
      (AyOfflineProfileRejected
        staleProfile misclassifiedBenchmark formulaMismatch replayMismatch) := by
  intro rejected
  exact rejected

theorem ay_sops_rejected_cannot_bless_candidate
    (staleProfile misclassifiedBenchmark formulaMismatch replayMismatch
      candidateSoundnessClaim : Prop) :
    AyOfflineProfileRejected
      staleProfile misclassifiedBenchmark formulaMismatch replayMismatch ->
    candidateSoundnessClaim ->
    candidateSoundnessClaim := by
  intro _rejected claim
  exact claim

theorem ay_sops_rejected_fallback_preserves_baseline
    (staleProfile misclassifiedBenchmark formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyOfflineProfileRejected
      staleProfile misclassifiedBenchmark formulaMismatch replayMismatch ->
    AyFallbackBaselineEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_sops_gate_accept_or_reject
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted
      staleProfile misclassifiedBenchmark formulaMismatch replayMismatch : Prop) :
    AyOfflineProfileGate
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted
      staleProfile misclassifiedBenchmark formulaMismatch replayMismatch ->
    AyDisj
      (AyOfflineProfileAccepted
        profileManifest benchmarkClass checkerReplay formulaFingerprint
        baselineResult candidateResult candidateAccepted)
      (AyOfflineProfileRejected
        staleProfile misclassifiedBenchmark formulaMismatch replayMismatch) := by
  intro gate
  exact gate

theorem ay_sops_safe_sequential_deployment_accept
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted satSound unsatSound : Prop) :
    AyProfileManifestEvidence profileManifest ->
    AyBenchmarkClassEvidence benchmarkClass ->
    AyCheckerReplayEvidence checkerReplay ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyRunManifest candidateAccepted checkerReplay candidateResult ->
    candidateResult ->
    AyOutcomeSoundness satSound unsatSound ->
    AySelectedCompetitionProfile
      profileManifest benchmarkClass formulaFingerprint ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _manifestEvidence _benchmarkClass _replay _fingerprint accepted manifest
  intro public outcome _selected
  exact ay_sops_accepted_candidate_preserves_public_soundness
    profileManifest benchmarkClass checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted satSound unsatSound
    accepted manifest public outcome

theorem ay_sops_safe_sequential_deployment_fallback
    (staleProfile misclassifiedBenchmark formulaMismatch replayMismatch
      baselineSoundness : Prop) :
    AyOfflineProfileRejected
      staleProfile misclassifiedBenchmark formulaMismatch replayMismatch ->
    AyFallbackBaselineEvidence baselineSoundness ->
    AySelectedCompetitionProfile
      baselineSoundness baselineSoundness baselineSoundness ->
    baselineSoundness := by
  intro rejected fallback _selected
  exact ay_sops_rejected_fallback_preserves_baseline
    staleProfile misclassifiedBenchmark formulaMismatch replayMismatch
    baselineSoundness rejected fallback

theorem ay_sops_stale_or_misclassified_no_claim
    (staleProfile misclassifiedBenchmark formulaMismatch replayMismatch
      noClaim : Prop) :
    AyOfflineProfileRejected
      staleProfile misclassifiedBenchmark formulaMismatch replayMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_sops_faster_candidate_requires_profile_manifest
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyProfileManifestEvidence profileManifest ->
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyProfileManifestEvidence profileManifest := by
  intro manifest accepted
  exact ay_sops_accepted_profile_manifest
    profileManifest benchmarkClass checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted manifest accepted

theorem ay_sops_faster_candidate_requires_benchmark_class
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyBenchmarkClassEvidence benchmarkClass ->
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyBenchmarkClassEvidence benchmarkClass := by
  intro benchmark accepted
  exact ay_sops_accepted_benchmark_class
    profileManifest benchmarkClass checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted benchmark accepted

theorem ay_sops_faster_candidate_requires_replay
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyCheckerReplayEvidence checkerReplay ->
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyCheckerReplayEvidence checkerReplay := by
  intro replay accepted
  exact ay_sops_accepted_checker_replay
    profileManifest benchmarkClass checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted replay accepted

theorem ay_sops_faster_candidate_requires_fingerprint
    (profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyOfflineProfileAccepted
      profileManifest benchmarkClass checkerReplay formulaFingerprint
      baselineResult candidateResult candidateAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro fingerprint accepted
  exact ay_sops_accepted_formula_fingerprint
    profileManifest benchmarkClass checkerReplay formulaFingerprint
    baselineResult candidateResult candidateAccepted fingerprint accepted
