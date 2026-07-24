def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyDynamicPreprocessInputs
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence : Prop) : Prop :=
  AyConj passPolicyReplay
    (AyConj benchmarkFeatures
      (AyConj fingerprintLineage
        (AyConj budgetLedger
          (AyConj reconstructionEvidence
            (AyConj soundnessGuard fallbackEvidence)))))

def AyPassPolicyReplayEvidence (passPolicyReplay : Prop) : Prop :=
  passPolicyReplay

def AyBenchmarkFeatureEvidence (benchmarkFeatures : Prop) : Prop :=
  benchmarkFeatures

def AyFingerprintLineageEvidence (fingerprintLineage : Prop) : Prop :=
  fingerprintLineage

def AyBudgetLedgerEvidence (budgetLedger : Prop) : Prop :=
  budgetLedger

def AyReconstructionEvidence (reconstructionEvidence : Prop) : Prop :=
  reconstructionEvidence

def AyPublicSoundnessGuardEvidence (soundnessGuard : Prop) : Prop :=
  soundnessGuard

def AyFallbackEvidence (fallbackEvidence : Prop) : Prop :=
  fallbackEvidence

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyDynamicPreprocessGateAccepted
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) : Prop :=
  gateAccepted

def AyDynamicPreprocessGateRejected
    (policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback : Prop) : Prop :=
  AyDisj policyDrift
    (AyDisj budgetMismatch
      (AyDisj missingReconstruction
        (AyDisj fingerprintDrift (AyDisj guardMismatch missingFallback))))

def AyDynamicPreprocessGate
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
      policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback : Prop) : Prop :=
  AyDisj
    (AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted)
    (AyDynamicPreprocessGateRejected
      policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback)

def AyPreprocessPerformanceHint
    (gateAccepted enabledPasses disabledPasses inSearchBudget : Prop) : Prop :=
  AyConj gateAccepted
    (AyConj enabledPasses (AyConj disabledPasses inSearchBudget))

def AyOptimizationPath
    (enabledPasses disabledPasses inSearchBudget selectedPolicy : Prop) : Prop :=
  AyConj enabledPasses
    (AyConj disabledPasses (AyConj inSearchBudget selectedPolicy))

theorem ay_sdpg_input_components
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence : Prop) :
    AyDynamicPreprocessInputs
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence ->
    AyConj passPolicyReplay
      (AyConj benchmarkFeatures
        (AyConj fingerprintLineage
          (AyConj budgetLedger
            (AyConj reconstructionEvidence
              (AyConj soundnessGuard fallbackEvidence))))) := by
  intro inputs
  exact inputs

theorem ay_sdpg_accepted_gate
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    gateAccepted := by
  intro accepted
  exact accepted

theorem ay_sdpg_accepted_policy_replay
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyPassPolicyReplayEvidence passPolicyReplay ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyPassPolicyReplayEvidence passPolicyReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_sdpg_accepted_benchmark_features
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyBenchmarkFeatureEvidence benchmarkFeatures ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyBenchmarkFeatureEvidence benchmarkFeatures := by
  intro evidence _accepted
  exact evidence

theorem ay_sdpg_accepted_fingerprint_lineage
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyFingerprintLineageEvidence fingerprintLineage ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyFingerprintLineageEvidence fingerprintLineage := by
  intro evidence _accepted
  exact evidence

theorem ay_sdpg_accepted_budget_ledger
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyBudgetLedgerEvidence budgetLedger ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyBudgetLedgerEvidence budgetLedger := by
  intro evidence _accepted
  exact evidence

theorem ay_sdpg_accepted_reconstruction
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyReconstructionEvidence reconstructionEvidence ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyReconstructionEvidence reconstructionEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_sdpg_accepted_soundness_guard
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyPublicSoundnessGuardEvidence soundnessGuard := by
  intro evidence _accepted
  exact evidence

theorem ay_sdpg_accepted_fallback_evidence
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_sdpg_gate_admissible_hint
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
      enabledPasses disabledPasses inSearchBudget : Prop) :
    AyPassPolicyReplayEvidence passPolicyReplay ->
    AyBenchmarkFeatureEvidence benchmarkFeatures ->
    AyFingerprintLineageEvidence fingerprintLineage ->
    AyBudgetLedgerEvidence budgetLedger ->
    AyReconstructionEvidence reconstructionEvidence ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    (passPolicyReplay -> benchmarkFeatures -> fingerprintLineage ->
      budgetLedger -> reconstructionEvidence -> soundnessGuard ->
      fallbackEvidence -> gateAccepted ->
      AyPreprocessPerformanceHint
        gateAccepted enabledPasses disabledPasses inSearchBudget) ->
    AyPreprocessPerformanceHint
      gateAccepted enabledPasses disabledPasses inSearchBudget := by
  intro policy features lineage ledger reconstruction guard fallback accepted
  intro sound
  exact sound policy features lineage ledger reconstruction guard fallback
    accepted

theorem ay_sdpg_hint_cannot_change_truth
    (gateAccepted enabledPasses disabledPasses inSearchBudget satSound
      unsatSound : Prop) :
    AyPreprocessPerformanceHint
      gateAccepted enabledPasses disabledPasses inSearchBudget ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _hint truth
  exact truth

theorem ay_sdpg_accepted_gate_preserves_public_soundness
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
      enabledPasses disabledPasses inSearchBudget satSound unsatSound : Prop) :
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyPreprocessPerformanceHint
      gateAccepted enabledPasses disabledPasses inSearchBudget ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted hint truth
  exact ay_sdpg_hint_cannot_change_truth
    gateAccepted enabledPasses disabledPasses inSearchBudget satSound
    unsatSound hint truth

theorem ay_sdpg_rejected_is_no_claim
    (policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback : Prop) :
    AyDynamicPreprocessGateRejected
      policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback ->
    AyNoClaimDiagnostic
      (AyDynamicPreprocessGateRejected
        policyDrift budgetMismatch missingReconstruction fingerprintDrift
        guardMismatch missingFallback) := by
  intro rejected
  exact rejected

theorem ay_sdpg_rejected_fallback_preserves_baseline
    (policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback baselineSoundness : Prop) :
    AyDynamicPreprocessGateRejected
      policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_sdpg_rejected_cannot_bless_public_result
    (policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback publicResultClaim : Prop) :
    AyDynamicPreprocessGateRejected
      policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback ->
    publicResultClaim ->
    publicResultClaim := by
  intro _rejected claim
  exact claim

theorem ay_sdpg_gate_accept_or_reject
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
      policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback : Prop) :
    AyDynamicPreprocessGate
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
      policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback ->
    AyDisj
      (AyDynamicPreprocessGateAccepted
        passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
        reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted)
      (AyDynamicPreprocessGateRejected
        policyDrift budgetMismatch missingReconstruction fingerprintDrift
        guardMismatch missingFallback) := by
  intro gate
  exact gate

theorem ay_sdpg_safe_preprocess_deployment_accept
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
      enabledPasses disabledPasses inSearchBudget satSound unsatSound : Prop) :
    AyPassPolicyReplayEvidence passPolicyReplay ->
    AyBenchmarkFeatureEvidence benchmarkFeatures ->
    AyFingerprintLineageEvidence fingerprintLineage ->
    AyBudgetLedgerEvidence budgetLedger ->
    AyReconstructionEvidence reconstructionEvidence ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    (passPolicyReplay -> benchmarkFeatures -> fingerprintLineage ->
      budgetLedger -> reconstructionEvidence -> soundnessGuard ->
      fallbackEvidence -> gateAccepted ->
      AyPreprocessPerformanceHint
        gateAccepted enabledPasses disabledPasses inSearchBudget) ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro policy features lineage ledger reconstruction guard fallback accepted
  intro sound truth
  let hint :=
    ay_sdpg_gate_admissible_hint
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
      enabledPasses disabledPasses inSearchBudget policy features lineage
      ledger reconstruction guard fallback accepted sound
  exact ay_sdpg_accepted_gate_preserves_public_soundness
    passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
    reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
    enabledPasses disabledPasses inSearchBudget satSound unsatSound
    accepted hint truth

theorem ay_sdpg_safe_preprocess_deployment_fallback
    (policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback baselineSoundness enabledPasses disabledPasses
      inSearchBudget selectedPolicy : Prop) :
    AyDynamicPreprocessGateRejected
      policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    AyOptimizationPath
      enabledPasses disabledPasses inSearchBudget selectedPolicy ->
    baselineSoundness := by
  intro rejected fallback _path
  exact ay_sdpg_rejected_fallback_preserves_baseline
    policyDrift budgetMismatch missingReconstruction fingerprintDrift
    guardMismatch missingFallback baselineSoundness rejected fallback

theorem ay_sdpg_mismatch_no_claim
    (policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback noClaim : Prop) :
    AyDynamicPreprocessGateRejected
      policyDrift budgetMismatch missingReconstruction fingerprintDrift
      guardMismatch missingFallback ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_sdpg_gate_requires_policy_replay
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyPassPolicyReplayEvidence passPolicyReplay ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyPassPolicyReplayEvidence passPolicyReplay := by
  intro evidence accepted
  exact ay_sdpg_accepted_policy_replay
    passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
    reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
    evidence accepted

theorem ay_sdpg_gate_requires_fingerprint_lineage
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyFingerprintLineageEvidence fingerprintLineage ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyFingerprintLineageEvidence fingerprintLineage := by
  intro evidence accepted
  exact ay_sdpg_accepted_fingerprint_lineage
    passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
    reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
    evidence accepted

theorem ay_sdpg_gate_requires_budget_ledger
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyBudgetLedgerEvidence budgetLedger ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyBudgetLedgerEvidence budgetLedger := by
  intro evidence accepted
  exact ay_sdpg_accepted_budget_ledger
    passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
    reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
    evidence accepted

theorem ay_sdpg_gate_requires_reconstruction
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyReconstructionEvidence reconstructionEvidence ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyReconstructionEvidence reconstructionEvidence := by
  intro evidence accepted
  exact ay_sdpg_accepted_reconstruction
    passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
    reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
    evidence accepted

theorem ay_sdpg_gate_requires_soundness_guard
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyPublicSoundnessGuardEvidence soundnessGuard := by
  intro evidence accepted
  exact ay_sdpg_accepted_soundness_guard
    passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
    reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
    evidence accepted

theorem ay_sdpg_gate_requires_fallback
    (passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted :
      Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyDynamicPreprocessGateAccepted
      passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
      reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence accepted
  exact ay_sdpg_accepted_fallback_evidence
    passPolicyReplay benchmarkFeatures fingerprintLineage budgetLedger
    reconstructionEvidence soundnessGuard fallbackEvidence gateAccepted
    evidence accepted
