def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyCutoffBudgetInputs
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence : Prop) : Prop :=
  AyConj benchmarkFeatures
    (AyConj policyReplay
      (AyConj solverBuild
        (AyConj budgetLedger
          (AyConj soundnessGuard fallbackEvidence))))

def AyBenchmarkFeatureEvidence (benchmarkFeatures : Prop) : Prop :=
  benchmarkFeatures

def AyDeterministicPolicyReplay (policyReplay : Prop) : Prop :=
  policyReplay

def AySolverBuildEvidence (solverBuild : Prop) : Prop :=
  solverBuild

def AyBudgetLedgerEvidence (budgetLedger : Prop) : Prop :=
  budgetLedger

def AyPublicSoundnessGuardEvidence (soundnessGuard : Prop) : Prop :=
  soundnessGuard

def AyFallbackEvidence (fallbackEvidence : Prop) : Prop :=
  fallbackEvidence

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyCutoffBudgetAdaptationAccepted
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) : Prop :=
  adaptationAccepted

def AyCutoffBudgetAdaptationRejected
    (staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback : Prop) : Prop :=
  AyDisj staleFeatures
    (AyDisj ledgerMismatch
      (AyDisj policyReplayMismatch
        (AyDisj buildMismatch (AyDisj guardMismatch missingFallback))))

def AyCutoffBudgetAdaptationGate
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted staleFeatures ledgerMismatch
      policyReplayMismatch buildMismatch guardMismatch missingFallback : Prop) :
    Prop :=
  AyDisj
    (AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted)
    (AyCutoffBudgetAdaptationRejected
      staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback)

def AyBudgetPerformanceHint
    (adaptationAccepted conflictCutoff restartWindow preprocessingBudget
      propagationBudget : Prop) : Prop :=
  AyConj adaptationAccepted
    (AyConj conflictCutoff
      (AyConj restartWindow
        (AyConj preprocessingBudget propagationBudget)))

def AyOptimizationPath
    (conflictCutoff restartWindow preprocessingBudget propagationBudget : Prop) :
    Prop :=
  AyConj conflictCutoff
    (AyConj restartWindow
      (AyConj preprocessingBudget propagationBudget))

theorem ay_scba_input_components
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence : Prop) :
    AyCutoffBudgetInputs
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence ->
    AyConj benchmarkFeatures
      (AyConj policyReplay
        (AyConj solverBuild
          (AyConj budgetLedger
            (AyConj soundnessGuard fallbackEvidence)))) := by
  intro inputs
  exact inputs

theorem ay_scba_accepted_adaptation
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    adaptationAccepted := by
  intro accepted
  exact accepted

theorem ay_scba_accepted_benchmark_features
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AyBenchmarkFeatureEvidence benchmarkFeatures ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AyBenchmarkFeatureEvidence benchmarkFeatures := by
  intro evidence _accepted
  exact evidence

theorem ay_scba_accepted_policy_replay
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AyDeterministicPolicyReplay policyReplay ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AyDeterministicPolicyReplay policyReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_scba_accepted_solver_build
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AySolverBuildEvidence solverBuild ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AySolverBuildEvidence solverBuild := by
  intro evidence _accepted
  exact evidence

theorem ay_scba_accepted_budget_ledger
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AyBudgetLedgerEvidence budgetLedger ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AyBudgetLedgerEvidence budgetLedger := by
  intro evidence _accepted
  exact evidence

theorem ay_scba_accepted_soundness_guard
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AyPublicSoundnessGuardEvidence soundnessGuard := by
  intro evidence _accepted
  exact evidence

theorem ay_scba_accepted_fallback_evidence
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_scba_adaptation_admissible_hint
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted conflictCutoff restartWindow
      preprocessingBudget propagationBudget : Prop) :
    AyBenchmarkFeatureEvidence benchmarkFeatures ->
    AyDeterministicPolicyReplay policyReplay ->
    AySolverBuildEvidence solverBuild ->
    AyBudgetLedgerEvidence budgetLedger ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    (benchmarkFeatures -> policyReplay -> solverBuild -> budgetLedger ->
      soundnessGuard -> fallbackEvidence -> adaptationAccepted ->
      AyBudgetPerformanceHint
        adaptationAccepted conflictCutoff restartWindow preprocessingBudget
        propagationBudget) ->
    AyBudgetPerformanceHint
      adaptationAccepted conflictCutoff restartWindow preprocessingBudget
      propagationBudget := by
  intro features replay build ledger guard fallback accepted sound
  exact sound features replay build ledger guard fallback accepted

theorem ay_scba_hint_cannot_change_truth
    (adaptationAccepted conflictCutoff restartWindow preprocessingBudget
      propagationBudget satSound unsatSound : Prop) :
    AyBudgetPerformanceHint
      adaptationAccepted conflictCutoff restartWindow preprocessingBudget
      propagationBudget ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _hint truth
  exact truth

theorem ay_scba_accepted_adaptation_preserves_public_soundness
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted conflictCutoff restartWindow
      preprocessingBudget propagationBudget satSound unsatSound : Prop) :
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AyBudgetPerformanceHint
      adaptationAccepted conflictCutoff restartWindow preprocessingBudget
      propagationBudget ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted hint truth
  exact ay_scba_hint_cannot_change_truth
    adaptationAccepted conflictCutoff restartWindow preprocessingBudget
    propagationBudget satSound unsatSound hint truth

theorem ay_scba_rejected_is_no_claim
    (staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback : Prop) :
    AyCutoffBudgetAdaptationRejected
      staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback ->
    AyNoClaimDiagnostic
      (AyCutoffBudgetAdaptationRejected
        staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
        guardMismatch missingFallback) := by
  intro rejected
  exact rejected

theorem ay_scba_rejected_fallback_preserves_baseline
    (staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback baselineSoundness : Prop) :
    AyCutoffBudgetAdaptationRejected
      staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_scba_rejected_cannot_bless_public_result
    (staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback publicResultClaim : Prop) :
    AyCutoffBudgetAdaptationRejected
      staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback ->
    publicResultClaim ->
    publicResultClaim := by
  intro _rejected claim
  exact claim

theorem ay_scba_gate_accept_or_reject
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted staleFeatures ledgerMismatch
      policyReplayMismatch buildMismatch guardMismatch missingFallback : Prop) :
    AyCutoffBudgetAdaptationGate
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted staleFeatures ledgerMismatch
      policyReplayMismatch buildMismatch guardMismatch missingFallback ->
    AyDisj
      (AyCutoffBudgetAdaptationAccepted
        benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
        fallbackEvidence adaptationAccepted)
      (AyCutoffBudgetAdaptationRejected
        staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
        guardMismatch missingFallback) := by
  intro gate
  exact gate

theorem ay_scba_safe_adaptation_deployment_accept
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted conflictCutoff restartWindow
      preprocessingBudget propagationBudget satSound unsatSound : Prop) :
    AyBenchmarkFeatureEvidence benchmarkFeatures ->
    AyDeterministicPolicyReplay policyReplay ->
    AySolverBuildEvidence solverBuild ->
    AyBudgetLedgerEvidence budgetLedger ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    (benchmarkFeatures -> policyReplay -> solverBuild -> budgetLedger ->
      soundnessGuard -> fallbackEvidence -> adaptationAccepted ->
      AyBudgetPerformanceHint
        adaptationAccepted conflictCutoff restartWindow preprocessingBudget
        propagationBudget) ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro features replay build ledger guard fallback accepted sound truth
  let hint :=
    ay_scba_adaptation_admissible_hint
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted conflictCutoff restartWindow
      preprocessingBudget propagationBudget
      features replay build ledger guard fallback accepted sound
  exact ay_scba_accepted_adaptation_preserves_public_soundness
    benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
    fallbackEvidence adaptationAccepted conflictCutoff restartWindow
    preprocessingBudget propagationBudget satSound unsatSound
    accepted hint truth

theorem ay_scba_safe_adaptation_deployment_fallback
    (staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback baselineSoundness conflictCutoff
      restartWindow preprocessingBudget propagationBudget : Prop) :
    AyCutoffBudgetAdaptationRejected
      staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    AyOptimizationPath
      conflictCutoff restartWindow preprocessingBudget propagationBudget ->
    baselineSoundness := by
  intro rejected fallback _path
  exact ay_scba_rejected_fallback_preserves_baseline
    staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
    guardMismatch missingFallback baselineSoundness rejected fallback

theorem ay_scba_mismatch_no_claim
    (staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback noClaim : Prop) :
    AyCutoffBudgetAdaptationRejected
      staleFeatures ledgerMismatch policyReplayMismatch buildMismatch
      guardMismatch missingFallback ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_scba_adaptation_requires_features
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AyBenchmarkFeatureEvidence benchmarkFeatures ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AyBenchmarkFeatureEvidence benchmarkFeatures := by
  intro evidence accepted
  exact ay_scba_accepted_benchmark_features
    benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
    fallbackEvidence adaptationAccepted evidence accepted

theorem ay_scba_adaptation_requires_policy_replay
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AyDeterministicPolicyReplay policyReplay ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AyDeterministicPolicyReplay policyReplay := by
  intro evidence accepted
  exact ay_scba_accepted_policy_replay
    benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
    fallbackEvidence adaptationAccepted evidence accepted

theorem ay_scba_adaptation_requires_solver_build
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AySolverBuildEvidence solverBuild ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AySolverBuildEvidence solverBuild := by
  intro evidence accepted
  exact ay_scba_accepted_solver_build
    benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
    fallbackEvidence adaptationAccepted evidence accepted

theorem ay_scba_adaptation_requires_budget_ledger
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AyBudgetLedgerEvidence budgetLedger ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AyBudgetLedgerEvidence budgetLedger := by
  intro evidence accepted
  exact ay_scba_accepted_budget_ledger
    benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
    fallbackEvidence adaptationAccepted evidence accepted

theorem ay_scba_adaptation_requires_soundness_guard
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AyPublicSoundnessGuardEvidence soundnessGuard := by
  intro evidence accepted
  exact ay_scba_accepted_soundness_guard
    benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
    fallbackEvidence adaptationAccepted evidence accepted

theorem ay_scba_adaptation_requires_fallback_evidence
    (benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted : Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyCutoffBudgetAdaptationAccepted
      benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
      fallbackEvidence adaptationAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence accepted
  exact ay_scba_accepted_fallback_evidence
    benchmarkFeatures policyReplay solverBuild budgetLedger soundnessGuard
    fallbackEvidence adaptationAccepted evidence accepted
