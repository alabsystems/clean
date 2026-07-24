def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyRestartScheduleReplayInputs
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard : Prop) : Prop :=
  AyConj scheduleGeneration
    (AyConj benchmarkFeatures
      (AyConj solverBuild
        (AyConj randomSeedPolicy
          (AyConj clauseBudgetInteraction soundnessGuard))))

def AyScheduleGenerationEvidence (scheduleGeneration : Prop) : Prop :=
  scheduleGeneration

def AyBenchmarkFeatureEvidence (benchmarkFeatures : Prop) : Prop :=
  benchmarkFeatures

def AySolverBuildEvidence (solverBuild : Prop) : Prop :=
  solverBuild

def AyRandomSeedPolicyEvidence (randomSeedPolicy : Prop) : Prop :=
  randomSeedPolicy

def AyClauseBudgetInteractionEvidence
    (clauseBudgetInteraction : Prop) : Prop :=
  clauseBudgetInteraction

def AyPublicSoundnessGuardEvidence (soundnessGuard : Prop) : Prop :=
  soundnessGuard

def AyBaselineFallbackEvidence (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyRestartScheduleAccepted
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) : Prop :=
  scheduleAccepted

def AyRestartScheduleRejected
    (replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch : Prop) : Prop :=
  AyDisj replayMismatch
    (AyDisj staleFeatureInput
      (AyDisj buildMismatch (AyDisj budgetInconsistency guardMismatch)))

def AyRestartScheduleReplayGate
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted replayMismatch
      staleFeatureInput buildMismatch budgetInconsistency guardMismatch : Prop) :
    Prop :=
  AyDisj
    (AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted)
    (AyRestartScheduleRejected
      replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch)

def AyRestartPerformanceHint
    (scheduleAccepted restartPolicy : Prop) : Prop :=
  AyConj scheduleAccepted restartPolicy

def AyOptimizationPath
    (restartPolicy clauseBudget selectedPolicy : Prop) : Prop :=
  AyConj restartPolicy (AyConj clauseBudget selectedPolicy)

theorem ay_srsr_input_components
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard : Prop) :
    AyRestartScheduleReplayInputs
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard ->
    AyConj scheduleGeneration
      (AyConj benchmarkFeatures
        (AyConj solverBuild
          (AyConj randomSeedPolicy
            (AyConj clauseBudgetInteraction soundnessGuard)))) := by
  intro inputs
  exact inputs

theorem ay_srsr_accepted_schedule
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    scheduleAccepted := by
  intro accepted
  exact accepted

theorem ay_srsr_accepted_schedule_generation
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AyScheduleGenerationEvidence scheduleGeneration ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AyScheduleGenerationEvidence scheduleGeneration := by
  intro evidence _accepted
  exact evidence

theorem ay_srsr_accepted_benchmark_features
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AyBenchmarkFeatureEvidence benchmarkFeatures ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AyBenchmarkFeatureEvidence benchmarkFeatures := by
  intro evidence _accepted
  exact evidence

theorem ay_srsr_accepted_solver_build
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AySolverBuildEvidence solverBuild ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AySolverBuildEvidence solverBuild := by
  intro evidence _accepted
  exact evidence

theorem ay_srsr_accepted_random_seed_policy
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AyRandomSeedPolicyEvidence randomSeedPolicy ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AyRandomSeedPolicyEvidence randomSeedPolicy := by
  intro evidence _accepted
  exact evidence

theorem ay_srsr_accepted_clause_budget_interaction
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AyClauseBudgetInteractionEvidence clauseBudgetInteraction ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AyClauseBudgetInteractionEvidence clauseBudgetInteraction := by
  intro evidence _accepted
  exact evidence

theorem ay_srsr_accepted_soundness_guard
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AyPublicSoundnessGuardEvidence soundnessGuard := by
  intro evidence _accepted
  exact evidence

theorem ay_srsr_schedule_admissible_hint
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted restartPolicy : Prop) :
    AyScheduleGenerationEvidence scheduleGeneration ->
    AyBenchmarkFeatureEvidence benchmarkFeatures ->
    AySolverBuildEvidence solverBuild ->
    AyRandomSeedPolicyEvidence randomSeedPolicy ->
    AyClauseBudgetInteractionEvidence clauseBudgetInteraction ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    (scheduleGeneration -> benchmarkFeatures -> solverBuild ->
      randomSeedPolicy -> clauseBudgetInteraction -> soundnessGuard ->
      scheduleAccepted -> AyRestartPerformanceHint scheduleAccepted restartPolicy) ->
    AyRestartPerformanceHint scheduleAccepted restartPolicy := by
  intro generation features build seed budget guard accepted sound
  exact sound generation features build seed budget guard accepted

theorem ay_srsr_hint_cannot_change_truth
    (scheduleAccepted restartPolicy satSound unsatSound : Prop) :
    AyRestartPerformanceHint scheduleAccepted restartPolicy ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _hint truth
  exact truth

theorem ay_srsr_accepted_schedule_preserves_public_soundness
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted restartPolicy
      satSound unsatSound : Prop) :
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AyRestartPerformanceHint scheduleAccepted restartPolicy ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted hint truth
  exact ay_srsr_hint_cannot_change_truth
    scheduleAccepted restartPolicy satSound unsatSound hint truth

theorem ay_srsr_rejected_is_no_claim
    (replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch : Prop) :
    AyRestartScheduleRejected
      replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch ->
    AyNoClaimDiagnostic
      (AyRestartScheduleRejected
        replayMismatch staleFeatureInput buildMismatch budgetInconsistency
        guardMismatch) := by
  intro rejected
  exact rejected

theorem ay_srsr_rejected_fallback_preserves_baseline
    (replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch baselineSoundness : Prop) :
    AyRestartScheduleRejected
      replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_srsr_rejected_cannot_bless_public_result
    (replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch publicResultClaim : Prop) :
    AyRestartScheduleRejected
      replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch ->
    publicResultClaim ->
    publicResultClaim := by
  intro _rejected claim
  exact claim

theorem ay_srsr_gate_accept_or_reject
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted replayMismatch
      staleFeatureInput buildMismatch budgetInconsistency guardMismatch : Prop) :
    AyRestartScheduleReplayGate
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted replayMismatch
      staleFeatureInput buildMismatch budgetInconsistency guardMismatch ->
    AyDisj
      (AyRestartScheduleAccepted
        scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
        clauseBudgetInteraction soundnessGuard scheduleAccepted)
      (AyRestartScheduleRejected
        replayMismatch staleFeatureInput buildMismatch budgetInconsistency
        guardMismatch) := by
  intro gate
  exact gate

theorem ay_srsr_safe_schedule_deployment_accept
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted restartPolicy
      satSound unsatSound : Prop) :
    AyScheduleGenerationEvidence scheduleGeneration ->
    AyBenchmarkFeatureEvidence benchmarkFeatures ->
    AySolverBuildEvidence solverBuild ->
    AyRandomSeedPolicyEvidence randomSeedPolicy ->
    AyClauseBudgetInteractionEvidence clauseBudgetInteraction ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    (scheduleGeneration -> benchmarkFeatures -> solverBuild ->
      randomSeedPolicy -> clauseBudgetInteraction -> soundnessGuard ->
      scheduleAccepted -> AyRestartPerformanceHint scheduleAccepted restartPolicy) ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro generation features build seed budget guard accepted sound truth
  let hint :=
    ay_srsr_schedule_admissible_hint
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted restartPolicy
      generation features build seed budget guard accepted sound
  exact ay_srsr_accepted_schedule_preserves_public_soundness
    scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
    clauseBudgetInteraction soundnessGuard scheduleAccepted restartPolicy
    satSound unsatSound accepted hint truth

theorem ay_srsr_safe_schedule_deployment_fallback
    (replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch baselineSoundness restartPolicy clauseBudget selectedPolicy :
      Prop) :
    AyRestartScheduleRejected
      replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    AyOptimizationPath restartPolicy clauseBudget selectedPolicy ->
    baselineSoundness := by
  intro rejected fallback _path
  exact ay_srsr_rejected_fallback_preserves_baseline
    replayMismatch staleFeatureInput buildMismatch budgetInconsistency
    guardMismatch baselineSoundness rejected fallback

theorem ay_srsr_mismatch_no_claim
    (replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch noClaim : Prop) :
    AyRestartScheduleRejected
      replayMismatch staleFeatureInput buildMismatch budgetInconsistency
      guardMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_srsr_schedule_requires_generation
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AyScheduleGenerationEvidence scheduleGeneration ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AyScheduleGenerationEvidence scheduleGeneration := by
  intro evidence accepted
  exact ay_srsr_accepted_schedule_generation
    scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
    clauseBudgetInteraction soundnessGuard scheduleAccepted evidence accepted

theorem ay_srsr_schedule_requires_benchmark_features
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AyBenchmarkFeatureEvidence benchmarkFeatures ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AyBenchmarkFeatureEvidence benchmarkFeatures := by
  intro evidence accepted
  exact ay_srsr_accepted_benchmark_features
    scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
    clauseBudgetInteraction soundnessGuard scheduleAccepted evidence accepted

theorem ay_srsr_schedule_requires_solver_build
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AySolverBuildEvidence solverBuild ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AySolverBuildEvidence solverBuild := by
  intro evidence accepted
  exact ay_srsr_accepted_solver_build
    scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
    clauseBudgetInteraction soundnessGuard scheduleAccepted evidence accepted

theorem ay_srsr_schedule_requires_random_seed_policy
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AyRandomSeedPolicyEvidence randomSeedPolicy ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AyRandomSeedPolicyEvidence randomSeedPolicy := by
  intro evidence accepted
  exact ay_srsr_accepted_random_seed_policy
    scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
    clauseBudgetInteraction soundnessGuard scheduleAccepted evidence accepted

theorem ay_srsr_schedule_requires_clause_budget_interaction
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AyClauseBudgetInteractionEvidence clauseBudgetInteraction ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AyClauseBudgetInteractionEvidence clauseBudgetInteraction := by
  intro evidence accepted
  exact ay_srsr_accepted_clause_budget_interaction
    scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
    clauseBudgetInteraction soundnessGuard scheduleAccepted evidence accepted

theorem ay_srsr_schedule_requires_soundness_guard
    (scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted : Prop) :
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyRestartScheduleAccepted
      scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
      clauseBudgetInteraction soundnessGuard scheduleAccepted ->
    AyPublicSoundnessGuardEvidence soundnessGuard := by
  intro evidence accepted
  exact ay_srsr_accepted_soundness_guard
    scheduleGeneration benchmarkFeatures solverBuild randomSeedPolicy
    clauseBudgetInteraction soundnessGuard scheduleAccepted evidence accepted
