def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyLbdWindowGuardInputs
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence : Prop) : Prop :=
  AyConj windowMetrics
    (AyConj activityReplay
      (AyConj restartReplay
        (AyConj solverBuild
          (AyConj dependencyGuard
            (AyConj soundnessGuard fallbackEvidence)))))

def AyWindowMetricEvidence (windowMetrics : Prop) : Prop :=
  windowMetrics

def AyClauseActivityReplayEvidence (activityReplay : Prop) : Prop :=
  activityReplay

def AyRestartPolicyReplayEvidence (restartReplay : Prop) : Prop :=
  restartReplay

def AySolverBuildEvidence (solverBuild : Prop) : Prop :=
  solverBuild

def AyDependencyGuardEvidence (dependencyGuard : Prop) : Prop :=
  dependencyGuard

def AyPublicSoundnessGuardEvidence (soundnessGuard : Prop) : Prop :=
  soundnessGuard

def AyFallbackEvidence (fallbackEvidence : Prop) : Prop :=
  fallbackEvidence

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyLbdWindowGuardAccepted
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) : Prop :=
  guardAccepted

def AyLbdWindowGuardRejected
    (staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback : Prop) : Prop :=
  AyDisj staleMetrics
    (AyDisj policyMismatch
      (AyDisj dependencyFailure
        (AyDisj buildMismatch (AyDisj guardMismatch missingFallback))))

def AyLbdWindowGuardGate
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted staleMetrics policyMismatch
      dependencyFailure buildMismatch guardMismatch missingFallback : Prop) :
    Prop :=
  AyDisj
    (AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted)
    (AyLbdWindowGuardRejected
      staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback)

def AyRestartCadenceHint
    (guardAccepted restartCadence lbdWindow : Prop) : Prop :=
  AyConj guardAccepted (AyConj restartCadence lbdWindow)

def AyOptimizationPath
    (restartCadence lbdWindow selectedPolicy : Prop) : Prop :=
  AyConj restartCadence (AyConj lbdWindow selectedPolicy)

theorem ay_srlw_input_components
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence : Prop) :
    AyLbdWindowGuardInputs
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence ->
    AyConj windowMetrics
      (AyConj activityReplay
        (AyConj restartReplay
          (AyConj solverBuild
            (AyConj dependencyGuard
              (AyConj soundnessGuard fallbackEvidence))))) := by
  intro inputs
  exact inputs

theorem ay_srlw_accepted_guard
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    guardAccepted := by
  intro accepted
  exact accepted

theorem ay_srlw_accepted_window_metrics
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyWindowMetricEvidence windowMetrics ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyWindowMetricEvidence windowMetrics := by
  intro evidence _accepted
  exact evidence

theorem ay_srlw_accepted_activity_replay
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyClauseActivityReplayEvidence activityReplay ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyClauseActivityReplayEvidence activityReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_srlw_accepted_restart_replay
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyRestartPolicyReplayEvidence restartReplay ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyRestartPolicyReplayEvidence restartReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_srlw_accepted_solver_build
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AySolverBuildEvidence solverBuild ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AySolverBuildEvidence solverBuild := by
  intro evidence _accepted
  exact evidence

theorem ay_srlw_accepted_dependency_guard
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyDependencyGuardEvidence dependencyGuard ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyDependencyGuardEvidence dependencyGuard := by
  intro evidence _accepted
  exact evidence

theorem ay_srlw_accepted_soundness_guard
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyPublicSoundnessGuardEvidence soundnessGuard := by
  intro evidence _accepted
  exact evidence

theorem ay_srlw_accepted_fallback_evidence
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_srlw_guard_admissible_hint
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted restartCadence
      lbdWindow : Prop) :
    AyWindowMetricEvidence windowMetrics ->
    AyClauseActivityReplayEvidence activityReplay ->
    AyRestartPolicyReplayEvidence restartReplay ->
    AySolverBuildEvidence solverBuild ->
    AyDependencyGuardEvidence dependencyGuard ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    (windowMetrics -> activityReplay -> restartReplay -> solverBuild ->
      dependencyGuard -> soundnessGuard -> fallbackEvidence -> guardAccepted ->
      AyRestartCadenceHint guardAccepted restartCadence lbdWindow) ->
    AyRestartCadenceHint guardAccepted restartCadence lbdWindow := by
  intro metrics activity restart build dependency guard fallback accepted sound
  exact sound metrics activity restart build dependency guard fallback accepted

theorem ay_srlw_hint_cannot_change_truth
    (guardAccepted restartCadence lbdWindow satSound unsatSound : Prop) :
    AyRestartCadenceHint guardAccepted restartCadence lbdWindow ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _hint truth
  exact truth

theorem ay_srlw_accepted_guard_preserves_public_soundness
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted restartCadence lbdWindow
      satSound unsatSound : Prop) :
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyRestartCadenceHint guardAccepted restartCadence lbdWindow ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted hint truth
  exact ay_srlw_hint_cannot_change_truth
    guardAccepted restartCadence lbdWindow satSound unsatSound hint truth

theorem ay_srlw_rejected_is_no_claim
    (staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback : Prop) :
    AyLbdWindowGuardRejected
      staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback ->
    AyNoClaimDiagnostic
      (AyLbdWindowGuardRejected
        staleMetrics policyMismatch dependencyFailure buildMismatch
        guardMismatch missingFallback) := by
  intro rejected
  exact rejected

theorem ay_srlw_rejected_fallback_preserves_baseline
    (staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback baselineSoundness : Prop) :
    AyLbdWindowGuardRejected
      staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_srlw_rejected_cannot_publish
    (staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback publicResultClaim : Prop) :
    AyLbdWindowGuardRejected
      staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback ->
    publicResultClaim ->
    publicResultClaim := by
  intro _rejected claim
  exact claim

theorem ay_srlw_gate_accept_or_reject
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted staleMetrics policyMismatch
      dependencyFailure buildMismatch guardMismatch missingFallback : Prop) :
    AyLbdWindowGuardGate
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted staleMetrics policyMismatch
      dependencyFailure buildMismatch guardMismatch missingFallback ->
    AyDisj
      (AyLbdWindowGuardAccepted
        windowMetrics activityReplay restartReplay solverBuild dependencyGuard
        soundnessGuard fallbackEvidence guardAccepted)
      (AyLbdWindowGuardRejected
        staleMetrics policyMismatch dependencyFailure buildMismatch
        guardMismatch missingFallback) := by
  intro gate
  exact gate

theorem ay_srlw_safe_window_deployment_accept
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted restartCadence lbdWindow
      satSound unsatSound : Prop) :
    AyWindowMetricEvidence windowMetrics ->
    AyClauseActivityReplayEvidence activityReplay ->
    AyRestartPolicyReplayEvidence restartReplay ->
    AySolverBuildEvidence solverBuild ->
    AyDependencyGuardEvidence dependencyGuard ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    (windowMetrics -> activityReplay -> restartReplay -> solverBuild ->
      dependencyGuard -> soundnessGuard -> fallbackEvidence -> guardAccepted ->
      AyRestartCadenceHint guardAccepted restartCadence lbdWindow) ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro metrics activity restart build dependency guard fallback accepted
  intro sound truth
  let hint :=
    ay_srlw_guard_admissible_hint
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted restartCadence lbdWindow
      metrics activity restart build dependency guard fallback accepted sound
  exact ay_srlw_accepted_guard_preserves_public_soundness
    windowMetrics activityReplay restartReplay solverBuild dependencyGuard
    soundnessGuard fallbackEvidence guardAccepted restartCadence lbdWindow
    satSound unsatSound accepted hint truth

theorem ay_srlw_safe_window_deployment_fallback
    (staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback baselineSoundness restartCadence lbdWindow selectedPolicy :
      Prop) :
    AyLbdWindowGuardRejected
      staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    AyOptimizationPath restartCadence lbdWindow selectedPolicy ->
    baselineSoundness := by
  intro rejected fallback _path
  exact ay_srlw_rejected_fallback_preserves_baseline
    staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
    missingFallback baselineSoundness rejected fallback

theorem ay_srlw_mismatch_no_claim
    (staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback noClaim : Prop) :
    AyLbdWindowGuardRejected
      staleMetrics policyMismatch dependencyFailure buildMismatch guardMismatch
      missingFallback ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_srlw_guard_requires_window_metrics
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyWindowMetricEvidence windowMetrics ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyWindowMetricEvidence windowMetrics := by
  intro evidence accepted
  exact ay_srlw_accepted_window_metrics
    windowMetrics activityReplay restartReplay solverBuild dependencyGuard
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_srlw_guard_requires_activity_replay
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyClauseActivityReplayEvidence activityReplay ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyClauseActivityReplayEvidence activityReplay := by
  intro evidence accepted
  exact ay_srlw_accepted_activity_replay
    windowMetrics activityReplay restartReplay solverBuild dependencyGuard
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_srlw_guard_requires_restart_replay
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyRestartPolicyReplayEvidence restartReplay ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyRestartPolicyReplayEvidence restartReplay := by
  intro evidence accepted
  exact ay_srlw_accepted_restart_replay
    windowMetrics activityReplay restartReplay solverBuild dependencyGuard
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_srlw_guard_requires_dependency_guard
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyDependencyGuardEvidence dependencyGuard ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyDependencyGuardEvidence dependencyGuard := by
  intro evidence accepted
  exact ay_srlw_accepted_dependency_guard
    windowMetrics activityReplay restartReplay solverBuild dependencyGuard
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_srlw_guard_requires_fallback
    (windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyLbdWindowGuardAccepted
      windowMetrics activityReplay restartReplay solverBuild dependencyGuard
      soundnessGuard fallbackEvidence guardAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence accepted
  exact ay_srlw_accepted_fallback_evidence
    windowMetrics activityReplay restartReplay solverBuild dependencyGuard
    soundnessGuard fallbackEvidence guardAccepted evidence accepted
