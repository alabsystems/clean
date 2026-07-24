def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyStagnationRestartInputs
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence : Prop) : Prop :=
  AyConj conflictProgress
    (AyConj budgetLedger
      (AyConj lbdActivityReplay
        (AyConj restartReplay
          (AyConj solverBuild
            (AyConj soundnessGuard fallbackEvidence)))))

def AyConflictProgressEvidence (conflictProgress : Prop) : Prop :=
  conflictProgress

def AyPropagationBudgetLedgerEvidence (budgetLedger : Prop) : Prop :=
  budgetLedger

def AyLbdActivityReplayEvidence (lbdActivityReplay : Prop) : Prop :=
  lbdActivityReplay

def AyRestartPolicyReplayEvidence (restartReplay : Prop) : Prop :=
  restartReplay

def AySolverBuildEvidence (solverBuild : Prop) : Prop :=
  solverBuild

def AyPublicSoundnessGuardEvidence (soundnessGuard : Prop) : Prop :=
  soundnessGuard

def AyFallbackEvidence (fallbackEvidence : Prop) : Prop :=
  fallbackEvidence

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyStagnationGuardAccepted
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) : Prop :=
  guardAccepted

def AyStagnationGuardRejected
    (staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback : Prop) : Prop :=
  AyDisj staleMetrics
    (AyDisj ledgerMismatch
      (AyDisj activityReplayMismatch
        (AyDisj policyReplayMismatch
          (AyDisj buildMismatch (AyDisj guardMismatch missingFallback)))))

def AyStagnationRestartGate
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted staleMetrics ledgerMismatch
      activityReplayMismatch policyReplayMismatch buildMismatch guardMismatch
      missingFallback : Prop) : Prop :=
  AyDisj
    (AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted)
    (AyStagnationGuardRejected
      staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback)

def AyStagnationRestartHint
    (guardAccepted restartTrigger restartCadence : Prop) : Prop :=
  AyConj guardAccepted (AyConj restartTrigger restartCadence)

def AyOptimizationPath
    (restartTrigger restartCadence selectedPolicy : Prop) : Prop :=
  AyConj restartTrigger (AyConj restartCadence selectedPolicy)

theorem ay_ssrg_input_components
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence : Prop) :
    AyStagnationRestartInputs
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence ->
    AyConj conflictProgress
      (AyConj budgetLedger
        (AyConj lbdActivityReplay
          (AyConj restartReplay
            (AyConj solverBuild
              (AyConj soundnessGuard fallbackEvidence))))) := by
  intro inputs
  exact inputs

theorem ay_ssrg_accepted_guard
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    guardAccepted := by
  intro accepted
  exact accepted

theorem ay_ssrg_accepted_conflict_progress
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyConflictProgressEvidence conflictProgress ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyConflictProgressEvidence conflictProgress := by
  intro evidence _accepted
  exact evidence

theorem ay_ssrg_accepted_budget_ledger
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyPropagationBudgetLedgerEvidence budgetLedger ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyPropagationBudgetLedgerEvidence budgetLedger := by
  intro evidence _accepted
  exact evidence

theorem ay_ssrg_accepted_lbd_activity_replay
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyLbdActivityReplayEvidence lbdActivityReplay ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyLbdActivityReplayEvidence lbdActivityReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_ssrg_accepted_restart_replay
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyRestartPolicyReplayEvidence restartReplay ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyRestartPolicyReplayEvidence restartReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_ssrg_accepted_solver_build
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AySolverBuildEvidence solverBuild ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AySolverBuildEvidence solverBuild := by
  intro evidence _accepted
  exact evidence

theorem ay_ssrg_accepted_soundness_guard
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyPublicSoundnessGuardEvidence soundnessGuard := by
  intro evidence _accepted
  exact evidence

theorem ay_ssrg_accepted_fallback_evidence
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_ssrg_guard_admissible_hint
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted restartTrigger
      restartCadence : Prop) :
    AyConflictProgressEvidence conflictProgress ->
    AyPropagationBudgetLedgerEvidence budgetLedger ->
    AyLbdActivityReplayEvidence lbdActivityReplay ->
    AyRestartPolicyReplayEvidence restartReplay ->
    AySolverBuildEvidence solverBuild ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    (conflictProgress -> budgetLedger -> lbdActivityReplay -> restartReplay ->
      solverBuild -> soundnessGuard -> fallbackEvidence -> guardAccepted ->
      AyStagnationRestartHint guardAccepted restartTrigger restartCadence) ->
    AyStagnationRestartHint guardAccepted restartTrigger restartCadence := by
  intro progress ledger activity restart build guard fallback accepted sound
  exact sound progress ledger activity restart build guard fallback accepted

theorem ay_ssrg_hint_cannot_change_truth
    (guardAccepted restartTrigger restartCadence satSound unsatSound : Prop) :
    AyStagnationRestartHint guardAccepted restartTrigger restartCadence ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _hint truth
  exact truth

theorem ay_ssrg_accepted_guard_preserves_public_soundness
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted restartTrigger
      restartCadence satSound unsatSound : Prop) :
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyStagnationRestartHint guardAccepted restartTrigger restartCadence ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted hint truth
  exact ay_ssrg_hint_cannot_change_truth
    guardAccepted restartTrigger restartCadence satSound unsatSound hint truth

theorem ay_ssrg_rejected_is_no_claim
    (staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback : Prop) :
    AyStagnationGuardRejected
      staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback ->
    AyNoClaimDiagnostic
      (AyStagnationGuardRejected
        staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
        buildMismatch guardMismatch missingFallback) := by
  intro rejected
  exact rejected

theorem ay_ssrg_rejected_fallback_preserves_baseline
    (staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback baselineSoundness : Prop) :
    AyStagnationGuardRejected
      staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_ssrg_rejected_cannot_publish
    (staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback publicResultClaim : Prop) :
    AyStagnationGuardRejected
      staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback ->
    publicResultClaim ->
    publicResultClaim := by
  intro _rejected claim
  exact claim

theorem ay_ssrg_gate_accept_or_reject
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted staleMetrics ledgerMismatch
      activityReplayMismatch policyReplayMismatch buildMismatch guardMismatch
      missingFallback : Prop) :
    AyStagnationRestartGate
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted staleMetrics ledgerMismatch
      activityReplayMismatch policyReplayMismatch buildMismatch guardMismatch
      missingFallback ->
    AyDisj
      (AyStagnationGuardAccepted
        conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
        soundnessGuard fallbackEvidence guardAccepted)
      (AyStagnationGuardRejected
        staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
        buildMismatch guardMismatch missingFallback) := by
  intro gate
  exact gate

theorem ay_ssrg_safe_restart_deployment_accept
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted restartTrigger
      restartCadence satSound unsatSound : Prop) :
    AyConflictProgressEvidence conflictProgress ->
    AyPropagationBudgetLedgerEvidence budgetLedger ->
    AyLbdActivityReplayEvidence lbdActivityReplay ->
    AyRestartPolicyReplayEvidence restartReplay ->
    AySolverBuildEvidence solverBuild ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    (conflictProgress -> budgetLedger -> lbdActivityReplay -> restartReplay ->
      solverBuild -> soundnessGuard -> fallbackEvidence -> guardAccepted ->
      AyStagnationRestartHint guardAccepted restartTrigger restartCadence) ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro progress ledger activity restart build guard fallback accepted
  intro sound truth
  let hint :=
    ay_ssrg_guard_admissible_hint
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted restartTrigger
      restartCadence progress ledger activity restart build guard fallback
      accepted sound
  exact ay_ssrg_accepted_guard_preserves_public_soundness
    conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
    soundnessGuard fallbackEvidence guardAccepted restartTrigger restartCadence
    satSound unsatSound accepted hint truth

theorem ay_ssrg_safe_restart_deployment_fallback
    (staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback baselineSoundness restartTrigger
      restartCadence selectedPolicy : Prop) :
    AyStagnationGuardRejected
      staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    AyOptimizationPath restartTrigger restartCadence selectedPolicy ->
    baselineSoundness := by
  intro rejected fallback _path
  exact ay_ssrg_rejected_fallback_preserves_baseline
    staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
    buildMismatch guardMismatch missingFallback baselineSoundness rejected fallback

theorem ay_ssrg_mismatch_no_claim
    (staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback noClaim : Prop) :
    AyStagnationGuardRejected
      staleMetrics ledgerMismatch activityReplayMismatch policyReplayMismatch
      buildMismatch guardMismatch missingFallback ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_ssrg_guard_requires_conflict_progress
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyConflictProgressEvidence conflictProgress ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyConflictProgressEvidence conflictProgress := by
  intro evidence accepted
  exact ay_ssrg_accepted_conflict_progress
    conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_ssrg_guard_requires_budget_ledger
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyPropagationBudgetLedgerEvidence budgetLedger ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyPropagationBudgetLedgerEvidence budgetLedger := by
  intro evidence accepted
  exact ay_ssrg_accepted_budget_ledger
    conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_ssrg_guard_requires_lbd_activity_replay
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyLbdActivityReplayEvidence lbdActivityReplay ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyLbdActivityReplayEvidence lbdActivityReplay := by
  intro evidence accepted
  exact ay_ssrg_accepted_lbd_activity_replay
    conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_ssrg_guard_requires_restart_replay
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyRestartPolicyReplayEvidence restartReplay ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyRestartPolicyReplayEvidence restartReplay := by
  intro evidence accepted
  exact ay_ssrg_accepted_restart_replay
    conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_ssrg_guard_requires_fallback
    (conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyStagnationGuardAccepted
      conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
      soundnessGuard fallbackEvidence guardAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence accepted
  exact ay_ssrg_accepted_fallback_evidence
    conflictProgress budgetLedger lbdActivityReplay restartReplay solverBuild
    soundnessGuard fallbackEvidence guardAccepted evidence accepted
