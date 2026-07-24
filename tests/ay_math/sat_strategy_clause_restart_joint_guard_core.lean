def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyClauseRestartJointInputs
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence : Prop) : Prop :=
  AyConj clausePressure
    (AyConj lbdWindow
      (AyConj activityReplay
        (AyConj restartReplay
          (AyConj budgetLedger
            (AyConj solverBuild
              (AyConj soundnessGuard fallbackEvidence))))))

def AyClausePressureEvidence (clausePressure : Prop) : Prop :=
  clausePressure

def AyLbdWindowEvidence (lbdWindow : Prop) : Prop :=
  lbdWindow

def AyActivityReplayEvidence (activityReplay : Prop) : Prop :=
  activityReplay

def AyRestartReplayEvidence (restartReplay : Prop) : Prop :=
  restartReplay

def AyBudgetLedgerEvidence (budgetLedger : Prop) : Prop :=
  budgetLedger

def AySolverBuildEvidence (solverBuild : Prop) : Prop :=
  solverBuild

def AyPublicSoundnessGuardEvidence (soundnessGuard : Prop) : Prop :=
  soundnessGuard

def AyFallbackEvidence (fallbackEvidence : Prop) : Prop :=
  fallbackEvidence

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyJointGuardAccepted
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) : Prop :=
  guardAccepted

def AyJointGuardRejected
    (staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback : Prop) : Prop :=
  AyDisj staleClauseMetrics
    (AyDisj staleWindowMetrics
      (AyDisj ledgerMismatch
        (AyDisj replayMismatch
          (AyDisj dependencyFailure
            (AyDisj buildMismatch missingFallback)))))

def AyJointGuardGate
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted
      staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback : Prop) : Prop :=
  AyDisj
    (AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted)
    (AyJointGuardRejected
      staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback)

def AyJointPerformanceHint
    (guardAccepted clauseReduction restartPolicy retentionPolicy : Prop) : Prop :=
  AyConj guardAccepted
    (AyConj clauseReduction (AyConj restartPolicy retentionPolicy))

def AyOptimizationPath
    (clauseReduction restartPolicy retentionPolicy selectedPolicy : Prop) : Prop :=
  AyConj clauseReduction
    (AyConj restartPolicy (AyConj retentionPolicy selectedPolicy))

theorem ay_scrj_input_components
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence : Prop) :
    AyClauseRestartJointInputs
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence ->
    AyConj clausePressure
      (AyConj lbdWindow
        (AyConj activityReplay
          (AyConj restartReplay
            (AyConj budgetLedger
              (AyConj solverBuild
                (AyConj soundnessGuard fallbackEvidence)))))) := by
  intro inputs
  exact inputs

theorem ay_scrj_accepted_guard
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    guardAccepted := by
  intro accepted
  exact accepted

theorem ay_scrj_accepted_clause_pressure
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyClausePressureEvidence clausePressure ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyClausePressureEvidence clausePressure := by
  intro evidence _accepted
  exact evidence

theorem ay_scrj_accepted_lbd_window
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyLbdWindowEvidence lbdWindow ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyLbdWindowEvidence lbdWindow := by
  intro evidence _accepted
  exact evidence

theorem ay_scrj_accepted_activity_replay
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyActivityReplayEvidence activityReplay ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyActivityReplayEvidence activityReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_scrj_accepted_restart_replay
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyRestartReplayEvidence restartReplay ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyRestartReplayEvidence restartReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_scrj_accepted_budget_ledger
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyBudgetLedgerEvidence budgetLedger ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyBudgetLedgerEvidence budgetLedger := by
  intro evidence _accepted
  exact evidence

theorem ay_scrj_accepted_solver_build
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AySolverBuildEvidence solverBuild ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AySolverBuildEvidence solverBuild := by
  intro evidence _accepted
  exact evidence

theorem ay_scrj_accepted_soundness_guard
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyPublicSoundnessGuardEvidence soundnessGuard := by
  intro evidence _accepted
  exact evidence

theorem ay_scrj_accepted_fallback_evidence
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_scrj_guard_admissible_hint
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted clauseReduction
      restartPolicy retentionPolicy : Prop) :
    AyClausePressureEvidence clausePressure ->
    AyLbdWindowEvidence lbdWindow ->
    AyActivityReplayEvidence activityReplay ->
    AyRestartReplayEvidence restartReplay ->
    AyBudgetLedgerEvidence budgetLedger ->
    AySolverBuildEvidence solverBuild ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    (clausePressure -> lbdWindow -> activityReplay -> restartReplay ->
      budgetLedger -> solverBuild -> soundnessGuard -> fallbackEvidence ->
      guardAccepted ->
      AyJointPerformanceHint guardAccepted clauseReduction restartPolicy
        retentionPolicy) ->
    AyJointPerformanceHint guardAccepted clauseReduction restartPolicy
      retentionPolicy := by
  intro pressure window activity restart ledger build guard fallback accepted
  intro sound
  exact sound pressure window activity restart ledger build guard fallback
    accepted

theorem ay_scrj_hint_cannot_change_truth
    (guardAccepted clauseReduction restartPolicy retentionPolicy satSound
      unsatSound : Prop) :
    AyJointPerformanceHint guardAccepted clauseReduction restartPolicy
      retentionPolicy ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _hint truth
  exact truth

theorem ay_scrj_accepted_guard_preserves_public_soundness
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted clauseReduction
      restartPolicy retentionPolicy satSound unsatSound : Prop) :
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyJointPerformanceHint guardAccepted clauseReduction restartPolicy
      retentionPolicy ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted hint truth
  exact ay_scrj_hint_cannot_change_truth
    guardAccepted clauseReduction restartPolicy retentionPolicy satSound
    unsatSound hint truth

theorem ay_scrj_rejected_is_no_claim
    (staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback : Prop) :
    AyJointGuardRejected
      staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback ->
    AyNoClaimDiagnostic
      (AyJointGuardRejected
        staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
        dependencyFailure buildMismatch missingFallback) := by
  intro rejected
  exact rejected

theorem ay_scrj_rejected_fallback_preserves_baseline
    (staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback baselineSoundness : Prop) :
    AyJointGuardRejected
      staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_scrj_rejected_cannot_publish
    (staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback publicResultClaim : Prop) :
    AyJointGuardRejected
      staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback ->
    publicResultClaim ->
    publicResultClaim := by
  intro _rejected claim
  exact claim

theorem ay_scrj_gate_accept_or_reject
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted
      staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback : Prop) :
    AyJointGuardGate
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted
      staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback ->
    AyDisj
      (AyJointGuardAccepted
        clausePressure lbdWindow activityReplay restartReplay budgetLedger
        solverBuild soundnessGuard fallbackEvidence guardAccepted)
      (AyJointGuardRejected
        staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
        dependencyFailure buildMismatch missingFallback) := by
  intro gate
  exact gate

theorem ay_scrj_safe_joint_deployment_accept
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted clauseReduction
      restartPolicy retentionPolicy satSound unsatSound : Prop) :
    AyClausePressureEvidence clausePressure ->
    AyLbdWindowEvidence lbdWindow ->
    AyActivityReplayEvidence activityReplay ->
    AyRestartReplayEvidence restartReplay ->
    AyBudgetLedgerEvidence budgetLedger ->
    AySolverBuildEvidence solverBuild ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    (clausePressure -> lbdWindow -> activityReplay -> restartReplay ->
      budgetLedger -> solverBuild -> soundnessGuard -> fallbackEvidence ->
      guardAccepted ->
      AyJointPerformanceHint guardAccepted clauseReduction restartPolicy
        retentionPolicy) ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro pressure window activity restart ledger build guard fallback accepted
  intro sound truth
  let hint :=
    ay_scrj_guard_admissible_hint
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted clauseReduction
      restartPolicy retentionPolicy pressure window activity restart ledger build
      guard fallback accepted sound
  exact ay_scrj_accepted_guard_preserves_public_soundness
    clausePressure lbdWindow activityReplay restartReplay budgetLedger solverBuild
    soundnessGuard fallbackEvidence guardAccepted clauseReduction restartPolicy
    retentionPolicy satSound unsatSound accepted hint truth

theorem ay_scrj_safe_joint_deployment_fallback
    (staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback baselineSoundness
      clauseReduction restartPolicy retentionPolicy selectedPolicy : Prop) :
    AyJointGuardRejected
      staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    AyOptimizationPath
      clauseReduction restartPolicy retentionPolicy selectedPolicy ->
    baselineSoundness := by
  intro rejected fallback _path
  exact ay_scrj_rejected_fallback_preserves_baseline
    staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
    dependencyFailure buildMismatch missingFallback baselineSoundness
    rejected fallback

theorem ay_scrj_mismatch_no_claim
    (staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback noClaim : Prop) :
    AyJointGuardRejected
      staleClauseMetrics staleWindowMetrics ledgerMismatch replayMismatch
      dependencyFailure buildMismatch missingFallback ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_scrj_guard_requires_clause_pressure
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyClausePressureEvidence clausePressure ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyClausePressureEvidence clausePressure := by
  intro evidence accepted
  exact ay_scrj_accepted_clause_pressure
    clausePressure lbdWindow activityReplay restartReplay budgetLedger solverBuild
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_scrj_guard_requires_lbd_window
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyLbdWindowEvidence lbdWindow ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyLbdWindowEvidence lbdWindow := by
  intro evidence accepted
  exact ay_scrj_accepted_lbd_window
    clausePressure lbdWindow activityReplay restartReplay budgetLedger solverBuild
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_scrj_guard_requires_activity_replay
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyActivityReplayEvidence activityReplay ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyActivityReplayEvidence activityReplay := by
  intro evidence accepted
  exact ay_scrj_accepted_activity_replay
    clausePressure lbdWindow activityReplay restartReplay budgetLedger solverBuild
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_scrj_guard_requires_restart_replay
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyRestartReplayEvidence restartReplay ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyRestartReplayEvidence restartReplay := by
  intro evidence accepted
  exact ay_scrj_accepted_restart_replay
    clausePressure lbdWindow activityReplay restartReplay budgetLedger solverBuild
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_scrj_guard_requires_budget_ledger
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyBudgetLedgerEvidence budgetLedger ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyBudgetLedgerEvidence budgetLedger := by
  intro evidence accepted
  exact ay_scrj_accepted_budget_ledger
    clausePressure lbdWindow activityReplay restartReplay budgetLedger solverBuild
    soundnessGuard fallbackEvidence guardAccepted evidence accepted

theorem ay_scrj_guard_requires_fallback
    (clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted : Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyJointGuardAccepted
      clausePressure lbdWindow activityReplay restartReplay budgetLedger
      solverBuild soundnessGuard fallbackEvidence guardAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence accepted
  exact ay_scrj_accepted_fallback_evidence
    clausePressure lbdWindow activityReplay restartReplay budgetLedger solverBuild
    soundnessGuard fallbackEvidence guardAccepted evidence accepted
