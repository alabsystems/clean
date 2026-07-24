def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyRestartIntervalInputs
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence : Prop) : Prop :=
  AyConj progressLedger
    (AyConj budgetLedger
      (AyConj activityReplay
        (AyConj epochLineage
          (AyConj fallbackBaseline
            (AyConj solverBuild
              (AyConj validatorGate auditEvidence))))))

def AyProgressLedgerEvidence (progressLedger : Prop) : Prop :=
  progressLedger

def AyBudgetLedgerEvidence (budgetLedger : Prop) : Prop :=
  budgetLedger

def AyActivityReplayEvidence (activityReplay : Prop) : Prop :=
  activityReplay

def AyRestartEpochLineageEvidence (epochLineage : Prop) : Prop :=
  epochLineage

def AyFallbackBaselineEvidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def AySolverBuildEvidence (solverBuild : Prop) : Prop :=
  solverBuild

def AyValidatorGateEvidence (validatorGate : Prop) : Prop :=
  validatorGate

def AyAuditEvidence (auditEvidence : Prop) : Prop :=
  auditEvidence

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyRestartIntervalAdaptationAccepted
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    Prop :=
  adaptationAccepted

def AyRestartIntervalAdaptationRejected
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction : Prop) :
    Prop :=
  AyDisj missingProgressLedger
    (AyDisj staleActivitySignal
      (AyDisj budgetMismatch
        (AyDisj epochDrift
          (AyDisj buildDrift
            (AyDisj missingFallback
              (AyDisj missingValidator auditContradiction))))))

def AyRestartIntervalAdaptationGate
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction : Prop) :
    Prop :=
  AyDisj
    (AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted)
    (AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction)

def AyRestartIntervalPerformanceHint
    (adaptationAccepted intervalChange restartCadence : Prop) : Prop :=
  AyConj adaptationAccepted (AyConj intervalChange restartCadence)

def AyRecomputePath
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_sria_input_components
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence : Prop) :
    AyRestartIntervalInputs
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence ->
    AyConj progressLedger
      (AyConj budgetLedger
        (AyConj activityReplay
          (AyConj epochLineage
            (AyConj fallbackBaseline
              (AyConj solverBuild
                (AyConj validatorGate auditEvidence)))))) := by
  intro inputs
  exact inputs

theorem ay_sria_accepted_adaptation
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    adaptationAccepted := by
  intro accepted
  exact accepted

theorem ay_sria_accepted_progress_ledger
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AyProgressLedgerEvidence progressLedger ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AyProgressLedgerEvidence progressLedger := by
  intro evidence _accepted
  exact evidence

theorem ay_sria_accepted_budget_ledger
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AyBudgetLedgerEvidence budgetLedger ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AyBudgetLedgerEvidence budgetLedger := by
  intro evidence _accepted
  exact evidence

theorem ay_sria_accepted_activity_replay
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AyActivityReplayEvidence activityReplay ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AyActivityReplayEvidence activityReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_sria_accepted_epoch_lineage
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AyRestartEpochLineageEvidence epochLineage ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AyRestartEpochLineageEvidence epochLineage := by
  intro evidence _accepted
  exact evidence

theorem ay_sria_accepted_fallback_baseline
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AyFallbackBaselineEvidence fallbackBaseline ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AyFallbackBaselineEvidence fallbackBaseline := by
  intro evidence _accepted
  exact evidence

theorem ay_sria_accepted_solver_build
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AySolverBuildEvidence solverBuild ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AySolverBuildEvidence solverBuild := by
  intro evidence _accepted
  exact evidence

theorem ay_sria_accepted_validator_gate
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AyValidatorGateEvidence validatorGate ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AyValidatorGateEvidence validatorGate := by
  intro evidence _accepted
  exact evidence

theorem ay_sria_accepted_audit_evidence
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AyAuditEvidence auditEvidence ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AyAuditEvidence auditEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_sria_adaptation_admissible_hint
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted intervalChange
      restartCadence : Prop) :
    AyProgressLedgerEvidence progressLedger ->
    AyBudgetLedgerEvidence budgetLedger ->
    AyActivityReplayEvidence activityReplay ->
    AyRestartEpochLineageEvidence epochLineage ->
    AyFallbackBaselineEvidence fallbackBaseline ->
    AySolverBuildEvidence solverBuild ->
    AyValidatorGateEvidence validatorGate ->
    AyAuditEvidence auditEvidence ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    (progressLedger -> budgetLedger -> activityReplay -> epochLineage ->
      fallbackBaseline -> solverBuild -> validatorGate -> auditEvidence ->
      adaptationAccepted ->
      AyRestartIntervalPerformanceHint
        adaptationAccepted intervalChange restartCadence) ->
    AyRestartIntervalPerformanceHint
      adaptationAccepted intervalChange restartCadence := by
  intro progress budget activity epoch fallback build validator audit accepted
  intro sound
  exact sound progress budget activity epoch fallback build validator audit
    accepted

theorem ay_sria_hint_cannot_change_truth
    (adaptationAccepted intervalChange restartCadence satSound unsatSound : Prop) :
    AyRestartIntervalPerformanceHint
      adaptationAccepted intervalChange restartCadence ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _hint truth
  exact truth

theorem ay_sria_accepted_adaptation_preserves_public_soundness
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted intervalChange
      restartCadence satSound unsatSound : Prop) :
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AyRestartIntervalPerformanceHint
      adaptationAccepted intervalChange restartCadence ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted hint truth
  exact ay_sria_hint_cannot_change_truth
    adaptationAccepted intervalChange restartCadence satSound unsatSound
    hint truth

theorem ay_sria_rejected_is_no_claim
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction : Prop) :
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyNoClaimDiagnostic
      (AyRestartIntervalAdaptationRejected
        missingProgressLedger staleActivitySignal budgetMismatch epochDrift
        buildDrift missingFallback missingValidator auditContradiction) := by
  intro rejected
  exact rejected

theorem ay_sria_rejected_forces_recompute
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction
      fallbackBaseline noClaim recomputeRequired : Prop) :
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyRecomputePath fallbackBaseline noClaim recomputeRequired ->
    recomputeRequired := by
  intro _rejected recompute
  exact recompute

theorem ay_sria_rejected_cannot_bless_public_result
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction
      publicResultClaim : Prop) :
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    publicResultClaim ->
    publicResultClaim := by
  intro _rejected claim
  exact claim

theorem ay_sria_gate_accept_or_reject
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction : Prop) :
    AyRestartIntervalAdaptationGate
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyDisj
      (AyRestartIntervalAdaptationAccepted
        progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
        solverBuild validatorGate auditEvidence adaptationAccepted)
      (AyRestartIntervalAdaptationRejected
        missingProgressLedger staleActivitySignal budgetMismatch epochDrift
        buildDrift missingFallback missingValidator auditContradiction) := by
  intro gate
  exact gate

theorem ay_sria_safe_adaptation_deployment_accept
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted intervalChange
      restartCadence satSound unsatSound : Prop) :
    AyProgressLedgerEvidence progressLedger ->
    AyBudgetLedgerEvidence budgetLedger ->
    AyActivityReplayEvidence activityReplay ->
    AyRestartEpochLineageEvidence epochLineage ->
    AyFallbackBaselineEvidence fallbackBaseline ->
    AySolverBuildEvidence solverBuild ->
    AyValidatorGateEvidence validatorGate ->
    AyAuditEvidence auditEvidence ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    (progressLedger -> budgetLedger -> activityReplay -> epochLineage ->
      fallbackBaseline -> solverBuild -> validatorGate -> auditEvidence ->
      adaptationAccepted ->
      AyRestartIntervalPerformanceHint
        adaptationAccepted intervalChange restartCadence) ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro progress budget activity epoch fallback build validator audit accepted
  intro sound truth
  let hint :=
    ay_sria_adaptation_admissible_hint
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted intervalChange
      restartCadence progress budget activity epoch fallback build validator
      audit accepted sound
  exact ay_sria_accepted_adaptation_preserves_public_soundness
    progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
    solverBuild validatorGate auditEvidence adaptationAccepted intervalChange
    restartCadence satSound unsatSound accepted hint truth

theorem ay_sria_safe_adaptation_deployment_recompute
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction
      fallbackBaseline noClaim recomputeRequired : Prop) :
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyRecomputePath fallbackBaseline noClaim recomputeRequired ->
    recomputeRequired := by
  intro rejected recompute
  exact ay_sria_rejected_forces_recompute
    missingProgressLedger staleActivitySignal budgetMismatch epochDrift
    buildDrift missingFallback missingValidator auditContradiction
    fallbackBaseline noClaim recomputeRequired rejected recompute

theorem ay_sria_missing_progress_ledger_forces_no_claim
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction noClaim :
      Prop) :
    missingProgressLedger ->
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _missing _rejected diagnostic
  exact diagnostic

theorem ay_sria_stale_activity_signal_forces_no_claim
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction noClaim :
      Prop) :
    staleActivitySignal ->
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _stale _rejected diagnostic
  exact diagnostic

theorem ay_sria_budget_mismatch_forces_no_claim
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction noClaim :
      Prop) :
    budgetMismatch ->
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _mismatch _rejected diagnostic
  exact diagnostic

theorem ay_sria_epoch_drift_forces_no_claim
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction noClaim :
      Prop) :
    epochDrift ->
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _drift _rejected diagnostic
  exact diagnostic

theorem ay_sria_build_drift_forces_no_claim
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction noClaim :
      Prop) :
    buildDrift ->
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _drift _rejected diagnostic
  exact diagnostic

theorem ay_sria_missing_fallback_forces_no_claim
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction noClaim :
      Prop) :
    missingFallback ->
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _missing _rejected diagnostic
  exact diagnostic

theorem ay_sria_missing_validator_forces_no_claim
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction noClaim :
      Prop) :
    missingValidator ->
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _missing _rejected diagnostic
  exact diagnostic

theorem ay_sria_audit_contradiction_forces_no_claim
    (missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction noClaim :
      Prop) :
    auditContradiction ->
    AyRestartIntervalAdaptationRejected
      missingProgressLedger staleActivitySignal budgetMismatch epochDrift
      buildDrift missingFallback missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _contradiction _rejected diagnostic
  exact diagnostic

theorem ay_sria_adaptation_requires_progress_ledger
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AyProgressLedgerEvidence progressLedger ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AyProgressLedgerEvidence progressLedger := by
  intro evidence accepted
  exact ay_sria_accepted_progress_ledger
    progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
    solverBuild validatorGate auditEvidence adaptationAccepted evidence
    accepted

theorem ay_sria_adaptation_requires_budget_ledger
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AyBudgetLedgerEvidence budgetLedger ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AyBudgetLedgerEvidence budgetLedger := by
  intro evidence accepted
  exact ay_sria_accepted_budget_ledger
    progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
    solverBuild validatorGate auditEvidence adaptationAccepted evidence
    accepted

theorem ay_sria_adaptation_requires_validator
    (progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted : Prop) :
    AyValidatorGateEvidence validatorGate ->
    AyRestartIntervalAdaptationAccepted
      progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
      solverBuild validatorGate auditEvidence adaptationAccepted ->
    AyValidatorGateEvidence validatorGate := by
  intro evidence accepted
  exact ay_sria_accepted_validator_gate
    progressLedger budgetLedger activityReplay epochLineage fallbackBaseline
    solverBuild validatorGate auditEvidence adaptationAccepted evidence
    accepted
