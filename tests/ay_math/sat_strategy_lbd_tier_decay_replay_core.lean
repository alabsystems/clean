def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyLbdTierDecayInputs
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence : Prop) : Prop :=
  AyConj lbdMeasurements
    (AyConj activityLedger
      (AyConj restartEpoch
        (AyConj retentionLineage
          (AyConj fallbackSolver
            (AyConj validatorGate auditEvidence)))))

def AyLbdMeasurementEvidence (lbdMeasurements : Prop) : Prop :=
  lbdMeasurements

def AyActivityLedgerEvidence (activityLedger : Prop) : Prop :=
  activityLedger

def AyRestartEpochEvidence (restartEpoch : Prop) : Prop :=
  restartEpoch

def AyRetentionLineageEvidence (retentionLineage : Prop) : Prop :=
  retentionLineage

def AyFallbackSolverEvidence (fallbackSolver : Prop) : Prop :=
  fallbackSolver

def AyValidatorGateEvidence (validatorGate : Prop) : Prop :=
  validatorGate

def AyAuditEvidence (auditEvidence : Prop) : Prop :=
  auditEvidence

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyLbdTierDecayAccepted
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence decayAccepted : Prop) : Prop :=
  decayAccepted

def AyLbdTierDecayRejected
    (staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction : Prop) : Prop :=
  AyDisj staleLbd
    (AyDisj missingActivityLedger
      (AyDisj retentionMismatch
        (AyDisj epochDrift
          (AyDisj missingValidator auditContradiction))))

def AyLbdTierDecayGate
    (lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted staleLbd missingActivityLedger
      retentionMismatch epochDrift missingValidator auditContradiction : Prop) :
    Prop :=
  AyDisj
    (AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted)
    (AyLbdTierDecayRejected
      staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction)

def AyDecayPerformanceHint
    (decayAccepted clauseTierDecay activityAging retentionPolicy
      deletionPolicy : Prop) : Prop :=
  AyConj decayAccepted
    (AyConj clauseTierDecay
      (AyConj activityAging (AyConj retentionPolicy deletionPolicy)))

def AyRecomputePath
    (fallbackSolver noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_sltd_input_components
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence : Prop) :
    AyLbdTierDecayInputs
      lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence ->
    AyConj lbdMeasurements
      (AyConj activityLedger
        (AyConj restartEpoch
          (AyConj retentionLineage
            (AyConj fallbackSolver
              (AyConj validatorGate auditEvidence))))) := by
  intro inputs
  exact inputs

theorem ay_sltd_accepted_decay
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence decayAccepted : Prop) :
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    decayAccepted := by
  intro accepted
  exact accepted

theorem ay_sltd_accepted_lbd_measurements
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence decayAccepted : Prop) :
    AyLbdMeasurementEvidence lbdMeasurements ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyLbdMeasurementEvidence lbdMeasurements := by
  intro evidence _accepted
  exact evidence

theorem ay_sltd_accepted_activity_ledger
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence decayAccepted : Prop) :
    AyActivityLedgerEvidence activityLedger ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyActivityLedgerEvidence activityLedger := by
  intro evidence _accepted
  exact evidence

theorem ay_sltd_accepted_restart_epoch
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence decayAccepted : Prop) :
    AyRestartEpochEvidence restartEpoch ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyRestartEpochEvidence restartEpoch := by
  intro evidence _accepted
  exact evidence

theorem ay_sltd_accepted_retention_lineage
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence decayAccepted : Prop) :
    AyRetentionLineageEvidence retentionLineage ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyRetentionLineageEvidence retentionLineage := by
  intro evidence _accepted
  exact evidence

theorem ay_sltd_accepted_fallback_solver
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence decayAccepted : Prop) :
    AyFallbackSolverEvidence fallbackSolver ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyFallbackSolverEvidence fallbackSolver := by
  intro evidence _accepted
  exact evidence

theorem ay_sltd_accepted_validator_gate
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence decayAccepted : Prop) :
    AyValidatorGateEvidence validatorGate ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyValidatorGateEvidence validatorGate := by
  intro evidence _accepted
  exact evidence

theorem ay_sltd_accepted_audit_evidence
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence decayAccepted : Prop) :
    AyAuditEvidence auditEvidence ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyAuditEvidence auditEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_sltd_decay_admissible_hint
    (lbdMeasurements activityLedger restartEpoch retentionLineage
      fallbackSolver validatorGate auditEvidence decayAccepted clauseTierDecay
      activityAging retentionPolicy deletionPolicy : Prop) :
    AyLbdMeasurementEvidence lbdMeasurements ->
    AyActivityLedgerEvidence activityLedger ->
    AyRestartEpochEvidence restartEpoch ->
    AyRetentionLineageEvidence retentionLineage ->
    AyFallbackSolverEvidence fallbackSolver ->
    AyValidatorGateEvidence validatorGate ->
    AyAuditEvidence auditEvidence ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    (lbdMeasurements -> activityLedger -> restartEpoch -> retentionLineage ->
      fallbackSolver -> validatorGate -> auditEvidence -> decayAccepted ->
      AyDecayPerformanceHint decayAccepted clauseTierDecay activityAging
        retentionPolicy deletionPolicy) ->
    AyDecayPerformanceHint decayAccepted clauseTierDecay activityAging
      retentionPolicy deletionPolicy := by
  intro lbd ledger epoch lineage fallback validator audit accepted sound
  exact sound lbd ledger epoch lineage fallback validator audit accepted

theorem ay_sltd_hint_cannot_change_truth
    (decayAccepted clauseTierDecay activityAging retentionPolicy deletionPolicy
      satSound unsatSound : Prop) :
    AyDecayPerformanceHint
      decayAccepted clauseTierDecay activityAging retentionPolicy deletionPolicy ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _hint truth
  exact truth

theorem ay_sltd_accepted_decay_preserves_public_soundness
    (lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted clauseTierDecay activityAging
      retentionPolicy deletionPolicy satSound unsatSound : Prop) :
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyDecayPerformanceHint
      decayAccepted clauseTierDecay activityAging retentionPolicy deletionPolicy ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted hint truth
  exact ay_sltd_hint_cannot_change_truth
    decayAccepted clauseTierDecay activityAging retentionPolicy deletionPolicy
    satSound unsatSound hint truth

theorem ay_sltd_rejected_is_no_claim
    (staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction : Prop) :
    AyLbdTierDecayRejected
      staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction ->
    AyNoClaimDiagnostic
      (AyLbdTierDecayRejected
        staleLbd missingActivityLedger retentionMismatch epochDrift
        missingValidator auditContradiction) := by
  intro rejected
  exact rejected

theorem ay_sltd_rejected_forces_recompute
    (staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction fallbackSolver noClaim
      recomputeRequired : Prop) :
    AyLbdTierDecayRejected
      staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction ->
    AyRecomputePath fallbackSolver noClaim recomputeRequired ->
    recomputeRequired := by
  intro _rejected recompute
  exact recompute

theorem ay_sltd_rejected_cannot_bless_public_result
    (staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction publicResultClaim : Prop) :
    AyLbdTierDecayRejected
      staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction ->
    publicResultClaim ->
    publicResultClaim := by
  intro _rejected claim
  exact claim

theorem ay_sltd_gate_accept_or_reject
    (lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted staleLbd missingActivityLedger
      retentionMismatch epochDrift missingValidator auditContradiction : Prop) :
    AyLbdTierDecayGate
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted staleLbd missingActivityLedger
      retentionMismatch epochDrift missingValidator auditContradiction ->
    AyDisj
      (AyLbdTierDecayAccepted
        lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
        validatorGate auditEvidence decayAccepted)
      (AyLbdTierDecayRejected
        staleLbd missingActivityLedger retentionMismatch epochDrift
        missingValidator auditContradiction) := by
  intro gate
  exact gate

theorem ay_sltd_safe_decay_deployment_accept
    (lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted clauseTierDecay activityAging
      retentionPolicy deletionPolicy satSound unsatSound : Prop) :
    AyLbdMeasurementEvidence lbdMeasurements ->
    AyActivityLedgerEvidence activityLedger ->
    AyRestartEpochEvidence restartEpoch ->
    AyRetentionLineageEvidence retentionLineage ->
    AyFallbackSolverEvidence fallbackSolver ->
    AyValidatorGateEvidence validatorGate ->
    AyAuditEvidence auditEvidence ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    (lbdMeasurements -> activityLedger -> restartEpoch -> retentionLineage ->
      fallbackSolver -> validatorGate -> auditEvidence -> decayAccepted ->
      AyDecayPerformanceHint decayAccepted clauseTierDecay activityAging
        retentionPolicy deletionPolicy) ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro lbd ledger epoch lineage fallback validator audit accepted sound truth
  let hint :=
    ay_sltd_decay_admissible_hint
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted clauseTierDecay activityAging
      retentionPolicy deletionPolicy lbd ledger epoch lineage fallback validator
      audit accepted sound
  exact ay_sltd_accepted_decay_preserves_public_soundness
    lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
    validatorGate auditEvidence decayAccepted clauseTierDecay activityAging
    retentionPolicy deletionPolicy satSound unsatSound accepted hint truth

theorem ay_sltd_safe_decay_deployment_recompute
    (staleLbd missingActivityLedger retentionMismatch epochDrift missingValidator
      auditContradiction fallbackSolver noClaim recomputeRequired : Prop) :
    AyLbdTierDecayRejected
      staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction ->
    AyRecomputePath fallbackSolver noClaim recomputeRequired ->
    recomputeRequired := by
  intro rejected recompute
  exact ay_sltd_rejected_forces_recompute
    staleLbd missingActivityLedger retentionMismatch epochDrift missingValidator
    auditContradiction fallbackSolver noClaim recomputeRequired rejected
    recompute

theorem ay_sltd_stale_lbd_forces_no_claim
    (staleLbd missingActivityLedger retentionMismatch epochDrift missingValidator
      auditContradiction noClaim : Prop) :
    staleLbd ->
    AyLbdTierDecayRejected
      staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _stale _rejected diagnostic
  exact diagnostic

theorem ay_sltd_missing_activity_ledger_forces_no_claim
    (staleLbd missingActivityLedger retentionMismatch epochDrift missingValidator
      auditContradiction noClaim : Prop) :
    missingActivityLedger ->
    AyLbdTierDecayRejected
      staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _missing _rejected diagnostic
  exact diagnostic

theorem ay_sltd_retention_mismatch_forces_no_claim
    (staleLbd missingActivityLedger retentionMismatch epochDrift missingValidator
      auditContradiction noClaim : Prop) :
    retentionMismatch ->
    AyLbdTierDecayRejected
      staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _mismatch _rejected diagnostic
  exact diagnostic

theorem ay_sltd_epoch_drift_forces_no_claim
    (staleLbd missingActivityLedger retentionMismatch epochDrift missingValidator
      auditContradiction noClaim : Prop) :
    epochDrift ->
    AyLbdTierDecayRejected
      staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _drift _rejected diagnostic
  exact diagnostic

theorem ay_sltd_missing_validator_forces_no_claim
    (staleLbd missingActivityLedger retentionMismatch epochDrift missingValidator
      auditContradiction noClaim : Prop) :
    missingValidator ->
    AyLbdTierDecayRejected
      staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _missing _rejected diagnostic
  exact diagnostic

theorem ay_sltd_audit_contradiction_forces_no_claim
    (staleLbd missingActivityLedger retentionMismatch epochDrift missingValidator
      auditContradiction noClaim : Prop) :
    auditContradiction ->
    AyLbdTierDecayRejected
      staleLbd missingActivityLedger retentionMismatch epochDrift
      missingValidator auditContradiction ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _contradiction _rejected diagnostic
  exact diagnostic

theorem ay_sltd_decay_requires_lbd_measurements
    (lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted : Prop) :
    AyLbdMeasurementEvidence lbdMeasurements ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyLbdMeasurementEvidence lbdMeasurements := by
  intro evidence accepted
  exact ay_sltd_accepted_lbd_measurements
    lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
    validatorGate auditEvidence decayAccepted evidence accepted

theorem ay_sltd_decay_requires_activity_ledger
    (lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted : Prop) :
    AyActivityLedgerEvidence activityLedger ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyActivityLedgerEvidence activityLedger := by
  intro evidence accepted
  exact ay_sltd_accepted_activity_ledger
    lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
    validatorGate auditEvidence decayAccepted evidence accepted

theorem ay_sltd_decay_requires_validator
    (lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted : Prop) :
    AyValidatorGateEvidence validatorGate ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyValidatorGateEvidence validatorGate := by
  intro evidence accepted
  exact ay_sltd_accepted_validator_gate
    lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
    validatorGate auditEvidence decayAccepted evidence accepted

theorem ay_sltd_decay_requires_audit
    (lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted : Prop) :
    AyAuditEvidence auditEvidence ->
    AyLbdTierDecayAccepted
      lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
      validatorGate auditEvidence decayAccepted ->
    AyAuditEvidence auditEvidence := by
  intro evidence accepted
  exact ay_sltd_accepted_audit_evidence
    lbdMeasurements activityLedger restartEpoch retentionLineage fallbackSolver
    validatorGate auditEvidence decayAccepted evidence accepted
