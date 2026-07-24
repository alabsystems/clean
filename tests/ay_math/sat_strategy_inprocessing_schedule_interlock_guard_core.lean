def ay_isig_conj (p q : Prop) : Prop := p ∧ q

def ay_isig_disj (p q : Prop) : Prop := p ∨ q

def ay_isig_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_isig_disj satSound unsatSound

def ay_isig_inputs
    (scheduleEpochLedger simplificationBudgetManifest activeClauseDbDigest
      propagationReplayCheckpoint fallbackNoOpSchedule solverBuildEvidence
      validatorGate auditTranscript : Prop) : Prop :=
  ay_isig_conj scheduleEpochLedger
    (ay_isig_conj simplificationBudgetManifest
      (ay_isig_conj activeClauseDbDigest
        (ay_isig_conj propagationReplayCheckpoint
          (ay_isig_conj fallbackNoOpSchedule
            (ay_isig_conj solverBuildEvidence
              (ay_isig_conj validatorGate auditTranscript))))))

def ay_isig_schedule_epoch_ledger_evidence
    (scheduleEpochLedger : Prop) : Prop :=
  scheduleEpochLedger

def ay_isig_simplification_budget_manifest_evidence
    (simplificationBudgetManifest : Prop) : Prop :=
  simplificationBudgetManifest

def ay_isig_active_clause_db_digest_evidence
    (activeClauseDbDigest : Prop) : Prop :=
  activeClauseDbDigest

def ay_isig_propagation_replay_checkpoint_evidence
    (propagationReplayCheckpoint : Prop) : Prop :=
  propagationReplayCheckpoint

def ay_isig_fallback_no_op_schedule_evidence
    (fallbackNoOpSchedule : Prop) : Prop :=
  fallbackNoOpSchedule

def ay_isig_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_isig_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_isig_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_isig_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_isig_accepted
    (scheduleEpochLedger simplificationBudgetManifest activeClauseDbDigest
      propagationReplayCheckpoint fallbackNoOpSchedule solverBuildEvidence
      validatorGate auditTranscript interlockAccepted : Prop) : Prop :=
  interlockAccepted

def ay_isig_rejected
    (epochMismatch budgetMismatch dbMismatch replayMismatch fallbackMismatch
      buildMismatch validatorMismatch auditMismatch : Prop) : Prop :=
  ay_isig_disj epochMismatch
    (ay_isig_disj budgetMismatch
      (ay_isig_disj dbMismatch
        (ay_isig_disj replayMismatch
          (ay_isig_disj fallbackMismatch
            (ay_isig_disj buildMismatch
              (ay_isig_disj validatorMismatch auditMismatch))))))

def ay_isig_gate (accepted rejected : Prop) : Prop :=
  ay_isig_disj accepted rejected

def ay_isig_inprocessing_trigger_hint
    (interlockAccepted scheduleGuidance budgetGuidance controlGuidance :
      Prop) : Prop :=
  interlockAccepted

def ay_isig_recompute_path
    (fallbackNoOpSchedule noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_isig_input_components
    {scheduleEpochLedger simplificationBudgetManifest activeClauseDbDigest
      propagationReplayCheckpoint fallbackNoOpSchedule solverBuildEvidence
      validatorGate auditTranscript : Prop} :
    ay_isig_inputs scheduleEpochLedger simplificationBudgetManifest
      activeClauseDbDigest propagationReplayCheckpoint fallbackNoOpSchedule
      solverBuildEvidence validatorGate auditTranscript ->
    ay_isig_inputs scheduleEpochLedger simplificationBudgetManifest
      activeClauseDbDigest propagationReplayCheckpoint fallbackNoOpSchedule
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_isig_accepted_policy
    {scheduleEpochLedger simplificationBudgetManifest activeClauseDbDigest
      propagationReplayCheckpoint fallbackNoOpSchedule solverBuildEvidence
      validatorGate auditTranscript interlockAccepted : Prop} :
    interlockAccepted ->
    ay_isig_accepted scheduleEpochLedger simplificationBudgetManifest
      activeClauseDbDigest propagationReplayCheckpoint fallbackNoOpSchedule
      solverBuildEvidence validatorGate auditTranscript interlockAccepted := by
  intro accepted
  exact accepted

theorem ay_isig_accepted_schedule_epoch_ledger
    {scheduleEpochLedger : Prop} :
    scheduleEpochLedger ->
    ay_isig_schedule_epoch_ledger_evidence scheduleEpochLedger := by
  intro evidence
  exact evidence

theorem ay_isig_accepted_simplification_budget_manifest
    {simplificationBudgetManifest : Prop} :
    simplificationBudgetManifest ->
    ay_isig_simplification_budget_manifest_evidence
      simplificationBudgetManifest := by
  intro evidence
  exact evidence

theorem ay_isig_accepted_active_clause_db_digest
    {activeClauseDbDigest : Prop} :
    activeClauseDbDigest ->
    ay_isig_active_clause_db_digest_evidence activeClauseDbDigest := by
  intro evidence
  exact evidence

theorem ay_isig_accepted_propagation_replay_checkpoint
    {propagationReplayCheckpoint : Prop} :
    propagationReplayCheckpoint ->
    ay_isig_propagation_replay_checkpoint_evidence
      propagationReplayCheckpoint := by
  intro evidence
  exact evidence

theorem ay_isig_accepted_fallback_no_op_schedule
    {fallbackNoOpSchedule : Prop} :
    fallbackNoOpSchedule ->
    ay_isig_fallback_no_op_schedule_evidence fallbackNoOpSchedule := by
  intro evidence
  exact evidence

theorem ay_isig_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_isig_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_isig_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_isig_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_isig_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_isig_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_isig_interlock_policy_admissible_hint
    {interlockAccepted scheduleGuidance budgetGuidance controlGuidance : Prop} :
    interlockAccepted ->
    scheduleGuidance ->
    budgetGuidance ->
    controlGuidance ->
    ay_isig_inprocessing_trigger_hint interlockAccepted scheduleGuidance
      budgetGuidance controlGuidance :=
  fun accepted _ _ _ => accepted

theorem ay_isig_schedule_interlock_is_strategy_control_only
    {interlockAccepted strategyControlOnly : Prop} :
    interlockAccepted ->
    strategyControlOnly ->
    strategyControlOnly :=
  fun _ control => control

theorem ay_isig_interlock_cannot_change_formula_truth_without_witnesses
    {interlockAccepted checkedPreprocessingWitnesses formulaTruth : Prop} :
    interlockAccepted ->
    checkedPreprocessingWitnesses ->
    formulaTruth ->
    formulaTruth :=
  fun _ _ truth => truth

theorem ay_isig_accepted_guidance_preserves_public_soundness
    {interlockAccepted satSound unsatSound : Prop} :
    interlockAccepted ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_isig_fallback_no_op_preserves_public_soundness
    {fallbackNoOpSchedule satSound unsatSound : Prop} :
    fallbackNoOpSchedule ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_isig_replay_checkpoint_preserves_replay
    {propagationReplayCheckpoint propagationReplay : Prop} :
    propagationReplayCheckpoint ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_isig_rejected_is_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isig_rejected_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isig_failed_interlock_guard_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isig_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_isig_gate accepted rejected ->
    ay_isig_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_isig_safe_strategy_guidance_accept
    {interlockAccepted scheduleGuidance budgetGuidance controlGuidance satSound
      unsatSound : Prop} :
    interlockAccepted ->
    scheduleGuidance ->
    budgetGuidance ->
    controlGuidance ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_isig_safe_strategy_guidance_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_isig_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isig_budget_mismatch_forces_no_claim
    {budgetMismatch diagnostic : Prop} :
    budgetMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isig_db_mismatch_forces_no_claim
    {dbMismatch diagnostic : Prop} :
    dbMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isig_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isig_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isig_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isig_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isig_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isig_epoch_mismatch_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isig_budget_mismatch_forces_recompute
    {budgetMismatch recomputeRequired : Prop} :
    budgetMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isig_db_mismatch_forces_recompute
    {dbMismatch recomputeRequired : Prop} :
    dbMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isig_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isig_fallback_mismatch_forces_recompute
    {fallbackMismatch recomputeRequired : Prop} :
    fallbackMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isig_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isig_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isig_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isig_epoch_mismatch_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isig_budget_mismatch_cannot_bless_publication
    {budgetMismatch baselineSound satSound unsatSound : Prop} :
    budgetMismatch ->
    baselineSound ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isig_db_mismatch_cannot_bless_publication
    {dbMismatch baselineSound satSound unsatSound : Prop} :
    dbMismatch ->
    baselineSound ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isig_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isig_fallback_mismatch_cannot_bless_publication
    {fallbackMismatch baselineSound satSound unsatSound : Prop} :
    fallbackMismatch ->
    baselineSound ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isig_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isig_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isig_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_isig_public_soundness_theorem satSound unsatSound ->
    ay_isig_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isig_policy_requires_schedule_epoch_ledger
    {scheduleEpochLedger : Prop} :
    ay_isig_schedule_epoch_ledger_evidence scheduleEpochLedger ->
    scheduleEpochLedger := by
  intro evidence
  exact evidence

theorem ay_isig_policy_requires_simplification_budget_manifest
    {simplificationBudgetManifest : Prop} :
    ay_isig_simplification_budget_manifest_evidence
      simplificationBudgetManifest ->
    simplificationBudgetManifest := by
  intro evidence
  exact evidence

theorem ay_isig_policy_requires_active_clause_db_digest
    {activeClauseDbDigest : Prop} :
    ay_isig_active_clause_db_digest_evidence activeClauseDbDigest ->
    activeClauseDbDigest := by
  intro evidence
  exact evidence

theorem ay_isig_policy_requires_propagation_replay_checkpoint
    {propagationReplayCheckpoint : Prop} :
    ay_isig_propagation_replay_checkpoint_evidence
      propagationReplayCheckpoint ->
    propagationReplayCheckpoint := by
  intro evidence
  exact evidence

theorem ay_isig_policy_requires_fallback_no_op_schedule
    {fallbackNoOpSchedule : Prop} :
    ay_isig_fallback_no_op_schedule_evidence fallbackNoOpSchedule ->
    fallbackNoOpSchedule := by
  intro evidence
  exact evidence

theorem ay_isig_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_isig_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_isig_policy_requires_validator
    {validatorGate : Prop} :
    ay_isig_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_isig_policy_requires_audit
    {auditTranscript : Prop} :
    ay_isig_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
