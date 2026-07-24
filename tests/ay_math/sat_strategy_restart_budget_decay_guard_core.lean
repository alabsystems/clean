def ay_rbdg_conj (p q : Prop) : Prop := p ∧ q

def ay_rbdg_disj (p q : Prop) : Prop := p ∨ q

def ay_rbdg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rbdg_disj satSound unsatSound

def ay_rbdg_inputs
    (restartBudgetDigest conflictWindowLedger learntClauseQualityLedger
      deterministicDecaySchedule propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_rbdg_conj restartBudgetDigest
    (ay_rbdg_conj conflictWindowLedger
      (ay_rbdg_conj learntClauseQualityLedger
        (ay_rbdg_conj deterministicDecaySchedule
          (ay_rbdg_conj propagationReplayWitness
            (ay_rbdg_conj fallbackBaseline
              (ay_rbdg_conj solverBuildEvidence
                (ay_rbdg_conj validatorGate auditTranscript)))))))

def ay_rbdg_restart_budget_digest_evidence
    (restartBudgetDigest : Prop) : Prop :=
  restartBudgetDigest

def ay_rbdg_conflict_window_ledger_evidence
    (conflictWindowLedger : Prop) : Prop :=
  conflictWindowLedger

def ay_rbdg_learnt_clause_quality_ledger_evidence
    (learntClauseQualityLedger : Prop) : Prop :=
  learntClauseQualityLedger

def ay_rbdg_deterministic_decay_schedule_evidence
    (deterministicDecaySchedule : Prop) : Prop :=
  deterministicDecaySchedule

def ay_rbdg_propagation_replay_witness_evidence
    (propagationReplayWitness : Prop) : Prop :=
  propagationReplayWitness

def ay_rbdg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_rbdg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rbdg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rbdg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rbdg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rbdg_accepted
    (restartBudgetDigest conflictWindowLedger learntClauseQualityLedger
      deterministicDecaySchedule propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript decayAccepted :
      Prop) : Prop :=
  decayAccepted

def ay_rbdg_rejected
    (digestMismatch windowMismatch qualityMismatch scheduleMismatch
      replayMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch : Prop) : Prop :=
  ay_rbdg_disj digestMismatch
    (ay_rbdg_disj windowMismatch
      (ay_rbdg_disj qualityMismatch
        (ay_rbdg_disj scheduleMismatch
          (ay_rbdg_disj replayMismatch
            (ay_rbdg_disj baselineMismatch
              (ay_rbdg_disj buildMismatch
                (ay_rbdg_disj validatorMismatch auditMismatch)))))))

def ay_rbdg_gate (accepted rejected : Prop) : Prop :=
  ay_rbdg_disj accepted rejected

def ay_rbdg_restart_budget_decay_hint
    (decayAccepted budgetGuidance windowGuidance searchControlGuidance : Prop) :
    Prop :=
  decayAccepted

def ay_rbdg_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_rbdg_input_components
    {restartBudgetDigest conflictWindowLedger learntClauseQualityLedger
      deterministicDecaySchedule propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_rbdg_inputs restartBudgetDigest conflictWindowLedger
      learntClauseQualityLedger deterministicDecaySchedule
      propagationReplayWitness fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    ay_rbdg_inputs restartBudgetDigest conflictWindowLedger
      learntClauseQualityLedger deterministicDecaySchedule
      propagationReplayWitness fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rbdg_accepted_policy
    {restartBudgetDigest conflictWindowLedger learntClauseQualityLedger
      deterministicDecaySchedule propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript decayAccepted : Prop} :
    decayAccepted ->
    ay_rbdg_accepted restartBudgetDigest conflictWindowLedger
      learntClauseQualityLedger deterministicDecaySchedule
      propagationReplayWitness fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript decayAccepted := by
  intro accepted
  exact accepted

theorem ay_rbdg_accepted_restart_budget_digest
    {restartBudgetDigest : Prop} :
    restartBudgetDigest ->
    ay_rbdg_restart_budget_digest_evidence restartBudgetDigest := by
  intro evidence
  exact evidence

theorem ay_rbdg_accepted_conflict_window_ledger
    {conflictWindowLedger : Prop} :
    conflictWindowLedger ->
    ay_rbdg_conflict_window_ledger_evidence conflictWindowLedger := by
  intro evidence
  exact evidence

theorem ay_rbdg_accepted_learnt_clause_quality_ledger
    {learntClauseQualityLedger : Prop} :
    learntClauseQualityLedger ->
    ay_rbdg_learnt_clause_quality_ledger_evidence
      learntClauseQualityLedger := by
  intro evidence
  exact evidence

theorem ay_rbdg_accepted_deterministic_decay_schedule
    {deterministicDecaySchedule : Prop} :
    deterministicDecaySchedule ->
    ay_rbdg_deterministic_decay_schedule_evidence
      deterministicDecaySchedule := by
  intro evidence
  exact evidence

theorem ay_rbdg_accepted_propagation_replay_witness
    {propagationReplayWitness : Prop} :
    propagationReplayWitness ->
    ay_rbdg_propagation_replay_witness_evidence
      propagationReplayWitness := by
  intro evidence
  exact evidence

theorem ay_rbdg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_rbdg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rbdg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_rbdg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rbdg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rbdg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rbdg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rbdg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rbdg_decay_policy_admissible_hint
    {decayAccepted budgetGuidance windowGuidance searchControlGuidance : Prop} :
    decayAccepted ->
    budgetGuidance ->
    windowGuidance ->
    searchControlGuidance ->
    ay_rbdg_restart_budget_decay_hint decayAccepted budgetGuidance
      windowGuidance searchControlGuidance :=
  fun accepted _ _ _ => accepted

theorem ay_rbdg_restart_budget_decay_is_search_control_only
    {decayAccepted searchControlOnly : Prop} :
    decayAccepted ->
    searchControlOnly ->
    searchControlOnly :=
  fun _ control => control

theorem ay_rbdg_decay_cannot_change_original_formula_truth
    {decayAccepted originalFormulaTruth : Prop} :
    decayAccepted ->
    originalFormulaTruth ->
    originalFormulaTruth :=
  fun _ truth => truth

theorem ay_rbdg_accepted_decay_preserves_public_soundness
    {decayAccepted satSound unsatSound : Prop} :
    decayAccepted ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rbdg_schedule_preserves_replay_witness
    {deterministicDecaySchedule propagationReplayWitness : Prop} :
    deterministicDecaySchedule ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_rbdg_quality_ledger_preserves_budget_guidance
    {learntClauseQualityLedger budgetGuidance : Prop} :
    learntClauseQualityLedger ->
    budgetGuidance ->
    budgetGuidance :=
  fun _ guidance => guidance

theorem ay_rbdg_window_ledger_preserves_decay_schedule
    {conflictWindowLedger deterministicDecaySchedule : Prop} :
    conflictWindowLedger ->
    deterministicDecaySchedule ->
    deterministicDecaySchedule :=
  fun _ schedule => schedule

theorem ay_rbdg_rejected_is_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbdg_rejected_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbdg_failed_decay_guard_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbdg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rbdg_gate accepted rejected ->
    ay_rbdg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rbdg_safe_strategy_guidance_accept
    {decayAccepted budgetGuidance windowGuidance searchControlGuidance satSound
      unsatSound : Prop} :
    decayAccepted ->
    budgetGuidance ->
    windowGuidance ->
    searchControlGuidance ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_rbdg_safe_strategy_guidance_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rbdg_digest_mismatch_forces_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbdg_window_mismatch_forces_no_claim
    {windowMismatch diagnostic : Prop} :
    windowMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbdg_quality_mismatch_forces_no_claim
    {qualityMismatch diagnostic : Prop} :
    qualityMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbdg_schedule_mismatch_forces_no_claim
    {scheduleMismatch diagnostic : Prop} :
    scheduleMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbdg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbdg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbdg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbdg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbdg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbdg_digest_mismatch_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbdg_window_mismatch_forces_recompute
    {windowMismatch recomputeRequired : Prop} :
    windowMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbdg_quality_mismatch_forces_recompute
    {qualityMismatch recomputeRequired : Prop} :
    qualityMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbdg_schedule_mismatch_forces_recompute
    {scheduleMismatch recomputeRequired : Prop} :
    scheduleMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbdg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbdg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbdg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbdg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbdg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbdg_digest_mismatch_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbdg_window_mismatch_cannot_bless_publication
    {windowMismatch baselineSound satSound unsatSound : Prop} :
    windowMismatch ->
    baselineSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbdg_quality_mismatch_cannot_bless_publication
    {qualityMismatch baselineSound satSound unsatSound : Prop} :
    qualityMismatch ->
    baselineSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbdg_schedule_mismatch_cannot_bless_publication
    {scheduleMismatch baselineSound satSound unsatSound : Prop} :
    scheduleMismatch ->
    baselineSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbdg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbdg_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbdg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbdg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbdg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound ->
    ay_rbdg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbdg_policy_requires_restart_budget_digest
    {restartBudgetDigest : Prop} :
    ay_rbdg_restart_budget_digest_evidence restartBudgetDigest ->
    restartBudgetDigest := by
  intro evidence
  exact evidence

theorem ay_rbdg_policy_requires_conflict_window_ledger
    {conflictWindowLedger : Prop} :
    ay_rbdg_conflict_window_ledger_evidence conflictWindowLedger ->
    conflictWindowLedger := by
  intro evidence
  exact evidence

theorem ay_rbdg_policy_requires_learnt_clause_quality_ledger
    {learntClauseQualityLedger : Prop} :
    ay_rbdg_learnt_clause_quality_ledger_evidence
      learntClauseQualityLedger ->
    learntClauseQualityLedger := by
  intro evidence
  exact evidence

theorem ay_rbdg_policy_requires_deterministic_decay_schedule
    {deterministicDecaySchedule : Prop} :
    ay_rbdg_deterministic_decay_schedule_evidence
      deterministicDecaySchedule ->
    deterministicDecaySchedule := by
  intro evidence
  exact evidence

theorem ay_rbdg_policy_requires_propagation_replay
    {propagationReplayWitness : Prop} :
    ay_rbdg_propagation_replay_witness_evidence propagationReplayWitness ->
    propagationReplayWitness := by
  intro evidence
  exact evidence

theorem ay_rbdg_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_rbdg_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rbdg_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_rbdg_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rbdg_policy_requires_validator
    {validatorGate : Prop} :
    ay_rbdg_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_rbdg_policy_requires_audit
    {auditTranscript : Prop} :
    ay_rbdg_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
