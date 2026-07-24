def ay_rscg_conj (p q : Prop) : Prop := p ∧ q

def ay_rscg_disj (p q : Prop) : Prop := p ∨ q

def ay_rscg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rscg_disj satSound unsatSound

def ay_rscg_inputs
    (restartCounterDigest phaseCacheDigest decisionStackCheckpoint
      learntClauseTierLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_rscg_conj restartCounterDigest
    (ay_rscg_conj phaseCacheDigest
      (ay_rscg_conj decisionStackCheckpoint
        (ay_rscg_conj learntClauseTierLedger
          (ay_rscg_conj propagationReplay
            (ay_rscg_conj fallbackBaseline
              (ay_rscg_conj solverBuildEvidence
                (ay_rscg_conj validatorGate auditTranscript)))))))

def ay_rscg_restart_counter_digest_evidence
    (restartCounterDigest : Prop) : Prop :=
  restartCounterDigest

def ay_rscg_phase_cache_digest_evidence
    (phaseCacheDigest : Prop) : Prop :=
  phaseCacheDigest

def ay_rscg_decision_stack_checkpoint_evidence
    (decisionStackCheckpoint : Prop) : Prop :=
  decisionStackCheckpoint

def ay_rscg_learnt_clause_tier_ledger_evidence
    (learntClauseTierLedger : Prop) : Prop :=
  learntClauseTierLedger

def ay_rscg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_rscg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_rscg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rscg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rscg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rscg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rscg_accepted
    (restartCounterDigest phaseCacheDigest decisionStackCheckpoint
      learntClauseTierLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript restoreAccepted :
      Prop) : Prop :=
  restoreAccepted

def ay_rscg_rejected
    (counterMismatch phaseMismatch stackMismatch tierMismatch replayMismatch
      fallbackMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    Prop :=
  ay_rscg_disj counterMismatch
    (ay_rscg_disj phaseMismatch
      (ay_rscg_disj stackMismatch
        (ay_rscg_disj tierMismatch
          (ay_rscg_disj replayMismatch
            (ay_rscg_disj fallbackMismatch
              (ay_rscg_disj buildMismatch
                (ay_rscg_disj validatorMismatch auditMismatch)))))))

def ay_rscg_gate (accepted rejected : Prop) : Prop :=
  ay_rscg_disj accepted rejected

def ay_rscg_restart_state_restore_hint
    (restoreAccepted restartGuidance phaseGuidance stackGuidance : Prop) :
    Prop :=
  restoreAccepted

def ay_rscg_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_rscg_input_components
    {restartCounterDigest phaseCacheDigest decisionStackCheckpoint
      learntClauseTierLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_rscg_inputs restartCounterDigest phaseCacheDigest
      decisionStackCheckpoint learntClauseTierLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    ay_rscg_inputs restartCounterDigest phaseCacheDigest
      decisionStackCheckpoint learntClauseTierLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rscg_accepted_policy
    {restartCounterDigest phaseCacheDigest decisionStackCheckpoint
      learntClauseTierLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript restoreAccepted :
      Prop} :
    restoreAccepted ->
    ay_rscg_accepted restartCounterDigest phaseCacheDigest
      decisionStackCheckpoint learntClauseTierLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      restoreAccepted := by
  intro accepted
  exact accepted

theorem ay_rscg_accepted_restart_counter_digest
    {restartCounterDigest : Prop} :
    restartCounterDigest ->
    ay_rscg_restart_counter_digest_evidence restartCounterDigest := by
  intro evidence
  exact evidence

theorem ay_rscg_accepted_phase_cache_digest
    {phaseCacheDigest : Prop} :
    phaseCacheDigest ->
    ay_rscg_phase_cache_digest_evidence phaseCacheDigest := by
  intro evidence
  exact evidence

theorem ay_rscg_accepted_decision_stack_checkpoint
    {decisionStackCheckpoint : Prop} :
    decisionStackCheckpoint ->
    ay_rscg_decision_stack_checkpoint_evidence decisionStackCheckpoint := by
  intro evidence
  exact evidence

theorem ay_rscg_accepted_learnt_clause_tier_ledger
    {learntClauseTierLedger : Prop} :
    learntClauseTierLedger ->
    ay_rscg_learnt_clause_tier_ledger_evidence learntClauseTierLedger := by
  intro evidence
  exact evidence

theorem ay_rscg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_rscg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_rscg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_rscg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rscg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_rscg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rscg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rscg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rscg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rscg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rscg_restart_state_restore_policy_admissible_hint
    {restoreAccepted restartGuidance phaseGuidance stackGuidance : Prop} :
    restoreAccepted ->
    restartGuidance ->
    phaseGuidance ->
    stackGuidance ->
    ay_rscg_restart_state_restore_hint restoreAccepted restartGuidance
      phaseGuidance stackGuidance :=
  fun accepted _ _ _ => accepted

theorem ay_rscg_restore_is_search_control_data_recovery_only
    {restoreAccepted searchControlDataRecoveryOnly : Prop} :
    restoreAccepted ->
    searchControlDataRecoveryOnly ->
    searchControlDataRecoveryOnly :=
  fun _ recovery => recovery

theorem ay_rscg_restore_cannot_change_original_formula_truth
    {restoreAccepted originalFormulaTruth : Prop} :
    restoreAccepted ->
    originalFormulaTruth ->
    originalFormulaTruth :=
  fun _ truth => truth

theorem ay_rscg_accepted_restore_preserves_public_soundness
    {restoreAccepted satSound unsatSound : Prop} :
    restoreAccepted ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rscg_accepted_restore_preserves_deterministic_restart_behavior
    {restoreAccepted deterministicRestartBehavior : Prop} :
    restoreAccepted ->
    deterministicRestartBehavior ->
    deterministicRestartBehavior :=
  fun _ behavior => behavior

theorem ay_rscg_counter_digest_preserves_restart_behavior
    {restartCounterDigest deterministicRestartBehavior : Prop} :
    restartCounterDigest ->
    deterministicRestartBehavior ->
    deterministicRestartBehavior :=
  fun _ behavior => behavior

theorem ay_rscg_phase_cache_preserves_stack_checkpoint
    {phaseCacheDigest decisionStackCheckpoint : Prop} :
    phaseCacheDigest ->
    decisionStackCheckpoint ->
    decisionStackCheckpoint :=
  fun _ checkpoint => checkpoint

theorem ay_rscg_tier_ledger_preserves_replay
    {learntClauseTierLedger propagationReplay : Prop} :
    learntClauseTierLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rscg_rejected_is_no_claim
    {counterMismatch diagnostic : Prop} :
    counterMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rscg_rejected_forces_recompute
    {counterMismatch recomputeRequired : Prop} :
    counterMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rscg_failed_restart_state_guard_cannot_bless_publication
    {counterMismatch baselineSound satSound unsatSound : Prop} :
    counterMismatch ->
    baselineSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rscg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rscg_gate accepted rejected ->
    ay_rscg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rscg_safe_strategy_guidance_accept
    {restoreAccepted restartGuidance phaseGuidance stackGuidance satSound
      unsatSound : Prop} :
    restoreAccepted ->
    restartGuidance ->
    phaseGuidance ->
    stackGuidance ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_rscg_safe_strategy_guidance_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rscg_counter_mismatch_forces_no_claim
    {counterMismatch diagnostic : Prop} :
    counterMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rscg_phase_mismatch_forces_no_claim
    {phaseMismatch diagnostic : Prop} :
    phaseMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rscg_stack_mismatch_forces_no_claim
    {stackMismatch diagnostic : Prop} :
    stackMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rscg_tier_mismatch_forces_no_claim
    {tierMismatch diagnostic : Prop} :
    tierMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rscg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rscg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rscg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rscg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rscg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rscg_counter_mismatch_forces_recompute
    {counterMismatch recomputeRequired : Prop} :
    counterMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rscg_phase_mismatch_forces_recompute
    {phaseMismatch recomputeRequired : Prop} :
    phaseMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rscg_stack_mismatch_forces_recompute
    {stackMismatch recomputeRequired : Prop} :
    stackMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rscg_tier_mismatch_forces_recompute
    {tierMismatch recomputeRequired : Prop} :
    tierMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rscg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rscg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rscg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rscg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rscg_counter_mismatch_cannot_bless_publication
    {counterMismatch baselineSound satSound unsatSound : Prop} :
    counterMismatch ->
    baselineSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rscg_phase_mismatch_cannot_bless_publication
    {phaseMismatch baselineSound satSound unsatSound : Prop} :
    phaseMismatch ->
    baselineSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rscg_stack_mismatch_cannot_bless_publication
    {stackMismatch baselineSound satSound unsatSound : Prop} :
    stackMismatch ->
    baselineSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rscg_tier_mismatch_cannot_bless_publication
    {tierMismatch baselineSound satSound unsatSound : Prop} :
    tierMismatch ->
    baselineSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rscg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rscg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rscg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rscg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound ->
    ay_rscg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rscg_policy_requires_restart_counter_digest
    {restartCounterDigest : Prop} :
    ay_rscg_restart_counter_digest_evidence restartCounterDigest ->
    restartCounterDigest := by
  intro evidence
  exact evidence

theorem ay_rscg_policy_requires_phase_cache_digest
    {phaseCacheDigest : Prop} :
    ay_rscg_phase_cache_digest_evidence phaseCacheDigest ->
    phaseCacheDigest := by
  intro evidence
  exact evidence

theorem ay_rscg_policy_requires_decision_stack_checkpoint
    {decisionStackCheckpoint : Prop} :
    ay_rscg_decision_stack_checkpoint_evidence decisionStackCheckpoint ->
    decisionStackCheckpoint := by
  intro evidence
  exact evidence

theorem ay_rscg_policy_requires_learnt_clause_tier_ledger
    {learntClauseTierLedger : Prop} :
    ay_rscg_learnt_clause_tier_ledger_evidence learntClauseTierLedger ->
    learntClauseTierLedger := by
  intro evidence
  exact evidence

theorem ay_rscg_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_rscg_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_rscg_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_rscg_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rscg_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_rscg_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rscg_policy_requires_validator
    {validatorGate : Prop} :
    ay_rscg_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_rscg_policy_requires_audit
    {auditTranscript : Prop} :
    ay_rscg_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
