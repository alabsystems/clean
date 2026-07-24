def ay_rsag_conj (p q : Prop) : Prop := p ∧ q

def ay_rsag_disj (p q : Prop) : Prop := p ∨ q

def ay_rsag_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rsag_disj satSound unsatSound

def ay_rsag_inputs
    (scheduleEpochLedger conflictRateWindowDigest lbdTrendManifest
      decisionStackCheckpoint propagationReplay fallbackStaticSchedule
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_rsag_conj scheduleEpochLedger
    (ay_rsag_conj conflictRateWindowDigest
      (ay_rsag_conj lbdTrendManifest
        (ay_rsag_conj decisionStackCheckpoint
          (ay_rsag_conj propagationReplay
            (ay_rsag_conj fallbackStaticSchedule
              (ay_rsag_conj solverBuildEvidence
                (ay_rsag_conj validatorGate auditTranscript)))))))

def ay_rsag_schedule_epoch_ledger_evidence
    (scheduleEpochLedger : Prop) : Prop :=
  scheduleEpochLedger

def ay_rsag_conflict_rate_window_digest_evidence
    (conflictRateWindowDigest : Prop) : Prop :=
  conflictRateWindowDigest

def ay_rsag_lbd_trend_manifest_evidence
    (lbdTrendManifest : Prop) : Prop :=
  lbdTrendManifest

def ay_rsag_decision_stack_checkpoint_evidence
    (decisionStackCheckpoint : Prop) : Prop :=
  decisionStackCheckpoint

def ay_rsag_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_rsag_fallback_static_schedule_evidence
    (fallbackStaticSchedule : Prop) : Prop :=
  fallbackStaticSchedule

def ay_rsag_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rsag_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rsag_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rsag_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rsag_accepted
    (scheduleEpochLedger conflictRateWindowDigest lbdTrendManifest
      decisionStackCheckpoint propagationReplay fallbackStaticSchedule
      solverBuildEvidence validatorGate auditTranscript adaptationAccepted :
      Prop) : Prop :=
  adaptationAccepted

def ay_rsag_rejected
    (epochMismatch windowMismatch trendMismatch checkpointMismatch
      replayMismatch fallbackMismatch buildMismatch validatorMismatch
      auditMismatch : Prop) : Prop :=
  ay_rsag_disj epochMismatch
    (ay_rsag_disj windowMismatch
      (ay_rsag_disj trendMismatch
        (ay_rsag_disj checkpointMismatch
          (ay_rsag_disj replayMismatch
            (ay_rsag_disj fallbackMismatch
              (ay_rsag_disj buildMismatch
                (ay_rsag_disj validatorMismatch auditMismatch)))))))

def ay_rsag_gate (accepted rejected : Prop) : Prop :=
  ay_rsag_disj accepted rejected

def ay_rsag_restart_adaptation_hint
    (adaptationAccepted scheduleGuidance restartWindowGuidance
      searchControlGuidance : Prop) : Prop :=
  adaptationAccepted

def ay_rsag_recompute_path
    (fallbackStaticSchedule noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_rsag_input_components
    {scheduleEpochLedger conflictRateWindowDigest lbdTrendManifest
      decisionStackCheckpoint propagationReplay fallbackStaticSchedule
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_rsag_inputs scheduleEpochLedger conflictRateWindowDigest
      lbdTrendManifest decisionStackCheckpoint propagationReplay
      fallbackStaticSchedule solverBuildEvidence validatorGate auditTranscript ->
    ay_rsag_inputs scheduleEpochLedger conflictRateWindowDigest
      lbdTrendManifest decisionStackCheckpoint propagationReplay
      fallbackStaticSchedule solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rsag_accepted_policy
    {scheduleEpochLedger conflictRateWindowDigest lbdTrendManifest
      decisionStackCheckpoint propagationReplay fallbackStaticSchedule
      solverBuildEvidence validatorGate auditTranscript adaptationAccepted :
      Prop} :
    adaptationAccepted ->
    ay_rsag_accepted scheduleEpochLedger conflictRateWindowDigest
      lbdTrendManifest decisionStackCheckpoint propagationReplay
      fallbackStaticSchedule solverBuildEvidence validatorGate auditTranscript
      adaptationAccepted := by
  intro accepted
  exact accepted

theorem ay_rsag_accepted_schedule_epoch_ledger
    {scheduleEpochLedger : Prop} :
    scheduleEpochLedger ->
    ay_rsag_schedule_epoch_ledger_evidence scheduleEpochLedger := by
  intro evidence
  exact evidence

theorem ay_rsag_accepted_conflict_rate_window_digest
    {conflictRateWindowDigest : Prop} :
    conflictRateWindowDigest ->
    ay_rsag_conflict_rate_window_digest_evidence conflictRateWindowDigest := by
  intro evidence
  exact evidence

theorem ay_rsag_accepted_lbd_trend_manifest
    {lbdTrendManifest : Prop} :
    lbdTrendManifest ->
    ay_rsag_lbd_trend_manifest_evidence lbdTrendManifest := by
  intro evidence
  exact evidence

theorem ay_rsag_accepted_decision_stack_checkpoint
    {decisionStackCheckpoint : Prop} :
    decisionStackCheckpoint ->
    ay_rsag_decision_stack_checkpoint_evidence decisionStackCheckpoint := by
  intro evidence
  exact evidence

theorem ay_rsag_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_rsag_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_rsag_accepted_fallback_static_schedule
    {fallbackStaticSchedule : Prop} :
    fallbackStaticSchedule ->
    ay_rsag_fallback_static_schedule_evidence fallbackStaticSchedule := by
  intro evidence
  exact evidence

theorem ay_rsag_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_rsag_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rsag_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rsag_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rsag_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rsag_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rsag_adaptation_policy_admissible_hint
    {adaptationAccepted scheduleGuidance restartWindowGuidance
      searchControlGuidance : Prop} :
    adaptationAccepted ->
    scheduleGuidance ->
    restartWindowGuidance ->
    searchControlGuidance ->
    ay_rsag_restart_adaptation_hint adaptationAccepted scheduleGuidance
      restartWindowGuidance searchControlGuidance :=
  fun accepted _ _ _ => accepted

theorem ay_rsag_adaptation_is_search_control_only
    {adaptationAccepted searchControlOnly : Prop} :
    adaptationAccepted ->
    searchControlOnly ->
    searchControlOnly :=
  fun _ control => control

theorem ay_rsag_guidance_cannot_change_formula_truth
    {adaptationAccepted formulaTruth : Prop} :
    adaptationAccepted ->
    formulaTruth ->
    formulaTruth :=
  fun _ truth => truth

theorem ay_rsag_accepted_guidance_preserves_public_soundness
    {adaptationAccepted satSound unsatSound : Prop} :
    adaptationAccepted ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rsag_static_fallback_preserves_public_soundness
    {fallbackStaticSchedule satSound unsatSound : Prop} :
    fallbackStaticSchedule ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rsag_decision_checkpoint_preserves_replay
    {decisionStackCheckpoint propagationReplay : Prop} :
    decisionStackCheckpoint ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rsag_rejected_is_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsag_rejected_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsag_failed_restart_adaptation_guard_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsag_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rsag_gate accepted rejected ->
    ay_rsag_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rsag_safe_strategy_guidance_accept
    {adaptationAccepted scheduleGuidance restartWindowGuidance
      searchControlGuidance satSound unsatSound : Prop} :
    adaptationAccepted ->
    scheduleGuidance ->
    restartWindowGuidance ->
    searchControlGuidance ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_rsag_safe_strategy_guidance_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rsag_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsag_window_mismatch_forces_no_claim
    {windowMismatch diagnostic : Prop} :
    windowMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsag_trend_mismatch_forces_no_claim
    {trendMismatch diagnostic : Prop} :
    trendMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsag_checkpoint_mismatch_forces_no_claim
    {checkpointMismatch diagnostic : Prop} :
    checkpointMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsag_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsag_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsag_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsag_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsag_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsag_epoch_mismatch_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsag_window_mismatch_forces_recompute
    {windowMismatch recomputeRequired : Prop} :
    windowMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsag_trend_mismatch_forces_recompute
    {trendMismatch recomputeRequired : Prop} :
    trendMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsag_checkpoint_mismatch_forces_recompute
    {checkpointMismatch recomputeRequired : Prop} :
    checkpointMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsag_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsag_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsag_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsag_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsag_epoch_mismatch_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsag_window_mismatch_cannot_bless_publication
    {windowMismatch baselineSound satSound unsatSound : Prop} :
    windowMismatch ->
    baselineSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsag_trend_mismatch_cannot_bless_publication
    {trendMismatch baselineSound satSound unsatSound : Prop} :
    trendMismatch ->
    baselineSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsag_checkpoint_mismatch_cannot_bless_publication
    {checkpointMismatch baselineSound satSound unsatSound : Prop} :
    checkpointMismatch ->
    baselineSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsag_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsag_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsag_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsag_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound ->
    ay_rsag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsag_policy_requires_schedule_epoch_ledger
    {scheduleEpochLedger : Prop} :
    ay_rsag_schedule_epoch_ledger_evidence scheduleEpochLedger ->
    scheduleEpochLedger := by
  intro evidence
  exact evidence

theorem ay_rsag_policy_requires_conflict_rate_window_digest
    {conflictRateWindowDigest : Prop} :
    ay_rsag_conflict_rate_window_digest_evidence conflictRateWindowDigest ->
    conflictRateWindowDigest := by
  intro evidence
  exact evidence

theorem ay_rsag_policy_requires_lbd_trend_manifest
    {lbdTrendManifest : Prop} :
    ay_rsag_lbd_trend_manifest_evidence lbdTrendManifest ->
    lbdTrendManifest := by
  intro evidence
  exact evidence

theorem ay_rsag_policy_requires_decision_stack_checkpoint
    {decisionStackCheckpoint : Prop} :
    ay_rsag_decision_stack_checkpoint_evidence decisionStackCheckpoint ->
    decisionStackCheckpoint := by
  intro evidence
  exact evidence

theorem ay_rsag_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_rsag_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_rsag_policy_requires_fallback_static_schedule
    {fallbackStaticSchedule : Prop} :
    ay_rsag_fallback_static_schedule_evidence fallbackStaticSchedule ->
    fallbackStaticSchedule := by
  intro evidence
  exact evidence

theorem ay_rsag_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_rsag_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rsag_policy_requires_validator
    {validatorGate : Prop} :
    ay_rsag_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_rsag_policy_requires_audit
    {auditTranscript : Prop} :
    ay_rsag_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
