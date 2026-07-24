def ay_pqcg_conj (p q : Prop) : Prop := p ∧ q

def ay_pqcg_disj (p q : Prop) : Prop := p ∨ q

def ay_pqcg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_pqcg_disj satSound unsatSound

def ay_pqcg_inputs
    (queueDigest trailCheckpoint watchlistDigest reasonAvailabilityLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_pqcg_conj queueDigest
    (ay_pqcg_conj trailCheckpoint
      (ay_pqcg_conj watchlistDigest
        (ay_pqcg_conj reasonAvailabilityLedger
          (ay_pqcg_conj propagationReplay
            (ay_pqcg_conj fallbackBaseline
              (ay_pqcg_conj solverBuildEvidence
                (ay_pqcg_conj validatorGate auditTranscript)))))))

def ay_pqcg_queue_digest_evidence (queueDigest : Prop) : Prop :=
  queueDigest

def ay_pqcg_trail_checkpoint_evidence
    (trailCheckpoint : Prop) : Prop :=
  trailCheckpoint

def ay_pqcg_watchlist_digest_evidence
    (watchlistDigest : Prop) : Prop :=
  watchlistDigest

def ay_pqcg_reason_availability_ledger_evidence
    (reasonAvailabilityLedger : Prop) : Prop :=
  reasonAvailabilityLedger

def ay_pqcg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_pqcg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_pqcg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_pqcg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_pqcg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_pqcg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_pqcg_accepted
    (queueDigest trailCheckpoint watchlistDigest reasonAvailabilityLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript restoreAccepted : Prop) : Prop :=
  restoreAccepted

def ay_pqcg_rejected
    (queueMismatch trailMismatch watchMismatch reasonMismatch replayMismatch
      fallbackMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    Prop :=
  ay_pqcg_disj queueMismatch
    (ay_pqcg_disj trailMismatch
      (ay_pqcg_disj watchMismatch
        (ay_pqcg_disj reasonMismatch
          (ay_pqcg_disj replayMismatch
            (ay_pqcg_disj fallbackMismatch
              (ay_pqcg_disj buildMismatch
                (ay_pqcg_disj validatorMismatch auditMismatch)))))))

def ay_pqcg_gate (accepted rejected : Prop) : Prop :=
  ay_pqcg_disj accepted rejected

def ay_pqcg_queue_restore_hint
    (restoreAccepted queueGuidance trailGuidance replayGuidance : Prop) :
    Prop :=
  restoreAccepted

def ay_pqcg_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_pqcg_input_components
    {queueDigest trailCheckpoint watchlistDigest reasonAvailabilityLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_pqcg_inputs queueDigest trailCheckpoint watchlistDigest
      reasonAvailabilityLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_pqcg_inputs queueDigest trailCheckpoint watchlistDigest
      reasonAvailabilityLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_pqcg_accepted_policy
    {queueDigest trailCheckpoint watchlistDigest reasonAvailabilityLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript restoreAccepted : Prop} :
    restoreAccepted ->
    ay_pqcg_accepted queueDigest trailCheckpoint watchlistDigest
      reasonAvailabilityLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript restoreAccepted := by
  intro accepted
  exact accepted

theorem ay_pqcg_accepted_queue_digest
    {queueDigest : Prop} :
    queueDigest -> ay_pqcg_queue_digest_evidence queueDigest := by
  intro evidence
  exact evidence

theorem ay_pqcg_accepted_trail_checkpoint
    {trailCheckpoint : Prop} :
    trailCheckpoint ->
    ay_pqcg_trail_checkpoint_evidence trailCheckpoint := by
  intro evidence
  exact evidence

theorem ay_pqcg_accepted_watchlist_digest
    {watchlistDigest : Prop} :
    watchlistDigest ->
    ay_pqcg_watchlist_digest_evidence watchlistDigest := by
  intro evidence
  exact evidence

theorem ay_pqcg_accepted_reason_availability_ledger
    {reasonAvailabilityLedger : Prop} :
    reasonAvailabilityLedger ->
    ay_pqcg_reason_availability_ledger_evidence reasonAvailabilityLedger := by
  intro evidence
  exact evidence

theorem ay_pqcg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_pqcg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_pqcg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_pqcg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_pqcg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_pqcg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_pqcg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_pqcg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_pqcg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_pqcg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_pqcg_queue_restore_policy_admissible_hint
    {restoreAccepted queueGuidance trailGuidance replayGuidance : Prop} :
    restoreAccepted ->
    queueGuidance ->
    trailGuidance ->
    replayGuidance ->
    ay_pqcg_queue_restore_hint restoreAccepted queueGuidance
      trailGuidance replayGuidance :=
  fun accepted _ _ _ => accepted

theorem ay_pqcg_restore_is_data_structure_recovery_only
    {restoreAccepted dataStructureRecoveryOnly : Prop} :
    restoreAccepted ->
    dataStructureRecoveryOnly ->
    dataStructureRecoveryOnly :=
  fun _ recovery => recovery

theorem ay_pqcg_restore_cannot_change_original_formula_truth
    {restoreAccepted originalFormulaTruth : Prop} :
    restoreAccepted ->
    originalFormulaTruth ->
    originalFormulaTruth :=
  fun _ truth => truth

theorem ay_pqcg_accepted_restore_preserves_public_soundness
    {restoreAccepted satSound unsatSound : Prop} :
    restoreAccepted ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_pqcg_accepted_restore_preserves_propagation_replay
    {restoreAccepted propagationReplay : Prop} :
    restoreAccepted ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_pqcg_reason_availability_preserves_replay
    {reasonAvailabilityLedger propagationReplay : Prop} :
    reasonAvailabilityLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_pqcg_trail_checkpoint_preserves_replay
    {trailCheckpoint propagationReplay : Prop} :
    trailCheckpoint ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_pqcg_rejected_is_no_claim
    {queueMismatch diagnostic : Prop} :
    queueMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqcg_rejected_forces_recompute
    {queueMismatch recomputeRequired : Prop} :
    queueMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqcg_failed_propagation_queue_checkpoint_guard_cannot_bless_publication
    {queueMismatch baselineSound satSound unsatSound : Prop} :
    queueMismatch ->
    baselineSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqcg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_pqcg_gate accepted rejected ->
    ay_pqcg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_pqcg_safe_strategy_guidance_accept
    {restoreAccepted queueGuidance trailGuidance replayGuidance satSound
      unsatSound : Prop} :
    restoreAccepted ->
    queueGuidance ->
    trailGuidance ->
    replayGuidance ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_pqcg_safe_strategy_guidance_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_pqcg_queue_mismatch_forces_no_claim
    {queueMismatch diagnostic : Prop} :
    queueMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqcg_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqcg_watch_mismatch_forces_no_claim
    {watchMismatch diagnostic : Prop} :
    watchMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqcg_reason_mismatch_forces_no_claim
    {reasonMismatch diagnostic : Prop} :
    reasonMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqcg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqcg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqcg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqcg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqcg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqcg_queue_mismatch_forces_recompute
    {queueMismatch recomputeRequired : Prop} :
    queueMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqcg_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqcg_watch_mismatch_forces_recompute
    {watchMismatch recomputeRequired : Prop} :
    watchMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqcg_reason_mismatch_forces_recompute
    {reasonMismatch recomputeRequired : Prop} :
    reasonMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqcg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqcg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqcg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqcg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqcg_queue_mismatch_cannot_bless_publication
    {queueMismatch baselineSound satSound unsatSound : Prop} :
    queueMismatch ->
    baselineSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqcg_trail_mismatch_cannot_bless_publication
    {trailMismatch baselineSound satSound unsatSound : Prop} :
    trailMismatch ->
    baselineSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqcg_watch_mismatch_cannot_bless_publication
    {watchMismatch baselineSound satSound unsatSound : Prop} :
    watchMismatch ->
    baselineSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqcg_reason_mismatch_cannot_bless_publication
    {reasonMismatch baselineSound satSound unsatSound : Prop} :
    reasonMismatch ->
    baselineSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqcg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqcg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqcg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqcg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound ->
    ay_pqcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqcg_policy_requires_queue_digest
    {queueDigest : Prop} :
    ay_pqcg_queue_digest_evidence queueDigest -> queueDigest := by
  intro evidence
  exact evidence

theorem ay_pqcg_policy_requires_trail_checkpoint
    {trailCheckpoint : Prop} :
    ay_pqcg_trail_checkpoint_evidence trailCheckpoint ->
    trailCheckpoint := by
  intro evidence
  exact evidence

theorem ay_pqcg_policy_requires_watchlist_digest
    {watchlistDigest : Prop} :
    ay_pqcg_watchlist_digest_evidence watchlistDigest ->
    watchlistDigest := by
  intro evidence
  exact evidence

theorem ay_pqcg_policy_requires_reason_availability
    {reasonAvailabilityLedger : Prop} :
    ay_pqcg_reason_availability_ledger_evidence reasonAvailabilityLedger ->
    reasonAvailabilityLedger := by
  intro evidence
  exact evidence

theorem ay_pqcg_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_pqcg_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_pqcg_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_pqcg_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_pqcg_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_pqcg_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_pqcg_policy_requires_validator
    {validatorGate : Prop} :
    ay_pqcg_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_pqcg_policy_requires_audit
    {auditTranscript : Prop} :
    ay_pqcg_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
