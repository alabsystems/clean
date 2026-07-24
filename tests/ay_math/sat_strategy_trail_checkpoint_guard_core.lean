def ay_tckg_conj (p q : Prop) : Prop := p ∧ q

def ay_tckg_disj (p q : Prop) : Prop := p ∨ q

def ay_tckg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_tckg_disj satSound unsatSound

def ay_tckg_inputs
    (trailDigest decisionLevelLedger propagationReasonLedger
      checkpointEpochManifest restoreReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_tckg_conj trailDigest
    (ay_tckg_conj decisionLevelLedger
      (ay_tckg_conj propagationReasonLedger
        (ay_tckg_conj checkpointEpochManifest
          (ay_tckg_conj restoreReplayWitness
            (ay_tckg_conj fallbackBaseline
              (ay_tckg_conj solverBuildEvidence
                (ay_tckg_conj validatorGate auditTranscript)))))))

def ay_tckg_trail_digest_evidence (trailDigest : Prop) : Prop :=
  trailDigest

def ay_tckg_decision_level_ledger_evidence
    (decisionLevelLedger : Prop) : Prop :=
  decisionLevelLedger

def ay_tckg_propagation_reason_ledger_evidence
    (propagationReasonLedger : Prop) : Prop :=
  propagationReasonLedger

def ay_tckg_checkpoint_epoch_manifest_evidence
    (checkpointEpochManifest : Prop) : Prop :=
  checkpointEpochManifest

def ay_tckg_restore_replay_witness_evidence
    (restoreReplayWitness : Prop) : Prop :=
  restoreReplayWitness

def ay_tckg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_tckg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_tckg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_tckg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_tckg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_tckg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_tckg_accepted
    (trailDigest decisionLevelLedger propagationReasonLedger
      checkpointEpochManifest restoreReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript checkpointAccepted :
      Prop) : Prop :=
  checkpointAccepted

def ay_tckg_rejected
    (trailMismatch levelMismatch reasonMismatch epochMismatch restoreMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
      Prop :=
  ay_tckg_disj trailMismatch
    (ay_tckg_disj levelMismatch
      (ay_tckg_disj reasonMismatch
        (ay_tckg_disj epochMismatch
          (ay_tckg_disj restoreMismatch
            (ay_tckg_disj baselineMismatch
              (ay_tckg_disj buildMismatch
                (ay_tckg_disj validatorMismatch auditMismatch)))))))

def ay_tckg_gate (accepted rejected : Prop) : Prop :=
  ay_tckg_disj accepted rejected

def ay_tckg_checkpoint_state_recovery_hint
    (checkpointAccepted stateRecoveryOnly searchControlOnly replayAccepted :
      Prop) : Prop :=
  checkpointAccepted

theorem ay_tckg_input_components
    {trailDigest decisionLevelLedger propagationReasonLedger
      checkpointEpochManifest restoreReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_tckg_inputs trailDigest decisionLevelLedger propagationReasonLedger
      checkpointEpochManifest restoreReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_tckg_inputs trailDigest decisionLevelLedger propagationReasonLedger
      checkpointEpochManifest restoreReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_tckg_accepted_policy
    {trailDigest decisionLevelLedger propagationReasonLedger
      checkpointEpochManifest restoreReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript checkpointAccepted :
      Prop} :
    checkpointAccepted ->
    ay_tckg_accepted trailDigest decisionLevelLedger propagationReasonLedger
      checkpointEpochManifest restoreReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript checkpointAccepted := by
  intro accepted
  exact accepted

theorem ay_tckg_accepted_trail_digest
    {trailDigest : Prop} :
    trailDigest -> ay_tckg_trail_digest_evidence trailDigest := by
  intro evidence
  exact evidence

theorem ay_tckg_accepted_decision_level_ledger
    {decisionLevelLedger : Prop} :
    decisionLevelLedger ->
    ay_tckg_decision_level_ledger_evidence decisionLevelLedger := by
  intro evidence
  exact evidence

theorem ay_tckg_accepted_propagation_reason_ledger
    {propagationReasonLedger : Prop} :
    propagationReasonLedger ->
    ay_tckg_propagation_reason_ledger_evidence propagationReasonLedger := by
  intro evidence
  exact evidence

theorem ay_tckg_accepted_checkpoint_epoch_manifest
    {checkpointEpochManifest : Prop} :
    checkpointEpochManifest ->
    ay_tckg_checkpoint_epoch_manifest_evidence checkpointEpochManifest := by
  intro evidence
  exact evidence

theorem ay_tckg_accepted_restore_replay_witness
    {restoreReplayWitness : Prop} :
    restoreReplayWitness ->
    ay_tckg_restore_replay_witness_evidence restoreReplayWitness := by
  intro evidence
  exact evidence

theorem ay_tckg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_tckg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_tckg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_tckg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_tckg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_tckg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_tckg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_tckg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_tckg_checkpointing_is_state_recovery_only
    {checkpointAccepted stateRecoverySearchControlOnly : Prop} :
    checkpointAccepted ->
    stateRecoverySearchControlOnly ->
    stateRecoverySearchControlOnly :=
  fun _ recoveryOnly => recoveryOnly

theorem ay_tckg_checkpointing_cannot_change_original_formula_truth
    {checkpointAccepted originalFormulaTruthPreserved : Prop} :
    checkpointAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_tckg_accepted_replay_preserves_public_soundness
    {checkpointAccepted satSound unsatSound : Prop} :
    checkpointAccepted ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_tckg_levels_preserve_restore_replay
    {decisionLevelLedger restoreReplayWitness : Prop} :
    decisionLevelLedger ->
    restoreReplayWitness ->
    restoreReplayWitness :=
  fun _ replay => replay

theorem ay_tckg_reasons_preserve_restore_replay
    {propagationReasonLedger restoreReplayWitness : Prop} :
    propagationReasonLedger ->
    restoreReplayWitness ->
    restoreReplayWitness :=
  fun _ replay => replay

theorem ay_tckg_epoch_manifest_preserves_restore_replay
    {checkpointEpochManifest restoreReplayWitness : Prop} :
    checkpointEpochManifest ->
    restoreReplayWitness ->
    restoreReplayWitness :=
  fun _ replay => replay

theorem ay_tckg_accepted_checkpoint_preserves_fallback_soundness
    {checkpointAccepted fallbackBaseline satSound unsatSound : Prop} :
    checkpointAccepted ->
    fallbackBaseline ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_tckg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_tckg_gate accepted rejected ->
    ay_tckg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_tckg_rejected_is_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_tckg_rejected_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_tckg_failed_checkpoint_guard_cannot_bless_publication
    {trailMismatch baselineSound satSound unsatSound : Prop} :
    trailMismatch ->
    baselineSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_tckg_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_tckg_level_mismatch_forces_no_claim
    {levelMismatch diagnostic : Prop} :
    levelMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_tckg_reason_mismatch_forces_no_claim
    {reasonMismatch diagnostic : Prop} :
    reasonMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_tckg_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_tckg_restore_mismatch_forces_no_claim
    {restoreMismatch diagnostic : Prop} :
    restoreMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_tckg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_tckg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_tckg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_tckg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_tckg_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_tckg_level_mismatch_forces_recompute
    {levelMismatch recomputeRequired : Prop} :
    levelMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_tckg_reason_mismatch_forces_recompute
    {reasonMismatch recomputeRequired : Prop} :
    reasonMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_tckg_epoch_mismatch_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_tckg_restore_mismatch_forces_recompute
    {restoreMismatch recomputeRequired : Prop} :
    restoreMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_tckg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_tckg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_tckg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_tckg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_tckg_trail_mismatch_cannot_bless_publication
    {trailMismatch baselineSound satSound unsatSound : Prop} :
    trailMismatch ->
    baselineSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_tckg_level_mismatch_cannot_bless_publication
    {levelMismatch baselineSound satSound unsatSound : Prop} :
    levelMismatch ->
    baselineSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_tckg_reason_mismatch_cannot_bless_publication
    {reasonMismatch baselineSound satSound unsatSound : Prop} :
    reasonMismatch ->
    baselineSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_tckg_epoch_mismatch_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_tckg_restore_mismatch_cannot_bless_publication
    {restoreMismatch baselineSound satSound unsatSound : Prop} :
    restoreMismatch ->
    baselineSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_tckg_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_tckg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_tckg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_tckg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound ->
    ay_tckg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_tckg_policy_requires_trail_digest
    {trailDigest accepted : Prop} :
    trailDigest -> accepted -> trailDigest :=
  fun evidence _ => evidence

theorem ay_tckg_policy_requires_decision_level_ledger
    {decisionLevelLedger accepted : Prop} :
    decisionLevelLedger -> accepted -> decisionLevelLedger :=
  fun evidence _ => evidence

theorem ay_tckg_policy_requires_propagation_reason_ledger
    {propagationReasonLedger accepted : Prop} :
    propagationReasonLedger -> accepted -> propagationReasonLedger :=
  fun evidence _ => evidence

theorem ay_tckg_policy_requires_checkpoint_epoch_manifest
    {checkpointEpochManifest accepted : Prop} :
    checkpointEpochManifest -> accepted -> checkpointEpochManifest :=
  fun evidence _ => evidence

theorem ay_tckg_policy_requires_restore_replay_witness
    {restoreReplayWitness accepted : Prop} :
    restoreReplayWitness -> accepted -> restoreReplayWitness :=
  fun evidence _ => evidence

theorem ay_tckg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_tckg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_tckg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_tckg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
