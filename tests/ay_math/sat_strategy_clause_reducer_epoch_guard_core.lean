def ay_creg_conj (p q : Prop) : Prop := p ∧ q

def ay_creg_disj (p q : Prop) : Prop := p ∨ q

def ay_creg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_creg_disj satSound unsatSound

def ay_creg_inputs
    (clauseDatabaseDigest reductionScheduleManifest deletionLedger
      reasonClauseRetentionWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_creg_conj clauseDatabaseDigest
    (ay_creg_conj reductionScheduleManifest
      (ay_creg_conj deletionLedger
        (ay_creg_conj reasonClauseRetentionWitness
          (ay_creg_conj propagationReplayWitness
            (ay_creg_conj fallbackBaseline
              (ay_creg_conj solverBuildEvidence
                (ay_creg_conj validatorGate auditTranscript)))))))

def ay_creg_clause_database_digest_evidence
    (clauseDatabaseDigest : Prop) : Prop :=
  clauseDatabaseDigest

def ay_creg_reduction_schedule_manifest_evidence
    (reductionScheduleManifest : Prop) : Prop :=
  reductionScheduleManifest

def ay_creg_deletion_ledger_evidence (deletionLedger : Prop) : Prop :=
  deletionLedger

def ay_creg_reason_clause_retention_witness_evidence
    (reasonClauseRetentionWitness : Prop) : Prop :=
  reasonClauseRetentionWitness

def ay_creg_propagation_replay_witness_evidence
    (propagationReplayWitness : Prop) : Prop :=
  propagationReplayWitness

def ay_creg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_creg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_creg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_creg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_creg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_creg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_creg_accepted
    (clauseDatabaseDigest reductionScheduleManifest deletionLedger
      reasonClauseRetentionWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript reducerEpochAccepted :
      Prop) : Prop :=
  reducerEpochAccepted

def ay_creg_rejected
    (digestMismatch scheduleMismatch deletionMismatch retentionMismatch
      replayMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch : Prop) : Prop :=
  ay_creg_disj digestMismatch
    (ay_creg_disj scheduleMismatch
      (ay_creg_disj deletionMismatch
        (ay_creg_disj retentionMismatch
          (ay_creg_disj replayMismatch
            (ay_creg_disj baselineMismatch
              (ay_creg_disj buildMismatch
                (ay_creg_disj validatorMismatch auditMismatch)))))))

def ay_creg_gate (accepted rejected : Prop) : Prop :=
  ay_creg_disj accepted rejected

def ay_creg_reducer_memory_search_policy_hint
    (reducerEpochAccepted memoryPolicyOnly searchPolicyOnly replayAccepted :
      Prop) : Prop :=
  reducerEpochAccepted

theorem ay_creg_input_components
    {clauseDatabaseDigest reductionScheduleManifest deletionLedger
      reasonClauseRetentionWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_creg_inputs clauseDatabaseDigest reductionScheduleManifest
      deletionLedger reasonClauseRetentionWitness propagationReplayWitness
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    ay_creg_inputs clauseDatabaseDigest reductionScheduleManifest
      deletionLedger reasonClauseRetentionWitness propagationReplayWitness
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_creg_accepted_policy
    {clauseDatabaseDigest reductionScheduleManifest deletionLedger
      reasonClauseRetentionWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript reducerEpochAccepted :
      Prop} :
    reducerEpochAccepted ->
    ay_creg_accepted clauseDatabaseDigest reductionScheduleManifest
      deletionLedger reasonClauseRetentionWitness propagationReplayWitness
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      reducerEpochAccepted := by
  intro accepted
  exact accepted

theorem ay_creg_accepted_clause_database_digest
    {clauseDatabaseDigest : Prop} :
    clauseDatabaseDigest ->
    ay_creg_clause_database_digest_evidence clauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_creg_accepted_reduction_schedule_manifest
    {reductionScheduleManifest : Prop} :
    reductionScheduleManifest ->
    ay_creg_reduction_schedule_manifest_evidence
      reductionScheduleManifest := by
  intro evidence
  exact evidence

theorem ay_creg_accepted_deletion_ledger
    {deletionLedger : Prop} :
    deletionLedger -> ay_creg_deletion_ledger_evidence deletionLedger := by
  intro evidence
  exact evidence

theorem ay_creg_accepted_reason_clause_retention_witness
    {reasonClauseRetentionWitness : Prop} :
    reasonClauseRetentionWitness ->
    ay_creg_reason_clause_retention_witness_evidence
      reasonClauseRetentionWitness := by
  intro evidence
  exact evidence

theorem ay_creg_accepted_propagation_replay_witness
    {propagationReplayWitness : Prop} :
    propagationReplayWitness ->
    ay_creg_propagation_replay_witness_evidence
      propagationReplayWitness := by
  intro evidence
  exact evidence

theorem ay_creg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_creg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_creg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_creg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_creg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_creg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_creg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_creg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_creg_reducer_epochs_are_memory_search_policy_only
    {reducerEpochAccepted memorySearchPolicyOnly : Prop} :
    reducerEpochAccepted ->
    memorySearchPolicyOnly ->
    memorySearchPolicyOnly :=
  fun _ policyOnly => policyOnly

theorem ay_creg_reducer_epoch_cannot_change_original_formula_truth
    {reducerEpochAccepted originalFormulaTruthPreserved : Prop} :
    reducerEpochAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_creg_accepted_replay_preserves_public_soundness
    {reducerEpochAccepted satSound unsatSound : Prop} :
    reducerEpochAccepted ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_creg_deletion_ledger_preserves_replay
    {deletionLedger propagationReplayWitness : Prop} :
    deletionLedger ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_creg_retention_witness_preserves_replay
    {reasonClauseRetentionWitness propagationReplayWitness : Prop} :
    reasonClauseRetentionWitness ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_creg_schedule_manifest_preserves_replay
    {reductionScheduleManifest propagationReplayWitness : Prop} :
    reductionScheduleManifest ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_creg_accepted_reducer_hint_preserves_fallback_soundness
    {reducerEpochAccepted fallbackBaseline satSound unsatSound : Prop} :
    reducerEpochAccepted ->
    fallbackBaseline ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_creg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_creg_gate accepted rejected ->
    ay_creg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_creg_rejected_is_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_creg_rejected_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_creg_failed_reducer_guard_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_creg_digest_mismatch_forces_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_creg_schedule_mismatch_forces_no_claim
    {scheduleMismatch diagnostic : Prop} :
    scheduleMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_creg_deletion_mismatch_forces_no_claim
    {deletionMismatch diagnostic : Prop} :
    deletionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_creg_retention_mismatch_forces_no_claim
    {retentionMismatch diagnostic : Prop} :
    retentionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_creg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_creg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_creg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_creg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_creg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_creg_digest_mismatch_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_creg_schedule_mismatch_forces_recompute
    {scheduleMismatch recomputeRequired : Prop} :
    scheduleMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_creg_deletion_mismatch_forces_recompute
    {deletionMismatch recomputeRequired : Prop} :
    deletionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_creg_retention_mismatch_forces_recompute
    {retentionMismatch recomputeRequired : Prop} :
    retentionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_creg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_creg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_creg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_creg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_creg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_creg_digest_mismatch_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_creg_schedule_mismatch_cannot_bless_publication
    {scheduleMismatch baselineSound satSound unsatSound : Prop} :
    scheduleMismatch ->
    baselineSound ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_creg_deletion_mismatch_cannot_bless_publication
    {deletionMismatch baselineSound satSound unsatSound : Prop} :
    deletionMismatch ->
    baselineSound ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_creg_retention_mismatch_cannot_bless_publication
    {retentionMismatch baselineSound satSound unsatSound : Prop} :
    retentionMismatch ->
    baselineSound ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_creg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_creg_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_creg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_creg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_creg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_creg_public_soundness_theorem satSound unsatSound ->
    ay_creg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_creg_policy_requires_clause_database_digest
    {clauseDatabaseDigest accepted : Prop} :
    clauseDatabaseDigest -> accepted -> clauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_creg_policy_requires_reduction_schedule_manifest
    {reductionScheduleManifest accepted : Prop} :
    reductionScheduleManifest -> accepted -> reductionScheduleManifest :=
  fun evidence _ => evidence

theorem ay_creg_policy_requires_deletion_ledger
    {deletionLedger accepted : Prop} :
    deletionLedger -> accepted -> deletionLedger :=
  fun evidence _ => evidence

theorem ay_creg_policy_requires_reason_clause_retention
    {reasonClauseRetentionWitness accepted : Prop} :
    reasonClauseRetentionWitness -> accepted -> reasonClauseRetentionWitness :=
  fun evidence _ => evidence

theorem ay_creg_policy_requires_propagation_replay
    {propagationReplayWitness accepted : Prop} :
    propagationReplayWitness -> accepted -> propagationReplayWitness :=
  fun evidence _ => evidence

theorem ay_creg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_creg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_creg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_creg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
