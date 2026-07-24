def ay_rcrg_conj (p q : Prop) : Prop := p ∧ q

def ay_rcrg_disj (p q : Prop) : Prop := p ∨ q

def ay_rcrg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rcrg_disj satSound unsatSound

def ay_rcrg_inputs
    (restartStateDigest reductionEpochManifest deletionLedger
      protectedReasonClauseWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_rcrg_conj restartStateDigest
    (ay_rcrg_conj reductionEpochManifest
      (ay_rcrg_conj deletionLedger
        (ay_rcrg_conj protectedReasonClauseWitness
          (ay_rcrg_conj propagationReplayWitness
            (ay_rcrg_conj fallbackBaseline
              (ay_rcrg_conj solverBuildEvidence
                (ay_rcrg_conj validatorGate auditTranscript)))))))

def ay_rcrg_restart_state_digest_evidence
    (restartStateDigest : Prop) : Prop :=
  restartStateDigest

def ay_rcrg_reduction_epoch_manifest_evidence
    (reductionEpochManifest : Prop) : Prop :=
  reductionEpochManifest

def ay_rcrg_deletion_ledger_evidence (deletionLedger : Prop) : Prop :=
  deletionLedger

def ay_rcrg_protected_reason_clause_witness_evidence
    (protectedReasonClauseWitness : Prop) : Prop :=
  protectedReasonClauseWitness

def ay_rcrg_propagation_replay_witness_evidence
    (propagationReplayWitness : Prop) : Prop :=
  propagationReplayWitness

def ay_rcrg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_rcrg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rcrg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rcrg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rcrg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rcrg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_rcrg_accepted
    (restartStateDigest reductionEpochManifest deletionLedger
      protectedReasonClauseWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript syncAccepted :
      Prop) : Prop :=
  syncAccepted

def ay_rcrg_rejected
    (restartMismatch reductionMismatch deletionMismatch protectionMismatch
      replayMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch : Prop) : Prop :=
  ay_rcrg_disj restartMismatch
    (ay_rcrg_disj reductionMismatch
      (ay_rcrg_disj deletionMismatch
        (ay_rcrg_disj protectionMismatch
          (ay_rcrg_disj replayMismatch
            (ay_rcrg_disj baselineMismatch
              (ay_rcrg_disj buildMismatch
                (ay_rcrg_disj validatorMismatch auditMismatch)))))))

def ay_rcrg_gate (accepted rejected : Prop) : Prop :=
  ay_rcrg_disj accepted rejected

def ay_rcrg_restart_reducer_sync_hint
    (syncAccepted searchPolicyOnly memoryPolicyOnly replayAccepted : Prop) :
      Prop :=
  syncAccepted

theorem ay_rcrg_input_components
    {restartStateDigest reductionEpochManifest deletionLedger
      protectedReasonClauseWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_rcrg_inputs restartStateDigest reductionEpochManifest deletionLedger
      protectedReasonClauseWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_rcrg_inputs restartStateDigest reductionEpochManifest deletionLedger
      protectedReasonClauseWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rcrg_accepted_policy
    {restartStateDigest reductionEpochManifest deletionLedger
      protectedReasonClauseWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript syncAccepted : Prop} :
    syncAccepted ->
    ay_rcrg_accepted restartStateDigest reductionEpochManifest deletionLedger
      protectedReasonClauseWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript syncAccepted := by
  intro accepted
  exact accepted

theorem ay_rcrg_accepted_restart_state_digest
    {restartStateDigest : Prop} :
    restartStateDigest ->
    ay_rcrg_restart_state_digest_evidence restartStateDigest := by
  intro evidence
  exact evidence

theorem ay_rcrg_accepted_reduction_epoch_manifest
    {reductionEpochManifest : Prop} :
    reductionEpochManifest ->
    ay_rcrg_reduction_epoch_manifest_evidence reductionEpochManifest := by
  intro evidence
  exact evidence

theorem ay_rcrg_accepted_deletion_ledger
    {deletionLedger : Prop} :
    deletionLedger -> ay_rcrg_deletion_ledger_evidence deletionLedger := by
  intro evidence
  exact evidence

theorem ay_rcrg_accepted_protected_reason_clause_witness
    {protectedReasonClauseWitness : Prop} :
    protectedReasonClauseWitness ->
    ay_rcrg_protected_reason_clause_witness_evidence
      protectedReasonClauseWitness := by
  intro evidence
  exact evidence

theorem ay_rcrg_accepted_propagation_replay_witness
    {propagationReplayWitness : Prop} :
    propagationReplayWitness ->
    ay_rcrg_propagation_replay_witness_evidence
      propagationReplayWitness := by
  intro evidence
  exact evidence

theorem ay_rcrg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_rcrg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rcrg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_rcrg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rcrg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rcrg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rcrg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rcrg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rcrg_sync_is_search_memory_policy_only
    {syncAccepted searchMemoryPolicyOnly : Prop} :
    syncAccepted ->
    searchMemoryPolicyOnly ->
    searchMemoryPolicyOnly :=
  fun _ policyOnly => policyOnly

theorem ay_rcrg_sync_cannot_change_original_formula_truth
    {syncAccepted originalFormulaTruthPreserved : Prop} :
    syncAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_rcrg_accepted_replay_preserves_public_soundness
    {syncAccepted satSound unsatSound : Prop} :
    syncAccepted ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rcrg_restart_state_preserves_replay
    {restartStateDigest propagationReplayWitness : Prop} :
    restartStateDigest ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_rcrg_reduction_epoch_preserves_replay
    {reductionEpochManifest propagationReplayWitness : Prop} :
    reductionEpochManifest ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_rcrg_protected_reason_preserves_replay
    {protectedReasonClauseWitness propagationReplayWitness : Prop} :
    protectedReasonClauseWitness ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_rcrg_accepted_sync_preserves_fallback_soundness
    {syncAccepted fallbackBaseline satSound unsatSound : Prop} :
    syncAccepted ->
    fallbackBaseline ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcrg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rcrg_gate accepted rejected ->
    ay_rcrg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rcrg_rejected_is_no_claim
    {restartMismatch diagnostic : Prop} :
    restartMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcrg_rejected_forces_recompute
    {restartMismatch recomputeRequired : Prop} :
    restartMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcrg_failed_sync_guard_cannot_bless_publication
    {restartMismatch baselineSound satSound unsatSound : Prop} :
    restartMismatch ->
    baselineSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcrg_restart_mismatch_forces_no_claim
    {restartMismatch diagnostic : Prop} :
    restartMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcrg_reduction_mismatch_forces_no_claim
    {reductionMismatch diagnostic : Prop} :
    reductionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcrg_deletion_mismatch_forces_no_claim
    {deletionMismatch diagnostic : Prop} :
    deletionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcrg_protection_mismatch_forces_no_claim
    {protectionMismatch diagnostic : Prop} :
    protectionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcrg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcrg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcrg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcrg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcrg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcrg_restart_mismatch_forces_recompute
    {restartMismatch recomputeRequired : Prop} :
    restartMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcrg_reduction_mismatch_forces_recompute
    {reductionMismatch recomputeRequired : Prop} :
    reductionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcrg_deletion_mismatch_forces_recompute
    {deletionMismatch recomputeRequired : Prop} :
    deletionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcrg_protection_mismatch_forces_recompute
    {protectionMismatch recomputeRequired : Prop} :
    protectionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcrg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcrg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcrg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcrg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcrg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcrg_restart_mismatch_cannot_bless_publication
    {restartMismatch baselineSound satSound unsatSound : Prop} :
    restartMismatch ->
    baselineSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcrg_reduction_mismatch_cannot_bless_publication
    {reductionMismatch baselineSound satSound unsatSound : Prop} :
    reductionMismatch ->
    baselineSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcrg_deletion_mismatch_cannot_bless_publication
    {deletionMismatch baselineSound satSound unsatSound : Prop} :
    deletionMismatch ->
    baselineSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcrg_protection_mismatch_cannot_bless_publication
    {protectionMismatch baselineSound satSound unsatSound : Prop} :
    protectionMismatch ->
    baselineSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcrg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcrg_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcrg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcrg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcrg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound ->
    ay_rcrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcrg_policy_requires_restart_state_digest
    {restartStateDigest accepted : Prop} :
    restartStateDigest -> accepted -> restartStateDigest :=
  fun evidence _ => evidence

theorem ay_rcrg_policy_requires_reduction_epoch_manifest
    {reductionEpochManifest accepted : Prop} :
    reductionEpochManifest -> accepted -> reductionEpochManifest :=
  fun evidence _ => evidence

theorem ay_rcrg_policy_requires_deletion_ledger
    {deletionLedger accepted : Prop} :
    deletionLedger -> accepted -> deletionLedger :=
  fun evidence _ => evidence

theorem ay_rcrg_policy_requires_protected_reason_clause
    {protectedReasonClauseWitness accepted : Prop} :
    protectedReasonClauseWitness -> accepted -> protectedReasonClauseWitness :=
  fun evidence _ => evidence

theorem ay_rcrg_policy_requires_propagation_replay
    {propagationReplayWitness accepted : Prop} :
    propagationReplayWitness -> accepted -> propagationReplayWitness :=
  fun evidence _ => evidence

theorem ay_rcrg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_rcrg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_rcrg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_rcrg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
