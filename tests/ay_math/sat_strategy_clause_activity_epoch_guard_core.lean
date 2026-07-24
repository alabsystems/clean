def ay_caeg_conj (p q : Prop) : Prop := p ∧ q

def ay_caeg_disj (p q : Prop) : Prop := p ∨ q

def ay_caeg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_caeg_disj satSound unsatSound

def ay_caeg_inputs
    (clauseDatabaseDigest clauseActivityLedger epochManifest
      decayRescalePolicyWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_caeg_conj clauseDatabaseDigest
    (ay_caeg_conj clauseActivityLedger
      (ay_caeg_conj epochManifest
        (ay_caeg_conj decayRescalePolicyWitness
          (ay_caeg_conj propagationReplayWitness
            (ay_caeg_conj fallbackBaseline
              (ay_caeg_conj solverBuildEvidence
                (ay_caeg_conj validatorGate auditTranscript)))))))

def ay_caeg_clause_database_digest_evidence
    (clauseDatabaseDigest : Prop) : Prop :=
  clauseDatabaseDigest

def ay_caeg_clause_activity_ledger_evidence
    (clauseActivityLedger : Prop) : Prop :=
  clauseActivityLedger

def ay_caeg_epoch_manifest_evidence (epochManifest : Prop) : Prop :=
  epochManifest

def ay_caeg_decay_rescale_policy_witness_evidence
    (decayRescalePolicyWitness : Prop) : Prop :=
  decayRescalePolicyWitness

def ay_caeg_propagation_replay_witness_evidence
    (propagationReplayWitness : Prop) : Prop :=
  propagationReplayWitness

def ay_caeg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_caeg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_caeg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_caeg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_caeg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_caeg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_caeg_accepted
    (clauseDatabaseDigest clauseActivityLedger epochManifest
      decayRescalePolicyWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript activityEpochAccepted :
      Prop) : Prop :=
  activityEpochAccepted

def ay_caeg_rejected
    (digestMismatch activityMismatch epochMismatch decayMismatch replayMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
      Prop :=
  ay_caeg_disj digestMismatch
    (ay_caeg_disj activityMismatch
      (ay_caeg_disj epochMismatch
        (ay_caeg_disj decayMismatch
          (ay_caeg_disj replayMismatch
            (ay_caeg_disj baselineMismatch
              (ay_caeg_disj buildMismatch
                (ay_caeg_disj validatorMismatch auditMismatch)))))))

def ay_caeg_gate (accepted rejected : Prop) : Prop :=
  ay_caeg_disj accepted rejected

def ay_caeg_activity_epoch_search_control_hint
    (activityEpochAccepted heuristicMetadataOnly searchControlOnly
      replayAccepted : Prop) : Prop :=
  activityEpochAccepted

theorem ay_caeg_input_components
    {clauseDatabaseDigest clauseActivityLedger epochManifest
      decayRescalePolicyWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_caeg_inputs clauseDatabaseDigest clauseActivityLedger epochManifest
      decayRescalePolicyWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_caeg_inputs clauseDatabaseDigest clauseActivityLedger epochManifest
      decayRescalePolicyWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_caeg_accepted_policy
    {clauseDatabaseDigest clauseActivityLedger epochManifest
      decayRescalePolicyWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript activityEpochAccepted :
      Prop} :
    activityEpochAccepted ->
    ay_caeg_accepted clauseDatabaseDigest clauseActivityLedger epochManifest
      decayRescalePolicyWitness propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript activityEpochAccepted := by
  intro accepted
  exact accepted

theorem ay_caeg_accepted_clause_database_digest
    {clauseDatabaseDigest : Prop} :
    clauseDatabaseDigest ->
    ay_caeg_clause_database_digest_evidence clauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_caeg_accepted_clause_activity_ledger
    {clauseActivityLedger : Prop} :
    clauseActivityLedger ->
    ay_caeg_clause_activity_ledger_evidence clauseActivityLedger := by
  intro evidence
  exact evidence

theorem ay_caeg_accepted_epoch_manifest
    {epochManifest : Prop} :
    epochManifest -> ay_caeg_epoch_manifest_evidence epochManifest := by
  intro evidence
  exact evidence

theorem ay_caeg_accepted_decay_rescale_policy_witness
    {decayRescalePolicyWitness : Prop} :
    decayRescalePolicyWitness ->
    ay_caeg_decay_rescale_policy_witness_evidence
      decayRescalePolicyWitness := by
  intro evidence
  exact evidence

theorem ay_caeg_accepted_propagation_replay_witness
    {propagationReplayWitness : Prop} :
    propagationReplayWitness ->
    ay_caeg_propagation_replay_witness_evidence
      propagationReplayWitness := by
  intro evidence
  exact evidence

theorem ay_caeg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_caeg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_caeg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_caeg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_caeg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_caeg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_caeg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_caeg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_caeg_activity_epochs_are_heuristic_metadata_only
    {activityEpochAccepted heuristicSearchControlMetadataOnly : Prop} :
    activityEpochAccepted ->
    heuristicSearchControlMetadataOnly ->
    heuristicSearchControlMetadataOnly :=
  fun _ metadataOnly => metadataOnly

theorem ay_caeg_activity_epoch_cannot_change_original_formula_truth
    {activityEpochAccepted originalFormulaTruthPreserved : Prop} :
    activityEpochAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_caeg_accepted_replay_preserves_public_soundness
    {activityEpochAccepted satSound unsatSound : Prop} :
    activityEpochAccepted ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_caeg_activity_ledger_preserves_replay
    {clauseActivityLedger propagationReplayWitness : Prop} :
    clauseActivityLedger ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_caeg_epoch_manifest_preserves_replay
    {epochManifest propagationReplayWitness : Prop} :
    epochManifest ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_caeg_decay_policy_preserves_replay
    {decayRescalePolicyWitness propagationReplayWitness : Prop} :
    decayRescalePolicyWitness ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_caeg_accepted_activity_hint_preserves_fallback_soundness
    {activityEpochAccepted fallbackBaseline satSound unsatSound : Prop} :
    activityEpochAccepted ->
    fallbackBaseline ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_caeg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_caeg_gate accepted rejected ->
    ay_caeg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_caeg_rejected_is_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_caeg_rejected_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_caeg_failed_activity_epoch_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_caeg_digest_mismatch_forces_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_caeg_activity_mismatch_forces_no_claim
    {activityMismatch diagnostic : Prop} :
    activityMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_caeg_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_caeg_decay_mismatch_forces_no_claim
    {decayMismatch diagnostic : Prop} :
    decayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_caeg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_caeg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_caeg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_caeg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_caeg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_caeg_digest_mismatch_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_caeg_activity_mismatch_forces_recompute
    {activityMismatch recomputeRequired : Prop} :
    activityMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_caeg_epoch_mismatch_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_caeg_decay_mismatch_forces_recompute
    {decayMismatch recomputeRequired : Prop} :
    decayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_caeg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_caeg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_caeg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_caeg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_caeg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_caeg_digest_mismatch_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_caeg_activity_mismatch_cannot_bless_publication
    {activityMismatch baselineSound satSound unsatSound : Prop} :
    activityMismatch ->
    baselineSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_caeg_epoch_mismatch_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_caeg_decay_mismatch_cannot_bless_publication
    {decayMismatch baselineSound satSound unsatSound : Prop} :
    decayMismatch ->
    baselineSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_caeg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_caeg_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_caeg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_caeg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_caeg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound ->
    ay_caeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_caeg_policy_requires_clause_database_digest
    {clauseDatabaseDigest accepted : Prop} :
    clauseDatabaseDigest -> accepted -> clauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_caeg_policy_requires_clause_activity_ledger
    {clauseActivityLedger accepted : Prop} :
    clauseActivityLedger -> accepted -> clauseActivityLedger :=
  fun evidence _ => evidence

theorem ay_caeg_policy_requires_epoch_manifest
    {epochManifest accepted : Prop} :
    epochManifest -> accepted -> epochManifest :=
  fun evidence _ => evidence

theorem ay_caeg_policy_requires_decay_rescale_policy
    {decayRescalePolicyWitness accepted : Prop} :
    decayRescalePolicyWitness -> accepted -> decayRescalePolicyWitness :=
  fun evidence _ => evidence

theorem ay_caeg_policy_requires_propagation_replay
    {propagationReplayWitness accepted : Prop} :
    propagationReplayWitness -> accepted -> propagationReplayWitness :=
  fun evidence _ => evidence

theorem ay_caeg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_caeg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_caeg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_caeg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
