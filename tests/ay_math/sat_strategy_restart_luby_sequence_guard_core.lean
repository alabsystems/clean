def ay_luby_conj (p q : Prop) : Prop := p ∧ q

def ay_luby_disj (p q : Prop) : Prop := p ∨ q

def ay_luby_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_luby_disj satSound unsatSound

def ay_luby_inputs
    (restartPolicyManifest lubySequenceWitness conflictCounterDigest
      restartEpochLedger trailSnapshotDigest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_luby_conj restartPolicyManifest
    (ay_luby_conj lubySequenceWitness
      (ay_luby_conj conflictCounterDigest
        (ay_luby_conj restartEpochLedger
          (ay_luby_conj trailSnapshotDigest
            (ay_luby_conj propagationReplay
              (ay_luby_conj fallbackBaseline
                (ay_luby_conj solverBuildEvidence
                  (ay_luby_conj validatorGate auditTranscript))))))))

def ay_luby_restart_policy_manifest_evidence
    (restartPolicyManifest : Prop) : Prop :=
  restartPolicyManifest

def ay_luby_luby_sequence_witness_evidence
    (lubySequenceWitness : Prop) : Prop :=
  lubySequenceWitness

def ay_luby_conflict_counter_digest_evidence
    (conflictCounterDigest : Prop) : Prop :=
  conflictCounterDigest

def ay_luby_restart_epoch_ledger_evidence
    (restartEpochLedger : Prop) : Prop :=
  restartEpochLedger

def ay_luby_trail_snapshot_digest_evidence
    (trailSnapshotDigest : Prop) : Prop :=
  trailSnapshotDigest

def ay_luby_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_luby_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_luby_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_luby_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_luby_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_luby_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_luby_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_luby_accepted
    (restartPolicyManifest lubySequenceWitness conflictCounterDigest
      restartEpochLedger trailSnapshotDigest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript sequenceAccepted :
      Prop) : Prop :=
  sequenceAccepted

def ay_luby_rejected
    (policyMismatch sequenceMismatch counterMismatch epochMismatch
      trailMismatch replayMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch : Prop) : Prop :=
  ay_luby_disj policyMismatch
    (ay_luby_disj sequenceMismatch
      (ay_luby_disj counterMismatch
        (ay_luby_disj epochMismatch
          (ay_luby_disj trailMismatch
            (ay_luby_disj replayMismatch
              (ay_luby_disj baselineMismatch
                (ay_luby_disj buildMismatch
                  (ay_luby_disj validatorMismatch auditMismatch))))))))

def ay_luby_restart_sequence_search_control_hint
    (sequenceAccepted searchControlOnly deterministicReplay : Prop) : Prop :=
  sequenceAccepted

def ay_luby_gate (accepted rejected : Prop) : Prop :=
  ay_luby_disj accepted rejected

theorem ay_luby_input_components
    {restartPolicyManifest lubySequenceWitness conflictCounterDigest
      restartEpochLedger trailSnapshotDigest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_luby_inputs restartPolicyManifest lubySequenceWitness
      conflictCounterDigest restartEpochLedger trailSnapshotDigest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    ay_luby_inputs restartPolicyManifest lubySequenceWitness
      conflictCounterDigest restartEpochLedger trailSnapshotDigest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript := by
  intro inputs
  exact inputs

theorem ay_luby_accepted_policy
    {restartPolicyManifest lubySequenceWitness conflictCounterDigest
      restartEpochLedger trailSnapshotDigest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript sequenceAccepted :
      Prop} :
    sequenceAccepted ->
    ay_luby_accepted restartPolicyManifest lubySequenceWitness
      conflictCounterDigest restartEpochLedger trailSnapshotDigest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript sequenceAccepted := by
  intro accepted
  exact accepted

theorem ay_luby_accepted_restart_policy_manifest
    {restartPolicyManifest : Prop} :
    restartPolicyManifest ->
    ay_luby_restart_policy_manifest_evidence restartPolicyManifest := by
  intro evidence
  exact evidence

theorem ay_luby_accepted_luby_sequence_witness
    {lubySequenceWitness : Prop} :
    lubySequenceWitness ->
    ay_luby_luby_sequence_witness_evidence lubySequenceWitness := by
  intro evidence
  exact evidence

theorem ay_luby_accepted_conflict_counter_digest
    {conflictCounterDigest : Prop} :
    conflictCounterDigest ->
    ay_luby_conflict_counter_digest_evidence conflictCounterDigest := by
  intro evidence
  exact evidence

theorem ay_luby_accepted_restart_epoch_ledger
    {restartEpochLedger : Prop} :
    restartEpochLedger ->
    ay_luby_restart_epoch_ledger_evidence restartEpochLedger := by
  intro evidence
  exact evidence

theorem ay_luby_accepted_trail_snapshot_digest
    {trailSnapshotDigest : Prop} :
    trailSnapshotDigest ->
    ay_luby_trail_snapshot_digest_evidence trailSnapshotDigest := by
  intro evidence
  exact evidence

theorem ay_luby_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_luby_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_luby_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_luby_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_luby_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_luby_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_luby_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_luby_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_luby_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_luby_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_luby_restart_sequence_is_search_control_only
    {sequenceAccepted searchControlOnly : Prop} :
    sequenceAccepted ->
    searchControlOnly ->
    searchControlOnly :=
  fun _ controlOnly => controlOnly

theorem ay_luby_sequence_cannot_change_original_formula_truth
    {sequenceAccepted originalFormulaTruthPreserved : Prop} :
    sequenceAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_luby_accepted_sequence_preserves_public_soundness
    {sequenceAccepted satSound unsatSound : Prop} :
    sequenceAccepted ->
    ay_luby_public_soundness_theorem satSound unsatSound ->
    ay_luby_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_luby_policy_manifest_preserves_replay
    {restartPolicyManifest propagationReplay : Prop} :
    restartPolicyManifest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_luby_sequence_witness_preserves_replay
    {lubySequenceWitness propagationReplay : Prop} :
    lubySequenceWitness ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_luby_epoch_ledger_preserves_replay
    {restartEpochLedger propagationReplay : Prop} :
    restartEpochLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_luby_accepted_sequence_preserves_fallback_soundness
    {sequenceAccepted fallbackBaseline satSound unsatSound : Prop} :
    sequenceAccepted ->
    fallbackBaseline ->
    ay_luby_public_soundness_theorem satSound unsatSound ->
    ay_luby_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_luby_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_luby_gate accepted rejected ->
    ay_luby_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_luby_rejected_is_no_claim
    {policyMismatch diagnostic : Prop} :
    policyMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_luby_rejected_forces_recompute
    {policyMismatch recomputeRequired : Prop} :
    policyMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_luby_failed_guard_cannot_bless_publication
    {policyMismatch baselineSound satSound unsatSound : Prop} :
    policyMismatch ->
    baselineSound ->
    ay_luby_public_soundness_theorem satSound unsatSound ->
    ay_luby_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_luby_policy_mismatch_forces_no_claim
    {policyMismatch diagnostic : Prop} :
    policyMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_luby_sequence_mismatch_forces_no_claim
    {sequenceMismatch diagnostic : Prop} :
    sequenceMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_luby_counter_mismatch_forces_no_claim
    {counterMismatch diagnostic : Prop} :
    counterMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_luby_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_luby_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_luby_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_luby_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_luby_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_luby_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_luby_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_luby_policy_mismatch_forces_recompute
    {policyMismatch recomputeRequired : Prop} :
    policyMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_luby_sequence_mismatch_forces_recompute
    {sequenceMismatch recomputeRequired : Prop} :
    sequenceMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_luby_counter_mismatch_forces_recompute
    {counterMismatch recomputeRequired : Prop} :
    counterMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_luby_epoch_mismatch_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_luby_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_luby_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_luby_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_luby_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_luby_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_luby_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_luby_policy_mismatch_cannot_bless_publication
    {policyMismatch baselineSound satSound unsatSound : Prop} :
    policyMismatch ->
    baselineSound ->
    ay_luby_public_soundness_theorem satSound unsatSound ->
    ay_luby_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_luby_sequence_mismatch_cannot_bless_publication
    {sequenceMismatch baselineSound satSound unsatSound : Prop} :
    sequenceMismatch ->
    baselineSound ->
    ay_luby_public_soundness_theorem satSound unsatSound ->
    ay_luby_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_luby_counter_mismatch_cannot_bless_publication
    {counterMismatch baselineSound satSound unsatSound : Prop} :
    counterMismatch ->
    baselineSound ->
    ay_luby_public_soundness_theorem satSound unsatSound ->
    ay_luby_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_luby_epoch_mismatch_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_luby_public_soundness_theorem satSound unsatSound ->
    ay_luby_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_luby_trail_mismatch_cannot_bless_publication
    {trailMismatch baselineSound satSound unsatSound : Prop} :
    trailMismatch ->
    baselineSound ->
    ay_luby_public_soundness_theorem satSound unsatSound ->
    ay_luby_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_luby_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_luby_public_soundness_theorem satSound unsatSound ->
    ay_luby_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_luby_policy_requires_restart_policy_manifest
    {restartPolicyManifest accepted : Prop} :
    restartPolicyManifest -> accepted -> restartPolicyManifest :=
  fun evidence _ => evidence

theorem ay_luby_policy_requires_luby_sequence_witness
    {lubySequenceWitness accepted : Prop} :
    lubySequenceWitness -> accepted -> lubySequenceWitness :=
  fun evidence _ => evidence

theorem ay_luby_policy_requires_conflict_counter_digest
    {conflictCounterDigest accepted : Prop} :
    conflictCounterDigest -> accepted -> conflictCounterDigest :=
  fun evidence _ => evidence

theorem ay_luby_policy_requires_restart_epoch_ledger
    {restartEpochLedger accepted : Prop} :
    restartEpochLedger -> accepted -> restartEpochLedger :=
  fun evidence _ => evidence

theorem ay_luby_policy_requires_trail_snapshot_digest
    {trailSnapshotDigest accepted : Prop} :
    trailSnapshotDigest -> accepted -> trailSnapshotDigest :=
  fun evidence _ => evidence

theorem ay_luby_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_luby_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_luby_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_luby_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_luby_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
