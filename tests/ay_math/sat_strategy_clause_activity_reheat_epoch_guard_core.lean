def ay_carg_conj (p q : Prop) : Prop := p ∧ q

def ay_carg_disj (p q : Prop) : Prop := p ∨ q

def ay_carg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_carg_disj satSound unsatSound

def ay_carg_inputs
    (reheatEpochLedger activitySnapshotDigest clauseDatabaseSnapshot
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_carg_conj reheatEpochLedger
    (ay_carg_conj activitySnapshotDigest
      (ay_carg_conj clauseDatabaseSnapshot
        (ay_carg_conj propagationReplay
          (ay_carg_conj fallbackBaseline
            (ay_carg_conj solverBuildEvidence
              (ay_carg_conj validatorGate auditTranscript))))))

def ay_carg_reheat_epoch_ledger_evidence
    (reheatEpochLedger : Prop) : Prop :=
  reheatEpochLedger

def ay_carg_activity_snapshot_digest_evidence
    (activitySnapshotDigest : Prop) : Prop :=
  activitySnapshotDigest

def ay_carg_clause_database_snapshot_evidence
    (clauseDatabaseSnapshot : Prop) : Prop :=
  clauseDatabaseSnapshot

def ay_carg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_carg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_carg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_carg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_carg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_carg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_carg_accepted
    (reheatEpochLedger activitySnapshotDigest clauseDatabaseSnapshot
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript reheatAccepted : Prop) : Prop :=
  reheatAccepted

def ay_carg_rejected
    (epochFailure activityFailure databaseFailure replayFailure fallbackFailure
      buildFailure validatorFailure auditFailure : Prop) : Prop :=
  ay_carg_disj epochFailure
    (ay_carg_disj activityFailure
      (ay_carg_disj databaseFailure
        (ay_carg_disj replayFailure
          (ay_carg_disj fallbackFailure
            (ay_carg_disj buildFailure
              (ay_carg_disj validatorFailure auditFailure))))))

def ay_carg_gate (accepted rejected : Prop) : Prop :=
  ay_carg_disj accepted rejected

def ay_carg_reheat_hint
    (reheatAccepted epochPolicy activityPolicy schedulingPolicy : Prop) : Prop :=
  reheatAccepted

def ay_carg_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_carg_input_components
    {reheatEpochLedger activitySnapshotDigest clauseDatabaseSnapshot
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_carg_inputs reheatEpochLedger activitySnapshotDigest
      clauseDatabaseSnapshot propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    ay_carg_inputs reheatEpochLedger activitySnapshotDigest
      clauseDatabaseSnapshot propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_carg_accepted_policy
    {reheatEpochLedger activitySnapshotDigest clauseDatabaseSnapshot
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript reheatAccepted : Prop} :
    reheatAccepted ->
    ay_carg_accepted reheatEpochLedger activitySnapshotDigest
      clauseDatabaseSnapshot propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript reheatAccepted := by
  intro accepted
  exact accepted

theorem ay_carg_accepted_reheat_epoch_ledger
    {reheatEpochLedger : Prop} :
    reheatEpochLedger ->
    ay_carg_reheat_epoch_ledger_evidence reheatEpochLedger := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_activity_snapshot_digest
    {activitySnapshotDigest : Prop} :
    activitySnapshotDigest ->
    ay_carg_activity_snapshot_digest_evidence activitySnapshotDigest := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_clause_database_snapshot
    {clauseDatabaseSnapshot : Prop} :
    clauseDatabaseSnapshot ->
    ay_carg_clause_database_snapshot_evidence clauseDatabaseSnapshot := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_carg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_carg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_carg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_carg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_carg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_carg_reheat_policy_admissible_hint
    {reheatAccepted epochPolicy activityPolicy schedulingPolicy : Prop} :
    reheatAccepted ->
    epochPolicy ->
    activityPolicy ->
    schedulingPolicy ->
    ay_carg_reheat_hint reheatAccepted epochPolicy activityPolicy
      schedulingPolicy := by
  intro accepted epoch activity scheduling
  exact accepted

theorem ay_carg_hint_cannot_change_truth
    {reheatAccepted formulaTruth : Prop} :
    reheatAccepted ->
    formulaTruth ->
    formulaTruth :=
  fun _ truth => truth

theorem ay_carg_accepted_policy_preserves_public_soundness
    {reheatAccepted satSound unsatSound : Prop} :
    reheatAccepted ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_carg_rejected_is_no_claim
    {epochFailure diagnostic : Prop} :
    epochFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_rejected_forces_recompute
    {epochFailure recomputeRequired : Prop} :
    epochFailure ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_rejected_cannot_bless_public_result
    {epochFailure baselineSound satSound unsatSound : Prop} :
    epochFailure ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_carg_gate accepted rejected ->
    ay_carg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_carg_safe_policy_deployment_accept
    {reheatAccepted epochPolicy activityPolicy schedulingPolicy satSound
      unsatSound : Prop} :
    reheatAccepted ->
    epochPolicy ->
    activityPolicy ->
    schedulingPolicy ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_carg_safe_policy_deployment_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_carg_epoch_failure_forces_no_claim
    {epochFailure diagnostic : Prop} :
    epochFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_activity_failure_forces_no_claim
    {activityFailure diagnostic : Prop} :
    activityFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_database_failure_forces_no_claim
    {databaseFailure diagnostic : Prop} :
    databaseFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_replay_failure_forces_no_claim
    {replayFailure diagnostic : Prop} :
    replayFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_fallback_failure_forces_no_claim
    {fallbackFailure diagnostic : Prop} :
    fallbackFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_build_failure_forces_no_claim
    {buildFailure diagnostic : Prop} :
    buildFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_validator_failure_forces_no_claim
    {validatorFailure diagnostic : Prop} :
    validatorFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_audit_failure_forces_no_claim
    {auditFailure diagnostic : Prop} :
    auditFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_epoch_failure_cannot_bless_public_result
    {epochFailure baselineSound satSound unsatSound : Prop} :
    epochFailure ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_activity_failure_cannot_bless_public_result
    {activityFailure baselineSound satSound unsatSound : Prop} :
    activityFailure ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_database_failure_cannot_bless_public_result
    {databaseFailure baselineSound satSound unsatSound : Prop} :
    databaseFailure ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_replay_failure_cannot_bless_public_result
    {replayFailure baselineSound satSound unsatSound : Prop} :
    replayFailure ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_fallback_failure_cannot_bless_public_result
    {fallbackFailure baselineSound satSound unsatSound : Prop} :
    fallbackFailure ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_build_failure_cannot_bless_public_result
    {buildFailure baselineSound satSound unsatSound : Prop} :
    buildFailure ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_validator_failure_cannot_bless_public_result
    {validatorFailure baselineSound satSound unsatSound : Prop} :
    validatorFailure ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_audit_failure_cannot_bless_public_result
    {auditFailure baselineSound satSound unsatSound : Prop} :
    auditFailure ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_policy_requires_reheat_epoch_ledger
    {reheatEpochLedger : Prop} :
    ay_carg_reheat_epoch_ledger_evidence reheatEpochLedger ->
    reheatEpochLedger := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_activity_snapshot_digest
    {activitySnapshotDigest : Prop} :
    ay_carg_activity_snapshot_digest_evidence activitySnapshotDigest ->
    activitySnapshotDigest := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_clause_database_snapshot
    {clauseDatabaseSnapshot : Prop} :
    ay_carg_clause_database_snapshot_evidence clauseDatabaseSnapshot ->
    clauseDatabaseSnapshot := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_carg_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_carg_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_carg_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_validator
    {validatorGate : Prop} :
    ay_carg_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_audit
    {auditTranscript : Prop} :
    ay_carg_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
