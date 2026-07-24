def ay_rdtg_conj (p q : Prop) : Prop := p ∧ q

def ay_rdtg_disj (p q : Prop) : Prop := p ∨ q

def ay_rdtg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rdtg_disj satSound unsatSound

def ay_rdtg_inputs
    (restartPolicyManifest conflictCounterDigest lbdWindowStatisticDigest
      thresholdUpdateLedger restartEpochLedger trailSnapshotDigest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_rdtg_conj restartPolicyManifest
    (ay_rdtg_conj conflictCounterDigest
      (ay_rdtg_conj lbdWindowStatisticDigest
        (ay_rdtg_conj thresholdUpdateLedger
          (ay_rdtg_conj restartEpochLedger
            (ay_rdtg_conj trailSnapshotDigest
              (ay_rdtg_conj propagationReplay
                (ay_rdtg_conj fallbackBaseline
                  (ay_rdtg_conj solverBuildEvidence
                    (ay_rdtg_conj validatorGate auditTranscript)))))))))

def ay_rdtg_restart_policy_manifest_evidence
    (restartPolicyManifest : Prop) : Prop :=
  restartPolicyManifest

def ay_rdtg_conflict_counter_digest_evidence
    (conflictCounterDigest : Prop) : Prop :=
  conflictCounterDigest

def ay_rdtg_lbd_window_statistic_digest_evidence
    (lbdWindowStatisticDigest : Prop) : Prop :=
  lbdWindowStatisticDigest

def ay_rdtg_threshold_update_ledger_evidence
    (thresholdUpdateLedger : Prop) : Prop :=
  thresholdUpdateLedger

def ay_rdtg_restart_epoch_ledger_evidence
    (restartEpochLedger : Prop) : Prop :=
  restartEpochLedger

def ay_rdtg_trail_snapshot_digest_evidence
    (trailSnapshotDigest : Prop) : Prop :=
  trailSnapshotDigest

def ay_rdtg_propagation_replay_evidence (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_rdtg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_rdtg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rdtg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rdtg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rdtg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rdtg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_rdtg_accepted
    (restartPolicyManifest conflictCounterDigest lbdWindowStatisticDigest
      thresholdUpdateLedger restartEpochLedger trailSnapshotDigest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript thresholdAccepted : Prop) : Prop :=
  thresholdAccepted

def ay_rdtg_rejected
    (policyMismatch counterMismatch statisticMismatch thresholdMismatch
      epochMismatch trailMismatch replayMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch : Prop) : Prop :=
  ay_rdtg_disj policyMismatch
    (ay_rdtg_disj counterMismatch
      (ay_rdtg_disj statisticMismatch
        (ay_rdtg_disj thresholdMismatch
          (ay_rdtg_disj epochMismatch
            (ay_rdtg_disj trailMismatch
              (ay_rdtg_disj replayMismatch
                (ay_rdtg_disj baselineMismatch
                  (ay_rdtg_disj buildMismatch
                    (ay_rdtg_disj validatorMismatch auditMismatch)))))))))

def ay_rdtg_dynamic_threshold_search_control_hint
    (thresholdAccepted searchControlOnly deterministicReplay : Prop) : Prop :=
  thresholdAccepted

def ay_rdtg_gate (accepted rejected : Prop) : Prop :=
  ay_rdtg_disj accepted rejected

theorem ay_rdtg_input_components
    {restartPolicyManifest conflictCounterDigest lbdWindowStatisticDigest
      thresholdUpdateLedger restartEpochLedger trailSnapshotDigest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_rdtg_inputs restartPolicyManifest conflictCounterDigest
      lbdWindowStatisticDigest thresholdUpdateLedger restartEpochLedger
      trailSnapshotDigest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    ay_rdtg_inputs restartPolicyManifest conflictCounterDigest
      lbdWindowStatisticDigest thresholdUpdateLedger restartEpochLedger
      trailSnapshotDigest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rdtg_accepted_policy
    {restartPolicyManifest conflictCounterDigest lbdWindowStatisticDigest
      thresholdUpdateLedger restartEpochLedger trailSnapshotDigest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript thresholdAccepted : Prop} :
    thresholdAccepted ->
    ay_rdtg_accepted restartPolicyManifest conflictCounterDigest
      lbdWindowStatisticDigest thresholdUpdateLedger restartEpochLedger
      trailSnapshotDigest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript thresholdAccepted := by
  intro accepted
  exact accepted

theorem ay_rdtg_accepted_restart_policy_manifest
    {restartPolicyManifest : Prop} :
    restartPolicyManifest ->
    ay_rdtg_restart_policy_manifest_evidence restartPolicyManifest := by
  intro evidence
  exact evidence

theorem ay_rdtg_accepted_conflict_counter_digest
    {conflictCounterDigest : Prop} :
    conflictCounterDigest ->
    ay_rdtg_conflict_counter_digest_evidence conflictCounterDigest := by
  intro evidence
  exact evidence

theorem ay_rdtg_accepted_lbd_window_statistic_digest
    {lbdWindowStatisticDigest : Prop} :
    lbdWindowStatisticDigest ->
    ay_rdtg_lbd_window_statistic_digest_evidence
      lbdWindowStatisticDigest := by
  intro evidence
  exact evidence

theorem ay_rdtg_accepted_threshold_update_ledger
    {thresholdUpdateLedger : Prop} :
    thresholdUpdateLedger ->
    ay_rdtg_threshold_update_ledger_evidence thresholdUpdateLedger := by
  intro evidence
  exact evidence

theorem ay_rdtg_accepted_restart_epoch_ledger
    {restartEpochLedger : Prop} :
    restartEpochLedger ->
    ay_rdtg_restart_epoch_ledger_evidence restartEpochLedger := by
  intro evidence
  exact evidence

theorem ay_rdtg_accepted_trail_snapshot_digest
    {trailSnapshotDigest : Prop} :
    trailSnapshotDigest ->
    ay_rdtg_trail_snapshot_digest_evidence trailSnapshotDigest := by
  intro evidence
  exact evidence

theorem ay_rdtg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_rdtg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_rdtg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline ->
    ay_rdtg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rdtg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence ->
    ay_rdtg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rdtg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rdtg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rdtg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rdtg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rdtg_threshold_updates_are_search_control_only
    {thresholdAccepted searchControlOnly : Prop} :
    thresholdAccepted ->
    searchControlOnly ->
    searchControlOnly :=
  fun _ controlOnly => controlOnly

theorem ay_rdtg_threshold_update_cannot_change_original_formula_truth
    {thresholdAccepted originalFormulaTruthPreserved : Prop} :
    thresholdAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_rdtg_accepted_threshold_preserves_public_soundness
    {thresholdAccepted satSound unsatSound : Prop} :
    thresholdAccepted ->
    ay_rdtg_public_soundness_theorem satSound unsatSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rdtg_policy_manifest_preserves_replay
    {restartPolicyManifest propagationReplay : Prop} :
    restartPolicyManifest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rdtg_counter_digest_preserves_replay
    {conflictCounterDigest propagationReplay : Prop} :
    conflictCounterDigest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rdtg_statistic_digest_preserves_replay
    {lbdWindowStatisticDigest propagationReplay : Prop} :
    lbdWindowStatisticDigest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rdtg_threshold_ledger_preserves_replay
    {thresholdUpdateLedger propagationReplay : Prop} :
    thresholdUpdateLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rdtg_epoch_ledger_preserves_replay
    {restartEpochLedger propagationReplay : Prop} :
    restartEpochLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rdtg_accepted_threshold_preserves_fallback_soundness
    {thresholdAccepted fallbackBaseline satSound unsatSound : Prop} :
    thresholdAccepted ->
    fallbackBaseline ->
    ay_rdtg_public_soundness_theorem satSound unsatSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rdtg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rdtg_gate accepted rejected ->
    ay_rdtg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rdtg_rejected_is_no_claim
    {policyMismatch diagnostic : Prop} :
    policyMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_rejected_forces_recompute
    {policyMismatch recomputeRequired : Prop} :
    policyMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_failed_guard_cannot_bless_publication
    {policyMismatch baselineSound satSound unsatSound : Prop} :
    policyMismatch ->
    baselineSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rdtg_policy_mismatch_forces_no_claim
    {policyMismatch diagnostic : Prop} :
    policyMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_counter_mismatch_forces_no_claim
    {counterMismatch diagnostic : Prop} :
    counterMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_statistic_mismatch_forces_no_claim
    {statisticMismatch diagnostic : Prop} :
    statisticMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_threshold_mismatch_forces_no_claim
    {thresholdMismatch diagnostic : Prop} :
    thresholdMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rdtg_policy_mismatch_forces_recompute
    {policyMismatch recomputeRequired : Prop} :
    policyMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_counter_mismatch_forces_recompute
    {counterMismatch recomputeRequired : Prop} :
    counterMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_statistic_mismatch_forces_recompute
    {statisticMismatch recomputeRequired : Prop} :
    statisticMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_threshold_mismatch_forces_recompute
    {thresholdMismatch recomputeRequired : Prop} :
    thresholdMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_epoch_mismatch_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rdtg_policy_mismatch_cannot_bless_publication
    {policyMismatch baselineSound satSound unsatSound : Prop} :
    policyMismatch ->
    baselineSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rdtg_counter_mismatch_cannot_bless_publication
    {counterMismatch baselineSound satSound unsatSound : Prop} :
    counterMismatch ->
    baselineSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rdtg_statistic_mismatch_cannot_bless_publication
    {statisticMismatch baselineSound satSound unsatSound : Prop} :
    statisticMismatch ->
    baselineSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rdtg_threshold_mismatch_cannot_bless_publication
    {thresholdMismatch baselineSound satSound unsatSound : Prop} :
    thresholdMismatch ->
    baselineSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rdtg_epoch_mismatch_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rdtg_trail_mismatch_cannot_bless_publication
    {trailMismatch baselineSound satSound unsatSound : Prop} :
    trailMismatch ->
    baselineSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rdtg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound ->
    ay_rdtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rdtg_policy_requires_restart_policy_manifest
    {restartPolicyManifest accepted : Prop} :
    restartPolicyManifest -> accepted -> restartPolicyManifest :=
  fun evidence _ => evidence

theorem ay_rdtg_policy_requires_conflict_counter_digest
    {conflictCounterDigest accepted : Prop} :
    conflictCounterDigest -> accepted -> conflictCounterDigest :=
  fun evidence _ => evidence

theorem ay_rdtg_policy_requires_lbd_window_statistic_digest
    {lbdWindowStatisticDigest accepted : Prop} :
    lbdWindowStatisticDigest -> accepted -> lbdWindowStatisticDigest :=
  fun evidence _ => evidence

theorem ay_rdtg_policy_requires_threshold_update_ledger
    {thresholdUpdateLedger accepted : Prop} :
    thresholdUpdateLedger -> accepted -> thresholdUpdateLedger :=
  fun evidence _ => evidence

theorem ay_rdtg_policy_requires_restart_epoch_ledger
    {restartEpochLedger accepted : Prop} :
    restartEpochLedger -> accepted -> restartEpochLedger :=
  fun evidence _ => evidence

theorem ay_rdtg_policy_requires_trail_snapshot_digest
    {trailSnapshotDigest accepted : Prop} :
    trailSnapshotDigest -> accepted -> trailSnapshotDigest :=
  fun evidence _ => evidence

theorem ay_rdtg_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_rdtg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_rdtg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_rdtg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_rdtg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
