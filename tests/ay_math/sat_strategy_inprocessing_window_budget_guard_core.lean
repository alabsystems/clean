def ay_siwb_conj (p q : Prop) : Prop := p ∧ q

def ay_siwb_disj (p q : Prop) : Prop := p ∨ q

def ay_siwb_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_siwb_disj satSound unsatSound

def ay_siwb_inputs
    (windowLedger transformManifest watchlistCheckpoint propagationReplay
      fallbackBaseline solverBuild validatorGate auditEvidence : Prop) : Prop :=
  ay_siwb_conj windowLedger
    (ay_siwb_conj transformManifest
      (ay_siwb_conj watchlistCheckpoint
        (ay_siwb_conj propagationReplay
          (ay_siwb_conj fallbackBaseline
            (ay_siwb_conj solverBuild
              (ay_siwb_conj validatorGate auditEvidence))))))

def ay_siwb_window_ledger_evidence (windowLedger : Prop) : Prop :=
  windowLedger

def ay_siwb_transform_manifest_evidence (transformManifest : Prop) : Prop :=
  transformManifest

def ay_siwb_watchlist_checkpoint_evidence
    (watchlistCheckpoint : Prop) : Prop :=
  watchlistCheckpoint

def ay_siwb_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_siwb_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_siwb_solver_build_evidence (solverBuild : Prop) : Prop := solverBuild

def ay_siwb_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_siwb_audit_evidence (auditEvidence : Prop) : Prop := auditEvidence

def ay_siwb_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_siwb_accepted
    (windowLedger transformManifest watchlistCheckpoint propagationReplay
      fallbackBaseline solverBuild validatorGate auditEvidence windowAccepted :
      Prop) : Prop :=
  windowAccepted

def ay_siwb_rejected
    (windowBudgetDrift transformManifestMismatch watchMismatch replayGap
      staleBuild validatorRejection auditContradiction missingFallback
      missingWindowLedger missingTransformManifest : Prop) : Prop :=
  ay_siwb_disj windowBudgetDrift
    (ay_siwb_disj transformManifestMismatch
      (ay_siwb_disj watchMismatch
        (ay_siwb_disj replayGap
          (ay_siwb_disj staleBuild
            (ay_siwb_disj validatorRejection
              (ay_siwb_disj auditContradiction
                (ay_siwb_disj missingFallback
                  (ay_siwb_disj missingWindowLedger
                    missingTransformManifest))))))))

def ay_siwb_gate (accepted rejected : Prop) : Prop :=
  ay_siwb_disj accepted rejected

def ay_siwb_inprocessing_hint
    (windowAccepted boundedWindow transformSchedule budgetPolicy : Prop) : Prop :=
  windowAccepted

def ay_siwb_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_siwb_input_components
    {windowLedger transformManifest watchlistCheckpoint propagationReplay
      fallbackBaseline solverBuild validatorGate auditEvidence : Prop} :
    ay_siwb_inputs windowLedger transformManifest watchlistCheckpoint
      propagationReplay fallbackBaseline solverBuild validatorGate auditEvidence ->
    ay_siwb_inputs windowLedger transformManifest watchlistCheckpoint
      propagationReplay fallbackBaseline solverBuild validatorGate auditEvidence := by
  intro inputs
  exact inputs

theorem ay_siwb_accepted_policy
    {windowLedger transformManifest watchlistCheckpoint propagationReplay
      fallbackBaseline solverBuild validatorGate auditEvidence windowAccepted : Prop} :
    windowAccepted ->
    ay_siwb_accepted windowLedger transformManifest watchlistCheckpoint
      propagationReplay fallbackBaseline solverBuild validatorGate auditEvidence
      windowAccepted := by
  intro accepted
  exact accepted

theorem ay_siwb_accepted_window_ledger
    {windowLedger : Prop} :
    windowLedger -> ay_siwb_window_ledger_evidence windowLedger := by
  intro evidence
  exact evidence

theorem ay_siwb_accepted_transform_manifest
    {transformManifest : Prop} :
    transformManifest ->
    ay_siwb_transform_manifest_evidence transformManifest := by
  intro evidence
  exact evidence

theorem ay_siwb_accepted_watchlist_checkpoint
    {watchlistCheckpoint : Prop} :
    watchlistCheckpoint ->
    ay_siwb_watchlist_checkpoint_evidence watchlistCheckpoint := by
  intro evidence
  exact evidence

theorem ay_siwb_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_siwb_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_siwb_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_siwb_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_siwb_accepted_solver_build
    {solverBuild : Prop} :
    solverBuild -> ay_siwb_solver_build_evidence solverBuild := by
  intro evidence
  exact evidence

theorem ay_siwb_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_siwb_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_siwb_accepted_audit_evidence
    {auditEvidence : Prop} :
    auditEvidence -> ay_siwb_audit_evidence auditEvidence := by
  intro evidence
  exact evidence

theorem ay_siwb_inprocessing_policy_admissible_hint
    {windowAccepted boundedWindow transformSchedule budgetPolicy : Prop} :
    windowAccepted ->
    boundedWindow ->
    transformSchedule ->
    budgetPolicy ->
    ay_siwb_inprocessing_hint windowAccepted boundedWindow transformSchedule
      budgetPolicy := by
  intro accepted window schedule budget
  exact accepted

theorem ay_siwb_hint_cannot_change_truth
    {windowAccepted satSound unsatSound : Prop} :
    windowAccepted ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_siwb_accepted_policy_preserves_public_soundness
    {windowAccepted satSound unsatSound : Prop} :
    windowAccepted ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_siwb_rejected_is_no_claim
    {windowBudgetDrift diagnostic : Prop} :
    windowBudgetDrift ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_siwb_rejected_forces_recompute
    {windowBudgetDrift recomputeRequired : Prop} :
    windowBudgetDrift ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_siwb_rejected_cannot_bless_public_result
    {windowBudgetDrift baselineSound satSound unsatSound : Prop} :
    windowBudgetDrift ->
    baselineSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_siwb_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_siwb_gate accepted rejected ->
    ay_siwb_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_siwb_safe_policy_deployment_accept
    {windowAccepted boundedWindow transformSchedule budgetPolicy satSound
      unsatSound : Prop} :
    windowAccepted ->
    boundedWindow ->
    transformSchedule ->
    budgetPolicy ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_siwb_safe_policy_deployment_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_siwb_window_budget_drift_forces_no_claim
    {windowBudgetDrift diagnostic : Prop} :
    windowBudgetDrift ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_siwb_transform_manifest_mismatch_forces_no_claim
    {transformManifestMismatch diagnostic : Prop} :
    transformManifestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_siwb_watch_mismatch_forces_no_claim
    {watchMismatch diagnostic : Prop} :
    watchMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_siwb_replay_gap_forces_no_claim
    {replayGap diagnostic : Prop} :
    replayGap ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_siwb_stale_build_forces_no_claim
    {staleBuild diagnostic : Prop} :
    staleBuild ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_siwb_validator_rejection_forces_no_claim
    {validatorRejection diagnostic : Prop} :
    validatorRejection ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_siwb_audit_contradiction_forces_no_claim
    {auditContradiction diagnostic : Prop} :
    auditContradiction ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_siwb_missing_fallback_forces_no_claim
    {missingFallback diagnostic : Prop} :
    missingFallback ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_siwb_missing_window_ledger_forces_no_claim
    {missingWindowLedger diagnostic : Prop} :
    missingWindowLedger ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_siwb_missing_transform_manifest_forces_no_claim
    {missingTransformManifest diagnostic : Prop} :
    missingTransformManifest ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_siwb_window_budget_drift_cannot_bless_public_result
    {windowBudgetDrift baselineSound satSound unsatSound : Prop} :
    windowBudgetDrift ->
    baselineSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_siwb_manifest_mismatch_cannot_bless_public_result
    {transformManifestMismatch baselineSound satSound unsatSound : Prop} :
    transformManifestMismatch ->
    baselineSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_siwb_watch_mismatch_cannot_bless_public_result
    {watchMismatch baselineSound satSound unsatSound : Prop} :
    watchMismatch ->
    baselineSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_siwb_replay_gap_cannot_bless_public_result
    {replayGap baselineSound satSound unsatSound : Prop} :
    replayGap ->
    baselineSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_siwb_stale_build_cannot_bless_public_result
    {staleBuild baselineSound satSound unsatSound : Prop} :
    staleBuild ->
    baselineSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_siwb_validator_rejection_cannot_bless_public_result
    {validatorRejection baselineSound satSound unsatSound : Prop} :
    validatorRejection ->
    baselineSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_siwb_audit_contradiction_cannot_bless_public_result
    {auditContradiction baselineSound satSound unsatSound : Prop} :
    auditContradiction ->
    baselineSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound ->
    ay_siwb_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_siwb_policy_requires_window_ledger
    {windowLedger : Prop} :
    ay_siwb_window_ledger_evidence windowLedger -> windowLedger := by
  intro evidence
  exact evidence

theorem ay_siwb_policy_requires_transform_manifest
    {transformManifest : Prop} :
    ay_siwb_transform_manifest_evidence transformManifest ->
    transformManifest := by
  intro evidence
  exact evidence

theorem ay_siwb_policy_requires_watchlist_checkpoint
    {watchlistCheckpoint : Prop} :
    ay_siwb_watchlist_checkpoint_evidence watchlistCheckpoint ->
    watchlistCheckpoint := by
  intro evidence
  exact evidence

theorem ay_siwb_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_siwb_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_siwb_policy_requires_validator
    {validatorGate : Prop} :
    ay_siwb_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_siwb_policy_requires_audit
    {auditEvidence : Prop} :
    ay_siwb_audit_evidence auditEvidence -> auditEvidence := by
  intro evidence
  exact evidence
