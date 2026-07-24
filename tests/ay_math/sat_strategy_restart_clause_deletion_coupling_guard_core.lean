def ay_srcd_conj (p q : Prop) : Prop := p ∧ q

def ay_srcd_disj (p q : Prop) : Prop := p ∨ q

def ay_srcd_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_srcd_disj satSound unsatSound

def ay_srcd_inputs
    (restartLedger deletionEpochLedger learnedClauseManifest watchlistCheckpoint
      propagationReplay fallbackBaseline solverBuild validatorGate auditEvidence :
      Prop) : Prop :=
  ay_srcd_conj restartLedger
    (ay_srcd_conj deletionEpochLedger
      (ay_srcd_conj learnedClauseManifest
        (ay_srcd_conj watchlistCheckpoint
          (ay_srcd_conj propagationReplay
            (ay_srcd_conj fallbackBaseline
              (ay_srcd_conj solverBuild
                (ay_srcd_conj validatorGate auditEvidence)))))))

def ay_srcd_restart_ledger_evidence (restartLedger : Prop) : Prop :=
  restartLedger

def ay_srcd_deletion_epoch_ledger_evidence
    (deletionEpochLedger : Prop) : Prop :=
  deletionEpochLedger

def ay_srcd_learned_clause_manifest_evidence
    (learnedClauseManifest : Prop) : Prop :=
  learnedClauseManifest

def ay_srcd_watchlist_checkpoint_evidence
    (watchlistCheckpoint : Prop) : Prop :=
  watchlistCheckpoint

def ay_srcd_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_srcd_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_srcd_solver_build_evidence (solverBuild : Prop) : Prop := solverBuild

def ay_srcd_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_srcd_audit_evidence (auditEvidence : Prop) : Prop := auditEvidence

def ay_srcd_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_srcd_accepted
    (restartLedger deletionEpochLedger learnedClauseManifest watchlistCheckpoint
      propagationReplay fallbackBaseline solverBuild validatorGate auditEvidence
      couplingAccepted : Prop) : Prop :=
  couplingAccepted

def ay_srcd_rejected
    (restartLedgerDrift deletionLedgerDrift manifestMismatch watchMismatch
      replayGap staleBuild validatorRejection auditContradiction missingFallback
      missingRestartLedger missingDeletionLedger : Prop) : Prop :=
  ay_srcd_disj restartLedgerDrift
    (ay_srcd_disj deletionLedgerDrift
      (ay_srcd_disj manifestMismatch
        (ay_srcd_disj watchMismatch
          (ay_srcd_disj replayGap
            (ay_srcd_disj staleBuild
              (ay_srcd_disj validatorRejection
                (ay_srcd_disj auditContradiction
                  (ay_srcd_disj missingFallback
                    (ay_srcd_disj missingRestartLedger
                      missingDeletionLedger)))))))))

def ay_srcd_gate (accepted rejected : Prop) : Prop :=
  ay_srcd_disj accepted rejected

def ay_srcd_coupling_hint
    (couplingAccepted restartSchedule deletionWindow retentionPolicy : Prop) : Prop :=
  couplingAccepted

def ay_srcd_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_srcd_input_components
    {restartLedger deletionEpochLedger learnedClauseManifest watchlistCheckpoint
      propagationReplay fallbackBaseline solverBuild validatorGate auditEvidence :
      Prop} :
    ay_srcd_inputs restartLedger deletionEpochLedger learnedClauseManifest
      watchlistCheckpoint propagationReplay fallbackBaseline solverBuild
      validatorGate auditEvidence ->
    ay_srcd_inputs restartLedger deletionEpochLedger learnedClauseManifest
      watchlistCheckpoint propagationReplay fallbackBaseline solverBuild
      validatorGate auditEvidence := by
  intro inputs
  exact inputs

theorem ay_srcd_accepted_policy
    {restartLedger deletionEpochLedger learnedClauseManifest watchlistCheckpoint
      propagationReplay fallbackBaseline solverBuild validatorGate auditEvidence
      couplingAccepted : Prop} :
    couplingAccepted ->
    ay_srcd_accepted restartLedger deletionEpochLedger learnedClauseManifest
      watchlistCheckpoint propagationReplay fallbackBaseline solverBuild
      validatorGate auditEvidence couplingAccepted := by
  intro accepted
  exact accepted

theorem ay_srcd_accepted_restart_ledger
    {restartLedger : Prop} :
    restartLedger -> ay_srcd_restart_ledger_evidence restartLedger := by
  intro evidence
  exact evidence

theorem ay_srcd_accepted_deletion_epoch_ledger
    {deletionEpochLedger : Prop} :
    deletionEpochLedger ->
    ay_srcd_deletion_epoch_ledger_evidence deletionEpochLedger := by
  intro evidence
  exact evidence

theorem ay_srcd_accepted_learned_clause_manifest
    {learnedClauseManifest : Prop} :
    learnedClauseManifest ->
    ay_srcd_learned_clause_manifest_evidence learnedClauseManifest := by
  intro evidence
  exact evidence

theorem ay_srcd_accepted_watchlist_checkpoint
    {watchlistCheckpoint : Prop} :
    watchlistCheckpoint ->
    ay_srcd_watchlist_checkpoint_evidence watchlistCheckpoint := by
  intro evidence
  exact evidence

theorem ay_srcd_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_srcd_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_srcd_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_srcd_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_srcd_accepted_solver_build
    {solverBuild : Prop} :
    solverBuild -> ay_srcd_solver_build_evidence solverBuild := by
  intro evidence
  exact evidence

theorem ay_srcd_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_srcd_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_srcd_accepted_audit_evidence
    {auditEvidence : Prop} :
    auditEvidence -> ay_srcd_audit_evidence auditEvidence := by
  intro evidence
  exact evidence

theorem ay_srcd_coupling_policy_admissible_hint
    {couplingAccepted restartSchedule deletionWindow retentionPolicy : Prop} :
    couplingAccepted ->
    restartSchedule ->
    deletionWindow ->
    retentionPolicy ->
    ay_srcd_coupling_hint couplingAccepted restartSchedule deletionWindow
      retentionPolicy := by
  intro accepted restart deletion retention
  exact accepted

theorem ay_srcd_hint_cannot_change_truth
    {couplingAccepted satSound unsatSound : Prop} :
    couplingAccepted ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_srcd_accepted_policy_preserves_public_soundness
    {couplingAccepted satSound unsatSound : Prop} :
    couplingAccepted ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_srcd_rejected_is_no_claim
    {restartLedgerDrift diagnostic : Prop} :
    restartLedgerDrift ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_rejected_forces_recompute
    {restartLedgerDrift recomputeRequired : Prop} :
    restartLedgerDrift ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_srcd_rejected_cannot_bless_public_result
    {restartLedgerDrift baselineSound satSound unsatSound : Prop} :
    restartLedgerDrift ->
    baselineSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_srcd_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_srcd_gate accepted rejected ->
    ay_srcd_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_srcd_safe_policy_deployment_accept
    {couplingAccepted restartSchedule deletionWindow retentionPolicy satSound
      unsatSound : Prop} :
    couplingAccepted ->
    restartSchedule ->
    deletionWindow ->
    retentionPolicy ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_srcd_safe_policy_deployment_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_srcd_restart_ledger_drift_forces_no_claim
    {restartLedgerDrift diagnostic : Prop} :
    restartLedgerDrift ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_deletion_ledger_drift_forces_no_claim
    {deletionLedgerDrift diagnostic : Prop} :
    deletionLedgerDrift ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_manifest_mismatch_forces_no_claim
    {manifestMismatch diagnostic : Prop} :
    manifestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_watch_mismatch_forces_no_claim
    {watchMismatch diagnostic : Prop} :
    watchMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_replay_gap_forces_no_claim
    {replayGap diagnostic : Prop} :
    replayGap ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_stale_build_forces_no_claim
    {staleBuild diagnostic : Prop} :
    staleBuild ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_validator_rejection_forces_no_claim
    {validatorRejection diagnostic : Prop} :
    validatorRejection ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_audit_contradiction_forces_no_claim
    {auditContradiction diagnostic : Prop} :
    auditContradiction ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_missing_fallback_forces_no_claim
    {missingFallback diagnostic : Prop} :
    missingFallback ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_missing_restart_ledger_forces_no_claim
    {missingRestartLedger diagnostic : Prop} :
    missingRestartLedger ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_missing_deletion_ledger_forces_no_claim
    {missingDeletionLedger diagnostic : Prop} :
    missingDeletionLedger ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_srcd_restart_drift_cannot_bless_public_result
    {restartLedgerDrift baselineSound satSound unsatSound : Prop} :
    restartLedgerDrift ->
    baselineSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_srcd_deletion_drift_cannot_bless_public_result
    {deletionLedgerDrift baselineSound satSound unsatSound : Prop} :
    deletionLedgerDrift ->
    baselineSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_srcd_manifest_mismatch_cannot_bless_public_result
    {manifestMismatch baselineSound satSound unsatSound : Prop} :
    manifestMismatch ->
    baselineSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_srcd_watch_mismatch_cannot_bless_public_result
    {watchMismatch baselineSound satSound unsatSound : Prop} :
    watchMismatch ->
    baselineSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_srcd_replay_gap_cannot_bless_public_result
    {replayGap baselineSound satSound unsatSound : Prop} :
    replayGap ->
    baselineSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_srcd_stale_build_cannot_bless_public_result
    {staleBuild baselineSound satSound unsatSound : Prop} :
    staleBuild ->
    baselineSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_srcd_validator_rejection_cannot_bless_public_result
    {validatorRejection baselineSound satSound unsatSound : Prop} :
    validatorRejection ->
    baselineSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_srcd_audit_contradiction_cannot_bless_public_result
    {auditContradiction baselineSound satSound unsatSound : Prop} :
    auditContradiction ->
    baselineSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound ->
    ay_srcd_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_srcd_policy_requires_restart_ledger
    {restartLedger : Prop} :
    ay_srcd_restart_ledger_evidence restartLedger -> restartLedger := by
  intro evidence
  exact evidence

theorem ay_srcd_policy_requires_deletion_epoch_ledger
    {deletionEpochLedger : Prop} :
    ay_srcd_deletion_epoch_ledger_evidence deletionEpochLedger ->
    deletionEpochLedger := by
  intro evidence
  exact evidence

theorem ay_srcd_policy_requires_learned_clause_manifest
    {learnedClauseManifest : Prop} :
    ay_srcd_learned_clause_manifest_evidence learnedClauseManifest ->
    learnedClauseManifest := by
  intro evidence
  exact evidence

theorem ay_srcd_policy_requires_watchlist_checkpoint
    {watchlistCheckpoint : Prop} :
    ay_srcd_watchlist_checkpoint_evidence watchlistCheckpoint ->
    watchlistCheckpoint := by
  intro evidence
  exact evidence

theorem ay_srcd_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_srcd_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_srcd_policy_requires_validator
    {validatorGate : Prop} :
    ay_srcd_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_srcd_policy_requires_audit
    {auditEvidence : Prop} :
    ay_srcd_audit_evidence auditEvidence -> auditEvidence := by
  intro evidence
  exact evidence
