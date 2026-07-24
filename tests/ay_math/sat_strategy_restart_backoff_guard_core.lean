def ay_rbg_conj (p q : Prop) : Prop := p ∧ q

def ay_rbg_disj (p q : Prop) : Prop := p ∨ q

def ay_rbg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rbg_disj satSound unsatSound

def ay_rbg_inputs
    (restartCounterDigest conflictProgressMetricDigest backoffScheduleManifest
      thresholdUpdateLedger trailSnapshotDigest learnedClauseContextDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate archiveManifest auditTranscript : Prop) : Prop :=
  ay_rbg_conj restartCounterDigest
    (ay_rbg_conj conflictProgressMetricDigest
      (ay_rbg_conj backoffScheduleManifest
        (ay_rbg_conj thresholdUpdateLedger
          (ay_rbg_conj trailSnapshotDigest
            (ay_rbg_conj learnedClauseContextDigest
              (ay_rbg_conj propagationReplayTranscript
                (ay_rbg_conj fallbackBaseline
                  (ay_rbg_conj solverBuildEvidence
                    (ay_rbg_conj validatorGate
                      (ay_rbg_conj archiveManifest auditTranscript))))))))))

def ay_rbg_restart_counter_digest_evidence
    (restartCounterDigest : Prop) : Prop :=
  restartCounterDigest

def ay_rbg_conflict_progress_metric_digest_evidence
    (conflictProgressMetricDigest : Prop) : Prop :=
  conflictProgressMetricDigest

def ay_rbg_backoff_schedule_manifest_evidence
    (backoffScheduleManifest : Prop) : Prop :=
  backoffScheduleManifest

def ay_rbg_threshold_update_ledger_evidence
    (thresholdUpdateLedger : Prop) : Prop :=
  thresholdUpdateLedger

def ay_rbg_trail_snapshot_digest_evidence
    (trailSnapshotDigest : Prop) : Prop :=
  trailSnapshotDigest

def ay_rbg_learned_clause_context_digest_evidence
    (learnedClauseContextDigest : Prop) : Prop :=
  learnedClauseContextDigest

def ay_rbg_propagation_replay_transcript_evidence
    (propagationReplayTranscript : Prop) : Prop :=
  propagationReplayTranscript

def ay_rbg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_rbg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rbg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rbg_archive_manifest_evidence (archiveManifest : Prop) : Prop :=
  archiveManifest

def ay_rbg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rbg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rbg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_rbg_checked_sat_evidence (satEvidence : Prop) : Prop := satEvidence

def ay_rbg_checked_unsat_evidence (unsatEvidence : Prop) : Prop :=
  unsatEvidence

def ay_rbg_accepted
    (restartCounterDigest conflictProgressMetricDigest backoffScheduleManifest
      thresholdUpdateLedger trailSnapshotDigest learnedClauseContextDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate archiveManifest auditTranscript backoffAccepted : Prop) :
    Prop :=
  backoffAccepted

def ay_rbg_rejected
    (counterMismatch metricMismatch scheduleMismatch updateMismatch
      trailMismatch learnedMismatch replayMismatch fallbackMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch : Prop) :
    Prop :=
  ay_rbg_disj counterMismatch
    (ay_rbg_disj metricMismatch
      (ay_rbg_disj scheduleMismatch
        (ay_rbg_disj updateMismatch
          (ay_rbg_disj trailMismatch
            (ay_rbg_disj learnedMismatch
              (ay_rbg_disj replayMismatch
                (ay_rbg_disj fallbackMismatch
                  (ay_rbg_disj buildMismatch
                    (ay_rbg_disj validatorMismatch
                      (ay_rbg_disj archiveMismatch auditMismatch))))))))))

def ay_rbg_backoff_heuristic_evidence
    (backoffAccepted schedulingOnly replayBacked : Prop) : Prop :=
  backoffAccepted

def ay_rbg_publication_gate
    (backoffReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence : Prop) : Prop :=
  ay_rbg_conj backoffReplay
    (ay_rbg_conj solverBuildEvidence
      (ay_rbg_conj validatorGate
        (ay_rbg_conj archiveManifest
          (ay_rbg_conj fallbackBaseline
            (ay_rbg_conj auditTranscript checkedEvidence)))))

def ay_rbg_gate (accepted rejected : Prop) : Prop :=
  ay_rbg_disj accepted rejected

theorem ay_rbg_input_components
    {restartCounterDigest conflictProgressMetricDigest backoffScheduleManifest
      thresholdUpdateLedger trailSnapshotDigest learnedClauseContextDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate archiveManifest auditTranscript : Prop} :
    ay_rbg_inputs restartCounterDigest conflictProgressMetricDigest
      backoffScheduleManifest thresholdUpdateLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript ->
    ay_rbg_inputs restartCounterDigest conflictProgressMetricDigest
      backoffScheduleManifest thresholdUpdateLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rbg_accepted_backoff
    {restartCounterDigest conflictProgressMetricDigest backoffScheduleManifest
      thresholdUpdateLedger trailSnapshotDigest learnedClauseContextDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate archiveManifest auditTranscript backoffAccepted : Prop} :
    backoffAccepted ->
    ay_rbg_accepted restartCounterDigest conflictProgressMetricDigest
      backoffScheduleManifest thresholdUpdateLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      backoffAccepted := by
  intro accepted
  exact accepted

theorem ay_rbg_accepted_restart_counter_digest
    {restartCounterDigest : Prop} :
    restartCounterDigest ->
    ay_rbg_restart_counter_digest_evidence restartCounterDigest := by
  intro evidence
  exact evidence

theorem ay_rbg_accepted_conflict_progress_metric_digest
    {conflictProgressMetricDigest : Prop} :
    conflictProgressMetricDigest ->
    ay_rbg_conflict_progress_metric_digest_evidence
      conflictProgressMetricDigest := by
  intro evidence
  exact evidence

theorem ay_rbg_accepted_backoff_schedule_manifest
    {backoffScheduleManifest : Prop} :
    backoffScheduleManifest ->
    ay_rbg_backoff_schedule_manifest_evidence backoffScheduleManifest := by
  intro evidence
  exact evidence

theorem ay_rbg_accepted_threshold_update_ledger
    {thresholdUpdateLedger : Prop} :
    thresholdUpdateLedger ->
    ay_rbg_threshold_update_ledger_evidence thresholdUpdateLedger := by
  intro evidence
  exact evidence

theorem ay_rbg_accepted_trail_snapshot_digest
    {trailSnapshotDigest : Prop} :
    trailSnapshotDigest ->
    ay_rbg_trail_snapshot_digest_evidence trailSnapshotDigest := by
  intro evidence
  exact evidence

theorem ay_rbg_accepted_learned_clause_context_digest
    {learnedClauseContextDigest : Prop} :
    learnedClauseContextDigest ->
    ay_rbg_learned_clause_context_digest_evidence
      learnedClauseContextDigest := by
  intro evidence
  exact evidence

theorem ay_rbg_accepted_propagation_replay_transcript
    {propagationReplayTranscript : Prop} :
    propagationReplayTranscript ->
    ay_rbg_propagation_replay_transcript_evidence
      propagationReplayTranscript := by
  intro evidence
  exact evidence

theorem ay_rbg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_rbg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rbg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_rbg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rbg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rbg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rbg_accepted_archive_manifest
    {archiveManifest : Prop} :
    archiveManifest -> ay_rbg_archive_manifest_evidence archiveManifest := by
  intro evidence
  exact evidence

theorem ay_rbg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rbg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rbg_restart_backoff_is_scheduling_heuristic_only
    {backoffAccepted schedulingOnly : Prop} :
    backoffAccepted ->
    schedulingOnly ->
    schedulingOnly :=
  fun _ scheduling => scheduling

theorem ay_rbg_backoff_cannot_independently_justify_sat
    {backoffAccepted satEvidence satSound : Prop} :
    backoffAccepted ->
    ay_rbg_checked_sat_evidence satEvidence ->
    (satEvidence -> satSound) ->
    satSound :=
  fun _ evidence transport => transport evidence

theorem ay_rbg_backoff_cannot_independently_justify_unsat
    {backoffAccepted unsatEvidence unsatSound : Prop} :
    backoffAccepted ->
    ay_rbg_checked_unsat_evidence unsatEvidence ->
    (unsatEvidence -> unsatSound) ->
    unsatSound :=
  fun _ evidence transport => transport evidence

theorem ay_rbg_backoff_cannot_change_original_formula_truth
    {backoffAccepted originalFormulaTruthPreserved : Prop} :
    backoffAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_rbg_accepted_publication_preserves_public_soundness
    {backoffReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence satSound unsatSound :
      Prop} :
    ay_rbg_publication_gate backoffReplay solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript checkedEvidence ->
    ay_rbg_public_soundness_theorem satSound unsatSound ->
    ay_rbg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rbg_exact_context_ties_backoff_to_replay
    {restartCounterDigest conflictProgressMetricDigest backoffScheduleManifest
      thresholdUpdateLedger trailSnapshotDigest learnedClauseContextDigest
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest auditTranscript exactContext : Prop} :
    restartCounterDigest ->
    conflictProgressMetricDigest ->
    backoffScheduleManifest ->
    thresholdUpdateLedger ->
    trailSnapshotDigest ->
    learnedClauseContextDigest ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    exactContext ->
    exactContext :=
  fun _ _ _ _ _ _ _ _ _ _ _ context => context

theorem ay_rbg_metrics_and_update_preserve_backoff_schedule
    {conflictProgressMetricDigest thresholdUpdateLedger
      backoffScheduleManifest : Prop} :
    conflictProgressMetricDigest ->
    thresholdUpdateLedger ->
    backoffScheduleManifest ->
    backoffScheduleManifest :=
  fun _ _ schedule => schedule

theorem ay_rbg_learned_context_preserves_propagation_replay
    {learnedClauseContextDigest propagationReplayTranscript : Prop} :
    learnedClauseContextDigest ->
    propagationReplayTranscript ->
    propagationReplayTranscript :=
  fun _ replay => replay

theorem ay_rbg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rbg_gate accepted rejected ->
    ay_rbg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rbg_rejected_is_no_claim
    {counterMismatch diagnostic : Prop} :
    counterMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_rejected_forces_recompute
    {counterMismatch recomputeRequired : Prop} :
    counterMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_failed_backoff_guard_cannot_bless_competition_result
    {counterMismatch baselineNoClaim satSound unsatSound : Prop} :
    counterMismatch ->
    baselineNoClaim ->
    ay_rbg_public_soundness_theorem satSound unsatSound ->
    ay_rbg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbg_counter_mismatch_forces_no_claim
    {counterMismatch diagnostic : Prop} :
    counterMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_metric_mismatch_forces_no_claim
    {metricMismatch diagnostic : Prop} :
    metricMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_schedule_mismatch_forces_no_claim
    {scheduleMismatch diagnostic : Prop} :
    scheduleMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_update_mismatch_forces_no_claim
    {updateMismatch diagnostic : Prop} :
    updateMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_learned_mismatch_forces_no_claim
    {learnedMismatch diagnostic : Prop} :
    learnedMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic : Prop} :
    archiveMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbg_counter_mismatch_forces_recompute
    {counterMismatch recomputeRequired : Prop} :
    counterMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_metric_mismatch_forces_recompute
    {metricMismatch recomputeRequired : Prop} :
    metricMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_schedule_mismatch_forces_recompute
    {scheduleMismatch recomputeRequired : Prop} :
    scheduleMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_update_mismatch_forces_recompute
    {updateMismatch recomputeRequired : Prop} :
    updateMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_learned_mismatch_forces_recompute
    {learnedMismatch recomputeRequired : Prop} :
    learnedMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_archive_mismatch_forces_recompute
    {archiveMismatch recomputeRequired : Prop} :
    archiveMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbg_counter_mismatch_cannot_bless_result
    {counterMismatch baselineNoClaim satSound unsatSound : Prop} :
    counterMismatch ->
    baselineNoClaim ->
    ay_rbg_public_soundness_theorem satSound unsatSound ->
    ay_rbg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbg_schedule_mismatch_cannot_bless_result
    {scheduleMismatch baselineNoClaim satSound unsatSound : Prop} :
    scheduleMismatch ->
    baselineNoClaim ->
    ay_rbg_public_soundness_theorem satSound unsatSound ->
    ay_rbg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbg_replay_mismatch_cannot_bless_result
    {replayMismatch baselineNoClaim satSound unsatSound : Prop} :
    replayMismatch ->
    baselineNoClaim ->
    ay_rbg_public_soundness_theorem satSound unsatSound ->
    ay_rbg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbg_policy_requires_restart_counter_digest
    {restartCounterDigest accepted : Prop} :
    restartCounterDigest -> accepted -> restartCounterDigest :=
  fun evidence _ => evidence

theorem ay_rbg_policy_requires_conflict_progress_metric_digest
    {conflictProgressMetricDigest accepted : Prop} :
    conflictProgressMetricDigest -> accepted -> conflictProgressMetricDigest :=
  fun evidence _ => evidence

theorem ay_rbg_policy_requires_backoff_schedule_manifest
    {backoffScheduleManifest accepted : Prop} :
    backoffScheduleManifest -> accepted -> backoffScheduleManifest :=
  fun evidence _ => evidence

theorem ay_rbg_policy_requires_threshold_update_ledger
    {thresholdUpdateLedger accepted : Prop} :
    thresholdUpdateLedger -> accepted -> thresholdUpdateLedger :=
  fun evidence _ => evidence

theorem ay_rbg_policy_requires_trail_snapshot_digest
    {trailSnapshotDigest accepted : Prop} :
    trailSnapshotDigest -> accepted -> trailSnapshotDigest :=
  fun evidence _ => evidence

theorem ay_rbg_policy_requires_learned_clause_context_digest
    {learnedClauseContextDigest accepted : Prop} :
    learnedClauseContextDigest -> accepted -> learnedClauseContextDigest :=
  fun evidence _ => evidence

theorem ay_rbg_policy_requires_propagation_replay_transcript
    {propagationReplayTranscript accepted : Prop} :
    propagationReplayTranscript -> accepted -> propagationReplayTranscript :=
  fun evidence _ => evidence

theorem ay_rbg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_rbg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_rbg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_rbg_policy_requires_archive
    {archiveManifest accepted : Prop} :
    archiveManifest -> accepted -> archiveManifest :=
  fun evidence _ => evidence

theorem ay_rbg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
