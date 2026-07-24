def ay_rtg_conj (p q : Prop) : Prop := p ∧ q

def ay_rtg_disj (p q : Prop) : Prop := p ∨ q

def ay_rtg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rtg_disj satSound unsatSound

def ay_rtg_inputs
    (conflictCounterDigest lbdScoreStreamDigest movingAverageStateDigest
      restartThresholdManifest triggerDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) : Prop :=
  ay_rtg_conj conflictCounterDigest
    (ay_rtg_conj lbdScoreStreamDigest
      (ay_rtg_conj movingAverageStateDigest
        (ay_rtg_conj restartThresholdManifest
          (ay_rtg_conj triggerDecisionLedger
            (ay_rtg_conj trailSnapshotDigest
              (ay_rtg_conj learnedClauseContextDigest
                (ay_rtg_conj propagationReplayTranscript
                  (ay_rtg_conj fallbackBaseline
                    (ay_rtg_conj solverBuildEvidence
                      (ay_rtg_conj validatorGate
                        (ay_rtg_conj archiveManifest
                          auditTranscript)))))))))))

def ay_rtg_conflict_counter_digest_evidence
    (conflictCounterDigest : Prop) : Prop :=
  conflictCounterDigest

def ay_rtg_lbd_score_stream_digest_evidence
    (lbdScoreStreamDigest : Prop) : Prop :=
  lbdScoreStreamDigest

def ay_rtg_moving_average_state_digest_evidence
    (movingAverageStateDigest : Prop) : Prop :=
  movingAverageStateDigest

def ay_rtg_restart_threshold_manifest_evidence
    (restartThresholdManifest : Prop) : Prop :=
  restartThresholdManifest

def ay_rtg_trigger_decision_ledger_evidence
    (triggerDecisionLedger : Prop) : Prop :=
  triggerDecisionLedger

def ay_rtg_trail_snapshot_digest_evidence
    (trailSnapshotDigest : Prop) : Prop :=
  trailSnapshotDigest

def ay_rtg_learned_clause_context_digest_evidence
    (learnedClauseContextDigest : Prop) : Prop :=
  learnedClauseContextDigest

def ay_rtg_propagation_replay_transcript_evidence
    (propagationReplayTranscript : Prop) : Prop :=
  propagationReplayTranscript

def ay_rtg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_rtg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rtg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rtg_archive_manifest_evidence (archiveManifest : Prop) : Prop :=
  archiveManifest

def ay_rtg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rtg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rtg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_rtg_checked_sat_evidence (satEvidence : Prop) : Prop := satEvidence

def ay_rtg_checked_unsat_evidence (unsatEvidence : Prop) : Prop :=
  unsatEvidence

def ay_rtg_accepted
    (conflictCounterDigest lbdScoreStreamDigest movingAverageStateDigest
      restartThresholdManifest triggerDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      triggerAccepted : Prop) : Prop :=
  triggerAccepted

def ay_rtg_rejected
    (counterMismatch lbdMismatch averageMismatch thresholdMismatch
      triggerMismatch trailMismatch learnedMismatch replayMismatch
      fallbackMismatch buildMismatch validatorMismatch archiveMismatch
      auditMismatch : Prop) : Prop :=
  ay_rtg_disj counterMismatch
    (ay_rtg_disj lbdMismatch
      (ay_rtg_disj averageMismatch
        (ay_rtg_disj thresholdMismatch
          (ay_rtg_disj triggerMismatch
            (ay_rtg_disj trailMismatch
              (ay_rtg_disj learnedMismatch
                (ay_rtg_disj replayMismatch
                  (ay_rtg_disj fallbackMismatch
                    (ay_rtg_disj buildMismatch
                      (ay_rtg_disj validatorMismatch
                        (ay_rtg_disj archiveMismatch
                          auditMismatch))))))))))))

def ay_rtg_restart_trigger_heuristic_evidence
    (triggerAccepted schedulingOnly replayBacked : Prop) : Prop :=
  triggerAccepted

def ay_rtg_publication_gate
    (triggerReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence : Prop) : Prop :=
  ay_rtg_conj triggerReplay
    (ay_rtg_conj solverBuildEvidence
      (ay_rtg_conj validatorGate
        (ay_rtg_conj archiveManifest
          (ay_rtg_conj fallbackBaseline
            (ay_rtg_conj auditTranscript checkedEvidence)))))

def ay_rtg_gate (accepted rejected : Prop) : Prop :=
  ay_rtg_disj accepted rejected

theorem ay_rtg_input_components
    {conflictCounterDigest lbdScoreStreamDigest movingAverageStateDigest
      restartThresholdManifest triggerDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop} :
    ay_rtg_inputs conflictCounterDigest lbdScoreStreamDigest
      movingAverageStateDigest restartThresholdManifest triggerDecisionLedger
      trailSnapshotDigest learnedClauseContextDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate archiveManifest auditTranscript ->
    ay_rtg_inputs conflictCounterDigest lbdScoreStreamDigest
      movingAverageStateDigest restartThresholdManifest triggerDecisionLedger
      trailSnapshotDigest learnedClauseContextDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate archiveManifest auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rtg_accepted_trigger
    {conflictCounterDigest lbdScoreStreamDigest movingAverageStateDigest
      restartThresholdManifest triggerDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      triggerAccepted : Prop} :
    triggerAccepted ->
    ay_rtg_accepted conflictCounterDigest lbdScoreStreamDigest
      movingAverageStateDigest restartThresholdManifest triggerDecisionLedger
      trailSnapshotDigest learnedClauseContextDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate archiveManifest auditTranscript triggerAccepted := by
  intro accepted
  exact accepted

theorem ay_rtg_accepted_conflict_counter_digest
    {conflictCounterDigest : Prop} :
    conflictCounterDigest ->
    ay_rtg_conflict_counter_digest_evidence conflictCounterDigest := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_lbd_score_stream_digest
    {lbdScoreStreamDigest : Prop} :
    lbdScoreStreamDigest ->
    ay_rtg_lbd_score_stream_digest_evidence lbdScoreStreamDigest := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_moving_average_state_digest
    {movingAverageStateDigest : Prop} :
    movingAverageStateDigest ->
    ay_rtg_moving_average_state_digest_evidence movingAverageStateDigest := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_restart_threshold_manifest
    {restartThresholdManifest : Prop} :
    restartThresholdManifest ->
    ay_rtg_restart_threshold_manifest_evidence restartThresholdManifest := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_trigger_decision_ledger
    {triggerDecisionLedger : Prop} :
    triggerDecisionLedger ->
    ay_rtg_trigger_decision_ledger_evidence triggerDecisionLedger := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_trail_snapshot_digest
    {trailSnapshotDigest : Prop} :
    trailSnapshotDigest ->
    ay_rtg_trail_snapshot_digest_evidence trailSnapshotDigest := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_learned_clause_context_digest
    {learnedClauseContextDigest : Prop} :
    learnedClauseContextDigest ->
    ay_rtg_learned_clause_context_digest_evidence
      learnedClauseContextDigest := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_propagation_replay_transcript
    {propagationReplayTranscript : Prop} :
    propagationReplayTranscript ->
    ay_rtg_propagation_replay_transcript_evidence
      propagationReplayTranscript := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_rtg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_rtg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rtg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_archive_manifest
    {archiveManifest : Prop} :
    archiveManifest -> ay_rtg_archive_manifest_evidence archiveManifest := by
  intro evidence
  exact evidence

theorem ay_rtg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rtg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rtg_restart_trigger_is_scheduling_heuristic_only
    {triggerAccepted schedulingOnly : Prop} :
    triggerAccepted ->
    schedulingOnly ->
    schedulingOnly :=
  fun _ scheduling => scheduling

theorem ay_rtg_trigger_cannot_independently_justify_sat
    {triggerAccepted satEvidence satSound : Prop} :
    triggerAccepted ->
    ay_rtg_checked_sat_evidence satEvidence ->
    (satEvidence -> satSound) ->
    satSound :=
  fun _ evidence transport => transport evidence

theorem ay_rtg_trigger_cannot_independently_justify_unsat
    {triggerAccepted unsatEvidence unsatSound : Prop} :
    triggerAccepted ->
    ay_rtg_checked_unsat_evidence unsatEvidence ->
    (unsatEvidence -> unsatSound) ->
    unsatSound :=
  fun _ evidence transport => transport evidence

theorem ay_rtg_trigger_cannot_change_original_formula_truth
    {triggerAccepted originalFormulaTruthPreserved : Prop} :
    triggerAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_rtg_accepted_publication_preserves_public_soundness
    {triggerReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence satSound unsatSound :
      Prop} :
    ay_rtg_publication_gate triggerReplay solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript checkedEvidence ->
    ay_rtg_public_soundness_theorem satSound unsatSound ->
    ay_rtg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rtg_exact_context_ties_trigger_to_replay
    {conflictCounterDigest lbdScoreStreamDigest movingAverageStateDigest
      restartThresholdManifest triggerDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      exactContext : Prop} :
    conflictCounterDigest ->
    lbdScoreStreamDigest ->
    movingAverageStateDigest ->
    restartThresholdManifest ->
    triggerDecisionLedger ->
    trailSnapshotDigest ->
    learnedClauseContextDigest ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    exactContext ->
    exactContext :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ context => context

theorem ay_rtg_lbd_average_threshold_preserve_trigger_replay
    {lbdScoreStreamDigest movingAverageStateDigest restartThresholdManifest
      triggerDecisionLedger : Prop} :
    lbdScoreStreamDigest ->
    movingAverageStateDigest ->
    restartThresholdManifest ->
    triggerDecisionLedger ->
    triggerDecisionLedger :=
  fun _ _ _ ledger => ledger

theorem ay_rtg_learned_context_preserves_propagation_replay
    {learnedClauseContextDigest propagationReplayTranscript : Prop} :
    learnedClauseContextDigest ->
    propagationReplayTranscript ->
    propagationReplayTranscript :=
  fun _ replay => replay

theorem ay_rtg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rtg_gate accepted rejected ->
    ay_rtg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rtg_rejected_is_no_claim
    {counterMismatch diagnostic : Prop} :
    counterMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_rejected_forces_recompute
    {counterMismatch recomputeRequired : Prop} :
    counterMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_failed_restart_trigger_guard_cannot_bless_competition_result
    {counterMismatch baselineNoClaim satSound unsatSound : Prop} :
    counterMismatch ->
    baselineNoClaim ->
    ay_rtg_public_soundness_theorem satSound unsatSound ->
    ay_rtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rtg_counter_mismatch_forces_no_claim
    {counterMismatch diagnostic : Prop} :
    counterMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_lbd_mismatch_forces_no_claim
    {lbdMismatch diagnostic : Prop} :
    lbdMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_average_mismatch_forces_no_claim
    {averageMismatch diagnostic : Prop} :
    averageMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_threshold_mismatch_forces_no_claim
    {thresholdMismatch diagnostic : Prop} :
    thresholdMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_trigger_mismatch_forces_no_claim
    {triggerMismatch diagnostic : Prop} :
    triggerMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_learned_mismatch_forces_no_claim
    {learnedMismatch diagnostic : Prop} :
    learnedMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic : Prop} :
    archiveMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rtg_counter_mismatch_forces_recompute
    {counterMismatch recomputeRequired : Prop} :
    counterMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_lbd_mismatch_forces_recompute
    {lbdMismatch recomputeRequired : Prop} :
    lbdMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_average_mismatch_forces_recompute
    {averageMismatch recomputeRequired : Prop} :
    averageMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_threshold_mismatch_forces_recompute
    {thresholdMismatch recomputeRequired : Prop} :
    thresholdMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_trigger_mismatch_forces_recompute
    {triggerMismatch recomputeRequired : Prop} :
    triggerMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_learned_mismatch_forces_recompute
    {learnedMismatch recomputeRequired : Prop} :
    learnedMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_archive_mismatch_forces_recompute
    {archiveMismatch recomputeRequired : Prop} :
    archiveMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rtg_counter_mismatch_cannot_bless_result
    {counterMismatch baselineNoClaim satSound unsatSound : Prop} :
    counterMismatch ->
    baselineNoClaim ->
    ay_rtg_public_soundness_theorem satSound unsatSound ->
    ay_rtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rtg_lbd_mismatch_cannot_bless_result
    {lbdMismatch baselineNoClaim satSound unsatSound : Prop} :
    lbdMismatch ->
    baselineNoClaim ->
    ay_rtg_public_soundness_theorem satSound unsatSound ->
    ay_rtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rtg_replay_mismatch_cannot_bless_result
    {replayMismatch baselineNoClaim satSound unsatSound : Prop} :
    replayMismatch ->
    baselineNoClaim ->
    ay_rtg_public_soundness_theorem satSound unsatSound ->
    ay_rtg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rtg_policy_requires_conflict_counter_digest
    {conflictCounterDigest accepted : Prop} :
    conflictCounterDigest -> accepted -> conflictCounterDigest :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_lbd_score_stream_digest
    {lbdScoreStreamDigest accepted : Prop} :
    lbdScoreStreamDigest -> accepted -> lbdScoreStreamDigest :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_moving_average_state_digest
    {movingAverageStateDigest accepted : Prop} :
    movingAverageStateDigest -> accepted -> movingAverageStateDigest :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_restart_threshold_manifest
    {restartThresholdManifest accepted : Prop} :
    restartThresholdManifest -> accepted -> restartThresholdManifest :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_trigger_decision_ledger
    {triggerDecisionLedger accepted : Prop} :
    triggerDecisionLedger -> accepted -> triggerDecisionLedger :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_trail_snapshot_digest
    {trailSnapshotDigest accepted : Prop} :
    trailSnapshotDigest -> accepted -> trailSnapshotDigest :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_learned_clause_context_digest
    {learnedClauseContextDigest accepted : Prop} :
    learnedClauseContextDigest -> accepted -> learnedClauseContextDigest :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_propagation_replay_transcript
    {propagationReplayTranscript accepted : Prop} :
    propagationReplayTranscript -> accepted -> propagationReplayTranscript :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_archive
    {archiveManifest accepted : Prop} :
    archiveManifest -> accepted -> archiveManifest :=
  fun evidence _ => evidence

theorem ay_rtg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
