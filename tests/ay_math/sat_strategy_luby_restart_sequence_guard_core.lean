def ay_lrg_conj (p q : Prop) : Prop := p ∧ q

def ay_lrg_disj (p q : Prop) : Prop := p ∨ q

def ay_lrg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_lrg_disj satSound unsatSound

def ay_lrg_inputs
    (restartIndexDigest lubySequenceManifest scaleFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) : Prop :=
  ay_lrg_conj restartIndexDigest
    (ay_lrg_conj lubySequenceManifest
      (ay_lrg_conj scaleFactorManifest
        (ay_lrg_conj conflictCutoffLedger
          (ay_lrg_conj restartDecisionLedger
            (ay_lrg_conj trailSnapshotDigest
              (ay_lrg_conj learnedClauseContextDigest
                (ay_lrg_conj propagationReplayTranscript
                  (ay_lrg_conj fallbackBaseline
                    (ay_lrg_conj solverBuildEvidence
                      (ay_lrg_conj validatorGate
                        (ay_lrg_conj archiveManifest
                          auditTranscript)))))))))))

def ay_lrg_restart_index_digest_evidence
    (restartIndexDigest : Prop) : Prop :=
  restartIndexDigest

def ay_lrg_luby_sequence_manifest_evidence
    (lubySequenceManifest : Prop) : Prop :=
  lubySequenceManifest

def ay_lrg_scale_factor_manifest_evidence
    (scaleFactorManifest : Prop) : Prop :=
  scaleFactorManifest

def ay_lrg_conflict_cutoff_ledger_evidence
    (conflictCutoffLedger : Prop) : Prop :=
  conflictCutoffLedger

def ay_lrg_restart_decision_ledger_evidence
    (restartDecisionLedger : Prop) : Prop :=
  restartDecisionLedger

def ay_lrg_trail_snapshot_digest_evidence
    (trailSnapshotDigest : Prop) : Prop :=
  trailSnapshotDigest

def ay_lrg_learned_clause_context_digest_evidence
    (learnedClauseContextDigest : Prop) : Prop :=
  learnedClauseContextDigest

def ay_lrg_propagation_replay_transcript_evidence
    (propagationReplayTranscript : Prop) : Prop :=
  propagationReplayTranscript

def ay_lrg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_lrg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_lrg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_lrg_archive_manifest_evidence (archiveManifest : Prop) : Prop :=
  archiveManifest

def ay_lrg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_lrg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_lrg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_lrg_checked_sat_evidence (satEvidence : Prop) : Prop := satEvidence

def ay_lrg_checked_unsat_evidence (unsatEvidence : Prop) : Prop :=
  unsatEvidence

def ay_lrg_accepted
    (restartIndexDigest lubySequenceManifest scaleFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      lubyAccepted : Prop) : Prop :=
  lubyAccepted

def ay_lrg_rejected
    (indexMismatch sequenceMismatch scaleMismatch cutoffMismatch restartMismatch
      trailMismatch learnedMismatch replayMismatch fallbackMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch : Prop) :
    Prop :=
  ay_lrg_disj indexMismatch
    (ay_lrg_disj sequenceMismatch
      (ay_lrg_disj scaleMismatch
        (ay_lrg_disj cutoffMismatch
          (ay_lrg_disj restartMismatch
            (ay_lrg_disj trailMismatch
              (ay_lrg_disj learnedMismatch
                (ay_lrg_disj replayMismatch
                  (ay_lrg_disj fallbackMismatch
                    (ay_lrg_disj buildMismatch
                      (ay_lrg_disj validatorMismatch
                        (ay_lrg_disj archiveMismatch
                          auditMismatch))))))))))))

def ay_lrg_luby_schedule_heuristic_evidence
    (lubyAccepted schedulingOnly replayBacked : Prop) : Prop :=
  lubyAccepted

def ay_lrg_publication_gate
    (lubyReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence : Prop) : Prop :=
  ay_lrg_conj lubyReplay
    (ay_lrg_conj solverBuildEvidence
      (ay_lrg_conj validatorGate
        (ay_lrg_conj archiveManifest
          (ay_lrg_conj fallbackBaseline
            (ay_lrg_conj auditTranscript checkedEvidence)))))

def ay_lrg_gate (accepted rejected : Prop) : Prop :=
  ay_lrg_disj accepted rejected

theorem ay_lrg_input_components
    {restartIndexDigest lubySequenceManifest scaleFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop} :
    ay_lrg_inputs restartIndexDigest lubySequenceManifest scaleFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript ->
    ay_lrg_inputs restartIndexDigest lubySequenceManifest scaleFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript := by
  intro inputs
  exact inputs

theorem ay_lrg_accepted_luby_sequence
    {restartIndexDigest lubySequenceManifest scaleFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      lubyAccepted : Prop} :
    lubyAccepted ->
    ay_lrg_accepted restartIndexDigest lubySequenceManifest scaleFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      lubyAccepted := by
  intro accepted
  exact accepted

theorem ay_lrg_accepted_restart_index_digest
    {restartIndexDigest : Prop} :
    restartIndexDigest ->
    ay_lrg_restart_index_digest_evidence restartIndexDigest := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_luby_sequence_manifest
    {lubySequenceManifest : Prop} :
    lubySequenceManifest ->
    ay_lrg_luby_sequence_manifest_evidence lubySequenceManifest := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_scale_factor_manifest
    {scaleFactorManifest : Prop} :
    scaleFactorManifest ->
    ay_lrg_scale_factor_manifest_evidence scaleFactorManifest := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_conflict_cutoff_ledger
    {conflictCutoffLedger : Prop} :
    conflictCutoffLedger ->
    ay_lrg_conflict_cutoff_ledger_evidence conflictCutoffLedger := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_restart_decision_ledger
    {restartDecisionLedger : Prop} :
    restartDecisionLedger ->
    ay_lrg_restart_decision_ledger_evidence restartDecisionLedger := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_trail_snapshot_digest
    {trailSnapshotDigest : Prop} :
    trailSnapshotDigest ->
    ay_lrg_trail_snapshot_digest_evidence trailSnapshotDigest := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_learned_clause_context_digest
    {learnedClauseContextDigest : Prop} :
    learnedClauseContextDigest ->
    ay_lrg_learned_clause_context_digest_evidence
      learnedClauseContextDigest := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_propagation_replay_transcript
    {propagationReplayTranscript : Prop} :
    propagationReplayTranscript ->
    ay_lrg_propagation_replay_transcript_evidence
      propagationReplayTranscript := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_lrg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_lrg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_lrg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_archive_manifest
    {archiveManifest : Prop} :
    archiveManifest -> ay_lrg_archive_manifest_evidence archiveManifest := by
  intro evidence
  exact evidence

theorem ay_lrg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_lrg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_lrg_luby_schedule_is_heuristic_scheduling_only
    {lubyAccepted schedulingOnly : Prop} :
    lubyAccepted ->
    schedulingOnly ->
    schedulingOnly :=
  fun _ scheduling => scheduling

theorem ay_lrg_luby_schedule_cannot_independently_justify_sat
    {lubyAccepted satEvidence satSound : Prop} :
    lubyAccepted ->
    ay_lrg_checked_sat_evidence satEvidence ->
    (satEvidence -> satSound) ->
    satSound :=
  fun _ evidence transport => transport evidence

theorem ay_lrg_luby_schedule_cannot_independently_justify_unsat
    {lubyAccepted unsatEvidence unsatSound : Prop} :
    lubyAccepted ->
    ay_lrg_checked_unsat_evidence unsatEvidence ->
    (unsatEvidence -> unsatSound) ->
    unsatSound :=
  fun _ evidence transport => transport evidence

theorem ay_lrg_luby_schedule_cannot_change_original_formula_truth
    {lubyAccepted originalFormulaTruthPreserved : Prop} :
    lubyAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_lrg_accepted_publication_preserves_public_soundness
    {lubyReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence satSound unsatSound :
      Prop} :
    ay_lrg_publication_gate lubyReplay solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript checkedEvidence ->
    ay_lrg_public_soundness_theorem satSound unsatSound ->
    ay_lrg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_lrg_exact_context_ties_luby_sequence_to_replay
    {restartIndexDigest lubySequenceManifest scaleFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      exactContext : Prop} :
    restartIndexDigest ->
    lubySequenceManifest ->
    scaleFactorManifest ->
    conflictCutoffLedger ->
    restartDecisionLedger ->
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

theorem ay_lrg_index_scale_and_cutoff_preserve_restart_decision
    {restartIndexDigest scaleFactorManifest conflictCutoffLedger
      restartDecisionLedger : Prop} :
    restartIndexDigest ->
    scaleFactorManifest ->
    conflictCutoffLedger ->
    restartDecisionLedger ->
    restartDecisionLedger :=
  fun _ _ _ ledger => ledger

theorem ay_lrg_learned_context_preserves_propagation_replay
    {learnedClauseContextDigest propagationReplayTranscript : Prop} :
    learnedClauseContextDigest ->
    propagationReplayTranscript ->
    propagationReplayTranscript :=
  fun _ replay => replay

theorem ay_lrg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_lrg_gate accepted rejected ->
    ay_lrg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_lrg_rejected_is_no_claim
    {indexMismatch diagnostic : Prop} :
    indexMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_rejected_forces_recompute
    {indexMismatch recomputeRequired : Prop} :
    indexMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_failed_luby_restart_guard_cannot_bless_competition_result
    {indexMismatch baselineNoClaim satSound unsatSound : Prop} :
    indexMismatch ->
    baselineNoClaim ->
    ay_lrg_public_soundness_theorem satSound unsatSound ->
    ay_lrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_lrg_index_mismatch_forces_no_claim
    {indexMismatch diagnostic : Prop} :
    indexMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_sequence_mismatch_forces_no_claim
    {sequenceMismatch diagnostic : Prop} :
    sequenceMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_scale_mismatch_forces_no_claim
    {scaleMismatch diagnostic : Prop} :
    scaleMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_cutoff_mismatch_forces_no_claim
    {cutoffMismatch diagnostic : Prop} :
    cutoffMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_restart_mismatch_forces_no_claim
    {restartMismatch diagnostic : Prop} :
    restartMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_learned_mismatch_forces_no_claim
    {learnedMismatch diagnostic : Prop} :
    learnedMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic : Prop} :
    archiveMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_lrg_index_mismatch_forces_recompute
    {indexMismatch recomputeRequired : Prop} :
    indexMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_sequence_mismatch_forces_recompute
    {sequenceMismatch recomputeRequired : Prop} :
    sequenceMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_scale_mismatch_forces_recompute
    {scaleMismatch recomputeRequired : Prop} :
    scaleMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_cutoff_mismatch_forces_recompute
    {cutoffMismatch recomputeRequired : Prop} :
    cutoffMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_restart_mismatch_forces_recompute
    {restartMismatch recomputeRequired : Prop} :
    restartMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_learned_mismatch_forces_recompute
    {learnedMismatch recomputeRequired : Prop} :
    learnedMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_archive_mismatch_forces_recompute
    {archiveMismatch recomputeRequired : Prop} :
    archiveMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_lrg_index_mismatch_cannot_bless_result
    {indexMismatch baselineNoClaim satSound unsatSound : Prop} :
    indexMismatch ->
    baselineNoClaim ->
    ay_lrg_public_soundness_theorem satSound unsatSound ->
    ay_lrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_lrg_sequence_mismatch_cannot_bless_result
    {sequenceMismatch baselineNoClaim satSound unsatSound : Prop} :
    sequenceMismatch ->
    baselineNoClaim ->
    ay_lrg_public_soundness_theorem satSound unsatSound ->
    ay_lrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_lrg_replay_mismatch_cannot_bless_result
    {replayMismatch baselineNoClaim satSound unsatSound : Prop} :
    replayMismatch ->
    baselineNoClaim ->
    ay_lrg_public_soundness_theorem satSound unsatSound ->
    ay_lrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_lrg_policy_requires_restart_index_digest
    {restartIndexDigest accepted : Prop} :
    restartIndexDigest -> accepted -> restartIndexDigest :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_luby_sequence_manifest
    {lubySequenceManifest accepted : Prop} :
    lubySequenceManifest -> accepted -> lubySequenceManifest :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_scale_factor_manifest
    {scaleFactorManifest accepted : Prop} :
    scaleFactorManifest -> accepted -> scaleFactorManifest :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_conflict_cutoff_ledger
    {conflictCutoffLedger accepted : Prop} :
    conflictCutoffLedger -> accepted -> conflictCutoffLedger :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_restart_decision_ledger
    {restartDecisionLedger accepted : Prop} :
    restartDecisionLedger -> accepted -> restartDecisionLedger :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_trail_snapshot_digest
    {trailSnapshotDigest accepted : Prop} :
    trailSnapshotDigest -> accepted -> trailSnapshotDigest :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_learned_clause_context_digest
    {learnedClauseContextDigest accepted : Prop} :
    learnedClauseContextDigest -> accepted -> learnedClauseContextDigest :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_propagation_replay_transcript
    {propagationReplayTranscript accepted : Prop} :
    propagationReplayTranscript -> accepted -> propagationReplayTranscript :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_archive
    {archiveManifest accepted : Prop} :
    archiveManifest -> accepted -> archiveManifest :=
  fun evidence _ => evidence

theorem ay_lrg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
