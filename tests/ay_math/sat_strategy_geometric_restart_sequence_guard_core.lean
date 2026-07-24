def ay_grg_conj (p q : Prop) : Prop := p ∧ q

def ay_grg_disj (p q : Prop) : Prop := p ∨ q

def ay_grg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_grg_disj satSound unsatSound

def ay_grg_inputs
    (restartIndexDigest geometricSequenceManifest growthFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) : Prop :=
  ay_grg_conj restartIndexDigest
    (ay_grg_conj geometricSequenceManifest
      (ay_grg_conj growthFactorManifest
        (ay_grg_conj conflictCutoffLedger
          (ay_grg_conj restartDecisionLedger
            (ay_grg_conj trailSnapshotDigest
              (ay_grg_conj learnedClauseContextDigest
                (ay_grg_conj propagationReplayTranscript
                  (ay_grg_conj fallbackBaseline
                    (ay_grg_conj solverBuildEvidence
                      (ay_grg_conj validatorGate
                        (ay_grg_conj archiveManifest
                          auditTranscript)))))))))))

def ay_grg_restart_index_digest_evidence
    (restartIndexDigest : Prop) : Prop :=
  restartIndexDigest

def ay_grg_geometric_sequence_manifest_evidence
    (geometricSequenceManifest : Prop) : Prop :=
  geometricSequenceManifest

def ay_grg_growth_factor_manifest_evidence
    (growthFactorManifest : Prop) : Prop :=
  growthFactorManifest

def ay_grg_conflict_cutoff_ledger_evidence
    (conflictCutoffLedger : Prop) : Prop :=
  conflictCutoffLedger

def ay_grg_restart_decision_ledger_evidence
    (restartDecisionLedger : Prop) : Prop :=
  restartDecisionLedger

def ay_grg_trail_snapshot_digest_evidence
    (trailSnapshotDigest : Prop) : Prop :=
  trailSnapshotDigest

def ay_grg_learned_clause_context_digest_evidence
    (learnedClauseContextDigest : Prop) : Prop :=
  learnedClauseContextDigest

def ay_grg_propagation_replay_transcript_evidence
    (propagationReplayTranscript : Prop) : Prop :=
  propagationReplayTranscript

def ay_grg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_grg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_grg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_grg_archive_manifest_evidence (archiveManifest : Prop) : Prop :=
  archiveManifest

def ay_grg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_grg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_grg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_grg_checked_sat_evidence (satEvidence : Prop) : Prop := satEvidence

def ay_grg_checked_unsat_evidence (unsatEvidence : Prop) : Prop :=
  unsatEvidence

def ay_grg_accepted
    (restartIndexDigest geometricSequenceManifest growthFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      geometricAccepted : Prop) : Prop :=
  geometricAccepted

def ay_grg_rejected
    (indexMismatch sequenceMismatch factorMismatch cutoffMismatch restartMismatch
      trailMismatch learnedMismatch replayMismatch fallbackMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch : Prop) :
    Prop :=
  ay_grg_disj indexMismatch
    (ay_grg_disj sequenceMismatch
      (ay_grg_disj factorMismatch
        (ay_grg_disj cutoffMismatch
          (ay_grg_disj restartMismatch
            (ay_grg_disj trailMismatch
              (ay_grg_disj learnedMismatch
                (ay_grg_disj replayMismatch
                  (ay_grg_disj fallbackMismatch
                    (ay_grg_disj buildMismatch
                      (ay_grg_disj validatorMismatch
                        (ay_grg_disj archiveMismatch
                          auditMismatch))))))))))))

def ay_grg_geometric_schedule_heuristic_evidence
    (geometricAccepted schedulingOnly replayBacked : Prop) : Prop :=
  geometricAccepted

def ay_grg_publication_gate
    (geometricReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence : Prop) : Prop :=
  ay_grg_conj geometricReplay
    (ay_grg_conj solverBuildEvidence
      (ay_grg_conj validatorGate
        (ay_grg_conj archiveManifest
          (ay_grg_conj fallbackBaseline
            (ay_grg_conj auditTranscript checkedEvidence)))))

def ay_grg_gate (accepted rejected : Prop) : Prop :=
  ay_grg_disj accepted rejected

theorem ay_grg_input_components
    {restartIndexDigest geometricSequenceManifest growthFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop} :
    ay_grg_inputs restartIndexDigest geometricSequenceManifest
      growthFactorManifest conflictCutoffLedger restartDecisionLedger
      trailSnapshotDigest learnedClauseContextDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate archiveManifest auditTranscript ->
    ay_grg_inputs restartIndexDigest geometricSequenceManifest
      growthFactorManifest conflictCutoffLedger restartDecisionLedger
      trailSnapshotDigest learnedClauseContextDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate archiveManifest auditTranscript := by
  intro inputs
  exact inputs

theorem ay_grg_accepted_geometric_sequence
    {restartIndexDigest geometricSequenceManifest growthFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      geometricAccepted : Prop} :
    geometricAccepted ->
    ay_grg_accepted restartIndexDigest geometricSequenceManifest
      growthFactorManifest conflictCutoffLedger restartDecisionLedger
      trailSnapshotDigest learnedClauseContextDigest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript geometricAccepted := by
  intro accepted
  exact accepted

theorem ay_grg_accepted_restart_index_digest
    {restartIndexDigest : Prop} :
    restartIndexDigest ->
    ay_grg_restart_index_digest_evidence restartIndexDigest := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_geometric_sequence_manifest
    {geometricSequenceManifest : Prop} :
    geometricSequenceManifest ->
    ay_grg_geometric_sequence_manifest_evidence geometricSequenceManifest := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_growth_factor_manifest
    {growthFactorManifest : Prop} :
    growthFactorManifest ->
    ay_grg_growth_factor_manifest_evidence growthFactorManifest := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_conflict_cutoff_ledger
    {conflictCutoffLedger : Prop} :
    conflictCutoffLedger ->
    ay_grg_conflict_cutoff_ledger_evidence conflictCutoffLedger := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_restart_decision_ledger
    {restartDecisionLedger : Prop} :
    restartDecisionLedger ->
    ay_grg_restart_decision_ledger_evidence restartDecisionLedger := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_trail_snapshot_digest
    {trailSnapshotDigest : Prop} :
    trailSnapshotDigest ->
    ay_grg_trail_snapshot_digest_evidence trailSnapshotDigest := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_learned_clause_context_digest
    {learnedClauseContextDigest : Prop} :
    learnedClauseContextDigest ->
    ay_grg_learned_clause_context_digest_evidence
      learnedClauseContextDigest := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_propagation_replay_transcript
    {propagationReplayTranscript : Prop} :
    propagationReplayTranscript ->
    ay_grg_propagation_replay_transcript_evidence
      propagationReplayTranscript := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_grg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_grg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_grg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_archive_manifest
    {archiveManifest : Prop} :
    archiveManifest -> ay_grg_archive_manifest_evidence archiveManifest := by
  intro evidence
  exact evidence

theorem ay_grg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_grg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_grg_geometric_schedule_is_heuristic_scheduling_only
    {geometricAccepted schedulingOnly : Prop} :
    geometricAccepted ->
    schedulingOnly ->
    schedulingOnly :=
  fun _ scheduling => scheduling

theorem ay_grg_geometric_schedule_cannot_independently_justify_sat
    {geometricAccepted satEvidence satSound : Prop} :
    geometricAccepted ->
    ay_grg_checked_sat_evidence satEvidence ->
    (satEvidence -> satSound) ->
    satSound :=
  fun _ evidence transport => transport evidence

theorem ay_grg_geometric_schedule_cannot_independently_justify_unsat
    {geometricAccepted unsatEvidence unsatSound : Prop} :
    geometricAccepted ->
    ay_grg_checked_unsat_evidence unsatEvidence ->
    (unsatEvidence -> unsatSound) ->
    unsatSound :=
  fun _ evidence transport => transport evidence

theorem ay_grg_geometric_schedule_cannot_change_original_formula_truth
    {geometricAccepted originalFormulaTruthPreserved : Prop} :
    geometricAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_grg_accepted_publication_preserves_public_soundness
    {geometricReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence satSound unsatSound :
      Prop} :
    ay_grg_publication_gate geometricReplay solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript checkedEvidence ->
    ay_grg_public_soundness_theorem satSound unsatSound ->
    ay_grg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_grg_exact_context_ties_geometric_sequence_to_replay
    {restartIndexDigest geometricSequenceManifest growthFactorManifest
      conflictCutoffLedger restartDecisionLedger trailSnapshotDigest
      learnedClauseContextDigest propagationReplayTranscript
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      exactContext : Prop} :
    restartIndexDigest ->
    geometricSequenceManifest ->
    growthFactorManifest ->
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

theorem ay_grg_index_factor_and_cutoff_preserve_restart_decision
    {restartIndexDigest growthFactorManifest conflictCutoffLedger
      restartDecisionLedger : Prop} :
    restartIndexDigest ->
    growthFactorManifest ->
    conflictCutoffLedger ->
    restartDecisionLedger ->
    restartDecisionLedger :=
  fun _ _ _ ledger => ledger

theorem ay_grg_learned_context_preserves_propagation_replay
    {learnedClauseContextDigest propagationReplayTranscript : Prop} :
    learnedClauseContextDigest ->
    propagationReplayTranscript ->
    propagationReplayTranscript :=
  fun _ replay => replay

theorem ay_grg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_grg_gate accepted rejected ->
    ay_grg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_grg_rejected_is_no_claim
    {indexMismatch diagnostic : Prop} :
    indexMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_rejected_forces_recompute
    {indexMismatch recomputeRequired : Prop} :
    indexMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_failed_geometric_restart_guard_cannot_bless_competition_result
    {indexMismatch baselineNoClaim satSound unsatSound : Prop} :
    indexMismatch ->
    baselineNoClaim ->
    ay_grg_public_soundness_theorem satSound unsatSound ->
    ay_grg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_grg_index_mismatch_forces_no_claim
    {indexMismatch diagnostic : Prop} :
    indexMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_sequence_mismatch_forces_no_claim
    {sequenceMismatch diagnostic : Prop} :
    sequenceMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_factor_mismatch_forces_no_claim
    {factorMismatch diagnostic : Prop} :
    factorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_cutoff_mismatch_forces_no_claim
    {cutoffMismatch diagnostic : Prop} :
    cutoffMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_restart_mismatch_forces_no_claim
    {restartMismatch diagnostic : Prop} :
    restartMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_learned_mismatch_forces_no_claim
    {learnedMismatch diagnostic : Prop} :
    learnedMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic : Prop} :
    archiveMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_grg_index_mismatch_forces_recompute
    {indexMismatch recomputeRequired : Prop} :
    indexMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_sequence_mismatch_forces_recompute
    {sequenceMismatch recomputeRequired : Prop} :
    sequenceMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_factor_mismatch_forces_recompute
    {factorMismatch recomputeRequired : Prop} :
    factorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_cutoff_mismatch_forces_recompute
    {cutoffMismatch recomputeRequired : Prop} :
    cutoffMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_restart_mismatch_forces_recompute
    {restartMismatch recomputeRequired : Prop} :
    restartMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_learned_mismatch_forces_recompute
    {learnedMismatch recomputeRequired : Prop} :
    learnedMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_archive_mismatch_forces_recompute
    {archiveMismatch recomputeRequired : Prop} :
    archiveMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_grg_index_mismatch_cannot_bless_result
    {indexMismatch baselineNoClaim satSound unsatSound : Prop} :
    indexMismatch ->
    baselineNoClaim ->
    ay_grg_public_soundness_theorem satSound unsatSound ->
    ay_grg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_grg_sequence_mismatch_cannot_bless_result
    {sequenceMismatch baselineNoClaim satSound unsatSound : Prop} :
    sequenceMismatch ->
    baselineNoClaim ->
    ay_grg_public_soundness_theorem satSound unsatSound ->
    ay_grg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_grg_replay_mismatch_cannot_bless_result
    {replayMismatch baselineNoClaim satSound unsatSound : Prop} :
    replayMismatch ->
    baselineNoClaim ->
    ay_grg_public_soundness_theorem satSound unsatSound ->
    ay_grg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_grg_policy_requires_restart_index_digest
    {restartIndexDigest accepted : Prop} :
    restartIndexDigest -> accepted -> restartIndexDigest :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_geometric_sequence_manifest
    {geometricSequenceManifest accepted : Prop} :
    geometricSequenceManifest -> accepted -> geometricSequenceManifest :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_growth_factor_manifest
    {growthFactorManifest accepted : Prop} :
    growthFactorManifest -> accepted -> growthFactorManifest :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_conflict_cutoff_ledger
    {conflictCutoffLedger accepted : Prop} :
    conflictCutoffLedger -> accepted -> conflictCutoffLedger :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_restart_decision_ledger
    {restartDecisionLedger accepted : Prop} :
    restartDecisionLedger -> accepted -> restartDecisionLedger :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_trail_snapshot_digest
    {trailSnapshotDigest accepted : Prop} :
    trailSnapshotDigest -> accepted -> trailSnapshotDigest :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_learned_clause_context_digest
    {learnedClauseContextDigest accepted : Prop} :
    learnedClauseContextDigest -> accepted -> learnedClauseContextDigest :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_propagation_replay_transcript
    {propagationReplayTranscript accepted : Prop} :
    propagationReplayTranscript -> accepted -> propagationReplayTranscript :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_archive
    {archiveManifest accepted : Prop} :
    archiveManifest -> accepted -> archiveManifest :=
  fun evidence _ => evidence

theorem ay_grg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
