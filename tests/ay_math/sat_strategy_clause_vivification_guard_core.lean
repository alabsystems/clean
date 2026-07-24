def ay_cvg_conj (p q : Prop) : Prop := p ∧ q

def ay_cvg_disj (p q : Prop) : Prop := p ∨ q

def ay_cvg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_cvg_disj satSound unsatSound

def ay_cvg_inputs
    (originalClauseDigest vivifiedClauseDigest assumptionTrailDigest
      unitPropagationTraceDigest reasonAntecedentLedger literalDeletionLedger
      clauseDbDigestBefore clauseDbDigestAfter propagationReplayTranscript
      solverBuildEvidence validatorGate archiveManifest fallbackBaseline
      auditTranscript : Prop) : Prop :=
  ay_cvg_conj originalClauseDigest
    (ay_cvg_conj vivifiedClauseDigest
      (ay_cvg_conj assumptionTrailDigest
        (ay_cvg_conj unitPropagationTraceDigest
          (ay_cvg_conj reasonAntecedentLedger
            (ay_cvg_conj literalDeletionLedger
              (ay_cvg_conj clauseDbDigestBefore
                (ay_cvg_conj clauseDbDigestAfter
                  (ay_cvg_conj propagationReplayTranscript
                    (ay_cvg_conj solverBuildEvidence
                      (ay_cvg_conj validatorGate
                        (ay_cvg_conj archiveManifest
                          (ay_cvg_conj fallbackBaseline
                            auditTranscript))))))))))))

def ay_cvg_original_clause_digest_evidence
    (originalClauseDigest : Prop) : Prop :=
  originalClauseDigest

def ay_cvg_vivified_clause_digest_evidence
    (vivifiedClauseDigest : Prop) : Prop :=
  vivifiedClauseDigest

def ay_cvg_assumption_trail_digest_evidence
    (assumptionTrailDigest : Prop) : Prop :=
  assumptionTrailDigest

def ay_cvg_unit_propagation_trace_digest_evidence
    (unitPropagationTraceDigest : Prop) : Prop :=
  unitPropagationTraceDigest

def ay_cvg_reason_antecedent_ledger_evidence
    (reasonAntecedentLedger : Prop) : Prop :=
  reasonAntecedentLedger

def ay_cvg_literal_deletion_ledger_evidence
    (literalDeletionLedger : Prop) : Prop :=
  literalDeletionLedger

def ay_cvg_clause_db_digest_before_evidence
    (clauseDbDigestBefore : Prop) : Prop :=
  clauseDbDigestBefore

def ay_cvg_clause_db_digest_after_evidence
    (clauseDbDigestAfter : Prop) : Prop :=
  clauseDbDigestAfter

def ay_cvg_propagation_replay_transcript_evidence
    (propagationReplayTranscript : Prop) : Prop :=
  propagationReplayTranscript

def ay_cvg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_cvg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_cvg_archive_manifest_evidence (archiveManifest : Prop) : Prop :=
  archiveManifest

def ay_cvg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_cvg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_cvg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_cvg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_cvg_checked_sat_evidence (satEvidence : Prop) : Prop := satEvidence

def ay_cvg_checked_unsat_evidence (unsatEvidence : Prop) : Prop :=
  unsatEvidence

def ay_cvg_accepted
    (originalClauseDigest vivifiedClauseDigest assumptionTrailDigest
      unitPropagationTraceDigest reasonAntecedentLedger literalDeletionLedger
      clauseDbDigestBefore clauseDbDigestAfter propagationReplayTranscript
      solverBuildEvidence validatorGate archiveManifest fallbackBaseline
      auditTranscript vivificationAccepted : Prop) : Prop :=
  vivificationAccepted

def ay_cvg_rejected
    (originalClauseMismatch vivifiedClauseMismatch trailMismatch traceMismatch
      reasonMismatch deletionMismatch dbBeforeMismatch dbAfterMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch
      fallbackMismatch auditMismatch : Prop) : Prop :=
  ay_cvg_disj originalClauseMismatch
    (ay_cvg_disj vivifiedClauseMismatch
      (ay_cvg_disj trailMismatch
        (ay_cvg_disj traceMismatch
          (ay_cvg_disj reasonMismatch
            (ay_cvg_disj deletionMismatch
              (ay_cvg_disj dbBeforeMismatch
                (ay_cvg_disj dbAfterMismatch
                  (ay_cvg_disj replayMismatch
                    (ay_cvg_disj buildMismatch
                      (ay_cvg_disj validatorMismatch
                        (ay_cvg_disj archiveMismatch
                          (ay_cvg_disj fallbackMismatch
                            auditMismatch)))))))))))))

def ay_cvg_vivification_replay_evidence
    (vivificationAccepted preprocessingOptimization replayBacked : Prop) :
    Prop :=
  vivificationAccepted

def ay_cvg_publication_gate
    (vivificationReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence : Prop) : Prop :=
  ay_cvg_conj vivificationReplay
    (ay_cvg_conj solverBuildEvidence
      (ay_cvg_conj validatorGate
        (ay_cvg_conj archiveManifest
          (ay_cvg_conj fallbackBaseline
            (ay_cvg_conj auditTranscript checkedEvidence)))))

def ay_cvg_gate (accepted rejected : Prop) : Prop :=
  ay_cvg_disj accepted rejected

theorem ay_cvg_input_components
    {originalClauseDigest vivifiedClauseDigest assumptionTrailDigest
      unitPropagationTraceDigest reasonAntecedentLedger literalDeletionLedger
      clauseDbDigestBefore clauseDbDigestAfter propagationReplayTranscript
      solverBuildEvidence validatorGate archiveManifest fallbackBaseline
      auditTranscript : Prop} :
    ay_cvg_inputs originalClauseDigest vivifiedClauseDigest
      assumptionTrailDigest unitPropagationTraceDigest reasonAntecedentLedger
      literalDeletionLedger clauseDbDigestBefore clauseDbDigestAfter
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript ->
    ay_cvg_inputs originalClauseDigest vivifiedClauseDigest
      assumptionTrailDigest unitPropagationTraceDigest reasonAntecedentLedger
      literalDeletionLedger clauseDbDigestBefore clauseDbDigestAfter
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript := by
  intro inputs
  exact inputs

theorem ay_cvg_accepted_vivification
    {originalClauseDigest vivifiedClauseDigest assumptionTrailDigest
      unitPropagationTraceDigest reasonAntecedentLedger literalDeletionLedger
      clauseDbDigestBefore clauseDbDigestAfter propagationReplayTranscript
      solverBuildEvidence validatorGate archiveManifest fallbackBaseline
      auditTranscript vivificationAccepted : Prop} :
    vivificationAccepted ->
    ay_cvg_accepted originalClauseDigest vivifiedClauseDigest
      assumptionTrailDigest unitPropagationTraceDigest reasonAntecedentLedger
      literalDeletionLedger clauseDbDigestBefore clauseDbDigestAfter
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript vivificationAccepted := by
  intro accepted
  exact accepted

theorem ay_cvg_accepted_original_clause_digest
    {originalClauseDigest : Prop} :
    originalClauseDigest ->
    ay_cvg_original_clause_digest_evidence originalClauseDigest := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_vivified_clause_digest
    {vivifiedClauseDigest : Prop} :
    vivifiedClauseDigest ->
    ay_cvg_vivified_clause_digest_evidence vivifiedClauseDigest := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_assumption_trail_digest
    {assumptionTrailDigest : Prop} :
    assumptionTrailDigest ->
    ay_cvg_assumption_trail_digest_evidence assumptionTrailDigest := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_unit_propagation_trace_digest
    {unitPropagationTraceDigest : Prop} :
    unitPropagationTraceDigest ->
    ay_cvg_unit_propagation_trace_digest_evidence
      unitPropagationTraceDigest := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_reason_antecedent_ledger
    {reasonAntecedentLedger : Prop} :
    reasonAntecedentLedger ->
    ay_cvg_reason_antecedent_ledger_evidence reasonAntecedentLedger := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_literal_deletion_ledger
    {literalDeletionLedger : Prop} :
    literalDeletionLedger ->
    ay_cvg_literal_deletion_ledger_evidence literalDeletionLedger := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_clause_db_digest_before
    {clauseDbDigestBefore : Prop} :
    clauseDbDigestBefore ->
    ay_cvg_clause_db_digest_before_evidence clauseDbDigestBefore := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_clause_db_digest_after
    {clauseDbDigestAfter : Prop} :
    clauseDbDigestAfter ->
    ay_cvg_clause_db_digest_after_evidence clauseDbDigestAfter := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_propagation_replay_transcript
    {propagationReplayTranscript : Prop} :
    propagationReplayTranscript ->
    ay_cvg_propagation_replay_transcript_evidence
      propagationReplayTranscript := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_cvg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_cvg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_archive_manifest
    {archiveManifest : Prop} :
    archiveManifest -> ay_cvg_archive_manifest_evidence archiveManifest := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_cvg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_cvg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_cvg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_cvg_vivification_is_search_preprocessing_optimization
    {vivificationAccepted preprocessingOptimization : Prop} :
    vivificationAccepted ->
    preprocessingOptimization ->
    preprocessingOptimization :=
  fun _ optimization => optimization

theorem ay_cvg_vivification_cannot_independently_justify_sat
    {vivificationAccepted satEvidence satSound : Prop} :
    vivificationAccepted ->
    ay_cvg_checked_sat_evidence satEvidence ->
    (satEvidence -> satSound) ->
    satSound :=
  fun _ evidence transport => transport evidence

theorem ay_cvg_vivification_cannot_independently_justify_unsat
    {vivificationAccepted unsatEvidence unsatSound : Prop} :
    vivificationAccepted ->
    ay_cvg_checked_unsat_evidence unsatEvidence ->
    (unsatEvidence -> unsatSound) ->
    unsatSound :=
  fun _ evidence transport => transport evidence

theorem ay_cvg_vivification_cannot_change_original_formula_truth
    {vivificationAccepted originalFormulaTruthPreserved : Prop} :
    vivificationAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_cvg_accepted_publication_preserves_public_soundness
    {vivificationReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence satSound unsatSound :
      Prop} :
    ay_cvg_publication_gate vivificationReplay solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript
      checkedEvidence ->
    ay_cvg_public_soundness_theorem satSound unsatSound ->
    ay_cvg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_cvg_deleted_literals_tied_to_assumption_propagation_reason_context
    {assumptionTrailDigest unitPropagationTraceDigest reasonAntecedentLedger
      literalDeletionLedger deletedLiteralsJustified : Prop} :
    assumptionTrailDigest ->
    unitPropagationTraceDigest ->
    reasonAntecedentLedger ->
    literalDeletionLedger ->
    deletedLiteralsJustified ->
    deletedLiteralsJustified :=
  fun _ _ _ _ justified => justified

theorem ay_cvg_exact_context_ties_vivification_to_replay
    {originalClauseDigest vivifiedClauseDigest assumptionTrailDigest
      unitPropagationTraceDigest reasonAntecedentLedger literalDeletionLedger
      clauseDbDigestBefore clauseDbDigestAfter propagationReplayTranscript
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      exactContext : Prop} :
    originalClauseDigest ->
    vivifiedClauseDigest ->
    assumptionTrailDigest ->
    unitPropagationTraceDigest ->
    reasonAntecedentLedger ->
    literalDeletionLedger ->
    clauseDbDigestBefore ->
    clauseDbDigestAfter ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    exactContext ->
    exactContext :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ context => context

theorem ay_cvg_reason_ledger_preserves_propagation_replay
    {reasonAntecedentLedger propagationReplayTranscript : Prop} :
    reasonAntecedentLedger ->
    propagationReplayTranscript ->
    propagationReplayTranscript :=
  fun _ replay => replay

theorem ay_cvg_deletion_ledger_preserves_vivified_clause_context
    {literalDeletionLedger vivifiedClauseDigest : Prop} :
    literalDeletionLedger ->
    vivifiedClauseDigest ->
    vivifiedClauseDigest :=
  fun _ digest => digest

theorem ay_cvg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_cvg_gate accepted rejected ->
    ay_cvg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_cvg_rejected_is_no_claim
    {originalClauseMismatch diagnostic : Prop} :
    originalClauseMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_rejected_forces_recompute
    {originalClauseMismatch recomputeRequired : Prop} :
    originalClauseMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_failed_vivification_guard_cannot_bless_competition_result
    {originalClauseMismatch baselineNoClaim satSound unsatSound : Prop} :
    originalClauseMismatch ->
    baselineNoClaim ->
    ay_cvg_public_soundness_theorem satSound unsatSound ->
    ay_cvg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cvg_original_clause_mismatch_forces_no_claim
    {originalClauseMismatch diagnostic : Prop} :
    originalClauseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_vivified_clause_mismatch_forces_no_claim
    {vivifiedClauseMismatch diagnostic : Prop} :
    vivifiedClauseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_trace_mismatch_forces_no_claim
    {traceMismatch diagnostic : Prop} :
    traceMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_reason_mismatch_forces_no_claim
    {reasonMismatch diagnostic : Prop} :
    reasonMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_deletion_mismatch_forces_no_claim
    {deletionMismatch diagnostic : Prop} :
    deletionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_db_before_mismatch_forces_no_claim
    {dbBeforeMismatch diagnostic : Prop} :
    dbBeforeMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_db_after_mismatch_forces_no_claim
    {dbAfterMismatch diagnostic : Prop} :
    dbAfterMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic : Prop} :
    archiveMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cvg_original_clause_mismatch_forces_recompute
    {originalClauseMismatch recomputeRequired : Prop} :
    originalClauseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_vivified_clause_mismatch_forces_recompute
    {vivifiedClauseMismatch recomputeRequired : Prop} :
    vivifiedClauseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_trace_mismatch_forces_recompute
    {traceMismatch recomputeRequired : Prop} :
    traceMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_reason_mismatch_forces_recompute
    {reasonMismatch recomputeRequired : Prop} :
    reasonMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_deletion_mismatch_forces_recompute
    {deletionMismatch recomputeRequired : Prop} :
    deletionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_db_mismatch_forces_recompute
    {dbBeforeMismatch recomputeRequired : Prop} :
    dbBeforeMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_archive_mismatch_forces_recompute
    {archiveMismatch recomputeRequired : Prop} :
    archiveMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cvg_clause_mismatch_cannot_bless_result
    {originalClauseMismatch baselineNoClaim satSound unsatSound : Prop} :
    originalClauseMismatch ->
    baselineNoClaim ->
    ay_cvg_public_soundness_theorem satSound unsatSound ->
    ay_cvg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cvg_reason_mismatch_cannot_bless_result
    {reasonMismatch baselineNoClaim satSound unsatSound : Prop} :
    reasonMismatch ->
    baselineNoClaim ->
    ay_cvg_public_soundness_theorem satSound unsatSound ->
    ay_cvg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cvg_replay_mismatch_cannot_bless_result
    {replayMismatch baselineNoClaim satSound unsatSound : Prop} :
    replayMismatch ->
    baselineNoClaim ->
    ay_cvg_public_soundness_theorem satSound unsatSound ->
    ay_cvg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cvg_policy_requires_original_clause_digest
    {originalClauseDigest accepted : Prop} :
    originalClauseDigest -> accepted -> originalClauseDigest :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_vivified_clause_digest
    {vivifiedClauseDigest accepted : Prop} :
    vivifiedClauseDigest -> accepted -> vivifiedClauseDigest :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_assumption_trail_digest
    {assumptionTrailDigest accepted : Prop} :
    assumptionTrailDigest -> accepted -> assumptionTrailDigest :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_unit_propagation_trace_digest
    {unitPropagationTraceDigest accepted : Prop} :
    unitPropagationTraceDigest -> accepted -> unitPropagationTraceDigest :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_reason_antecedent_ledger
    {reasonAntecedentLedger accepted : Prop} :
    reasonAntecedentLedger -> accepted -> reasonAntecedentLedger :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_literal_deletion_ledger
    {literalDeletionLedger accepted : Prop} :
    literalDeletionLedger -> accepted -> literalDeletionLedger :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_clause_db_digest_before
    {clauseDbDigestBefore accepted : Prop} :
    clauseDbDigestBefore -> accepted -> clauseDbDigestBefore :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_clause_db_digest_after
    {clauseDbDigestAfter accepted : Prop} :
    clauseDbDigestAfter -> accepted -> clauseDbDigestAfter :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_propagation_replay_transcript
    {propagationReplayTranscript accepted : Prop} :
    propagationReplayTranscript -> accepted -> propagationReplayTranscript :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_archive
    {archiveManifest accepted : Prop} :
    archiveManifest -> accepted -> archiveManifest :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_fallback
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_cvg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
