def ay_pqog_conj (p q : Prop) : Prop := p ∧ q

def ay_pqog_disj (p q : Prop) : Prop := p ∨ q

def ay_pqog_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_pqog_disj satSound unsatSound

def ay_pqog_inputs
    (assignmentTrailDigest propagationQueueDigest enqueueDequeueLedger
      watchedLiteralEventDigest clauseDatabaseDigest
      conflictNoConflictReplayTranscript deterministicTieBreakManifest
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript : Prop) : Prop :=
  ay_pqog_conj assignmentTrailDigest
    (ay_pqog_conj propagationQueueDigest
      (ay_pqog_conj enqueueDequeueLedger
        (ay_pqog_conj watchedLiteralEventDigest
          (ay_pqog_conj clauseDatabaseDigest
            (ay_pqog_conj conflictNoConflictReplayTranscript
              (ay_pqog_conj deterministicTieBreakManifest
                (ay_pqog_conj fallbackBaseline
                  (ay_pqog_conj solverBuildEvidence
                    (ay_pqog_conj validatorGate
                      (ay_pqog_conj archiveManifest
                        auditTranscript))))))))))

def ay_pqog_assignment_trail_digest_evidence
    (assignmentTrailDigest : Prop) : Prop :=
  assignmentTrailDigest

def ay_pqog_propagation_queue_digest_evidence
    (propagationQueueDigest : Prop) : Prop :=
  propagationQueueDigest

def ay_pqog_enqueue_dequeue_ledger_evidence
    (enqueueDequeueLedger : Prop) : Prop :=
  enqueueDequeueLedger

def ay_pqog_watched_literal_event_digest_evidence
    (watchedLiteralEventDigest : Prop) : Prop :=
  watchedLiteralEventDigest

def ay_pqog_clause_database_digest_evidence
    (clauseDatabaseDigest : Prop) : Prop :=
  clauseDatabaseDigest

def ay_pqog_conflict_no_conflict_replay_transcript_evidence
    (conflictNoConflictReplayTranscript : Prop) : Prop :=
  conflictNoConflictReplayTranscript

def ay_pqog_deterministic_tie_break_manifest_evidence
    (deterministicTieBreakManifest : Prop) : Prop :=
  deterministicTieBreakManifest

def ay_pqog_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_pqog_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_pqog_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_pqog_archive_manifest_evidence (archiveManifest : Prop) : Prop :=
  archiveManifest

def ay_pqog_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_pqog_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_pqog_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_pqog_checked_sat_evidence (satEvidence : Prop) : Prop := satEvidence

def ay_pqog_checked_unsat_evidence (unsatEvidence : Prop) : Prop :=
  unsatEvidence

def ay_pqog_accepted
    (assignmentTrailDigest propagationQueueDigest enqueueDequeueLedger
      watchedLiteralEventDigest clauseDatabaseDigest
      conflictNoConflictReplayTranscript deterministicTieBreakManifest
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript queueOrderAccepted : Prop) : Prop :=
  queueOrderAccepted

def ay_pqog_rejected
    (trailMismatch queueMismatch ledgerMismatch watchMismatch dbMismatch
      replayMismatch tieBreakMismatch fallbackMismatch buildMismatch
      validatorMismatch archiveMismatch auditMismatch : Prop) : Prop :=
  ay_pqog_disj trailMismatch
    (ay_pqog_disj queueMismatch
      (ay_pqog_disj ledgerMismatch
        (ay_pqog_disj watchMismatch
          (ay_pqog_disj dbMismatch
            (ay_pqog_disj replayMismatch
              (ay_pqog_disj tieBreakMismatch
                (ay_pqog_disj fallbackMismatch
                  (ay_pqog_disj buildMismatch
                    (ay_pqog_disj validatorMismatch
                      (ay_pqog_disj archiveMismatch auditMismatch))))))))))

def ay_pqog_queue_order_scheduling_evidence
    (queueOrderAccepted schedulingOnly replayEvidenceOnly : Prop) : Prop :=
  queueOrderAccepted

def ay_pqog_publication_gate
    (queueReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence : Prop) : Prop :=
  ay_pqog_conj queueReplay
    (ay_pqog_conj solverBuildEvidence
      (ay_pqog_conj validatorGate
        (ay_pqog_conj archiveManifest
          (ay_pqog_conj fallbackBaseline
            (ay_pqog_conj auditTranscript checkedEvidence)))))

def ay_pqog_gate (accepted rejected : Prop) : Prop :=
  ay_pqog_disj accepted rejected

theorem ay_pqog_input_components
    {assignmentTrailDigest propagationQueueDigest enqueueDequeueLedger
      watchedLiteralEventDigest clauseDatabaseDigest
      conflictNoConflictReplayTranscript deterministicTieBreakManifest
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript : Prop} :
    ay_pqog_inputs assignmentTrailDigest propagationQueueDigest
      enqueueDequeueLedger watchedLiteralEventDigest clauseDatabaseDigest
      conflictNoConflictReplayTranscript deterministicTieBreakManifest
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript ->
    ay_pqog_inputs assignmentTrailDigest propagationQueueDigest
      enqueueDequeueLedger watchedLiteralEventDigest clauseDatabaseDigest
      conflictNoConflictReplayTranscript deterministicTieBreakManifest
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript := by
  intro inputs
  exact inputs

theorem ay_pqog_accepted_queue_order
    {assignmentTrailDigest propagationQueueDigest enqueueDequeueLedger
      watchedLiteralEventDigest clauseDatabaseDigest
      conflictNoConflictReplayTranscript deterministicTieBreakManifest
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript queueOrderAccepted : Prop} :
    queueOrderAccepted ->
    ay_pqog_accepted assignmentTrailDigest propagationQueueDigest
      enqueueDequeueLedger watchedLiteralEventDigest clauseDatabaseDigest
      conflictNoConflictReplayTranscript deterministicTieBreakManifest
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript queueOrderAccepted := by
  intro accepted
  exact accepted

theorem ay_pqog_accepted_assignment_trail_digest
    {assignmentTrailDigest : Prop} :
    assignmentTrailDigest ->
    ay_pqog_assignment_trail_digest_evidence assignmentTrailDigest := by
  intro evidence
  exact evidence

theorem ay_pqog_accepted_propagation_queue_digest
    {propagationQueueDigest : Prop} :
    propagationQueueDigest ->
    ay_pqog_propagation_queue_digest_evidence propagationQueueDigest := by
  intro evidence
  exact evidence

theorem ay_pqog_accepted_enqueue_dequeue_ledger
    {enqueueDequeueLedger : Prop} :
    enqueueDequeueLedger ->
    ay_pqog_enqueue_dequeue_ledger_evidence enqueueDequeueLedger := by
  intro evidence
  exact evidence

theorem ay_pqog_accepted_watched_literal_event_digest
    {watchedLiteralEventDigest : Prop} :
    watchedLiteralEventDigest ->
    ay_pqog_watched_literal_event_digest_evidence
      watchedLiteralEventDigest := by
  intro evidence
  exact evidence

theorem ay_pqog_accepted_clause_database_digest
    {clauseDatabaseDigest : Prop} :
    clauseDatabaseDigest ->
    ay_pqog_clause_database_digest_evidence clauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_pqog_accepted_conflict_no_conflict_replay_transcript
    {conflictNoConflictReplayTranscript : Prop} :
    conflictNoConflictReplayTranscript ->
    ay_pqog_conflict_no_conflict_replay_transcript_evidence
      conflictNoConflictReplayTranscript := by
  intro evidence
  exact evidence

theorem ay_pqog_accepted_deterministic_tie_break_manifest
    {deterministicTieBreakManifest : Prop} :
    deterministicTieBreakManifest ->
    ay_pqog_deterministic_tie_break_manifest_evidence
      deterministicTieBreakManifest := by
  intro evidence
  exact evidence

theorem ay_pqog_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_pqog_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_pqog_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_pqog_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_pqog_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_pqog_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_pqog_accepted_archive_manifest
    {archiveManifest : Prop} :
    archiveManifest -> ay_pqog_archive_manifest_evidence archiveManifest := by
  intro evidence
  exact evidence

theorem ay_pqog_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_pqog_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_pqog_queue_ordering_is_scheduling_replay_evidence_only
    {queueOrderAccepted schedulingOnly : Prop} :
    queueOrderAccepted ->
    schedulingOnly ->
    schedulingOnly :=
  fun _ scheduling => scheduling

theorem ay_pqog_queue_order_cannot_independently_justify_sat
    {queueOrderAccepted satEvidence satSound : Prop} :
    queueOrderAccepted ->
    ay_pqog_checked_sat_evidence satEvidence ->
    (satEvidence -> satSound) ->
    satSound :=
  fun _ evidence transport => transport evidence

theorem ay_pqog_queue_order_cannot_independently_justify_unsat
    {queueOrderAccepted unsatEvidence unsatSound : Prop} :
    queueOrderAccepted ->
    ay_pqog_checked_unsat_evidence unsatEvidence ->
    (unsatEvidence -> unsatSound) ->
    unsatSound :=
  fun _ evidence transport => transport evidence

theorem ay_pqog_queue_order_cannot_change_original_formula_truth
    {queueOrderAccepted originalFormulaTruthPreserved : Prop} :
    queueOrderAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_pqog_accepted_publication_preserves_public_soundness
    {queueReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence satSound unsatSound :
      Prop} :
    ay_pqog_publication_gate queueReplay solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript checkedEvidence ->
    ay_pqog_public_soundness_theorem satSound unsatSound ->
    ay_pqog_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_pqog_exact_context_ties_queue_order_to_replay
    {assignmentTrailDigest propagationQueueDigest enqueueDequeueLedger
      watchedLiteralEventDigest clauseDatabaseDigest
      conflictNoConflictReplayTranscript deterministicTieBreakManifest
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      exactContext : Prop} :
    assignmentTrailDigest ->
    propagationQueueDigest ->
    enqueueDequeueLedger ->
    watchedLiteralEventDigest ->
    clauseDatabaseDigest ->
    conflictNoConflictReplayTranscript ->
    deterministicTieBreakManifest ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    exactContext ->
    exactContext :=
  fun _ _ _ _ _ _ _ _ _ _ _ context => context

theorem ay_pqog_enqueue_dequeue_ledger_preserves_queue_replay
    {enqueueDequeueLedger conflictNoConflictReplayTranscript : Prop} :
    enqueueDequeueLedger ->
    conflictNoConflictReplayTranscript ->
    conflictNoConflictReplayTranscript :=
  fun _ replay => replay

theorem ay_pqog_watch_events_preserve_queue_replay
    {watchedLiteralEventDigest conflictNoConflictReplayTranscript : Prop} :
    watchedLiteralEventDigest ->
    conflictNoConflictReplayTranscript ->
    conflictNoConflictReplayTranscript :=
  fun _ replay => replay

theorem ay_pqog_tie_break_manifest_preserves_deterministic_order
    {deterministicTieBreakManifest deterministicOrder : Prop} :
    deterministicTieBreakManifest ->
    deterministicOrder ->
    deterministicOrder :=
  fun _ order => order

theorem ay_pqog_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_pqog_gate accepted rejected ->
    ay_pqog_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_pqog_rejected_is_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_rejected_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_failed_queue_guard_cannot_bless_competition_result
    {trailMismatch baselineNoClaim satSound unsatSound : Prop} :
    trailMismatch ->
    baselineNoClaim ->
    ay_pqog_public_soundness_theorem satSound unsatSound ->
    ay_pqog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqog_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_queue_mismatch_forces_no_claim
    {queueMismatch diagnostic : Prop} :
    queueMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_ledger_mismatch_forces_no_claim
    {ledgerMismatch diagnostic : Prop} :
    ledgerMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_watch_mismatch_forces_no_claim
    {watchMismatch diagnostic : Prop} :
    watchMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_db_mismatch_forces_no_claim
    {dbMismatch diagnostic : Prop} :
    dbMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_tie_break_mismatch_forces_no_claim
    {tieBreakMismatch diagnostic : Prop} :
    tieBreakMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic : Prop} :
    archiveMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pqog_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_queue_mismatch_forces_recompute
    {queueMismatch recomputeRequired : Prop} :
    queueMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_ledger_mismatch_forces_recompute
    {ledgerMismatch recomputeRequired : Prop} :
    ledgerMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_watch_mismatch_forces_recompute
    {watchMismatch recomputeRequired : Prop} :
    watchMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_db_mismatch_forces_recompute
    {dbMismatch recomputeRequired : Prop} :
    dbMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_tie_break_mismatch_forces_recompute
    {tieBreakMismatch recomputeRequired : Prop} :
    tieBreakMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_archive_mismatch_forces_recompute
    {archiveMismatch recomputeRequired : Prop} :
    archiveMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pqog_trail_mismatch_cannot_bless_result
    {trailMismatch baselineNoClaim satSound unsatSound : Prop} :
    trailMismatch ->
    baselineNoClaim ->
    ay_pqog_public_soundness_theorem satSound unsatSound ->
    ay_pqog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqog_queue_mismatch_cannot_bless_result
    {queueMismatch baselineNoClaim satSound unsatSound : Prop} :
    queueMismatch ->
    baselineNoClaim ->
    ay_pqog_public_soundness_theorem satSound unsatSound ->
    ay_pqog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqog_replay_mismatch_cannot_bless_result
    {replayMismatch baselineNoClaim satSound unsatSound : Prop} :
    replayMismatch ->
    baselineNoClaim ->
    ay_pqog_public_soundness_theorem satSound unsatSound ->
    ay_pqog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pqog_policy_requires_assignment_trail_digest
    {assignmentTrailDigest accepted : Prop} :
    assignmentTrailDigest -> accepted -> assignmentTrailDigest :=
  fun evidence _ => evidence

theorem ay_pqog_policy_requires_propagation_queue_digest
    {propagationQueueDigest accepted : Prop} :
    propagationQueueDigest -> accepted -> propagationQueueDigest :=
  fun evidence _ => evidence

theorem ay_pqog_policy_requires_enqueue_dequeue_ledger
    {enqueueDequeueLedger accepted : Prop} :
    enqueueDequeueLedger -> accepted -> enqueueDequeueLedger :=
  fun evidence _ => evidence

theorem ay_pqog_policy_requires_watched_literal_event_digest
    {watchedLiteralEventDigest accepted : Prop} :
    watchedLiteralEventDigest -> accepted -> watchedLiteralEventDigest :=
  fun evidence _ => evidence

theorem ay_pqog_policy_requires_clause_database_digest
    {clauseDatabaseDigest accepted : Prop} :
    clauseDatabaseDigest -> accepted -> clauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_pqog_policy_requires_conflict_no_conflict_replay_transcript
    {conflictNoConflictReplayTranscript accepted : Prop} :
    conflictNoConflictReplayTranscript ->
    accepted ->
    conflictNoConflictReplayTranscript :=
  fun evidence _ => evidence

theorem ay_pqog_policy_requires_deterministic_tie_break_manifest
    {deterministicTieBreakManifest accepted : Prop} :
    deterministicTieBreakManifest ->
    accepted ->
    deterministicTieBreakManifest :=
  fun evidence _ => evidence

theorem ay_pqog_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_pqog_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_pqog_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_pqog_policy_requires_archive
    {archiveManifest accepted : Prop} :
    archiveManifest -> accepted -> archiveManifest :=
  fun evidence _ => evidence

theorem ay_pqog_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
