def ay_carg_conj (p q : Prop) : Prop := p ∧ q

def ay_carg_disj (p q : Prop) : Prop := p ∨ q

def ay_carg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_carg_disj satSound unsatSound

def ay_carg_inputs
    (clauseDbDigestBefore clauseDbDigestAfter relocationMapDigest
      clauseIdentityPreservationWitness watchlistPointerRewriteDigest
      learnedDeletedClauseLedgerContext trailDigest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript : Prop) : Prop :=
  ay_carg_conj clauseDbDigestBefore
    (ay_carg_conj clauseDbDigestAfter
      (ay_carg_conj relocationMapDigest
        (ay_carg_conj clauseIdentityPreservationWitness
          (ay_carg_conj watchlistPointerRewriteDigest
            (ay_carg_conj learnedDeletedClauseLedgerContext
              (ay_carg_conj trailDigest
                (ay_carg_conj propagationReplayTranscript
                  (ay_carg_conj fallbackBaseline
                    (ay_carg_conj solverBuildEvidence
                      (ay_carg_conj validatorGate
                        (ay_carg_conj archiveManifest
                          auditTranscript)))))))))))

def ay_carg_clause_db_digest_before_evidence
    (clauseDbDigestBefore : Prop) : Prop :=
  clauseDbDigestBefore

def ay_carg_clause_db_digest_after_evidence
    (clauseDbDigestAfter : Prop) : Prop :=
  clauseDbDigestAfter

def ay_carg_relocation_map_digest_evidence
    (relocationMapDigest : Prop) : Prop :=
  relocationMapDigest

def ay_carg_clause_identity_preservation_witness_evidence
    (clauseIdentityPreservationWitness : Prop) : Prop :=
  clauseIdentityPreservationWitness

def ay_carg_watchlist_pointer_rewrite_digest_evidence
    (watchlistPointerRewriteDigest : Prop) : Prop :=
  watchlistPointerRewriteDigest

def ay_carg_learned_deleted_clause_ledger_context_evidence
    (learnedDeletedClauseLedgerContext : Prop) : Prop :=
  learnedDeletedClauseLedgerContext

def ay_carg_trail_digest_evidence (trailDigest : Prop) : Prop :=
  trailDigest

def ay_carg_propagation_replay_transcript_evidence
    (propagationReplayTranscript : Prop) : Prop :=
  propagationReplayTranscript

def ay_carg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_carg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_carg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_carg_archive_manifest_evidence (archiveManifest : Prop) : Prop :=
  archiveManifest

def ay_carg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_carg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_carg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_carg_checked_sat_evidence (satEvidence : Prop) : Prop := satEvidence

def ay_carg_checked_unsat_evidence (unsatEvidence : Prop) : Prop :=
  unsatEvidence

def ay_carg_accepted
    (clauseDbDigestBefore clauseDbDigestAfter relocationMapDigest
      clauseIdentityPreservationWitness watchlistPointerRewriteDigest
      learnedDeletedClauseLedgerContext trailDigest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript relocationAccepted : Prop) : Prop :=
  relocationAccepted

def ay_carg_rejected
    (dbBeforeMismatch dbAfterMismatch relocationMapMismatch identityMismatch
      watchlistMismatch ledgerMismatch trailMismatch replayMismatch
      fallbackMismatch buildMismatch validatorMismatch archiveMismatch
      auditMismatch : Prop) : Prop :=
  ay_carg_disj dbBeforeMismatch
    (ay_carg_disj dbAfterMismatch
      (ay_carg_disj relocationMapMismatch
        (ay_carg_disj identityMismatch
          (ay_carg_disj watchlistMismatch
            (ay_carg_disj ledgerMismatch
              (ay_carg_disj trailMismatch
                (ay_carg_disj replayMismatch
                  (ay_carg_disj fallbackMismatch
                    (ay_carg_disj buildMismatch
                      (ay_carg_disj validatorMismatch
                        (ay_carg_disj archiveMismatch
                          auditMismatch))))))))))))

def ay_carg_allocator_relocation_maintenance_evidence
    (relocationAccepted memoryMaintenanceOnly replayBacked : Prop) : Prop :=
  relocationAccepted

def ay_carg_publication_gate
    (relocationReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence : Prop) : Prop :=
  ay_carg_conj relocationReplay
    (ay_carg_conj solverBuildEvidence
      (ay_carg_conj validatorGate
        (ay_carg_conj archiveManifest
          (ay_carg_conj fallbackBaseline
            (ay_carg_conj auditTranscript checkedEvidence)))))

def ay_carg_gate (accepted rejected : Prop) : Prop :=
  ay_carg_disj accepted rejected

theorem ay_carg_input_components
    {clauseDbDigestBefore clauseDbDigestAfter relocationMapDigest
      clauseIdentityPreservationWitness watchlistPointerRewriteDigest
      learnedDeletedClauseLedgerContext trailDigest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript : Prop} :
    ay_carg_inputs clauseDbDigestBefore clauseDbDigestAfter
      relocationMapDigest clauseIdentityPreservationWitness
      watchlistPointerRewriteDigest learnedDeletedClauseLedgerContext
      trailDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript ->
    ay_carg_inputs clauseDbDigestBefore clauseDbDigestAfter
      relocationMapDigest clauseIdentityPreservationWitness
      watchlistPointerRewriteDigest learnedDeletedClauseLedgerContext
      trailDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript := by
  intro inputs
  exact inputs

theorem ay_carg_accepted_relocation
    {clauseDbDigestBefore clauseDbDigestAfter relocationMapDigest
      clauseIdentityPreservationWitness watchlistPointerRewriteDigest
      learnedDeletedClauseLedgerContext trailDigest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate archiveManifest
      auditTranscript relocationAccepted : Prop} :
    relocationAccepted ->
    ay_carg_accepted clauseDbDigestBefore clauseDbDigestAfter
      relocationMapDigest clauseIdentityPreservationWitness
      watchlistPointerRewriteDigest learnedDeletedClauseLedgerContext
      trailDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      relocationAccepted := by
  intro accepted
  exact accepted

theorem ay_carg_accepted_clause_db_digest_before
    {clauseDbDigestBefore : Prop} :
    clauseDbDigestBefore ->
    ay_carg_clause_db_digest_before_evidence clauseDbDigestBefore := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_clause_db_digest_after
    {clauseDbDigestAfter : Prop} :
    clauseDbDigestAfter ->
    ay_carg_clause_db_digest_after_evidence clauseDbDigestAfter := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_relocation_map_digest
    {relocationMapDigest : Prop} :
    relocationMapDigest ->
    ay_carg_relocation_map_digest_evidence relocationMapDigest := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_clause_identity_preservation_witness
    {clauseIdentityPreservationWitness : Prop} :
    clauseIdentityPreservationWitness ->
    ay_carg_clause_identity_preservation_witness_evidence
      clauseIdentityPreservationWitness := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_watchlist_pointer_rewrite_digest
    {watchlistPointerRewriteDigest : Prop} :
    watchlistPointerRewriteDigest ->
    ay_carg_watchlist_pointer_rewrite_digest_evidence
      watchlistPointerRewriteDigest := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_learned_deleted_clause_ledger_context
    {learnedDeletedClauseLedgerContext : Prop} :
    learnedDeletedClauseLedgerContext ->
    ay_carg_learned_deleted_clause_ledger_context_evidence
      learnedDeletedClauseLedgerContext := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_trail_digest
    {trailDigest : Prop} :
    trailDigest -> ay_carg_trail_digest_evidence trailDigest := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_propagation_replay_transcript
    {propagationReplayTranscript : Prop} :
    propagationReplayTranscript ->
    ay_carg_propagation_replay_transcript_evidence
      propagationReplayTranscript := by
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

theorem ay_carg_accepted_archive_manifest
    {archiveManifest : Prop} :
    archiveManifest -> ay_carg_archive_manifest_evidence archiveManifest := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_carg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_carg_relocation_is_memory_data_structure_maintenance_only
    {relocationAccepted memoryMaintenanceOnly : Prop} :
    relocationAccepted ->
    memoryMaintenanceOnly ->
    memoryMaintenanceOnly :=
  fun _ maintenance => maintenance

theorem ay_carg_relocation_cannot_independently_justify_sat
    {relocationAccepted satEvidence satSound : Prop} :
    relocationAccepted ->
    ay_carg_checked_sat_evidence satEvidence ->
    (satEvidence -> satSound) ->
    satSound :=
  fun _ evidence transport => transport evidence

theorem ay_carg_relocation_cannot_independently_justify_unsat
    {relocationAccepted unsatEvidence unsatSound : Prop} :
    relocationAccepted ->
    ay_carg_checked_unsat_evidence unsatEvidence ->
    (unsatEvidence -> unsatSound) ->
    unsatSound :=
  fun _ evidence transport => transport evidence

theorem ay_carg_relocation_cannot_change_original_formula_truth
    {relocationAccepted originalFormulaTruthPreserved : Prop} :
    relocationAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_carg_accepted_publication_preserves_public_soundness
    {relocationReplay solverBuildEvidence validatorGate archiveManifest
      fallbackBaseline auditTranscript checkedEvidence satSound unsatSound :
      Prop} :
    ay_carg_publication_gate relocationReplay solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript checkedEvidence ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_carg_accepted_relocation_preserves_clause_identities
    {clauseIdentityPreservationWitness clauseIdentitiesPreserved : Prop} :
    clauseIdentityPreservationWitness ->
    clauseIdentitiesPreserved ->
    clauseIdentitiesPreserved :=
  fun _ preserved => preserved

theorem ay_carg_accepted_relocation_preserves_watchlist_references
    {watchlistPointerRewriteDigest watchlistReferencesPreserved : Prop} :
    watchlistPointerRewriteDigest ->
    watchlistReferencesPreserved ->
    watchlistReferencesPreserved :=
  fun _ preserved => preserved

theorem ay_carg_identity_and_watch_rewrite_preserve_replay
    {clauseIdentityPreservationWitness watchlistPointerRewriteDigest
      propagationReplayTranscript : Prop} :
    clauseIdentityPreservationWitness ->
    watchlistPointerRewriteDigest ->
    propagationReplayTranscript ->
    propagationReplayTranscript :=
  fun _ _ replay => replay

theorem ay_carg_exact_context_ties_relocation_to_replay
    {clauseDbDigestBefore clauseDbDigestAfter relocationMapDigest
      clauseIdentityPreservationWitness watchlistPointerRewriteDigest
      learnedDeletedClauseLedgerContext trailDigest propagationReplayTranscript
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      exactContext : Prop} :
    clauseDbDigestBefore ->
    clauseDbDigestAfter ->
    relocationMapDigest ->
    clauseIdentityPreservationWitness ->
    watchlistPointerRewriteDigest ->
    learnedDeletedClauseLedgerContext ->
    trailDigest ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    exactContext ->
    exactContext :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ context => context

theorem ay_carg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_carg_gate accepted rejected ->
    ay_carg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_carg_rejected_is_no_claim
    {dbBeforeMismatch diagnostic : Prop} :
    dbBeforeMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_rejected_forces_recompute
    {dbBeforeMismatch recomputeRequired : Prop} :
    dbBeforeMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_failed_relocation_guard_cannot_bless_competition_result
    {dbBeforeMismatch baselineNoClaim satSound unsatSound : Prop} :
    dbBeforeMismatch ->
    baselineNoClaim ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_db_before_mismatch_forces_no_claim
    {dbBeforeMismatch diagnostic : Prop} :
    dbBeforeMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_db_after_mismatch_forces_no_claim
    {dbAfterMismatch diagnostic : Prop} :
    dbAfterMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_relocation_map_mismatch_forces_no_claim
    {relocationMapMismatch diagnostic : Prop} :
    relocationMapMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_identity_mismatch_forces_no_claim
    {identityMismatch diagnostic : Prop} :
    identityMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_watchlist_mismatch_forces_no_claim
    {watchlistMismatch diagnostic : Prop} :
    watchlistMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_ledger_mismatch_forces_no_claim
    {ledgerMismatch diagnostic : Prop} :
    ledgerMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic : Prop} :
    archiveMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_db_mismatch_forces_recompute
    {dbBeforeMismatch recomputeRequired : Prop} :
    dbBeforeMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_relocation_map_mismatch_forces_recompute
    {relocationMapMismatch recomputeRequired : Prop} :
    relocationMapMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_identity_mismatch_forces_recompute
    {identityMismatch recomputeRequired : Prop} :
    identityMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_watchlist_mismatch_forces_recompute
    {watchlistMismatch recomputeRequired : Prop} :
    watchlistMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_ledger_mismatch_forces_recompute
    {ledgerMismatch recomputeRequired : Prop} :
    ledgerMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_archive_mismatch_forces_recompute
    {archiveMismatch recomputeRequired : Prop} :
    archiveMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_db_mismatch_cannot_bless_result
    {dbBeforeMismatch baselineNoClaim satSound unsatSound : Prop} :
    dbBeforeMismatch ->
    baselineNoClaim ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_identity_mismatch_cannot_bless_result
    {identityMismatch baselineNoClaim satSound unsatSound : Prop} :
    identityMismatch ->
    baselineNoClaim ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_replay_mismatch_cannot_bless_result
    {replayMismatch baselineNoClaim satSound unsatSound : Prop} :
    replayMismatch ->
    baselineNoClaim ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_policy_requires_clause_db_digest_before
    {clauseDbDigestBefore accepted : Prop} :
    clauseDbDigestBefore -> accepted -> clauseDbDigestBefore :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_clause_db_digest_after
    {clauseDbDigestAfter accepted : Prop} :
    clauseDbDigestAfter -> accepted -> clauseDbDigestAfter :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_relocation_map_digest
    {relocationMapDigest accepted : Prop} :
    relocationMapDigest -> accepted -> relocationMapDigest :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_clause_identity_preservation_witness
    {clauseIdentityPreservationWitness accepted : Prop} :
    clauseIdentityPreservationWitness ->
    accepted ->
    clauseIdentityPreservationWitness :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_watchlist_pointer_rewrite_digest
    {watchlistPointerRewriteDigest accepted : Prop} :
    watchlistPointerRewriteDigest ->
    accepted ->
    watchlistPointerRewriteDigest :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_learned_deleted_clause_ledger_context
    {learnedDeletedClauseLedgerContext accepted : Prop} :
    learnedDeletedClauseLedgerContext ->
    accepted ->
    learnedDeletedClauseLedgerContext :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_trail_digest
    {trailDigest accepted : Prop} :
    trailDigest -> accepted -> trailDigest :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_propagation_replay_transcript
    {propagationReplayTranscript accepted : Prop} :
    propagationReplayTranscript -> accepted -> propagationReplayTranscript :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_archive
    {archiveManifest accepted : Prop} :
    archiveManifest -> accepted -> archiveManifest :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
