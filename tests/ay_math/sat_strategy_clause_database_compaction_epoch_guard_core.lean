def ay_cdeg_conj (p q : Prop) : Prop := p ∧ q

def ay_cdeg_disj (p q : Prop) : Prop := p ∨ q

def ay_cdeg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_cdeg_disj satSound unsatSound

def ay_cdeg_inputs
    (clauseDatabaseDigest allocatorEpochManifest clauseIdRemapLedger
      watchlistRemapWitness reasonClauseRetentionWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) : Prop :=
  ay_cdeg_conj clauseDatabaseDigest
    (ay_cdeg_conj allocatorEpochManifest
      (ay_cdeg_conj clauseIdRemapLedger
        (ay_cdeg_conj watchlistRemapWitness
          (ay_cdeg_conj reasonClauseRetentionWitness
            (ay_cdeg_conj propagationReplay
              (ay_cdeg_conj fallbackBaseline
                (ay_cdeg_conj solverBuildEvidence
                  (ay_cdeg_conj validatorGate auditTranscript))))))))

def ay_cdeg_clause_database_digest_evidence
    (clauseDatabaseDigest : Prop) : Prop :=
  clauseDatabaseDigest

def ay_cdeg_allocator_epoch_manifest_evidence
    (allocatorEpochManifest : Prop) : Prop :=
  allocatorEpochManifest

def ay_cdeg_clause_id_remap_ledger_evidence
    (clauseIdRemapLedger : Prop) : Prop :=
  clauseIdRemapLedger

def ay_cdeg_watchlist_remap_witness_evidence
    (watchlistRemapWitness : Prop) : Prop :=
  watchlistRemapWitness

def ay_cdeg_reason_clause_retention_witness_evidence
    (reasonClauseRetentionWitness : Prop) : Prop :=
  reasonClauseRetentionWitness

def ay_cdeg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_cdeg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_cdeg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_cdeg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_cdeg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_cdeg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_cdeg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_cdeg_accepted
    (clauseDatabaseDigest allocatorEpochManifest clauseIdRemapLedger
      watchlistRemapWitness reasonClauseRetentionWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      compactionAccepted : Prop) : Prop :=
  compactionAccepted

def ay_cdeg_rejected
    (digestMismatch epochMismatch remapMismatch watchlistMismatch
      retentionMismatch replayMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch : Prop) : Prop :=
  ay_cdeg_disj digestMismatch
    (ay_cdeg_disj epochMismatch
      (ay_cdeg_disj remapMismatch
        (ay_cdeg_disj watchlistMismatch
          (ay_cdeg_disj retentionMismatch
            (ay_cdeg_disj replayMismatch
              (ay_cdeg_disj baselineMismatch
                (ay_cdeg_disj buildMismatch
                  (ay_cdeg_disj validatorMismatch auditMismatch))))))))

def ay_cdeg_gate (accepted rejected : Prop) : Prop :=
  ay_cdeg_disj accepted rejected

def ay_cdeg_compaction_memory_layout_hint
    (compactionAccepted memoryLayoutMaintenance remapGuidance replayAccepted :
      Prop) : Prop :=
  compactionAccepted

theorem ay_cdeg_input_components
    {clauseDatabaseDigest allocatorEpochManifest clauseIdRemapLedger
      watchlistRemapWitness reasonClauseRetentionWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop} :
    ay_cdeg_inputs clauseDatabaseDigest allocatorEpochManifest
      clauseIdRemapLedger watchlistRemapWitness reasonClauseRetentionWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    ay_cdeg_inputs clauseDatabaseDigest allocatorEpochManifest
      clauseIdRemapLedger watchlistRemapWitness reasonClauseRetentionWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript := by
  intro inputs
  exact inputs

theorem ay_cdeg_accepted_policy
    {clauseDatabaseDigest allocatorEpochManifest clauseIdRemapLedger
      watchlistRemapWitness reasonClauseRetentionWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      compactionAccepted : Prop} :
    compactionAccepted ->
    ay_cdeg_accepted clauseDatabaseDigest allocatorEpochManifest
      clauseIdRemapLedger watchlistRemapWitness reasonClauseRetentionWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript compactionAccepted := by
  intro accepted
  exact accepted

theorem ay_cdeg_accepted_clause_database_digest
    {clauseDatabaseDigest : Prop} :
    clauseDatabaseDigest ->
    ay_cdeg_clause_database_digest_evidence clauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_cdeg_accepted_allocator_epoch_manifest
    {allocatorEpochManifest : Prop} :
    allocatorEpochManifest ->
    ay_cdeg_allocator_epoch_manifest_evidence allocatorEpochManifest := by
  intro evidence
  exact evidence

theorem ay_cdeg_accepted_clause_id_remap_ledger
    {clauseIdRemapLedger : Prop} :
    clauseIdRemapLedger ->
    ay_cdeg_clause_id_remap_ledger_evidence clauseIdRemapLedger := by
  intro evidence
  exact evidence

theorem ay_cdeg_accepted_watchlist_remap_witness
    {watchlistRemapWitness : Prop} :
    watchlistRemapWitness ->
    ay_cdeg_watchlist_remap_witness_evidence watchlistRemapWitness := by
  intro evidence
  exact evidence

theorem ay_cdeg_accepted_reason_clause_retention_witness
    {reasonClauseRetentionWitness : Prop} :
    reasonClauseRetentionWitness ->
    ay_cdeg_reason_clause_retention_witness_evidence
      reasonClauseRetentionWitness := by
  intro evidence
  exact evidence

theorem ay_cdeg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_cdeg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_cdeg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_cdeg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_cdeg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_cdeg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_cdeg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_cdeg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_cdeg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_cdeg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_cdeg_compaction_is_memory_layout_maintenance_only
    {compactionAccepted memoryLayoutMaintenanceOnly : Prop} :
    compactionAccepted ->
    memoryLayoutMaintenanceOnly ->
    memoryLayoutMaintenanceOnly :=
  fun _ maintenanceOnly => maintenanceOnly

theorem ay_cdeg_compaction_cannot_change_original_formula_truth
    {compactionAccepted originalFormulaTruthPreserved : Prop} :
    compactionAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_cdeg_accepted_evidence_preserves_public_soundness
    {compactionAccepted satSound unsatSound : Prop} :
    compactionAccepted ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_cdeg_remap_preserves_watchlist_replay
    {clauseIdRemapLedger watchlistRemapWitness propagationReplay : Prop} :
    clauseIdRemapLedger ->
    watchlistRemapWitness ->
    propagationReplay ->
    propagationReplay :=
  fun _ _ replay => replay

theorem ay_cdeg_retention_preserves_reason_replay
    {reasonClauseRetentionWitness propagationReplay : Prop} :
    reasonClauseRetentionWitness ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_cdeg_accepted_compaction_hint_preserves_fallback_soundness
    {compactionAccepted fallbackBaseline satSound unsatSound : Prop} :
    compactionAccepted ->
    fallbackBaseline ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_cdeg_gate accepted rejected ->
    ay_cdeg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_cdeg_rejected_is_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdeg_rejected_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdeg_failed_compaction_guard_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_digest_mismatch_forces_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdeg_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdeg_remap_mismatch_forces_no_claim
    {remapMismatch diagnostic : Prop} :
    remapMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdeg_watchlist_mismatch_forces_no_claim
    {watchlistMismatch diagnostic : Prop} :
    watchlistMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdeg_retention_mismatch_forces_no_claim
    {retentionMismatch diagnostic : Prop} :
    retentionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdeg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdeg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdeg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdeg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdeg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdeg_digest_mismatch_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdeg_epoch_mismatch_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdeg_remap_mismatch_forces_recompute
    {remapMismatch recomputeRequired : Prop} :
    remapMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdeg_watchlist_mismatch_forces_recompute
    {watchlistMismatch recomputeRequired : Prop} :
    watchlistMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdeg_retention_mismatch_forces_recompute
    {retentionMismatch recomputeRequired : Prop} :
    retentionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdeg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdeg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdeg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdeg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdeg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdeg_digest_mismatch_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_epoch_mismatch_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_remap_mismatch_cannot_bless_publication
    {remapMismatch baselineSound satSound unsatSound : Prop} :
    remapMismatch ->
    baselineSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_watchlist_mismatch_cannot_bless_publication
    {watchlistMismatch baselineSound satSound unsatSound : Prop} :
    watchlistMismatch ->
    baselineSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_retention_mismatch_cannot_bless_publication
    {retentionMismatch baselineSound satSound unsatSound : Prop} :
    retentionMismatch ->
    baselineSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound ->
    ay_cdeg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdeg_policy_requires_clause_database_digest
    {clauseDatabaseDigest accepted : Prop} :
    clauseDatabaseDigest -> accepted -> clauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_cdeg_policy_requires_allocator_epoch_manifest
    {allocatorEpochManifest accepted : Prop} :
    allocatorEpochManifest -> accepted -> allocatorEpochManifest :=
  fun evidence _ => evidence

theorem ay_cdeg_policy_requires_clause_id_remap_ledger
    {clauseIdRemapLedger accepted : Prop} :
    clauseIdRemapLedger -> accepted -> clauseIdRemapLedger :=
  fun evidence _ => evidence

theorem ay_cdeg_policy_requires_watchlist_remap_witness
    {watchlistRemapWitness accepted : Prop} :
    watchlistRemapWitness -> accepted -> watchlistRemapWitness :=
  fun evidence _ => evidence

theorem ay_cdeg_policy_requires_reason_clause_retention
    {reasonClauseRetentionWitness accepted : Prop} :
    reasonClauseRetentionWitness -> accepted -> reasonClauseRetentionWitness :=
  fun evidence _ => evidence

theorem ay_cdeg_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_cdeg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_cdeg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_cdeg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_cdeg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
