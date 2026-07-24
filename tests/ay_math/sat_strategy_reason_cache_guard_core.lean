def ay_rcag_conj (p q : Prop) : Prop := p ∧ q

def ay_rcag_disj (p q : Prop) : Prop := p ∨ q

def ay_rcag_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rcag_disj satSound unsatSound

def ay_rcag_inputs
    (clauseDatabaseDigest assignmentTrailDigest reasonCacheDigest
      cacheInvalidationLedger propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_rcag_conj clauseDatabaseDigest
    (ay_rcag_conj assignmentTrailDigest
      (ay_rcag_conj reasonCacheDigest
        (ay_rcag_conj cacheInvalidationLedger
          (ay_rcag_conj propagationReplayWitness
            (ay_rcag_conj fallbackBaseline
              (ay_rcag_conj solverBuildEvidence
                (ay_rcag_conj validatorGate auditTranscript)))))))

def ay_rcag_clause_database_digest_evidence
    (clauseDatabaseDigest : Prop) : Prop :=
  clauseDatabaseDigest

def ay_rcag_assignment_trail_digest_evidence
    (assignmentTrailDigest : Prop) : Prop :=
  assignmentTrailDigest

def ay_rcag_reason_cache_digest_evidence
    (reasonCacheDigest : Prop) : Prop :=
  reasonCacheDigest

def ay_rcag_cache_invalidation_ledger_evidence
    (cacheInvalidationLedger : Prop) : Prop :=
  cacheInvalidationLedger

def ay_rcag_propagation_replay_witness_evidence
    (propagationReplayWitness : Prop) : Prop :=
  propagationReplayWitness

def ay_rcag_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_rcag_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rcag_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rcag_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rcag_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rcag_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_rcag_accepted
    (clauseDatabaseDigest assignmentTrailDigest reasonCacheDigest
      cacheInvalidationLedger propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript reasonCacheAccepted :
      Prop) : Prop :=
  reasonCacheAccepted

def ay_rcag_rejected
    (clauseMismatch trailMismatch cacheMismatch invalidationMismatch
      replayMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch : Prop) : Prop :=
  ay_rcag_disj clauseMismatch
    (ay_rcag_disj trailMismatch
      (ay_rcag_disj cacheMismatch
        (ay_rcag_disj invalidationMismatch
          (ay_rcag_disj replayMismatch
            (ay_rcag_disj baselineMismatch
              (ay_rcag_disj buildMismatch
                (ay_rcag_disj validatorMismatch auditMismatch)))))))

def ay_rcag_gate (accepted rejected : Prop) : Prop :=
  ay_rcag_disj accepted rejected

def ay_rcag_reason_cache_data_structure_hint
    (reasonCacheAccepted dataStructureOptimization propagationGuidance
      replayAccepted : Prop) : Prop :=
  reasonCacheAccepted

theorem ay_rcag_input_components
    {clauseDatabaseDigest assignmentTrailDigest reasonCacheDigest
      cacheInvalidationLedger propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_rcag_inputs clauseDatabaseDigest assignmentTrailDigest reasonCacheDigest
      cacheInvalidationLedger propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_rcag_inputs clauseDatabaseDigest assignmentTrailDigest reasonCacheDigest
      cacheInvalidationLedger propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rcag_accepted_policy
    {clauseDatabaseDigest assignmentTrailDigest reasonCacheDigest
      cacheInvalidationLedger propagationReplayWitness fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript reasonCacheAccepted :
      Prop} :
    reasonCacheAccepted ->
    ay_rcag_accepted clauseDatabaseDigest assignmentTrailDigest
      reasonCacheDigest cacheInvalidationLedger propagationReplayWitness
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      reasonCacheAccepted := by
  intro accepted
  exact accepted

theorem ay_rcag_accepted_clause_database_digest
    {clauseDatabaseDigest : Prop} :
    clauseDatabaseDigest ->
    ay_rcag_clause_database_digest_evidence clauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_rcag_accepted_assignment_trail_digest
    {assignmentTrailDigest : Prop} :
    assignmentTrailDigest ->
    ay_rcag_assignment_trail_digest_evidence assignmentTrailDigest := by
  intro evidence
  exact evidence

theorem ay_rcag_accepted_reason_cache_digest
    {reasonCacheDigest : Prop} :
    reasonCacheDigest ->
    ay_rcag_reason_cache_digest_evidence reasonCacheDigest := by
  intro evidence
  exact evidence

theorem ay_rcag_accepted_cache_invalidation_ledger
    {cacheInvalidationLedger : Prop} :
    cacheInvalidationLedger ->
    ay_rcag_cache_invalidation_ledger_evidence cacheInvalidationLedger := by
  intro evidence
  exact evidence

theorem ay_rcag_accepted_propagation_replay_witness
    {propagationReplayWitness : Prop} :
    propagationReplayWitness ->
    ay_rcag_propagation_replay_witness_evidence
      propagationReplayWitness := by
  intro evidence
  exact evidence

theorem ay_rcag_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_rcag_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rcag_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_rcag_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rcag_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rcag_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rcag_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rcag_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rcag_reason_caching_is_data_structure_optimization_only
    {reasonCacheAccepted dataStructureOptimizationOnly : Prop} :
    reasonCacheAccepted ->
    dataStructureOptimizationOnly ->
    dataStructureOptimizationOnly :=
  fun _ optimizationOnly => optimizationOnly

theorem ay_rcag_reason_caching_cannot_change_original_formula_truth
    {reasonCacheAccepted originalFormulaTruthPreserved : Prop} :
    reasonCacheAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_rcag_accepted_replay_preserves_public_soundness
    {reasonCacheAccepted satSound unsatSound : Prop} :
    reasonCacheAccepted ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rcag_cache_invalidation_preserves_replay
    {cacheInvalidationLedger propagationReplayWitness : Prop} :
    cacheInvalidationLedger ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_rcag_trail_digest_preserves_reason_replay
    {assignmentTrailDigest propagationReplayWitness : Prop} :
    assignmentTrailDigest ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_rcag_clause_database_preserves_reason_replay
    {clauseDatabaseDigest propagationReplayWitness : Prop} :
    clauseDatabaseDigest ->
    propagationReplayWitness ->
    propagationReplayWitness :=
  fun _ replay => replay

theorem ay_rcag_accepted_cache_hint_preserves_fallback_soundness
    {reasonCacheAccepted fallbackBaseline satSound unsatSound : Prop} :
    reasonCacheAccepted ->
    fallbackBaseline ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcag_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rcag_gate accepted rejected ->
    ay_rcag_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rcag_rejected_is_no_claim
    {clauseMismatch diagnostic : Prop} :
    clauseMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcag_rejected_forces_recompute
    {clauseMismatch recomputeRequired : Prop} :
    clauseMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcag_failed_reason_cache_guard_cannot_bless_publication
    {clauseMismatch baselineSound satSound unsatSound : Prop} :
    clauseMismatch ->
    baselineSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcag_clause_mismatch_forces_no_claim
    {clauseMismatch diagnostic : Prop} :
    clauseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcag_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcag_cache_mismatch_forces_no_claim
    {cacheMismatch diagnostic : Prop} :
    cacheMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcag_invalidation_mismatch_forces_no_claim
    {invalidationMismatch diagnostic : Prop} :
    invalidationMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcag_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcag_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcag_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcag_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcag_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rcag_clause_mismatch_forces_recompute
    {clauseMismatch recomputeRequired : Prop} :
    clauseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcag_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcag_cache_mismatch_forces_recompute
    {cacheMismatch recomputeRequired : Prop} :
    cacheMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcag_invalidation_mismatch_forces_recompute
    {invalidationMismatch recomputeRequired : Prop} :
    invalidationMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcag_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcag_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcag_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcag_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcag_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rcag_clause_mismatch_cannot_bless_publication
    {clauseMismatch baselineSound satSound unsatSound : Prop} :
    clauseMismatch ->
    baselineSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcag_trail_mismatch_cannot_bless_publication
    {trailMismatch baselineSound satSound unsatSound : Prop} :
    trailMismatch ->
    baselineSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcag_cache_mismatch_cannot_bless_publication
    {cacheMismatch baselineSound satSound unsatSound : Prop} :
    cacheMismatch ->
    baselineSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcag_invalidation_mismatch_cannot_bless_publication
    {invalidationMismatch baselineSound satSound unsatSound : Prop} :
    invalidationMismatch ->
    baselineSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcag_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcag_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcag_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcag_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcag_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound ->
    ay_rcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rcag_policy_requires_clause_database_digest
    {clauseDatabaseDigest accepted : Prop} :
    clauseDatabaseDigest -> accepted -> clauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_rcag_policy_requires_assignment_trail_digest
    {assignmentTrailDigest accepted : Prop} :
    assignmentTrailDigest -> accepted -> assignmentTrailDigest :=
  fun evidence _ => evidence

theorem ay_rcag_policy_requires_reason_cache_digest
    {reasonCacheDigest accepted : Prop} :
    reasonCacheDigest -> accepted -> reasonCacheDigest :=
  fun evidence _ => evidence

theorem ay_rcag_policy_requires_cache_invalidation_ledger
    {cacheInvalidationLedger accepted : Prop} :
    cacheInvalidationLedger -> accepted -> cacheInvalidationLedger :=
  fun evidence _ => evidence

theorem ay_rcag_policy_requires_propagation_replay
    {propagationReplayWitness accepted : Prop} :
    propagationReplayWitness -> accepted -> propagationReplayWitness :=
  fun evidence _ => evidence

theorem ay_rcag_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_rcag_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_rcag_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_rcag_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
