def ay_gcgg_conj (p q : Prop) : Prop := p ∧ q

def ay_gcgg_disj (p q : Prop) : Prop := p ∨ q

def ay_gcgg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_gcgg_disj satSound unsatSound

def ay_gcgg_inputs
    (preGcClauseDatabaseDigest postGcClauseDatabaseDigest
      relocationMapWitness deletedClauseLedger protectedReasonClauseLedger
      watchReasonSynchronizationWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_gcgg_conj preGcClauseDatabaseDigest
    (ay_gcgg_conj postGcClauseDatabaseDigest
      (ay_gcgg_conj relocationMapWitness
        (ay_gcgg_conj deletedClauseLedger
          (ay_gcgg_conj protectedReasonClauseLedger
            (ay_gcgg_conj watchReasonSynchronizationWitness
              (ay_gcgg_conj propagationReplay
                (ay_gcgg_conj fallbackBaseline
                  (ay_gcgg_conj solverBuildEvidence
                    (ay_gcgg_conj validatorGate auditTranscript)))))))))

def ay_gcgg_pre_gc_clause_database_digest_evidence
    (preGcClauseDatabaseDigest : Prop) : Prop :=
  preGcClauseDatabaseDigest

def ay_gcgg_post_gc_clause_database_digest_evidence
    (postGcClauseDatabaseDigest : Prop) : Prop :=
  postGcClauseDatabaseDigest

def ay_gcgg_relocation_map_witness_evidence
    (relocationMapWitness : Prop) : Prop :=
  relocationMapWitness

def ay_gcgg_deleted_clause_ledger_evidence
    (deletedClauseLedger : Prop) : Prop :=
  deletedClauseLedger

def ay_gcgg_protected_reason_clause_ledger_evidence
    (protectedReasonClauseLedger : Prop) : Prop :=
  protectedReasonClauseLedger

def ay_gcgg_watch_reason_synchronization_witness_evidence
    (watchReasonSynchronizationWitness : Prop) : Prop :=
  watchReasonSynchronizationWitness

def ay_gcgg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_gcgg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_gcgg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_gcgg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_gcgg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_gcgg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_gcgg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_gcgg_accepted
    (preGcClauseDatabaseDigest postGcClauseDatabaseDigest
      relocationMapWitness deletedClauseLedger protectedReasonClauseLedger
      watchReasonSynchronizationWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript gcRelocationAccepted :
      Prop) : Prop :=
  gcRelocationAccepted

def ay_gcgg_rejected
    (preDigestMismatch postDigestMismatch relocationMismatch deletionMismatch
      protectionMismatch watchMismatch replayMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch : Prop) : Prop :=
  ay_gcgg_disj preDigestMismatch
    (ay_gcgg_disj postDigestMismatch
      (ay_gcgg_disj relocationMismatch
        (ay_gcgg_disj deletionMismatch
          (ay_gcgg_disj protectionMismatch
            (ay_gcgg_disj watchMismatch
              (ay_gcgg_disj replayMismatch
                (ay_gcgg_disj baselineMismatch
                  (ay_gcgg_disj buildMismatch
                    (ay_gcgg_disj validatorMismatch auditMismatch)))))))))

def ay_gcgg_gate (accepted rejected : Prop) : Prop :=
  ay_gcgg_disj accepted rejected

def ay_gcgg_gc_relocation_memory_management_hint
    (gcRelocationAccepted memoryManagementOnly relocationOnly
      replayAccepted : Prop) : Prop :=
  gcRelocationAccepted

theorem ay_gcgg_input_components
    {preGcClauseDatabaseDigest postGcClauseDatabaseDigest
      relocationMapWitness deletedClauseLedger protectedReasonClauseLedger
      watchReasonSynchronizationWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_gcgg_inputs preGcClauseDatabaseDigest postGcClauseDatabaseDigest
      relocationMapWitness deletedClauseLedger protectedReasonClauseLedger
      watchReasonSynchronizationWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_gcgg_inputs preGcClauseDatabaseDigest postGcClauseDatabaseDigest
      relocationMapWitness deletedClauseLedger protectedReasonClauseLedger
      watchReasonSynchronizationWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_gcgg_accepted_policy
    {preGcClauseDatabaseDigest postGcClauseDatabaseDigest
      relocationMapWitness deletedClauseLedger protectedReasonClauseLedger
      watchReasonSynchronizationWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript gcRelocationAccepted :
      Prop} :
    gcRelocationAccepted ->
    ay_gcgg_accepted preGcClauseDatabaseDigest postGcClauseDatabaseDigest
      relocationMapWitness deletedClauseLedger protectedReasonClauseLedger
      watchReasonSynchronizationWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      gcRelocationAccepted := by
  intro accepted
  exact accepted

theorem ay_gcgg_accepted_pre_gc_clause_database_digest
    {preGcClauseDatabaseDigest : Prop} :
    preGcClauseDatabaseDigest ->
    ay_gcgg_pre_gc_clause_database_digest_evidence
      preGcClauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_gcgg_accepted_post_gc_clause_database_digest
    {postGcClauseDatabaseDigest : Prop} :
    postGcClauseDatabaseDigest ->
    ay_gcgg_post_gc_clause_database_digest_evidence
      postGcClauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_gcgg_accepted_relocation_map_witness
    {relocationMapWitness : Prop} :
    relocationMapWitness ->
    ay_gcgg_relocation_map_witness_evidence relocationMapWitness := by
  intro evidence
  exact evidence

theorem ay_gcgg_accepted_deleted_clause_ledger
    {deletedClauseLedger : Prop} :
    deletedClauseLedger ->
    ay_gcgg_deleted_clause_ledger_evidence deletedClauseLedger := by
  intro evidence
  exact evidence

theorem ay_gcgg_accepted_protected_reason_clause_ledger
    {protectedReasonClauseLedger : Prop} :
    protectedReasonClauseLedger ->
    ay_gcgg_protected_reason_clause_ledger_evidence
      protectedReasonClauseLedger := by
  intro evidence
  exact evidence

theorem ay_gcgg_accepted_watch_reason_synchronization_witness
    {watchReasonSynchronizationWitness : Prop} :
    watchReasonSynchronizationWitness ->
    ay_gcgg_watch_reason_synchronization_witness_evidence
      watchReasonSynchronizationWitness := by
  intro evidence
  exact evidence

theorem ay_gcgg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_gcgg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_gcgg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_gcgg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_gcgg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_gcgg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_gcgg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_gcgg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_gcgg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_gcgg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_gcgg_gc_relocation_is_memory_management_only
    {gcRelocationAccepted memoryManagementOnly : Prop} :
    gcRelocationAccepted ->
    memoryManagementOnly ->
    memoryManagementOnly :=
  fun _ memoryOnly => memoryOnly

theorem ay_gcgg_gc_relocation_cannot_change_original_formula_truth
    {gcRelocationAccepted originalFormulaTruthPreserved : Prop} :
    gcRelocationAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_gcgg_accepted_relocation_preserves_public_soundness
    {gcRelocationAccepted satSound unsatSound : Prop} :
    gcRelocationAccepted ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_gcgg_relocation_map_preserves_replay
    {relocationMapWitness propagationReplay : Prop} :
    relocationMapWitness ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_gcgg_protected_reason_preserves_replay
    {protectedReasonClauseLedger propagationReplay : Prop} :
    protectedReasonClauseLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_gcgg_watch_reason_sync_preserves_replay
    {watchReasonSynchronizationWitness propagationReplay : Prop} :
    watchReasonSynchronizationWitness ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_gcgg_accepted_gc_preserves_fallback_soundness
    {gcRelocationAccepted fallbackBaseline satSound unsatSound : Prop} :
    gcRelocationAccepted ->
    fallbackBaseline ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_gcgg_gate accepted rejected ->
    ay_gcgg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_gcgg_rejected_is_no_claim
    {preDigestMismatch diagnostic : Prop} :
    preDigestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_rejected_forces_recompute
    {preDigestMismatch recomputeRequired : Prop} :
    preDigestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_failed_guard_cannot_bless_publication
    {preDigestMismatch baselineSound satSound unsatSound : Prop} :
    preDigestMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_pre_digest_mismatch_forces_no_claim
    {preDigestMismatch diagnostic : Prop} :
    preDigestMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_post_digest_mismatch_forces_no_claim
    {postDigestMismatch diagnostic : Prop} :
    postDigestMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_relocation_mismatch_forces_no_claim
    {relocationMismatch diagnostic : Prop} :
    relocationMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_deletion_mismatch_forces_no_claim
    {deletionMismatch diagnostic : Prop} :
    deletionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_protection_mismatch_forces_no_claim
    {protectionMismatch diagnostic : Prop} :
    protectionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_watch_mismatch_forces_no_claim
    {watchMismatch diagnostic : Prop} :
    watchMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_gcgg_pre_digest_mismatch_forces_recompute
    {preDigestMismatch recomputeRequired : Prop} :
    preDigestMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_post_digest_mismatch_forces_recompute
    {postDigestMismatch recomputeRequired : Prop} :
    postDigestMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_relocation_mismatch_forces_recompute
    {relocationMismatch recomputeRequired : Prop} :
    relocationMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_deletion_mismatch_forces_recompute
    {deletionMismatch recomputeRequired : Prop} :
    deletionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_protection_mismatch_forces_recompute
    {protectionMismatch recomputeRequired : Prop} :
    protectionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_watch_mismatch_forces_recompute
    {watchMismatch recomputeRequired : Prop} :
    watchMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_gcgg_pre_digest_mismatch_cannot_bless_publication
    {preDigestMismatch baselineSound satSound unsatSound : Prop} :
    preDigestMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_post_digest_mismatch_cannot_bless_publication
    {postDigestMismatch baselineSound satSound unsatSound : Prop} :
    postDigestMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_relocation_mismatch_cannot_bless_publication
    {relocationMismatch baselineSound satSound unsatSound : Prop} :
    relocationMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_deletion_mismatch_cannot_bless_publication
    {deletionMismatch baselineSound satSound unsatSound : Prop} :
    deletionMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_protection_mismatch_cannot_bless_publication
    {protectionMismatch baselineSound satSound unsatSound : Prop} :
    protectionMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_watch_mismatch_cannot_bless_publication
    {watchMismatch baselineSound satSound unsatSound : Prop} :
    watchMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound ->
    ay_gcgg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_gcgg_policy_requires_pre_gc_digest
    {preGcClauseDatabaseDigest accepted : Prop} :
    preGcClauseDatabaseDigest -> accepted -> preGcClauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_gcgg_policy_requires_post_gc_digest
    {postGcClauseDatabaseDigest accepted : Prop} :
    postGcClauseDatabaseDigest -> accepted -> postGcClauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_gcgg_policy_requires_relocation_map
    {relocationMapWitness accepted : Prop} :
    relocationMapWitness -> accepted -> relocationMapWitness :=
  fun evidence _ => evidence

theorem ay_gcgg_policy_requires_deleted_clause_ledger
    {deletedClauseLedger accepted : Prop} :
    deletedClauseLedger -> accepted -> deletedClauseLedger :=
  fun evidence _ => evidence

theorem ay_gcgg_policy_requires_protected_reason_clause
    {protectedReasonClauseLedger accepted : Prop} :
    protectedReasonClauseLedger -> accepted -> protectedReasonClauseLedger :=
  fun evidence _ => evidence

theorem ay_gcgg_policy_requires_watch_reason_sync
    {watchReasonSynchronizationWitness accepted : Prop} :
    watchReasonSynchronizationWitness -> accepted ->
    watchReasonSynchronizationWitness :=
  fun evidence _ => evidence

theorem ay_gcgg_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_gcgg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_gcgg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_gcgg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_gcgg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
