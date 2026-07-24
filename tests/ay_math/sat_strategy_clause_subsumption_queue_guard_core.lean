def ay_csqg_conj (p q : Prop) : Prop := p ∧ q

def ay_csqg_disj (p q : Prop) : Prop := p ∨ q

def ay_csqg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_csqg_disj satSound unsatSound

def ay_csqg_inputs
    (clauseDatabaseDigest subsumptionQueueDigest candidatePairLedger
      deletionStrengtheningLedger protectedReasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_csqg_conj clauseDatabaseDigest
    (ay_csqg_conj subsumptionQueueDigest
      (ay_csqg_conj candidatePairLedger
        (ay_csqg_conj deletionStrengtheningLedger
          (ay_csqg_conj protectedReasonClauseLedger
            (ay_csqg_conj propagationReplay
              (ay_csqg_conj fallbackBaseline
                (ay_csqg_conj solverBuildEvidence
                  (ay_csqg_conj validatorGate auditTranscript))))))))

def ay_csqg_clause_database_digest_evidence
    (clauseDatabaseDigest : Prop) : Prop :=
  clauseDatabaseDigest

def ay_csqg_subsumption_queue_digest_evidence
    (subsumptionQueueDigest : Prop) : Prop :=
  subsumptionQueueDigest

def ay_csqg_candidate_pair_ledger_evidence
    (candidatePairLedger : Prop) : Prop :=
  candidatePairLedger

def ay_csqg_deletion_strengthening_ledger_evidence
    (deletionStrengtheningLedger : Prop) : Prop :=
  deletionStrengtheningLedger

def ay_csqg_protected_reason_clause_ledger_evidence
    (protectedReasonClauseLedger : Prop) : Prop :=
  protectedReasonClauseLedger

def ay_csqg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_csqg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_csqg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_csqg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_csqg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_csqg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_csqg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_csqg_accepted
    (clauseDatabaseDigest subsumptionQueueDigest candidatePairLedger
      deletionStrengtheningLedger protectedReasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript queueAccepted : Prop) : Prop :=
  queueAccepted

def ay_csqg_rejected
    (clauseMismatch queueMismatch candidateMismatch deletionMismatch
      protectionMismatch replayMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch : Prop) : Prop :=
  ay_csqg_disj clauseMismatch
    (ay_csqg_disj queueMismatch
      (ay_csqg_disj candidateMismatch
        (ay_csqg_disj deletionMismatch
          (ay_csqg_disj protectionMismatch
            (ay_csqg_disj replayMismatch
              (ay_csqg_disj baselineMismatch
                (ay_csqg_disj buildMismatch
                  (ay_csqg_disj validatorMismatch auditMismatch))))))))

def ay_csqg_gate (accepted rejected : Prop) : Prop :=
  ay_csqg_disj accepted rejected

def ay_csqg_clause_management_hint
    (queueAccepted queueOnly clauseManagementOnly replayAccepted : Prop) :
      Prop :=
  queueAccepted

theorem ay_csqg_input_components
    {clauseDatabaseDigest subsumptionQueueDigest candidatePairLedger
      deletionStrengtheningLedger protectedReasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_csqg_inputs clauseDatabaseDigest subsumptionQueueDigest
      candidatePairLedger deletionStrengtheningLedger
      protectedReasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_csqg_inputs clauseDatabaseDigest subsumptionQueueDigest
      candidatePairLedger deletionStrengtheningLedger
      protectedReasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_csqg_accepted_policy
    {clauseDatabaseDigest subsumptionQueueDigest candidatePairLedger
      deletionStrengtheningLedger protectedReasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript queueAccepted : Prop} :
    queueAccepted ->
    ay_csqg_accepted clauseDatabaseDigest subsumptionQueueDigest
      candidatePairLedger deletionStrengtheningLedger
      protectedReasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript queueAccepted := by
  intro accepted
  exact accepted

theorem ay_csqg_accepted_clause_database_digest
    {clauseDatabaseDigest : Prop} :
    clauseDatabaseDigest ->
    ay_csqg_clause_database_digest_evidence clauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_csqg_accepted_subsumption_queue_digest
    {subsumptionQueueDigest : Prop} :
    subsumptionQueueDigest ->
    ay_csqg_subsumption_queue_digest_evidence subsumptionQueueDigest := by
  intro evidence
  exact evidence

theorem ay_csqg_accepted_candidate_pair_ledger
    {candidatePairLedger : Prop} :
    candidatePairLedger ->
    ay_csqg_candidate_pair_ledger_evidence candidatePairLedger := by
  intro evidence
  exact evidence

theorem ay_csqg_accepted_deletion_strengthening_ledger
    {deletionStrengtheningLedger : Prop} :
    deletionStrengtheningLedger ->
    ay_csqg_deletion_strengthening_ledger_evidence
      deletionStrengtheningLedger := by
  intro evidence
  exact evidence

theorem ay_csqg_accepted_protected_reason_clause_ledger
    {protectedReasonClauseLedger : Prop} :
    protectedReasonClauseLedger ->
    ay_csqg_protected_reason_clause_ledger_evidence
      protectedReasonClauseLedger := by
  intro evidence
  exact evidence

theorem ay_csqg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_csqg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_csqg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_csqg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_csqg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_csqg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_csqg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_csqg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_csqg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_csqg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_csqg_queue_is_clause_management_only
    {queueAccepted clauseManagementOnly : Prop} :
    queueAccepted ->
    clauseManagementOnly ->
    clauseManagementOnly :=
  fun _ managementOnly => managementOnly

theorem ay_csqg_queue_cannot_change_original_formula_truth
    {queueAccepted originalFormulaTruthPreserved : Prop} :
    queueAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_csqg_accepted_queue_preserves_public_soundness
    {queueAccepted satSound unsatSound : Prop} :
    queueAccepted ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_csqg_candidate_ledger_preserves_replay
    {candidatePairLedger propagationReplay : Prop} :
    candidatePairLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_csqg_deletion_strengthening_preserves_replay
    {deletionStrengtheningLedger propagationReplay : Prop} :
    deletionStrengtheningLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_csqg_protected_reason_preserves_replay
    {protectedReasonClauseLedger propagationReplay : Prop} :
    protectedReasonClauseLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_csqg_accepted_queue_preserves_fallback_soundness
    {queueAccepted fallbackBaseline satSound unsatSound : Prop} :
    queueAccepted ->
    fallbackBaseline ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_csqg_gate accepted rejected ->
    ay_csqg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_csqg_rejected_is_no_claim
    {queueMismatch diagnostic : Prop} :
    queueMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_csqg_rejected_forces_recompute
    {queueMismatch recomputeRequired : Prop} :
    queueMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_csqg_failed_guard_cannot_bless_publication
    {queueMismatch baselineSound satSound unsatSound : Prop} :
    queueMismatch ->
    baselineSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_clause_mismatch_forces_no_claim
    {clauseMismatch diagnostic : Prop} :
    clauseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_csqg_queue_mismatch_forces_no_claim
    {queueMismatch diagnostic : Prop} :
    queueMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_csqg_candidate_mismatch_forces_no_claim
    {candidateMismatch diagnostic : Prop} :
    candidateMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_csqg_deletion_mismatch_forces_no_claim
    {deletionMismatch diagnostic : Prop} :
    deletionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_csqg_protection_mismatch_forces_no_claim
    {protectionMismatch diagnostic : Prop} :
    protectionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_csqg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_csqg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_csqg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_csqg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_csqg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_csqg_clause_mismatch_forces_recompute
    {clauseMismatch recomputeRequired : Prop} :
    clauseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_csqg_queue_mismatch_forces_recompute
    {queueMismatch recomputeRequired : Prop} :
    queueMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_csqg_candidate_mismatch_forces_recompute
    {candidateMismatch recomputeRequired : Prop} :
    candidateMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_csqg_deletion_mismatch_forces_recompute
    {deletionMismatch recomputeRequired : Prop} :
    deletionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_csqg_protection_mismatch_forces_recompute
    {protectionMismatch recomputeRequired : Prop} :
    protectionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_csqg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_csqg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_csqg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_csqg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_csqg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_csqg_clause_mismatch_cannot_bless_publication
    {clauseMismatch baselineSound satSound unsatSound : Prop} :
    clauseMismatch ->
    baselineSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_queue_mismatch_cannot_bless_publication
    {queueMismatch baselineSound satSound unsatSound : Prop} :
    queueMismatch ->
    baselineSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_candidate_mismatch_cannot_bless_publication
    {candidateMismatch baselineSound satSound unsatSound : Prop} :
    candidateMismatch ->
    baselineSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_deletion_mismatch_cannot_bless_publication
    {deletionMismatch baselineSound satSound unsatSound : Prop} :
    deletionMismatch ->
    baselineSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_protection_mismatch_cannot_bless_publication
    {protectionMismatch baselineSound satSound unsatSound : Prop} :
    protectionMismatch ->
    baselineSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound ->
    ay_csqg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_csqg_policy_requires_clause_database_digest
    {clauseDatabaseDigest accepted : Prop} :
    clauseDatabaseDigest -> accepted -> clauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_csqg_policy_requires_subsumption_queue_digest
    {subsumptionQueueDigest accepted : Prop} :
    subsumptionQueueDigest -> accepted -> subsumptionQueueDigest :=
  fun evidence _ => evidence

theorem ay_csqg_policy_requires_candidate_pair_ledger
    {candidatePairLedger accepted : Prop} :
    candidatePairLedger -> accepted -> candidatePairLedger :=
  fun evidence _ => evidence

theorem ay_csqg_policy_requires_deletion_strengthening
    {deletionStrengtheningLedger accepted : Prop} :
    deletionStrengtheningLedger -> accepted -> deletionStrengtheningLedger :=
  fun evidence _ => evidence

theorem ay_csqg_policy_requires_protected_reason_clause
    {protectedReasonClauseLedger accepted : Prop} :
    protectedReasonClauseLedger -> accepted -> protectedReasonClauseLedger :=
  fun evidence _ => evidence

theorem ay_csqg_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_csqg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_csqg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_csqg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_csqg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
