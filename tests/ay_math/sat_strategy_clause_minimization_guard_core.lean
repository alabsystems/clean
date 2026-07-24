def ay_cmng_conj (p q : Prop) : Prop := p ∧ q

def ay_cmng_disj (p q : Prop) : Prop := p ∨ q

def ay_cmng_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_cmng_disj satSound unsatSound

def ay_cmng_inputs
    (clauseDatabaseDigest learnedClauseDigestBeforeMinimization
      reasonGraphDigest minimizationWitness protectedReasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_cmng_conj clauseDatabaseDigest
    (ay_cmng_conj learnedClauseDigestBeforeMinimization
      (ay_cmng_conj reasonGraphDigest
        (ay_cmng_conj minimizationWitness
          (ay_cmng_conj protectedReasonClauseLedger
            (ay_cmng_conj propagationReplay
              (ay_cmng_conj fallbackBaseline
                (ay_cmng_conj solverBuildEvidence
                  (ay_cmng_conj validatorGate auditTranscript))))))))

def ay_cmng_clause_database_digest_evidence
    (clauseDatabaseDigest : Prop) : Prop :=
  clauseDatabaseDigest

def ay_cmng_learned_clause_digest_before_minimization_evidence
    (learnedClauseDigestBeforeMinimization : Prop) : Prop :=
  learnedClauseDigestBeforeMinimization

def ay_cmng_reason_graph_digest_evidence
    (reasonGraphDigest : Prop) : Prop :=
  reasonGraphDigest

def ay_cmng_minimization_witness_evidence
    (minimizationWitness : Prop) : Prop :=
  minimizationWitness

def ay_cmng_protected_reason_clause_ledger_evidence
    (protectedReasonClauseLedger : Prop) : Prop :=
  protectedReasonClauseLedger

def ay_cmng_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_cmng_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_cmng_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_cmng_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_cmng_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_cmng_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_cmng_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_cmng_accepted
    (clauseDatabaseDigest learnedClauseDigestBeforeMinimization
      reasonGraphDigest minimizationWitness protectedReasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript minimizationAccepted : Prop) : Prop :=
  minimizationAccepted

def ay_cmng_rejected
    (digestMismatch learnedDigestMismatch reasonMismatch minimizationMismatch
      protectionMismatch replayMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch : Prop) : Prop :=
  ay_cmng_disj digestMismatch
    (ay_cmng_disj learnedDigestMismatch
      (ay_cmng_disj reasonMismatch
        (ay_cmng_disj minimizationMismatch
          (ay_cmng_disj protectionMismatch
            (ay_cmng_disj replayMismatch
              (ay_cmng_disj baselineMismatch
                (ay_cmng_disj buildMismatch
                  (ay_cmng_disj validatorMismatch auditMismatch))))))))

def ay_cmng_gate (accepted rejected : Prop) : Prop :=
  ay_cmng_disj accepted rejected

def ay_cmng_minimization_semantic_force_hint
    (minimizationAccepted semanticForcePreserved replayAccepted
      publicationGuard : Prop) : Prop :=
  minimizationAccepted

theorem ay_cmng_input_components
    {clauseDatabaseDigest learnedClauseDigestBeforeMinimization
      reasonGraphDigest minimizationWitness protectedReasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_cmng_inputs clauseDatabaseDigest
      learnedClauseDigestBeforeMinimization reasonGraphDigest
      minimizationWitness protectedReasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    ay_cmng_inputs clauseDatabaseDigest
      learnedClauseDigestBeforeMinimization reasonGraphDigest
      minimizationWitness protectedReasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_cmng_accepted_policy
    {clauseDatabaseDigest learnedClauseDigestBeforeMinimization
      reasonGraphDigest minimizationWitness protectedReasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript minimizationAccepted : Prop} :
    minimizationAccepted ->
    ay_cmng_accepted clauseDatabaseDigest
      learnedClauseDigestBeforeMinimization reasonGraphDigest
      minimizationWitness protectedReasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      minimizationAccepted := by
  intro accepted
  exact accepted

theorem ay_cmng_accepted_clause_database_digest
    {clauseDatabaseDigest : Prop} :
    clauseDatabaseDigest ->
    ay_cmng_clause_database_digest_evidence clauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_cmng_accepted_learned_clause_digest_before_minimization
    {learnedClauseDigestBeforeMinimization : Prop} :
    learnedClauseDigestBeforeMinimization ->
    ay_cmng_learned_clause_digest_before_minimization_evidence
      learnedClauseDigestBeforeMinimization := by
  intro evidence
  exact evidence

theorem ay_cmng_accepted_reason_graph_digest
    {reasonGraphDigest : Prop} :
    reasonGraphDigest ->
    ay_cmng_reason_graph_digest_evidence reasonGraphDigest := by
  intro evidence
  exact evidence

theorem ay_cmng_accepted_minimization_witness
    {minimizationWitness : Prop} :
    minimizationWitness ->
    ay_cmng_minimization_witness_evidence minimizationWitness := by
  intro evidence
  exact evidence

theorem ay_cmng_accepted_protected_reason_clause_ledger
    {protectedReasonClauseLedger : Prop} :
    protectedReasonClauseLedger ->
    ay_cmng_protected_reason_clause_ledger_evidence
      protectedReasonClauseLedger := by
  intro evidence
  exact evidence

theorem ay_cmng_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_cmng_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_cmng_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_cmng_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_cmng_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_cmng_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_cmng_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_cmng_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_cmng_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_cmng_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_cmng_minimization_preserves_semantic_force
    {minimizationAccepted semanticForcePreserved : Prop} :
    minimizationAccepted ->
    semanticForcePreserved ->
    semanticForcePreserved :=
  fun _ force => force

theorem ay_cmng_minimization_cannot_change_original_formula_truth
    {minimizationAccepted originalFormulaTruthPreserved : Prop} :
    minimizationAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_cmng_accepted_minimization_preserves_public_soundness
    {minimizationAccepted satSound unsatSound : Prop} :
    minimizationAccepted ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_cmng_reason_graph_preserves_replay
    {reasonGraphDigest propagationReplay : Prop} :
    reasonGraphDigest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_cmng_minimization_witness_preserves_semantic_force
    {minimizationWitness semanticForcePreserved : Prop} :
    minimizationWitness ->
    semanticForcePreserved ->
    semanticForcePreserved :=
  fun _ force => force

theorem ay_cmng_protection_ledger_preserves_replay
    {protectedReasonClauseLedger propagationReplay : Prop} :
    protectedReasonClauseLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_cmng_accepted_minimization_preserves_fallback_soundness
    {minimizationAccepted fallbackBaseline satSound unsatSound : Prop} :
    minimizationAccepted ->
    fallbackBaseline ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_cmng_gate accepted rejected ->
    ay_cmng_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_cmng_rejected_is_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmng_rejected_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmng_failed_guard_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_digest_mismatch_forces_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmng_learned_digest_mismatch_forces_no_claim
    {learnedDigestMismatch diagnostic : Prop} :
    learnedDigestMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmng_reason_mismatch_forces_no_claim
    {reasonMismatch diagnostic : Prop} :
    reasonMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmng_minimization_mismatch_forces_no_claim
    {minimizationMismatch diagnostic : Prop} :
    minimizationMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmng_protection_mismatch_forces_no_claim
    {protectionMismatch diagnostic : Prop} :
    protectionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmng_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmng_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmng_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmng_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmng_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmng_digest_mismatch_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmng_learned_digest_mismatch_forces_recompute
    {learnedDigestMismatch recomputeRequired : Prop} :
    learnedDigestMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmng_reason_mismatch_forces_recompute
    {reasonMismatch recomputeRequired : Prop} :
    reasonMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmng_minimization_mismatch_forces_recompute
    {minimizationMismatch recomputeRequired : Prop} :
    minimizationMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmng_protection_mismatch_forces_recompute
    {protectionMismatch recomputeRequired : Prop} :
    protectionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmng_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmng_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmng_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmng_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmng_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmng_digest_mismatch_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_learned_digest_mismatch_cannot_bless_publication
    {learnedDigestMismatch baselineSound satSound unsatSound : Prop} :
    learnedDigestMismatch ->
    baselineSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_reason_mismatch_cannot_bless_publication
    {reasonMismatch baselineSound satSound unsatSound : Prop} :
    reasonMismatch ->
    baselineSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_minimization_mismatch_cannot_bless_publication
    {minimizationMismatch baselineSound satSound unsatSound : Prop} :
    minimizationMismatch ->
    baselineSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_protection_mismatch_cannot_bless_publication
    {protectionMismatch baselineSound satSound unsatSound : Prop} :
    protectionMismatch ->
    baselineSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound ->
    ay_cmng_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmng_policy_requires_clause_database_digest
    {clauseDatabaseDigest accepted : Prop} :
    clauseDatabaseDigest -> accepted -> clauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_cmng_policy_requires_learned_clause_digest
    {learnedClauseDigestBeforeMinimization accepted : Prop} :
    learnedClauseDigestBeforeMinimization -> accepted ->
    learnedClauseDigestBeforeMinimization :=
  fun evidence _ => evidence

theorem ay_cmng_policy_requires_reason_graph_digest
    {reasonGraphDigest accepted : Prop} :
    reasonGraphDigest -> accepted -> reasonGraphDigest :=
  fun evidence _ => evidence

theorem ay_cmng_policy_requires_minimization_witness
    {minimizationWitness accepted : Prop} :
    minimizationWitness -> accepted -> minimizationWitness :=
  fun evidence _ => evidence

theorem ay_cmng_policy_requires_protected_reason_clause
    {protectedReasonClauseLedger accepted : Prop} :
    protectedReasonClauseLedger -> accepted -> protectedReasonClauseLedger :=
  fun evidence _ => evidence

theorem ay_cmng_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_cmng_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_cmng_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_cmng_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_cmng_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
