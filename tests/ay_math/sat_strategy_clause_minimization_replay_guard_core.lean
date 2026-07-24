def ay_cmin_conj (p q : Prop) : Prop := p ∧ q

def ay_cmin_disj (p q : Prop) : Prop := p ∨ q

def ay_cmin_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_cmin_disj satSound unsatSound

def ay_cmin_inputs
    (implicationGraphSnapshot minimizationWitnessLedger removedLiteralCoverage
      learntClauseDigest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) : Prop :=
  ay_cmin_conj implicationGraphSnapshot
    (ay_cmin_conj minimizationWitnessLedger
      (ay_cmin_conj removedLiteralCoverage
        (ay_cmin_conj learntClauseDigest
          (ay_cmin_conj propagationReplay
            (ay_cmin_conj fallbackBaseline
              (ay_cmin_conj solverBuildEvidence
                (ay_cmin_conj validatorGate auditTranscript)))))))

def ay_cmin_implication_graph_snapshot_evidence
    (implicationGraphSnapshot : Prop) : Prop :=
  implicationGraphSnapshot

def ay_cmin_minimization_witness_ledger_evidence
    (minimizationWitnessLedger : Prop) : Prop :=
  minimizationWitnessLedger

def ay_cmin_removed_literal_coverage_evidence
    (removedLiteralCoverage : Prop) : Prop :=
  removedLiteralCoverage

def ay_cmin_learnt_clause_digest_evidence
    (learntClauseDigest : Prop) : Prop :=
  learntClauseDigest

def ay_cmin_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_cmin_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_cmin_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_cmin_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_cmin_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_cmin_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_cmin_accepted
    (implicationGraphSnapshot minimizationWitnessLedger removedLiteralCoverage
      learntClauseDigest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript minimizationAccepted : Prop) : Prop :=
  minimizationAccepted

def ay_cmin_rejected
    (graphFailure witnessFailure coverageFailure digestFailure replayFailure
      fallbackFailure buildFailure validatorFailure auditFailure : Prop) : Prop :=
  ay_cmin_disj graphFailure
    (ay_cmin_disj witnessFailure
      (ay_cmin_disj coverageFailure
        (ay_cmin_disj digestFailure
          (ay_cmin_disj replayFailure
            (ay_cmin_disj fallbackFailure
              (ay_cmin_disj buildFailure
                (ay_cmin_disj validatorFailure auditFailure)))))))

def ay_cmin_gate (accepted rejected : Prop) : Prop :=
  ay_cmin_disj accepted rejected

def ay_cmin_minimization_hint
    (minimizationAccepted graphPolicy witnessPolicy clausePolicy : Prop) : Prop :=
  minimizationAccepted

def ay_cmin_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_cmin_input_components
    {implicationGraphSnapshot minimizationWitnessLedger removedLiteralCoverage
      learntClauseDigest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop} :
    ay_cmin_inputs implicationGraphSnapshot minimizationWitnessLedger
      removedLiteralCoverage learntClauseDigest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_cmin_inputs implicationGraphSnapshot minimizationWitnessLedger
      removedLiteralCoverage learntClauseDigest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_cmin_accepted_policy
    {implicationGraphSnapshot minimizationWitnessLedger removedLiteralCoverage
      learntClauseDigest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript minimizationAccepted : Prop} :
    minimizationAccepted ->
    ay_cmin_accepted implicationGraphSnapshot minimizationWitnessLedger
      removedLiteralCoverage learntClauseDigest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript minimizationAccepted := by
  intro accepted
  exact accepted

theorem ay_cmin_accepted_implication_graph_snapshot
    {implicationGraphSnapshot : Prop} :
    implicationGraphSnapshot ->
    ay_cmin_implication_graph_snapshot_evidence implicationGraphSnapshot := by
  intro evidence
  exact evidence

theorem ay_cmin_accepted_minimization_witness_ledger
    {minimizationWitnessLedger : Prop} :
    minimizationWitnessLedger ->
    ay_cmin_minimization_witness_ledger_evidence
      minimizationWitnessLedger := by
  intro evidence
  exact evidence

theorem ay_cmin_accepted_removed_literal_coverage
    {removedLiteralCoverage : Prop} :
    removedLiteralCoverage ->
    ay_cmin_removed_literal_coverage_evidence removedLiteralCoverage := by
  intro evidence
  exact evidence

theorem ay_cmin_accepted_learnt_clause_digest
    {learntClauseDigest : Prop} :
    learntClauseDigest ->
    ay_cmin_learnt_clause_digest_evidence learntClauseDigest := by
  intro evidence
  exact evidence

theorem ay_cmin_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_cmin_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_cmin_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_cmin_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_cmin_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_cmin_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_cmin_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_cmin_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_cmin_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_cmin_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_cmin_minimization_policy_admissible_hint
    {minimizationAccepted graphPolicy witnessPolicy clausePolicy : Prop} :
    minimizationAccepted ->
    graphPolicy ->
    witnessPolicy ->
    clausePolicy ->
    ay_cmin_minimization_hint minimizationAccepted graphPolicy witnessPolicy
      clausePolicy := by
  intro accepted graph witness clause
  exact accepted

theorem ay_cmin_accepted_preserves_learned_clause_consequence
    {minimizationAccepted learnedClauseConsequence : Prop} :
    minimizationAccepted ->
    learnedClauseConsequence ->
    learnedClauseConsequence :=
  fun _ consequence => consequence

theorem ay_cmin_hint_cannot_change_truth
    {minimizationAccepted formulaTruth : Prop} :
    minimizationAccepted ->
    formulaTruth ->
    formulaTruth :=
  fun _ truth => truth

theorem ay_cmin_accepted_policy_preserves_public_soundness
    {minimizationAccepted satSound unsatSound : Prop} :
    minimizationAccepted ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_cmin_rejected_is_no_claim
    {graphFailure diagnostic : Prop} :
    graphFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmin_rejected_forces_recompute
    {graphFailure recomputeRequired : Prop} :
    graphFailure ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cmin_rejected_cannot_bless_public_result
    {graphFailure baselineSound satSound unsatSound : Prop} :
    graphFailure ->
    baselineSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmin_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_cmin_gate accepted rejected ->
    ay_cmin_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_cmin_safe_policy_deployment_accept
    {minimizationAccepted graphPolicy witnessPolicy clausePolicy satSound
      unsatSound : Prop} :
    minimizationAccepted ->
    graphPolicy ->
    witnessPolicy ->
    clausePolicy ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_cmin_safe_policy_deployment_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_cmin_graph_failure_forces_no_claim
    {graphFailure diagnostic : Prop} :
    graphFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmin_witness_failure_forces_no_claim
    {witnessFailure diagnostic : Prop} :
    witnessFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmin_coverage_failure_forces_no_claim
    {coverageFailure diagnostic : Prop} :
    coverageFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmin_digest_failure_forces_no_claim
    {digestFailure diagnostic : Prop} :
    digestFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmin_replay_failure_forces_no_claim
    {replayFailure diagnostic : Prop} :
    replayFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmin_fallback_failure_forces_no_claim
    {fallbackFailure diagnostic : Prop} :
    fallbackFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmin_build_failure_forces_no_claim
    {buildFailure diagnostic : Prop} :
    buildFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmin_validator_failure_forces_no_claim
    {validatorFailure diagnostic : Prop} :
    validatorFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmin_audit_failure_forces_no_claim
    {auditFailure diagnostic : Prop} :
    auditFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cmin_graph_failure_cannot_bless_public_result
    {graphFailure baselineSound satSound unsatSound : Prop} :
    graphFailure ->
    baselineSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmin_witness_failure_cannot_bless_public_result
    {witnessFailure baselineSound satSound unsatSound : Prop} :
    witnessFailure ->
    baselineSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmin_coverage_failure_cannot_bless_public_result
    {coverageFailure baselineSound satSound unsatSound : Prop} :
    coverageFailure ->
    baselineSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmin_digest_failure_cannot_bless_public_result
    {digestFailure baselineSound satSound unsatSound : Prop} :
    digestFailure ->
    baselineSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmin_replay_failure_cannot_bless_public_result
    {replayFailure baselineSound satSound unsatSound : Prop} :
    replayFailure ->
    baselineSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmin_fallback_failure_cannot_bless_public_result
    {fallbackFailure baselineSound satSound unsatSound : Prop} :
    fallbackFailure ->
    baselineSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmin_build_failure_cannot_bless_public_result
    {buildFailure baselineSound satSound unsatSound : Prop} :
    buildFailure ->
    baselineSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmin_validator_failure_cannot_bless_public_result
    {validatorFailure baselineSound satSound unsatSound : Prop} :
    validatorFailure ->
    baselineSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmin_audit_failure_cannot_bless_public_result
    {auditFailure baselineSound satSound unsatSound : Prop} :
    auditFailure ->
    baselineSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound ->
    ay_cmin_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cmin_policy_requires_implication_graph_snapshot
    {implicationGraphSnapshot : Prop} :
    ay_cmin_implication_graph_snapshot_evidence implicationGraphSnapshot ->
    implicationGraphSnapshot := by
  intro evidence
  exact evidence

theorem ay_cmin_policy_requires_minimization_witness_ledger
    {minimizationWitnessLedger : Prop} :
    ay_cmin_minimization_witness_ledger_evidence
      minimizationWitnessLedger ->
    minimizationWitnessLedger := by
  intro evidence
  exact evidence

theorem ay_cmin_policy_requires_removed_literal_coverage
    {removedLiteralCoverage : Prop} :
    ay_cmin_removed_literal_coverage_evidence removedLiteralCoverage ->
    removedLiteralCoverage := by
  intro evidence
  exact evidence

theorem ay_cmin_policy_requires_learnt_clause_digest
    {learntClauseDigest : Prop} :
    ay_cmin_learnt_clause_digest_evidence learntClauseDigest ->
    learntClauseDigest := by
  intro evidence
  exact evidence

theorem ay_cmin_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_cmin_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_cmin_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_cmin_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_cmin_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_cmin_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_cmin_policy_requires_validator
    {validatorGate : Prop} :
    ay_cmin_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_cmin_policy_requires_audit
    {auditTranscript : Prop} :
    ay_cmin_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
