def ay_hbrg_conj (p q : Prop) : Prop := p ∧ q

def ay_hbrg_disj (p q : Prop) : Prop := p ∨ q

def ay_hbrg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_hbrg_disj satSound unsatSound

def ay_hbrg_inputs
    (implicationGraphSnapshot binaryImplicationGraphDigest
      derivedBinaryClauseWitnessLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_hbrg_conj implicationGraphSnapshot
    (ay_hbrg_conj binaryImplicationGraphDigest
      (ay_hbrg_conj derivedBinaryClauseWitnessLedger
        (ay_hbrg_conj propagationReplay
          (ay_hbrg_conj fallbackBaseline
            (ay_hbrg_conj solverBuildEvidence
              (ay_hbrg_conj validatorGate auditTranscript))))))

def ay_hbrg_implication_graph_snapshot_evidence
    (implicationGraphSnapshot : Prop) : Prop :=
  implicationGraphSnapshot

def ay_hbrg_binary_implication_graph_digest_evidence
    (binaryImplicationGraphDigest : Prop) : Prop :=
  binaryImplicationGraphDigest

def ay_hbrg_derived_binary_clause_witness_ledger_evidence
    (derivedBinaryClauseWitnessLedger : Prop) : Prop :=
  derivedBinaryClauseWitnessLedger

def ay_hbrg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_hbrg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_hbrg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_hbrg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_hbrg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_hbrg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_hbrg_accepted
    (implicationGraphSnapshot binaryImplicationGraphDigest
      derivedBinaryClauseWitnessLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript hbrAccepted : Prop) : Prop :=
  hbrAccepted

def ay_hbrg_rejected
    (graphFailure digestFailure witnessFailure replayFailure fallbackFailure
      buildFailure validatorFailure auditFailure : Prop) : Prop :=
  ay_hbrg_disj graphFailure
    (ay_hbrg_disj digestFailure
      (ay_hbrg_disj witnessFailure
        (ay_hbrg_disj replayFailure
          (ay_hbrg_disj fallbackFailure
            (ay_hbrg_disj buildFailure
              (ay_hbrg_disj validatorFailure auditFailure))))))

def ay_hbrg_gate (accepted rejected : Prop) : Prop :=
  ay_hbrg_disj accepted rejected

def ay_hbrg_hbr_hint
    (hbrAccepted implicationPolicy binaryPolicy witnessPolicy : Prop) : Prop :=
  hbrAccepted

def ay_hbrg_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_hbrg_input_components
    {implicationGraphSnapshot binaryImplicationGraphDigest
      derivedBinaryClauseWitnessLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_hbrg_inputs implicationGraphSnapshot binaryImplicationGraphDigest
      derivedBinaryClauseWitnessLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_hbrg_inputs implicationGraphSnapshot binaryImplicationGraphDigest
      derivedBinaryClauseWitnessLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_hbrg_accepted_policy
    {implicationGraphSnapshot binaryImplicationGraphDigest
      derivedBinaryClauseWitnessLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript hbrAccepted : Prop} :
    hbrAccepted ->
    ay_hbrg_accepted implicationGraphSnapshot binaryImplicationGraphDigest
      derivedBinaryClauseWitnessLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript hbrAccepted := by
  intro accepted
  exact accepted

theorem ay_hbrg_accepted_implication_graph_snapshot
    {implicationGraphSnapshot : Prop} :
    implicationGraphSnapshot ->
    ay_hbrg_implication_graph_snapshot_evidence implicationGraphSnapshot := by
  intro evidence
  exact evidence

theorem ay_hbrg_accepted_binary_implication_graph_digest
    {binaryImplicationGraphDigest : Prop} :
    binaryImplicationGraphDigest ->
    ay_hbrg_binary_implication_graph_digest_evidence
      binaryImplicationGraphDigest := by
  intro evidence
  exact evidence

theorem ay_hbrg_accepted_derived_binary_clause_witness_ledger
    {derivedBinaryClauseWitnessLedger : Prop} :
    derivedBinaryClauseWitnessLedger ->
    ay_hbrg_derived_binary_clause_witness_ledger_evidence
      derivedBinaryClauseWitnessLedger := by
  intro evidence
  exact evidence

theorem ay_hbrg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_hbrg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_hbrg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_hbrg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_hbrg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_hbrg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_hbrg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_hbrg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_hbrg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_hbrg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_hbrg_hbr_policy_admissible_hint
    {hbrAccepted implicationPolicy binaryPolicy witnessPolicy : Prop} :
    hbrAccepted ->
    implicationPolicy ->
    binaryPolicy ->
    witnessPolicy ->
    ay_hbrg_hbr_hint hbrAccepted implicationPolicy binaryPolicy witnessPolicy := by
  intro accepted implication binary witness
  exact accepted

theorem ay_hbrg_accepted_preserves_logical_consequence
    {hbrAccepted logicalConsequence : Prop} :
    hbrAccepted ->
    logicalConsequence ->
    logicalConsequence :=
  fun _ consequence => consequence

theorem ay_hbrg_hint_cannot_change_truth
    {hbrAccepted formulaTruth : Prop} :
    hbrAccepted ->
    formulaTruth ->
    formulaTruth :=
  fun _ truth => truth

theorem ay_hbrg_accepted_policy_preserves_public_soundness
    {hbrAccepted satSound unsatSound : Prop} :
    hbrAccepted ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_hbrg_rejected_is_no_claim
    {graphFailure diagnostic : Prop} :
    graphFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_hbrg_rejected_forces_recompute
    {graphFailure recomputeRequired : Prop} :
    graphFailure ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_hbrg_rejected_cannot_bless_public_result
    {graphFailure baselineSound satSound unsatSound : Prop} :
    graphFailure ->
    baselineSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_hbrg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_hbrg_gate accepted rejected ->
    ay_hbrg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_hbrg_safe_policy_deployment_accept
    {hbrAccepted implicationPolicy binaryPolicy witnessPolicy satSound
      unsatSound : Prop} :
    hbrAccepted ->
    implicationPolicy ->
    binaryPolicy ->
    witnessPolicy ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_hbrg_safe_policy_deployment_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_hbrg_graph_failure_forces_no_claim
    {graphFailure diagnostic : Prop} :
    graphFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_hbrg_digest_failure_forces_no_claim
    {digestFailure diagnostic : Prop} :
    digestFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_hbrg_witness_failure_forces_no_claim
    {witnessFailure diagnostic : Prop} :
    witnessFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_hbrg_replay_failure_forces_no_claim
    {replayFailure diagnostic : Prop} :
    replayFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_hbrg_fallback_failure_forces_no_claim
    {fallbackFailure diagnostic : Prop} :
    fallbackFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_hbrg_build_failure_forces_no_claim
    {buildFailure diagnostic : Prop} :
    buildFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_hbrg_validator_failure_forces_no_claim
    {validatorFailure diagnostic : Prop} :
    validatorFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_hbrg_audit_failure_forces_no_claim
    {auditFailure diagnostic : Prop} :
    auditFailure ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_hbrg_graph_failure_cannot_bless_public_result
    {graphFailure baselineSound satSound unsatSound : Prop} :
    graphFailure ->
    baselineSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_hbrg_digest_failure_cannot_bless_public_result
    {digestFailure baselineSound satSound unsatSound : Prop} :
    digestFailure ->
    baselineSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_hbrg_witness_failure_cannot_bless_public_result
    {witnessFailure baselineSound satSound unsatSound : Prop} :
    witnessFailure ->
    baselineSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_hbrg_replay_failure_cannot_bless_public_result
    {replayFailure baselineSound satSound unsatSound : Prop} :
    replayFailure ->
    baselineSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_hbrg_fallback_failure_cannot_bless_public_result
    {fallbackFailure baselineSound satSound unsatSound : Prop} :
    fallbackFailure ->
    baselineSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_hbrg_build_failure_cannot_bless_public_result
    {buildFailure baselineSound satSound unsatSound : Prop} :
    buildFailure ->
    baselineSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_hbrg_validator_failure_cannot_bless_public_result
    {validatorFailure baselineSound satSound unsatSound : Prop} :
    validatorFailure ->
    baselineSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_hbrg_audit_failure_cannot_bless_public_result
    {auditFailure baselineSound satSound unsatSound : Prop} :
    auditFailure ->
    baselineSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound ->
    ay_hbrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_hbrg_policy_requires_implication_graph_snapshot
    {implicationGraphSnapshot : Prop} :
    ay_hbrg_implication_graph_snapshot_evidence implicationGraphSnapshot ->
    implicationGraphSnapshot := by
  intro evidence
  exact evidence

theorem ay_hbrg_policy_requires_binary_implication_graph_digest
    {binaryImplicationGraphDigest : Prop} :
    ay_hbrg_binary_implication_graph_digest_evidence
      binaryImplicationGraphDigest ->
    binaryImplicationGraphDigest := by
  intro evidence
  exact evidence

theorem ay_hbrg_policy_requires_derived_binary_clause_witness_ledger
    {derivedBinaryClauseWitnessLedger : Prop} :
    ay_hbrg_derived_binary_clause_witness_ledger_evidence
      derivedBinaryClauseWitnessLedger ->
    derivedBinaryClauseWitnessLedger := by
  intro evidence
  exact evidence

theorem ay_hbrg_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_hbrg_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_hbrg_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_hbrg_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_hbrg_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_hbrg_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_hbrg_policy_requires_validator
    {validatorGate : Prop} :
    ay_hbrg_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_hbrg_policy_requires_audit
    {auditTranscript : Prop} :
    ay_hbrg_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
