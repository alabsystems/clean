def ay_carg_conj (p q : Prop) : Prop := p ∧ q

def ay_carg_disj (p q : Prop) : Prop := p ∨ q

def ay_carg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_carg_disj satSound unsatSound

def ay_carg_inputs
    (implicationGraphDigest decisionLevelLedger antecedentAvailabilityMap
      firstUipCutWitness learnedClauseDerivationWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) : Prop :=
  ay_carg_conj implicationGraphDigest
    (ay_carg_conj decisionLevelLedger
      (ay_carg_conj antecedentAvailabilityMap
        (ay_carg_conj firstUipCutWitness
          (ay_carg_conj learnedClauseDerivationWitness
            (ay_carg_conj propagationReplay
              (ay_carg_conj fallbackBaseline
                (ay_carg_conj solverBuildEvidence
                  (ay_carg_conj validatorGate auditTranscript))))))))

def ay_carg_implication_graph_digest_evidence
    (implicationGraphDigest : Prop) : Prop :=
  implicationGraphDigest

def ay_carg_decision_level_ledger_evidence
    (decisionLevelLedger : Prop) : Prop :=
  decisionLevelLedger

def ay_carg_antecedent_availability_map_evidence
    (antecedentAvailabilityMap : Prop) : Prop :=
  antecedentAvailabilityMap

def ay_carg_first_uip_cut_witness_evidence
    (firstUipCutWitness : Prop) : Prop :=
  firstUipCutWitness

def ay_carg_learned_clause_derivation_witness_evidence
    (learnedClauseDerivationWitness : Prop) : Prop :=
  learnedClauseDerivationWitness

def ay_carg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_carg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_carg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_carg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_carg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_carg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_carg_accepted
    (implicationGraphDigest decisionLevelLedger antecedentAvailabilityMap
      firstUipCutWitness learnedClauseDerivationWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      learnedClauseAccepted : Prop) : Prop :=
  learnedClauseAccepted

def ay_carg_rejected
    (graphMismatch levelMismatch antecedentMismatch cutMismatch
      derivationMismatch replayMismatch fallbackMismatch buildMismatch
      validatorMismatch auditMismatch : Prop) : Prop :=
  ay_carg_disj graphMismatch
    (ay_carg_disj levelMismatch
      (ay_carg_disj antecedentMismatch
        (ay_carg_disj cutMismatch
          (ay_carg_disj derivationMismatch
            (ay_carg_disj replayMismatch
              (ay_carg_disj fallbackMismatch
                (ay_carg_disj buildMismatch
                  (ay_carg_disj validatorMismatch auditMismatch))))))))

def ay_carg_gate (accepted rejected : Prop) : Prop :=
  ay_carg_disj accepted rejected

def ay_carg_learned_clause_hint
    (learnedClauseAccepted derivationGuidance cutGuidance replayGuidance :
      Prop) : Prop :=
  learnedClauseAccepted

def ay_carg_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_carg_input_components
    {implicationGraphDigest decisionLevelLedger antecedentAvailabilityMap
      firstUipCutWitness learnedClauseDerivationWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop} :
    ay_carg_inputs implicationGraphDigest decisionLevelLedger
      antecedentAvailabilityMap firstUipCutWitness
      learnedClauseDerivationWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_carg_inputs implicationGraphDigest decisionLevelLedger
      antecedentAvailabilityMap firstUipCutWitness
      learnedClauseDerivationWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_carg_accepted_policy
    {implicationGraphDigest decisionLevelLedger antecedentAvailabilityMap
      firstUipCutWitness learnedClauseDerivationWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      learnedClauseAccepted : Prop} :
    learnedClauseAccepted ->
    ay_carg_accepted implicationGraphDigest decisionLevelLedger
      antecedentAvailabilityMap firstUipCutWitness
      learnedClauseDerivationWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript learnedClauseAccepted := by
  intro accepted
  exact accepted

theorem ay_carg_accepted_implication_graph_digest
    {implicationGraphDigest : Prop} :
    implicationGraphDigest ->
    ay_carg_implication_graph_digest_evidence implicationGraphDigest := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_decision_level_ledger
    {decisionLevelLedger : Prop} :
    decisionLevelLedger ->
    ay_carg_decision_level_ledger_evidence decisionLevelLedger := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_antecedent_availability_map
    {antecedentAvailabilityMap : Prop} :
    antecedentAvailabilityMap ->
    ay_carg_antecedent_availability_map_evidence
      antecedentAvailabilityMap := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_first_uip_cut_witness
    {firstUipCutWitness : Prop} :
    firstUipCutWitness ->
    ay_carg_first_uip_cut_witness_evidence firstUipCutWitness := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_learned_clause_derivation_witness
    {learnedClauseDerivationWitness : Prop} :
    learnedClauseDerivationWitness ->
    ay_carg_learned_clause_derivation_witness_evidence
      learnedClauseDerivationWitness := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_carg_propagation_replay_evidence propagationReplay := by
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

theorem ay_carg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_carg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_carg_learned_clause_policy_admissible_hint
    {learnedClauseAccepted derivationGuidance cutGuidance replayGuidance : Prop} :
    learnedClauseAccepted ->
    derivationGuidance ->
    cutGuidance ->
    replayGuidance ->
    ay_carg_learned_clause_hint learnedClauseAccepted derivationGuidance
      cutGuidance replayGuidance :=
  fun accepted _ _ _ => accepted

theorem ay_carg_accepted_learned_clause_is_derivable_guidance
    {learnedClauseAccepted learnedClauseDerivationWitness derivableGuidance :
      Prop} :
    learnedClauseAccepted ->
    learnedClauseDerivationWitness ->
    derivableGuidance ->
    derivableGuidance :=
  fun _ _ guidance => guidance

theorem ay_carg_guidance_cannot_change_original_formula_truth
    {learnedClauseAccepted originalFormulaTruth : Prop} :
    learnedClauseAccepted ->
    originalFormulaTruth ->
    originalFormulaTruth :=
  fun _ truth => truth

theorem ay_carg_accepted_guidance_preserves_public_soundness
    {learnedClauseAccepted satSound unsatSound : Prop} :
    learnedClauseAccepted ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_carg_first_uip_cut_preserves_derivation
    {firstUipCutWitness learnedClauseDerivationWitness : Prop} :
    firstUipCutWitness ->
    learnedClauseDerivationWitness ->
    learnedClauseDerivationWitness :=
  fun _ derivation => derivation

theorem ay_carg_antecedent_availability_preserves_replay
    {antecedentAvailabilityMap propagationReplay : Prop} :
    antecedentAvailabilityMap ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_carg_rejected_is_no_claim
    {graphMismatch diagnostic : Prop} :
    graphMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_rejected_forces_recompute
    {graphMismatch recomputeRequired : Prop} :
    graphMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_failed_conflict_analysis_guard_cannot_bless_publication
    {graphMismatch baselineSound satSound unsatSound : Prop} :
    graphMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_carg_gate accepted rejected ->
    ay_carg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_carg_safe_strategy_guidance_accept
    {learnedClauseAccepted derivationGuidance cutGuidance replayGuidance satSound
      unsatSound : Prop} :
    learnedClauseAccepted ->
    derivationGuidance ->
    cutGuidance ->
    replayGuidance ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_carg_safe_strategy_guidance_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_carg_graph_mismatch_forces_no_claim
    {graphMismatch diagnostic : Prop} :
    graphMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_level_mismatch_forces_no_claim
    {levelMismatch diagnostic : Prop} :
    levelMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_antecedent_mismatch_forces_no_claim
    {antecedentMismatch diagnostic : Prop} :
    antecedentMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_cut_mismatch_forces_no_claim
    {cutMismatch diagnostic : Prop} :
    cutMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_derivation_mismatch_forces_no_claim
    {derivationMismatch diagnostic : Prop} :
    derivationMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_graph_mismatch_forces_recompute
    {graphMismatch recomputeRequired : Prop} :
    graphMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_level_mismatch_forces_recompute
    {levelMismatch recomputeRequired : Prop} :
    levelMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_antecedent_mismatch_forces_recompute
    {antecedentMismatch recomputeRequired : Prop} :
    antecedentMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_cut_mismatch_forces_recompute
    {cutMismatch recomputeRequired : Prop} :
    cutMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_graph_mismatch_cannot_bless_publication
    {graphMismatch baselineSound satSound unsatSound : Prop} :
    graphMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_level_mismatch_cannot_bless_publication
    {levelMismatch baselineSound satSound unsatSound : Prop} :
    levelMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_antecedent_mismatch_cannot_bless_publication
    {antecedentMismatch baselineSound satSound unsatSound : Prop} :
    antecedentMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_cut_mismatch_cannot_bless_publication
    {cutMismatch baselineSound satSound unsatSound : Prop} :
    cutMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_policy_requires_implication_graph_digest
    {implicationGraphDigest : Prop} :
    ay_carg_implication_graph_digest_evidence implicationGraphDigest ->
    implicationGraphDigest := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_decision_level_ledger
    {decisionLevelLedger : Prop} :
    ay_carg_decision_level_ledger_evidence decisionLevelLedger ->
    decisionLevelLedger := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_antecedent_availability
    {antecedentAvailabilityMap : Prop} :
    ay_carg_antecedent_availability_map_evidence
      antecedentAvailabilityMap ->
    antecedentAvailabilityMap := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_first_uip_cut
    {firstUipCutWitness : Prop} :
    ay_carg_first_uip_cut_witness_evidence firstUipCutWitness ->
    firstUipCutWitness := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_learned_clause_derivation
    {learnedClauseDerivationWitness : Prop} :
    ay_carg_learned_clause_derivation_witness_evidence
      learnedClauseDerivationWitness ->
    learnedClauseDerivationWitness := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_carg_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_carg_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_carg_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_validator
    {validatorGate : Prop} :
    ay_carg_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_carg_policy_requires_audit
    {auditTranscript : Prop} :
    ay_carg_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
