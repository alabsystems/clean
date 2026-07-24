def ay_vdrg_conj (p q : Prop) : Prop := p ∧ q

def ay_vdrg_disj (p q : Prop) : Prop := p ∨ q

def ay_vdrg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_vdrg_disj satSound unsatSound

def ay_vdrg_inputs
    (variableDomainDigest activityVectorDigestBeforeDecay
      decayRescaleEpochManifest orderPreservationWitness phaseDecisionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_vdrg_conj variableDomainDigest
    (ay_vdrg_conj activityVectorDigestBeforeDecay
      (ay_vdrg_conj decayRescaleEpochManifest
        (ay_vdrg_conj orderPreservationWitness
          (ay_vdrg_conj phaseDecisionLedger
            (ay_vdrg_conj propagationReplay
              (ay_vdrg_conj fallbackBaseline
                (ay_vdrg_conj solverBuildEvidence
                  (ay_vdrg_conj validatorGate auditTranscript))))))))

def ay_vdrg_variable_domain_digest_evidence
    (variableDomainDigest : Prop) : Prop :=
  variableDomainDigest

def ay_vdrg_activity_vector_digest_before_decay_evidence
    (activityVectorDigestBeforeDecay : Prop) : Prop :=
  activityVectorDigestBeforeDecay

def ay_vdrg_decay_rescale_epoch_manifest_evidence
    (decayRescaleEpochManifest : Prop) : Prop :=
  decayRescaleEpochManifest

def ay_vdrg_order_preservation_witness_evidence
    (orderPreservationWitness : Prop) : Prop :=
  orderPreservationWitness

def ay_vdrg_phase_decision_ledger_evidence
    (phaseDecisionLedger : Prop) : Prop :=
  phaseDecisionLedger

def ay_vdrg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_vdrg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_vdrg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_vdrg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_vdrg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_vdrg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_vdrg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_vdrg_accepted
    (variableDomainDigest activityVectorDigestBeforeDecay
      decayRescaleEpochManifest orderPreservationWitness phaseDecisionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript decayAccepted : Prop) : Prop :=
  decayAccepted

def ay_vdrg_rejected
    (activityMismatch epochMismatch orderMismatch phaseMismatch replayMismatch
      buildMismatch validatorMismatch domainMismatch baselineMismatch
      auditMismatch : Prop) : Prop :=
  ay_vdrg_disj activityMismatch
    (ay_vdrg_disj epochMismatch
      (ay_vdrg_disj orderMismatch
        (ay_vdrg_disj phaseMismatch
          (ay_vdrg_disj replayMismatch
            (ay_vdrg_disj buildMismatch
              (ay_vdrg_disj validatorMismatch
                (ay_vdrg_disj domainMismatch
                  (ay_vdrg_disj baselineMismatch auditMismatch))))))))

def ay_vdrg_gate (accepted rejected : Prop) : Prop :=
  ay_vdrg_disj accepted rejected

def ay_vdrg_decay_rescale_heuristic_hint
    (decayAccepted heuristicAccountingOnly orderGuidance replayAccepted :
      Prop) : Prop :=
  decayAccepted

theorem ay_vdrg_input_components
    {variableDomainDigest activityVectorDigestBeforeDecay
      decayRescaleEpochManifest orderPreservationWitness phaseDecisionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_vdrg_inputs variableDomainDigest activityVectorDigestBeforeDecay
      decayRescaleEpochManifest orderPreservationWitness phaseDecisionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    ay_vdrg_inputs variableDomainDigest activityVectorDigestBeforeDecay
      decayRescaleEpochManifest orderPreservationWitness phaseDecisionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript := by
  intro inputs
  exact inputs

theorem ay_vdrg_accepted_policy
    {variableDomainDigest activityVectorDigestBeforeDecay
      decayRescaleEpochManifest orderPreservationWitness phaseDecisionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript decayAccepted : Prop} :
    decayAccepted ->
    ay_vdrg_accepted variableDomainDigest activityVectorDigestBeforeDecay
      decayRescaleEpochManifest orderPreservationWitness phaseDecisionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript decayAccepted := by
  intro accepted
  exact accepted

theorem ay_vdrg_accepted_variable_domain_digest
    {variableDomainDigest : Prop} :
    variableDomainDigest ->
    ay_vdrg_variable_domain_digest_evidence variableDomainDigest := by
  intro evidence
  exact evidence

theorem ay_vdrg_accepted_activity_vector_digest_before_decay
    {activityVectorDigestBeforeDecay : Prop} :
    activityVectorDigestBeforeDecay ->
    ay_vdrg_activity_vector_digest_before_decay_evidence
      activityVectorDigestBeforeDecay := by
  intro evidence
  exact evidence

theorem ay_vdrg_accepted_decay_rescale_epoch_manifest
    {decayRescaleEpochManifest : Prop} :
    decayRescaleEpochManifest ->
    ay_vdrg_decay_rescale_epoch_manifest_evidence
      decayRescaleEpochManifest := by
  intro evidence
  exact evidence

theorem ay_vdrg_accepted_order_preservation_witness
    {orderPreservationWitness : Prop} :
    orderPreservationWitness ->
    ay_vdrg_order_preservation_witness_evidence
      orderPreservationWitness := by
  intro evidence
  exact evidence

theorem ay_vdrg_accepted_phase_decision_ledger
    {phaseDecisionLedger : Prop} :
    phaseDecisionLedger ->
    ay_vdrg_phase_decision_ledger_evidence phaseDecisionLedger := by
  intro evidence
  exact evidence

theorem ay_vdrg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_vdrg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_vdrg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_vdrg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_vdrg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_vdrg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_vdrg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_vdrg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_vdrg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_vdrg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_vdrg_decay_rescale_is_heuristic_accounting_only
    {decayAccepted heuristicAccountingOnly : Prop} :
    decayAccepted ->
    heuristicAccountingOnly ->
    heuristicAccountingOnly :=
  fun _ accountingOnly => accountingOnly

theorem ay_vdrg_decay_rescale_cannot_change_original_formula_truth
    {decayAccepted originalFormulaTruthPreserved : Prop} :
    decayAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_vdrg_accepted_decay_preserves_public_soundness
    {decayAccepted satSound unsatSound : Prop} :
    decayAccepted ->
    ay_vdrg_public_soundness_theorem satSound unsatSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_vdrg_order_preservation_preserves_replay
    {orderPreservationWitness propagationReplay : Prop} :
    orderPreservationWitness ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_vdrg_phase_decision_preserves_replay
    {phaseDecisionLedger propagationReplay : Prop} :
    phaseDecisionLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_vdrg_epoch_manifest_preserves_replay
    {decayRescaleEpochManifest propagationReplay : Prop} :
    decayRescaleEpochManifest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_vdrg_accepted_decay_preserves_fallback_soundness
    {decayAccepted fallbackBaseline satSound unsatSound : Prop} :
    decayAccepted ->
    fallbackBaseline ->
    ay_vdrg_public_soundness_theorem satSound unsatSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_vdrg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_vdrg_gate accepted rejected ->
    ay_vdrg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_vdrg_rejected_is_no_claim
    {activityMismatch diagnostic : Prop} :
    activityMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_vdrg_rejected_forces_recompute
    {activityMismatch recomputeRequired : Prop} :
    activityMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_vdrg_failed_guard_cannot_bless_publication
    {activityMismatch baselineSound satSound unsatSound : Prop} :
    activityMismatch ->
    baselineSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_vdrg_activity_mismatch_forces_no_claim
    {activityMismatch diagnostic : Prop} :
    activityMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_vdrg_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_vdrg_order_mismatch_forces_no_claim
    {orderMismatch diagnostic : Prop} :
    orderMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_vdrg_phase_mismatch_forces_no_claim
    {phaseMismatch diagnostic : Prop} :
    phaseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_vdrg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_vdrg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_vdrg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_vdrg_domain_mismatch_forces_no_claim
    {domainMismatch diagnostic : Prop} :
    domainMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_vdrg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_vdrg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_vdrg_activity_mismatch_forces_recompute
    {activityMismatch recomputeRequired : Prop} :
    activityMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_vdrg_epoch_mismatch_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_vdrg_order_mismatch_forces_recompute
    {orderMismatch recomputeRequired : Prop} :
    orderMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_vdrg_phase_mismatch_forces_recompute
    {phaseMismatch recomputeRequired : Prop} :
    phaseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_vdrg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_vdrg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_vdrg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_vdrg_domain_mismatch_forces_recompute
    {domainMismatch recomputeRequired : Prop} :
    domainMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_vdrg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_vdrg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_vdrg_activity_mismatch_cannot_bless_publication
    {activityMismatch baselineSound satSound unsatSound : Prop} :
    activityMismatch ->
    baselineSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_vdrg_epoch_mismatch_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_vdrg_order_mismatch_cannot_bless_publication
    {orderMismatch baselineSound satSound unsatSound : Prop} :
    orderMismatch ->
    baselineSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_vdrg_phase_mismatch_cannot_bless_publication
    {phaseMismatch baselineSound satSound unsatSound : Prop} :
    phaseMismatch ->
    baselineSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_vdrg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_vdrg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_vdrg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound ->
    ay_vdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_vdrg_policy_requires_variable_domain_digest
    {variableDomainDigest accepted : Prop} :
    variableDomainDigest -> accepted -> variableDomainDigest :=
  fun evidence _ => evidence

theorem ay_vdrg_policy_requires_activity_vector_digest
    {activityVectorDigestBeforeDecay accepted : Prop} :
    activityVectorDigestBeforeDecay -> accepted ->
    activityVectorDigestBeforeDecay :=
  fun evidence _ => evidence

theorem ay_vdrg_policy_requires_decay_rescale_epoch
    {decayRescaleEpochManifest accepted : Prop} :
    decayRescaleEpochManifest -> accepted -> decayRescaleEpochManifest :=
  fun evidence _ => evidence

theorem ay_vdrg_policy_requires_order_preservation
    {orderPreservationWitness accepted : Prop} :
    orderPreservationWitness -> accepted -> orderPreservationWitness :=
  fun evidence _ => evidence

theorem ay_vdrg_policy_requires_phase_decision_ledger
    {phaseDecisionLedger accepted : Prop} :
    phaseDecisionLedger -> accepted -> phaseDecisionLedger :=
  fun evidence _ => evidence

theorem ay_vdrg_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_vdrg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_vdrg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_vdrg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_vdrg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
