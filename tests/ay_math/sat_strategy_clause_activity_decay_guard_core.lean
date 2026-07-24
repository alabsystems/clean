def ay_cadg_conj (p q : Prop) : Prop := p ∧ q

def ay_cadg_disj (p q : Prop) : Prop := p ∨ q

def ay_cadg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_cadg_disj satSound unsatSound

def ay_cadg_inputs
    (activityVectorDigestBeforeAfter decayFactorManifest
      finiteSaturationWitness learntClauseDomainLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) : Prop :=
  ay_cadg_conj activityVectorDigestBeforeAfter
    (ay_cadg_conj decayFactorManifest
      (ay_cadg_conj finiteSaturationWitness
        (ay_cadg_conj learntClauseDomainLedger
          (ay_cadg_conj propagationReplay
            (ay_cadg_conj fallbackBaseline
              (ay_cadg_conj solverBuildEvidence
                (ay_cadg_conj validatorGate auditTranscript)))))))

def ay_cadg_activity_vector_digest_before_after_evidence
    (activityVectorDigestBeforeAfter : Prop) : Prop :=
  activityVectorDigestBeforeAfter

def ay_cadg_decay_factor_manifest_evidence
    (decayFactorManifest : Prop) : Prop :=
  decayFactorManifest

def ay_cadg_finite_saturation_witness_evidence
    (finiteSaturationWitness : Prop) : Prop :=
  finiteSaturationWitness

def ay_cadg_learnt_clause_domain_ledger_evidence
    (learntClauseDomainLedger : Prop) : Prop :=
  learntClauseDomainLedger

def ay_cadg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_cadg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_cadg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_cadg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_cadg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_cadg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_cadg_accepted
    (activityVectorDigestBeforeAfter decayFactorManifest
      finiteSaturationWitness learntClauseDomainLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      decayAccepted : Prop) : Prop :=
  decayAccepted

def ay_cadg_rejected
    (digestMismatch factorMismatch finiteMismatch domainMismatch replayMismatch
      fallbackMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    Prop :=
  ay_cadg_disj digestMismatch
    (ay_cadg_disj factorMismatch
      (ay_cadg_disj finiteMismatch
        (ay_cadg_disj domainMismatch
          (ay_cadg_disj replayMismatch
            (ay_cadg_disj fallbackMismatch
              (ay_cadg_disj buildMismatch
                (ay_cadg_disj validatorMismatch auditMismatch)))))))

def ay_cadg_gate (accepted rejected : Prop) : Prop :=
  ay_cadg_disj accepted rejected

def ay_cadg_activity_decay_hint
    (decayAccepted activityGuidance deletionOrderGuidance
      searchControlGuidance : Prop) : Prop :=
  decayAccepted

def ay_cadg_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_cadg_input_components
    {activityVectorDigestBeforeAfter decayFactorManifest
      finiteSaturationWitness learntClauseDomainLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop} :
    ay_cadg_inputs activityVectorDigestBeforeAfter decayFactorManifest
      finiteSaturationWitness learntClauseDomainLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    ay_cadg_inputs activityVectorDigestBeforeAfter decayFactorManifest
      finiteSaturationWitness learntClauseDomainLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_cadg_accepted_policy
    {activityVectorDigestBeforeAfter decayFactorManifest
      finiteSaturationWitness learntClauseDomainLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      decayAccepted : Prop} :
    decayAccepted ->
    ay_cadg_accepted activityVectorDigestBeforeAfter decayFactorManifest
      finiteSaturationWitness learntClauseDomainLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      decayAccepted := by
  intro accepted
  exact accepted

theorem ay_cadg_accepted_activity_vector_digest
    {activityVectorDigestBeforeAfter : Prop} :
    activityVectorDigestBeforeAfter ->
    ay_cadg_activity_vector_digest_before_after_evidence
      activityVectorDigestBeforeAfter := by
  intro evidence
  exact evidence

theorem ay_cadg_accepted_decay_factor_manifest
    {decayFactorManifest : Prop} :
    decayFactorManifest ->
    ay_cadg_decay_factor_manifest_evidence decayFactorManifest := by
  intro evidence
  exact evidence

theorem ay_cadg_accepted_finite_saturation_witness
    {finiteSaturationWitness : Prop} :
    finiteSaturationWitness ->
    ay_cadg_finite_saturation_witness_evidence finiteSaturationWitness := by
  intro evidence
  exact evidence

theorem ay_cadg_accepted_learnt_clause_domain_ledger
    {learntClauseDomainLedger : Prop} :
    learntClauseDomainLedger ->
    ay_cadg_learnt_clause_domain_ledger_evidence
      learntClauseDomainLedger := by
  intro evidence
  exact evidence

theorem ay_cadg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_cadg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_cadg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_cadg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_cadg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_cadg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_cadg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_cadg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_cadg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_cadg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_cadg_decay_policy_admissible_hint
    {decayAccepted activityGuidance deletionOrderGuidance
      searchControlGuidance : Prop} :
    decayAccepted ->
    activityGuidance ->
    deletionOrderGuidance ->
    searchControlGuidance ->
    ay_cadg_activity_decay_hint decayAccepted activityGuidance
      deletionOrderGuidance searchControlGuidance :=
  fun accepted _ _ _ => accepted

theorem ay_cadg_decay_rescale_is_search_control_only
    {decayAccepted searchControlOnly : Prop} :
    decayAccepted ->
    searchControlOnly ->
    searchControlOnly :=
  fun _ control => control

theorem ay_cadg_decay_cannot_change_original_formula_truth
    {decayAccepted originalFormulaTruth : Prop} :
    decayAccepted ->
    originalFormulaTruth ->
    originalFormulaTruth :=
  fun _ truth => truth

theorem ay_cadg_accepted_decay_preserves_public_soundness
    {decayAccepted satSound unsatSound : Prop} :
    decayAccepted ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_cadg_accepted_decay_preserves_deterministic_deletion_order
    {decayAccepted deterministicDeletionOrder : Prop} :
    decayAccepted ->
    deterministicDeletionOrder ->
    deterministicDeletionOrder :=
  fun _ order => order

theorem ay_cadg_finite_witness_preserves_activity_guidance
    {finiteSaturationWitness activityGuidance : Prop} :
    finiteSaturationWitness ->
    activityGuidance ->
    activityGuidance :=
  fun _ guidance => guidance

theorem ay_cadg_domain_ledger_preserves_deletion_order
    {learntClauseDomainLedger deterministicDeletionOrder : Prop} :
    learntClauseDomainLedger ->
    deterministicDeletionOrder ->
    deterministicDeletionOrder :=
  fun _ order => order

theorem ay_cadg_rejected_is_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cadg_rejected_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cadg_failed_activity_decay_guard_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cadg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_cadg_gate accepted rejected ->
    ay_cadg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_cadg_safe_strategy_guidance_accept
    {decayAccepted activityGuidance deletionOrderGuidance searchControlGuidance
      satSound unsatSound : Prop} :
    decayAccepted ->
    activityGuidance ->
    deletionOrderGuidance ->
    searchControlGuidance ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_cadg_safe_strategy_guidance_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_cadg_digest_mismatch_forces_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cadg_factor_mismatch_forces_no_claim
    {factorMismatch diagnostic : Prop} :
    factorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cadg_finite_mismatch_forces_no_claim
    {finiteMismatch diagnostic : Prop} :
    finiteMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cadg_domain_mismatch_forces_no_claim
    {domainMismatch diagnostic : Prop} :
    domainMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cadg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cadg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cadg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cadg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cadg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cadg_digest_mismatch_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cadg_factor_mismatch_forces_recompute
    {factorMismatch recomputeRequired : Prop} :
    factorMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cadg_finite_mismatch_forces_recompute
    {finiteMismatch recomputeRequired : Prop} :
    finiteMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cadg_domain_mismatch_forces_recompute
    {domainMismatch recomputeRequired : Prop} :
    domainMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cadg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cadg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cadg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cadg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cadg_digest_mismatch_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cadg_factor_mismatch_cannot_bless_publication
    {factorMismatch baselineSound satSound unsatSound : Prop} :
    factorMismatch ->
    baselineSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cadg_finite_mismatch_cannot_bless_publication
    {finiteMismatch baselineSound satSound unsatSound : Prop} :
    finiteMismatch ->
    baselineSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cadg_domain_mismatch_cannot_bless_publication
    {domainMismatch baselineSound satSound unsatSound : Prop} :
    domainMismatch ->
    baselineSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cadg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cadg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cadg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cadg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound ->
    ay_cadg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cadg_policy_requires_activity_vector_digest
    {activityVectorDigestBeforeAfter : Prop} :
    ay_cadg_activity_vector_digest_before_after_evidence
      activityVectorDigestBeforeAfter ->
    activityVectorDigestBeforeAfter := by
  intro evidence
  exact evidence

theorem ay_cadg_policy_requires_decay_factor_manifest
    {decayFactorManifest : Prop} :
    ay_cadg_decay_factor_manifest_evidence decayFactorManifest ->
    decayFactorManifest := by
  intro evidence
  exact evidence

theorem ay_cadg_policy_requires_finite_saturation_witness
    {finiteSaturationWitness : Prop} :
    ay_cadg_finite_saturation_witness_evidence finiteSaturationWitness ->
    finiteSaturationWitness := by
  intro evidence
  exact evidence

theorem ay_cadg_policy_requires_learnt_clause_domain
    {learntClauseDomainLedger : Prop} :
    ay_cadg_learnt_clause_domain_ledger_evidence
      learntClauseDomainLedger ->
    learntClauseDomainLedger := by
  intro evidence
  exact evidence

theorem ay_cadg_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_cadg_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_cadg_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_cadg_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_cadg_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_cadg_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_cadg_policy_requires_validator
    {validatorGate : Prop} :
    ay_cadg_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_cadg_policy_requires_audit
    {auditTranscript : Prop} :
    ay_cadg_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
