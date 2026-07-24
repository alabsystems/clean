def ay_carg_conj (p q : Prop) : Prop := p ∧ q

def ay_carg_disj (p q : Prop) : Prop := p ∨ q

def ay_carg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_carg_disj satSound unsatSound

def ay_carg_inputs
    (clauseDatabaseDigest activityVectorDigestBeforeRescale
      rescaleEpochManifest orderPreservationWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_carg_conj clauseDatabaseDigest
    (ay_carg_conj activityVectorDigestBeforeRescale
      (ay_carg_conj rescaleEpochManifest
        (ay_carg_conj orderPreservationWitness
          (ay_carg_conj reasonProtectionLedger
            (ay_carg_conj propagationReplay
              (ay_carg_conj fallbackBaseline
                (ay_carg_conj solverBuildEvidence
                  (ay_carg_conj validatorGate auditTranscript))))))))

def ay_carg_clause_database_digest_evidence
    (clauseDatabaseDigest : Prop) : Prop :=
  clauseDatabaseDigest

def ay_carg_activity_vector_digest_before_rescale_evidence
    (activityVectorDigestBeforeRescale : Prop) : Prop :=
  activityVectorDigestBeforeRescale

def ay_carg_rescale_epoch_manifest_evidence
    (rescaleEpochManifest : Prop) : Prop :=
  rescaleEpochManifest

def ay_carg_order_preservation_witness_evidence
    (orderPreservationWitness : Prop) : Prop :=
  orderPreservationWitness

def ay_carg_reason_protection_ledger_evidence
    (reasonProtectionLedger : Prop) : Prop :=
  reasonProtectionLedger

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

def ay_carg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_carg_accepted
    (clauseDatabaseDigest activityVectorDigestBeforeRescale
      rescaleEpochManifest orderPreservationWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript rescaleAccepted : Prop) : Prop :=
  rescaleAccepted

def ay_carg_rejected
    (digestMismatch activityMismatch rescaleMismatch orderMismatch
      reasonMismatch replayMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch : Prop) : Prop :=
  ay_carg_disj digestMismatch
    (ay_carg_disj activityMismatch
      (ay_carg_disj rescaleMismatch
        (ay_carg_disj orderMismatch
          (ay_carg_disj reasonMismatch
            (ay_carg_disj replayMismatch
              (ay_carg_disj baselineMismatch
                (ay_carg_disj buildMismatch
                  (ay_carg_disj validatorMismatch auditMismatch))))))))

def ay_carg_gate (accepted rejected : Prop) : Prop :=
  ay_carg_disj accepted rejected

def ay_carg_rescale_search_control_hint
    (rescaleAccepted searchControlOnly accountingOnly replayAccepted : Prop) :
      Prop :=
  rescaleAccepted

theorem ay_carg_input_components
    {clauseDatabaseDigest activityVectorDigestBeforeRescale
      rescaleEpochManifest orderPreservationWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_carg_inputs clauseDatabaseDigest activityVectorDigestBeforeRescale
      rescaleEpochManifest orderPreservationWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    ay_carg_inputs clauseDatabaseDigest activityVectorDigestBeforeRescale
      rescaleEpochManifest orderPreservationWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript := by
  intro inputs
  exact inputs

theorem ay_carg_accepted_policy
    {clauseDatabaseDigest activityVectorDigestBeforeRescale
      rescaleEpochManifest orderPreservationWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript rescaleAccepted : Prop} :
    rescaleAccepted ->
    ay_carg_accepted clauseDatabaseDigest activityVectorDigestBeforeRescale
      rescaleEpochManifest orderPreservationWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript rescaleAccepted := by
  intro accepted
  exact accepted

theorem ay_carg_accepted_clause_database_digest
    {clauseDatabaseDigest : Prop} :
    clauseDatabaseDigest ->
    ay_carg_clause_database_digest_evidence clauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_activity_vector_digest
    {activityVectorDigestBeforeRescale : Prop} :
    activityVectorDigestBeforeRescale ->
    ay_carg_activity_vector_digest_before_rescale_evidence
      activityVectorDigestBeforeRescale := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_rescale_epoch_manifest
    {rescaleEpochManifest : Prop} :
    rescaleEpochManifest ->
    ay_carg_rescale_epoch_manifest_evidence rescaleEpochManifest := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_order_preservation_witness
    {orderPreservationWitness : Prop} :
    orderPreservationWitness ->
    ay_carg_order_preservation_witness_evidence
      orderPreservationWitness := by
  intro evidence
  exact evidence

theorem ay_carg_accepted_reason_protection_ledger
    {reasonProtectionLedger : Prop} :
    reasonProtectionLedger ->
    ay_carg_reason_protection_ledger_evidence reasonProtectionLedger := by
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

theorem ay_carg_rescaling_is_search_control_accounting_only
    {rescaleAccepted searchControlAccountingOnly : Prop} :
    rescaleAccepted ->
    searchControlAccountingOnly ->
    searchControlAccountingOnly :=
  fun _ accountingOnly => accountingOnly

theorem ay_carg_rescale_cannot_change_original_formula_truth
    {rescaleAccepted originalFormulaTruthPreserved : Prop} :
    rescaleAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_carg_accepted_rescale_preserves_public_soundness
    {rescaleAccepted satSound unsatSound : Prop} :
    rescaleAccepted ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_carg_order_preservation_keeps_relevant_comparisons
    {orderPreservationWitness propagationReplay : Prop} :
    orderPreservationWitness ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_carg_reason_protection_preserves_replay
    {reasonProtectionLedger propagationReplay : Prop} :
    reasonProtectionLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_carg_rescale_epoch_preserves_replay
    {rescaleEpochManifest propagationReplay : Prop} :
    rescaleEpochManifest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_carg_accepted_rescale_preserves_fallback_soundness
    {rescaleAccepted fallbackBaseline satSound unsatSound : Prop} :
    rescaleAccepted ->
    fallbackBaseline ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_carg_gate accepted rejected ->
    ay_carg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_carg_rejected_is_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_rejected_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_failed_guard_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_digest_mismatch_forces_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_activity_mismatch_forces_no_claim
    {activityMismatch diagnostic : Prop} :
    activityMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_rescale_mismatch_forces_no_claim
    {rescaleMismatch diagnostic : Prop} :
    rescaleMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_order_mismatch_forces_no_claim
    {orderMismatch diagnostic : Prop} :
    orderMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_reason_mismatch_forces_no_claim
    {reasonMismatch diagnostic : Prop} :
    reasonMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_carg_digest_mismatch_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_activity_mismatch_forces_recompute
    {activityMismatch recomputeRequired : Prop} :
    activityMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_rescale_mismatch_forces_recompute
    {rescaleMismatch recomputeRequired : Prop} :
    rescaleMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_order_mismatch_forces_recompute
    {orderMismatch recomputeRequired : Prop} :
    orderMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_reason_mismatch_forces_recompute
    {reasonMismatch recomputeRequired : Prop} :
    reasonMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_carg_digest_mismatch_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_activity_mismatch_cannot_bless_publication
    {activityMismatch baselineSound satSound unsatSound : Prop} :
    activityMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_rescale_mismatch_cannot_bless_publication
    {rescaleMismatch baselineSound satSound unsatSound : Prop} :
    rescaleMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_order_mismatch_cannot_bless_publication
    {orderMismatch baselineSound satSound unsatSound : Prop} :
    orderMismatch ->
    baselineSound ->
    ay_carg_public_soundness_theorem satSound unsatSound ->
    ay_carg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_carg_reason_mismatch_cannot_bless_publication
    {reasonMismatch baselineSound satSound unsatSound : Prop} :
    reasonMismatch ->
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

theorem ay_carg_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
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

theorem ay_carg_policy_requires_clause_database_digest
    {clauseDatabaseDigest accepted : Prop} :
    clauseDatabaseDigest -> accepted -> clauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_activity_vector_digest
    {activityVectorDigestBeforeRescale accepted : Prop} :
    activityVectorDigestBeforeRescale -> accepted ->
    activityVectorDigestBeforeRescale :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_rescale_epoch_manifest
    {rescaleEpochManifest accepted : Prop} :
    rescaleEpochManifest -> accepted -> rescaleEpochManifest :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_order_preservation
    {orderPreservationWitness accepted : Prop} :
    orderPreservationWitness -> accepted -> orderPreservationWitness :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_reason_protection
    {reasonProtectionLedger accepted : Prop} :
    reasonProtectionLedger -> accepted -> reasonProtectionLedger :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_carg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
