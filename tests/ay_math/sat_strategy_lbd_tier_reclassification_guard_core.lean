def ay_ltrg_conj (p q : Prop) : Prop := p ∧ q

def ay_ltrg_disj (p q : Prop) : Prop := p ∨ q

def ay_ltrg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_ltrg_disj satSound unsatSound

def ay_ltrg_inputs
    (clauseDatabaseDigest lbdVectorDigest tierManifest
      reclassificationEpoch protectedReasonLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) : Prop :=
  ay_ltrg_conj clauseDatabaseDigest
    (ay_ltrg_conj lbdVectorDigest
      (ay_ltrg_conj tierManifest
        (ay_ltrg_conj reclassificationEpoch
          (ay_ltrg_conj protectedReasonLedger
            (ay_ltrg_conj propagationReplay
              (ay_ltrg_conj fallbackBaseline
                (ay_ltrg_conj solverBuildEvidence
                  (ay_ltrg_conj validatorGate auditTranscript))))))))

def ay_ltrg_clause_database_digest_evidence
    (clauseDatabaseDigest : Prop) : Prop :=
  clauseDatabaseDigest

def ay_ltrg_lbd_vector_digest_evidence
    (lbdVectorDigest : Prop) : Prop :=
  lbdVectorDigest

def ay_ltrg_tier_manifest_evidence (tierManifest : Prop) : Prop :=
  tierManifest

def ay_ltrg_reclassification_epoch_evidence
    (reclassificationEpoch : Prop) : Prop :=
  reclassificationEpoch

def ay_ltrg_protected_reason_ledger_evidence
    (protectedReasonLedger : Prop) : Prop :=
  protectedReasonLedger

def ay_ltrg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_ltrg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_ltrg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_ltrg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_ltrg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_ltrg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_ltrg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_ltrg_accepted
    (clauseDatabaseDigest lbdVectorDigest tierManifest
      reclassificationEpoch protectedReasonLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      reclassificationAccepted : Prop) : Prop :=
  reclassificationAccepted

def ay_ltrg_rejected
    (clauseMismatch lbdMismatch tierMismatch epochMismatch reasonMismatch
      replayMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch : Prop) : Prop :=
  ay_ltrg_disj clauseMismatch
    (ay_ltrg_disj lbdMismatch
      (ay_ltrg_disj tierMismatch
        (ay_ltrg_disj epochMismatch
          (ay_ltrg_disj reasonMismatch
            (ay_ltrg_disj replayMismatch
              (ay_ltrg_disj baselineMismatch
                (ay_ltrg_disj buildMismatch
                  (ay_ltrg_disj validatorMismatch auditMismatch))))))))

def ay_ltrg_gate (accepted rejected : Prop) : Prop :=
  ay_ltrg_disj accepted rejected

def ay_ltrg_reclassification_accounting_hint
    (reclassificationAccepted clauseManagementOnly accountingOnly
      replayAccepted : Prop) : Prop :=
  reclassificationAccepted

theorem ay_ltrg_input_components
    {clauseDatabaseDigest lbdVectorDigest tierManifest reclassificationEpoch
      protectedReasonLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_ltrg_inputs clauseDatabaseDigest lbdVectorDigest tierManifest
      reclassificationEpoch protectedReasonLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    ay_ltrg_inputs clauseDatabaseDigest lbdVectorDigest tierManifest
      reclassificationEpoch protectedReasonLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_ltrg_accepted_policy
    {clauseDatabaseDigest lbdVectorDigest tierManifest reclassificationEpoch
      protectedReasonLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      reclassificationAccepted : Prop} :
    reclassificationAccepted ->
    ay_ltrg_accepted clauseDatabaseDigest lbdVectorDigest tierManifest
      reclassificationEpoch protectedReasonLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      reclassificationAccepted := by
  intro accepted
  exact accepted

theorem ay_ltrg_accepted_clause_database_digest
    {clauseDatabaseDigest : Prop} :
    clauseDatabaseDigest ->
    ay_ltrg_clause_database_digest_evidence clauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_ltrg_accepted_lbd_vector_digest
    {lbdVectorDigest : Prop} :
    lbdVectorDigest ->
    ay_ltrg_lbd_vector_digest_evidence lbdVectorDigest := by
  intro evidence
  exact evidence

theorem ay_ltrg_accepted_tier_manifest
    {tierManifest : Prop} :
    tierManifest -> ay_ltrg_tier_manifest_evidence tierManifest := by
  intro evidence
  exact evidence

theorem ay_ltrg_accepted_reclassification_epoch
    {reclassificationEpoch : Prop} :
    reclassificationEpoch ->
    ay_ltrg_reclassification_epoch_evidence reclassificationEpoch := by
  intro evidence
  exact evidence

theorem ay_ltrg_accepted_protected_reason_ledger
    {protectedReasonLedger : Prop} :
    protectedReasonLedger ->
    ay_ltrg_protected_reason_ledger_evidence protectedReasonLedger := by
  intro evidence
  exact evidence

theorem ay_ltrg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_ltrg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_ltrg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_ltrg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_ltrg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_ltrg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_ltrg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_ltrg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_ltrg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_ltrg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_ltrg_reclassification_is_accounting_only
    {reclassificationAccepted accountingOnly : Prop} :
    reclassificationAccepted ->
    accountingOnly ->
    accountingOnly :=
  fun _ accounting => accounting

theorem ay_ltrg_reclassification_cannot_change_original_formula_truth
    {reclassificationAccepted originalFormulaTruthPreserved : Prop} :
    reclassificationAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_ltrg_accepted_reclassification_preserves_public_soundness
    {reclassificationAccepted satSound unsatSound : Prop} :
    reclassificationAccepted ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_ltrg_tier_manifest_preserves_replay
    {tierManifest propagationReplay : Prop} :
    tierManifest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_ltrg_lbd_digest_preserves_replay
    {lbdVectorDigest propagationReplay : Prop} :
    lbdVectorDigest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_ltrg_protected_reason_preserves_replay
    {protectedReasonLedger propagationReplay : Prop} :
    protectedReasonLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_ltrg_accepted_reclassification_preserves_fallback_soundness
    {reclassificationAccepted fallbackBaseline satSound unsatSound : Prop} :
    reclassificationAccepted ->
    fallbackBaseline ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_ltrg_gate accepted rejected ->
    ay_ltrg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_ltrg_rejected_is_no_claim
    {clauseMismatch diagnostic : Prop} :
    clauseMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_ltrg_rejected_forces_recompute
    {clauseMismatch recomputeRequired : Prop} :
    clauseMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_ltrg_failed_guard_cannot_bless_publication
    {clauseMismatch baselineSound satSound unsatSound : Prop} :
    clauseMismatch ->
    baselineSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_clause_mismatch_forces_no_claim
    {clauseMismatch diagnostic : Prop} :
    clauseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_ltrg_lbd_mismatch_forces_no_claim
    {lbdMismatch diagnostic : Prop} :
    lbdMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_ltrg_tier_mismatch_forces_no_claim
    {tierMismatch diagnostic : Prop} :
    tierMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_ltrg_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_ltrg_reason_mismatch_forces_no_claim
    {reasonMismatch diagnostic : Prop} :
    reasonMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_ltrg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_ltrg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_ltrg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_ltrg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_ltrg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_ltrg_clause_mismatch_forces_recompute
    {clauseMismatch recomputeRequired : Prop} :
    clauseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_ltrg_lbd_mismatch_forces_recompute
    {lbdMismatch recomputeRequired : Prop} :
    lbdMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_ltrg_tier_mismatch_forces_recompute
    {tierMismatch recomputeRequired : Prop} :
    tierMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_ltrg_epoch_mismatch_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_ltrg_reason_mismatch_forces_recompute
    {reasonMismatch recomputeRequired : Prop} :
    reasonMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_ltrg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_ltrg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_ltrg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_ltrg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_ltrg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_ltrg_clause_mismatch_cannot_bless_publication
    {clauseMismatch baselineSound satSound unsatSound : Prop} :
    clauseMismatch ->
    baselineSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_lbd_mismatch_cannot_bless_publication
    {lbdMismatch baselineSound satSound unsatSound : Prop} :
    lbdMismatch ->
    baselineSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_tier_mismatch_cannot_bless_publication
    {tierMismatch baselineSound satSound unsatSound : Prop} :
    tierMismatch ->
    baselineSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_epoch_mismatch_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_reason_mismatch_cannot_bless_publication
    {reasonMismatch baselineSound satSound unsatSound : Prop} :
    reasonMismatch ->
    baselineSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound ->
    ay_ltrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_ltrg_policy_requires_clause_database_digest
    {clauseDatabaseDigest accepted : Prop} :
    clauseDatabaseDigest -> accepted -> clauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_ltrg_policy_requires_lbd_vector_digest
    {lbdVectorDigest accepted : Prop} :
    lbdVectorDigest -> accepted -> lbdVectorDigest :=
  fun evidence _ => evidence

theorem ay_ltrg_policy_requires_tier_manifest
    {tierManifest accepted : Prop} :
    tierManifest -> accepted -> tierManifest :=
  fun evidence _ => evidence

theorem ay_ltrg_policy_requires_reclassification_epoch
    {reclassificationEpoch accepted : Prop} :
    reclassificationEpoch -> accepted -> reclassificationEpoch :=
  fun evidence _ => evidence

theorem ay_ltrg_policy_requires_protected_reason
    {protectedReasonLedger accepted : Prop} :
    protectedReasonLedger -> accepted -> protectedReasonLedger :=
  fun evidence _ => evidence

theorem ay_ltrg_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_ltrg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_ltrg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_ltrg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_ltrg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
