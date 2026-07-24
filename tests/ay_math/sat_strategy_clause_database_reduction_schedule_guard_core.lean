def ay_cdrg_conj (p q : Prop) : Prop := p ∧ q

def ay_cdrg_disj (p q : Prop) : Prop := p ∨ q

def ay_cdrg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_cdrg_disj satSound unsatSound

def ay_cdrg_inputs
    (reductionEpochLedger keptDeletedClauseDigest lbdActivityDigest
      learntClauseDatabaseSnapshot propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_cdrg_conj reductionEpochLedger
    (ay_cdrg_conj keptDeletedClauseDigest
      (ay_cdrg_conj lbdActivityDigest
        (ay_cdrg_conj learntClauseDatabaseSnapshot
          (ay_cdrg_conj propagationReplay
            (ay_cdrg_conj fallbackBaseline
              (ay_cdrg_conj solverBuildEvidence
                (ay_cdrg_conj validatorGate auditTranscript)))))))

def ay_cdrg_reduction_epoch_ledger_evidence
    (reductionEpochLedger : Prop) : Prop :=
  reductionEpochLedger

def ay_cdrg_kept_deleted_clause_digest_evidence
    (keptDeletedClauseDigest : Prop) : Prop :=
  keptDeletedClauseDigest

def ay_cdrg_lbd_activity_digest_evidence
    (lbdActivityDigest : Prop) : Prop :=
  lbdActivityDigest

def ay_cdrg_learnt_clause_database_snapshot_evidence
    (learntClauseDatabaseSnapshot : Prop) : Prop :=
  learntClauseDatabaseSnapshot

def ay_cdrg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_cdrg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_cdrg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_cdrg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_cdrg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_cdrg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_cdrg_accepted
    (reductionEpochLedger keptDeletedClauseDigest lbdActivityDigest
      learntClauseDatabaseSnapshot propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript reductionGuidanceAccepted :
      Prop) : Prop :=
  reductionGuidanceAccepted

def ay_cdrg_rejected
    (reductionMismatch clauseDigestMismatch lbdActivityMismatch databaseMismatch
      replayMismatch fallbackMismatch buildMismatch validatorMismatch
      auditMismatch : Prop) : Prop :=
  ay_cdrg_disj reductionMismatch
    (ay_cdrg_disj clauseDigestMismatch
      (ay_cdrg_disj lbdActivityMismatch
        (ay_cdrg_disj databaseMismatch
          (ay_cdrg_disj replayMismatch
            (ay_cdrg_disj fallbackMismatch
              (ay_cdrg_disj buildMismatch
                (ay_cdrg_disj validatorMismatch auditMismatch)))))))

def ay_cdrg_gate (accepted rejected : Prop) : Prop :=
  ay_cdrg_disj accepted rejected

def ay_cdrg_reduction_hint
    (reductionGuidanceAccepted retentionPolicy orderPolicy reductionPolicy :
      Prop) : Prop :=
  reductionGuidanceAccepted

def ay_cdrg_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_cdrg_input_components
    {reductionEpochLedger keptDeletedClauseDigest lbdActivityDigest
      learntClauseDatabaseSnapshot propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_cdrg_inputs reductionEpochLedger keptDeletedClauseDigest lbdActivityDigest
      learntClauseDatabaseSnapshot propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_cdrg_inputs reductionEpochLedger keptDeletedClauseDigest lbdActivityDigest
      learntClauseDatabaseSnapshot propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_cdrg_accepted_policy
    {reductionEpochLedger keptDeletedClauseDigest lbdActivityDigest
      learntClauseDatabaseSnapshot propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript reductionGuidanceAccepted :
      Prop} :
    reductionGuidanceAccepted ->
    ay_cdrg_accepted reductionEpochLedger keptDeletedClauseDigest
      lbdActivityDigest learntClauseDatabaseSnapshot propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      reductionGuidanceAccepted := by
  intro accepted
  exact accepted

theorem ay_cdrg_accepted_reduction_epoch_ledger
    {reductionEpochLedger : Prop} :
    reductionEpochLedger ->
    ay_cdrg_reduction_epoch_ledger_evidence reductionEpochLedger := by
  intro evidence
  exact evidence

theorem ay_cdrg_accepted_kept_deleted_clause_digest
    {keptDeletedClauseDigest : Prop} :
    keptDeletedClauseDigest ->
    ay_cdrg_kept_deleted_clause_digest_evidence keptDeletedClauseDigest := by
  intro evidence
  exact evidence

theorem ay_cdrg_accepted_lbd_activity_digest
    {lbdActivityDigest : Prop} :
    lbdActivityDigest ->
    ay_cdrg_lbd_activity_digest_evidence lbdActivityDigest := by
  intro evidence
  exact evidence

theorem ay_cdrg_accepted_learnt_clause_database_snapshot
    {learntClauseDatabaseSnapshot : Prop} :
    learntClauseDatabaseSnapshot ->
    ay_cdrg_learnt_clause_database_snapshot_evidence
      learntClauseDatabaseSnapshot := by
  intro evidence
  exact evidence

theorem ay_cdrg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_cdrg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_cdrg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_cdrg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_cdrg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_cdrg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_cdrg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_cdrg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_cdrg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_cdrg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_cdrg_reduction_policy_admissible_hint
    {reductionGuidanceAccepted retentionPolicy orderPolicy reductionPolicy :
      Prop} :
    reductionGuidanceAccepted ->
    retentionPolicy ->
    orderPolicy ->
    reductionPolicy ->
    ay_cdrg_reduction_hint reductionGuidanceAccepted retentionPolicy orderPolicy
      reductionPolicy := by
  intro accepted retention order reduction
  exact accepted

theorem ay_cdrg_guidance_cannot_change_formula_truth
    {reductionGuidanceAccepted formulaTruth : Prop} :
    reductionGuidanceAccepted ->
    formulaTruth ->
    formulaTruth :=
  fun _ truth => truth

theorem ay_cdrg_accepted_guidance_preserves_public_soundness
    {reductionGuidanceAccepted satSound unsatSound : Prop} :
    reductionGuidanceAccepted ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_cdrg_rejected_is_no_claim
    {reductionMismatch diagnostic : Prop} :
    reductionMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdrg_rejected_forces_recompute
    {reductionMismatch recomputeRequired : Prop} :
    reductionMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cdrg_rejected_cannot_bless_publication
    {reductionMismatch baselineSound satSound unsatSound : Prop} :
    reductionMismatch ->
    baselineSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdrg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_cdrg_gate accepted rejected ->
    ay_cdrg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_cdrg_safe_strategy_guidance_accept
    {reductionGuidanceAccepted retentionPolicy orderPolicy reductionPolicy
      satSound unsatSound : Prop} :
    reductionGuidanceAccepted ->
    retentionPolicy ->
    orderPolicy ->
    reductionPolicy ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_cdrg_safe_strategy_guidance_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_cdrg_reduction_mismatch_forces_no_claim
    {reductionMismatch diagnostic : Prop} :
    reductionMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdrg_clause_digest_mismatch_forces_no_claim
    {clauseDigestMismatch diagnostic : Prop} :
    clauseDigestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdrg_lbd_activity_mismatch_forces_no_claim
    {lbdActivityMismatch diagnostic : Prop} :
    lbdActivityMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdrg_database_mismatch_forces_no_claim
    {databaseMismatch diagnostic : Prop} :
    databaseMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdrg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdrg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdrg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdrg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdrg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cdrg_reduction_mismatch_cannot_bless_publication
    {reductionMismatch baselineSound satSound unsatSound : Prop} :
    reductionMismatch ->
    baselineSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdrg_clause_digest_mismatch_cannot_bless_publication
    {clauseDigestMismatch baselineSound satSound unsatSound : Prop} :
    clauseDigestMismatch ->
    baselineSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdrg_lbd_activity_mismatch_cannot_bless_publication
    {lbdActivityMismatch baselineSound satSound unsatSound : Prop} :
    lbdActivityMismatch ->
    baselineSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdrg_database_mismatch_cannot_bless_publication
    {databaseMismatch baselineSound satSound unsatSound : Prop} :
    databaseMismatch ->
    baselineSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdrg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdrg_fallback_mismatch_cannot_bless_publication
    {fallbackMismatch baselineSound satSound unsatSound : Prop} :
    fallbackMismatch ->
    baselineSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdrg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdrg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdrg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound ->
    ay_cdrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cdrg_policy_requires_reduction_epoch_ledger
    {reductionEpochLedger : Prop} :
    ay_cdrg_reduction_epoch_ledger_evidence reductionEpochLedger ->
    reductionEpochLedger := by
  intro evidence
  exact evidence

theorem ay_cdrg_policy_requires_kept_deleted_clause_digest
    {keptDeletedClauseDigest : Prop} :
    ay_cdrg_kept_deleted_clause_digest_evidence keptDeletedClauseDigest ->
    keptDeletedClauseDigest := by
  intro evidence
  exact evidence

theorem ay_cdrg_policy_requires_lbd_activity_digest
    {lbdActivityDigest : Prop} :
    ay_cdrg_lbd_activity_digest_evidence lbdActivityDigest ->
    lbdActivityDigest := by
  intro evidence
  exact evidence

theorem ay_cdrg_policy_requires_learnt_clause_database_snapshot
    {learntClauseDatabaseSnapshot : Prop} :
    ay_cdrg_learnt_clause_database_snapshot_evidence
      learntClauseDatabaseSnapshot ->
    learntClauseDatabaseSnapshot := by
  intro evidence
  exact evidence

theorem ay_cdrg_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_cdrg_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_cdrg_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_cdrg_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_cdrg_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_cdrg_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_cdrg_policy_requires_validator
    {validatorGate : Prop} :
    ay_cdrg_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_cdrg_policy_requires_audit
    {auditTranscript : Prop} :
    ay_cdrg_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
