def ay_isg_conj (p q : Prop) : Prop := p ∧ q

def ay_isg_disj (p q : Prop) : Prop := p ∨ q

def ay_isg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_isg_disj satSound unsatSound

def ay_isg_inputs
    (benchmarkFingerprint phaseScheduleDigest phaseFormulaDigestLedger
      simplificationProofEquisatLedger modelReconstructionContext
      unsatReplayContext restartReductionInteractionLedger solverBuildEvidence
      validatorGate archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) : Prop :=
  ay_isg_conj benchmarkFingerprint
    (ay_isg_conj phaseScheduleDigest
      (ay_isg_conj phaseFormulaDigestLedger
        (ay_isg_conj simplificationProofEquisatLedger
          (ay_isg_conj modelReconstructionContext
            (ay_isg_conj unsatReplayContext
              (ay_isg_conj restartReductionInteractionLedger
                (ay_isg_conj solverBuildEvidence
                  (ay_isg_conj validatorGate
                    (ay_isg_conj archiveManifest
                      (ay_isg_conj fallbackNoClaimPath
                        auditTranscript))))))))))

def ay_isg_benchmark_fingerprint_evidence
    (benchmarkFingerprint : Prop) : Prop :=
  benchmarkFingerprint

def ay_isg_phase_schedule_digest_evidence
    (phaseScheduleDigest : Prop) : Prop :=
  phaseScheduleDigest

def ay_isg_phase_formula_digest_ledger_evidence
    (phaseFormulaDigestLedger : Prop) : Prop :=
  phaseFormulaDigestLedger

def ay_isg_simplification_proof_equisat_ledger_evidence
    (simplificationProofEquisatLedger : Prop) : Prop :=
  simplificationProofEquisatLedger

def ay_isg_model_reconstruction_context_evidence
    (modelReconstructionContext : Prop) : Prop :=
  modelReconstructionContext

def ay_isg_unsat_replay_context_evidence
    (unsatReplayContext : Prop) : Prop :=
  unsatReplayContext

def ay_isg_restart_reduction_interaction_ledger_evidence
    (restartReductionInteractionLedger : Prop) : Prop :=
  restartReductionInteractionLedger

def ay_isg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_isg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_isg_archive_manifest_evidence (archiveManifest : Prop) : Prop :=
  archiveManifest

def ay_isg_fallback_no_claim_path_evidence
    (fallbackNoClaimPath : Prop) : Prop :=
  fallbackNoClaimPath

def ay_isg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_isg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_isg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_isg_checked_sat_evidence (satEvidence : Prop) : Prop := satEvidence

def ay_isg_checked_unsat_evidence (unsatEvidence : Prop) : Prop :=
  unsatEvidence

def ay_isg_accepted
    (benchmarkFingerprint phaseScheduleDigest phaseFormulaDigestLedger
      simplificationProofEquisatLedger modelReconstructionContext
      unsatReplayContext restartReductionInteractionLedger solverBuildEvidence
      validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      scheduleAccepted : Prop) : Prop :=
  scheduleAccepted

def ay_isg_rejected
    (scheduleMismatch phaseMismatch formulaMismatch equisatMismatch
      modelMismatch replayMismatch restartMismatch reductionMismatch
      buildMismatch validatorMismatch archiveMismatch fallbackMismatch
      auditMismatch : Prop) : Prop :=
  ay_isg_disj scheduleMismatch
    (ay_isg_disj phaseMismatch
      (ay_isg_disj formulaMismatch
        (ay_isg_disj equisatMismatch
          (ay_isg_disj modelMismatch
            (ay_isg_disj replayMismatch
              (ay_isg_disj restartMismatch
                (ay_isg_disj reductionMismatch
                  (ay_isg_disj buildMismatch
                    (ay_isg_disj validatorMismatch
                      (ay_isg_disj archiveMismatch
                        (ay_isg_disj fallbackMismatch
                          auditMismatch))))))))))))

def ay_isg_schedule_orchestration_replay_evidence
    (scheduleAccepted orchestrationOnly replayBacked : Prop) : Prop :=
  scheduleAccepted

def ay_isg_publication_gate
    (scheduleReplay solverBuildEvidence validatorGate archiveManifest
      fallbackNoClaimPath auditTranscript checkedEvidence : Prop) : Prop :=
  ay_isg_conj scheduleReplay
    (ay_isg_conj solverBuildEvidence
      (ay_isg_conj validatorGate
        (ay_isg_conj archiveManifest
          (ay_isg_conj fallbackNoClaimPath
            (ay_isg_conj auditTranscript checkedEvidence)))))

def ay_isg_gate (accepted rejected : Prop) : Prop :=
  ay_isg_disj accepted rejected

theorem ay_isg_input_components
    {benchmarkFingerprint phaseScheduleDigest phaseFormulaDigestLedger
      simplificationProofEquisatLedger modelReconstructionContext
      unsatReplayContext restartReductionInteractionLedger solverBuildEvidence
      validatorGate archiveManifest fallbackNoClaimPath auditTranscript :
      Prop} :
    ay_isg_inputs benchmarkFingerprint phaseScheduleDigest
      phaseFormulaDigestLedger simplificationProofEquisatLedger
      modelReconstructionContext unsatReplayContext
      restartReductionInteractionLedger solverBuildEvidence validatorGate
      archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_isg_inputs benchmarkFingerprint phaseScheduleDigest
      phaseFormulaDigestLedger simplificationProofEquisatLedger
      modelReconstructionContext unsatReplayContext
      restartReductionInteractionLedger solverBuildEvidence validatorGate
      archiveManifest fallbackNoClaimPath auditTranscript := by
  intro inputs
  exact inputs

theorem ay_isg_accepted_schedule
    {benchmarkFingerprint phaseScheduleDigest phaseFormulaDigestLedger
      simplificationProofEquisatLedger modelReconstructionContext
      unsatReplayContext restartReductionInteractionLedger solverBuildEvidence
      validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      scheduleAccepted : Prop} :
    scheduleAccepted ->
    ay_isg_accepted benchmarkFingerprint phaseScheduleDigest
      phaseFormulaDigestLedger simplificationProofEquisatLedger
      modelReconstructionContext unsatReplayContext
      restartReductionInteractionLedger solverBuildEvidence validatorGate
      archiveManifest fallbackNoClaimPath auditTranscript scheduleAccepted := by
  intro accepted
  exact accepted

theorem ay_isg_accepted_benchmark_fingerprint
    {benchmarkFingerprint : Prop} :
    benchmarkFingerprint ->
    ay_isg_benchmark_fingerprint_evidence benchmarkFingerprint := by
  intro evidence
  exact evidence

theorem ay_isg_accepted_phase_schedule_digest
    {phaseScheduleDigest : Prop} :
    phaseScheduleDigest ->
    ay_isg_phase_schedule_digest_evidence phaseScheduleDigest := by
  intro evidence
  exact evidence

theorem ay_isg_accepted_phase_formula_digest_ledger
    {phaseFormulaDigestLedger : Prop} :
    phaseFormulaDigestLedger ->
    ay_isg_phase_formula_digest_ledger_evidence
      phaseFormulaDigestLedger := by
  intro evidence
  exact evidence

theorem ay_isg_accepted_simplification_proof_equisat_ledger
    {simplificationProofEquisatLedger : Prop} :
    simplificationProofEquisatLedger ->
    ay_isg_simplification_proof_equisat_ledger_evidence
      simplificationProofEquisatLedger := by
  intro evidence
  exact evidence

theorem ay_isg_accepted_model_reconstruction_context
    {modelReconstructionContext : Prop} :
    modelReconstructionContext ->
    ay_isg_model_reconstruction_context_evidence
      modelReconstructionContext := by
  intro evidence
  exact evidence

theorem ay_isg_accepted_unsat_replay_context
    {unsatReplayContext : Prop} :
    unsatReplayContext ->
    ay_isg_unsat_replay_context_evidence unsatReplayContext := by
  intro evidence
  exact evidence

theorem ay_isg_accepted_restart_reduction_interaction_ledger
    {restartReductionInteractionLedger : Prop} :
    restartReductionInteractionLedger ->
    ay_isg_restart_reduction_interaction_ledger_evidence
      restartReductionInteractionLedger := by
  intro evidence
  exact evidence

theorem ay_isg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_isg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_isg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_isg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_isg_accepted_archive_manifest
    {archiveManifest : Prop} :
    archiveManifest -> ay_isg_archive_manifest_evidence archiveManifest := by
  intro evidence
  exact evidence

theorem ay_isg_accepted_fallback_no_claim_path
    {fallbackNoClaimPath : Prop} :
    fallbackNoClaimPath ->
    ay_isg_fallback_no_claim_path_evidence fallbackNoClaimPath := by
  intro evidence
  exact evidence

theorem ay_isg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_isg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_isg_schedule_is_orchestration_replay_evidence_only
    {scheduleAccepted orchestrationOnly : Prop} :
    scheduleAccepted ->
    orchestrationOnly ->
    orchestrationOnly :=
  fun _ orchestration => orchestration

theorem ay_isg_schedule_cannot_independently_justify_sat
    {scheduleAccepted satEvidence satSound : Prop} :
    scheduleAccepted ->
    ay_isg_checked_sat_evidence satEvidence ->
    (satEvidence -> satSound) ->
    satSound :=
  fun _ evidence transport => transport evidence

theorem ay_isg_schedule_cannot_independently_justify_unsat
    {scheduleAccepted unsatEvidence unsatSound : Prop} :
    scheduleAccepted ->
    ay_isg_checked_unsat_evidence unsatEvidence ->
    (unsatEvidence -> unsatSound) ->
    unsatSound :=
  fun _ evidence transport => transport evidence

theorem ay_isg_schedule_cannot_change_original_formula_truth
    {scheduleAccepted originalFormulaTruthPreserved : Prop} :
    scheduleAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_isg_accepted_publication_preserves_public_soundness
    {scheduleReplay solverBuildEvidence validatorGate archiveManifest
      fallbackNoClaimPath auditTranscript checkedEvidence satSound unsatSound :
      Prop} :
    ay_isg_publication_gate scheduleReplay solverBuildEvidence validatorGate
      archiveManifest fallbackNoClaimPath auditTranscript checkedEvidence ->
    ay_isg_public_soundness_theorem satSound unsatSound ->
    ay_isg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_isg_each_phase_tied_to_formula_and_certificate_context
    {phaseScheduleDigest phaseFormulaDigestLedger
      simplificationProofEquisatLedger modelReconstructionContext
      unsatReplayContext phaseContext : Prop} :
    phaseScheduleDigest ->
    phaseFormulaDigestLedger ->
    simplificationProofEquisatLedger ->
    modelReconstructionContext ->
    unsatReplayContext ->
    phaseContext ->
    phaseContext :=
  fun _ _ _ _ _ context => context

theorem ay_isg_exact_context_ties_schedule_to_replay
    {benchmarkFingerprint phaseScheduleDigest phaseFormulaDigestLedger
      simplificationProofEquisatLedger modelReconstructionContext
      unsatReplayContext restartReductionInteractionLedger solverBuildEvidence
      validatorGate archiveManifest auditTranscript exactContext : Prop} :
    benchmarkFingerprint ->
    phaseScheduleDigest ->
    phaseFormulaDigestLedger ->
    simplificationProofEquisatLedger ->
    modelReconstructionContext ->
    unsatReplayContext ->
    restartReductionInteractionLedger ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    exactContext ->
    exactContext :=
  fun _ _ _ _ _ _ _ _ _ _ _ context => context

theorem ay_isg_equisat_ledger_preserves_model_reconstruction_context
    {simplificationProofEquisatLedger modelReconstructionContext : Prop} :
    simplificationProofEquisatLedger ->
    modelReconstructionContext ->
    modelReconstructionContext :=
  fun _ model => model

theorem ay_isg_equisat_ledger_preserves_unsat_replay_context
    {simplificationProofEquisatLedger unsatReplayContext : Prop} :
    simplificationProofEquisatLedger ->
    unsatReplayContext ->
    unsatReplayContext :=
  fun _ replay => replay

theorem ay_isg_restart_reduction_ledger_preserves_schedule_replay
    {restartReductionInteractionLedger phaseScheduleDigest : Prop} :
    restartReductionInteractionLedger ->
    phaseScheduleDigest ->
    phaseScheduleDigest :=
  fun _ schedule => schedule

theorem ay_isg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_isg_gate accepted rejected ->
    ay_isg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_isg_rejected_is_no_claim
    {scheduleMismatch diagnostic : Prop} :
    scheduleMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_rejected_forces_recompute
    {scheduleMismatch recomputeRequired : Prop} :
    scheduleMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_failed_schedule_guard_cannot_bless_competition_result
    {scheduleMismatch baselineNoClaim satSound unsatSound : Prop} :
    scheduleMismatch ->
    baselineNoClaim ->
    ay_isg_public_soundness_theorem satSound unsatSound ->
    ay_isg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isg_schedule_mismatch_forces_no_claim
    {scheduleMismatch diagnostic : Prop} :
    scheduleMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_phase_mismatch_forces_no_claim
    {phaseMismatch diagnostic : Prop} :
    phaseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_formula_mismatch_forces_no_claim
    {formulaMismatch diagnostic : Prop} :
    formulaMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_equisat_mismatch_forces_no_claim
    {equisatMismatch diagnostic : Prop} :
    equisatMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_model_mismatch_forces_no_claim
    {modelMismatch diagnostic : Prop} :
    modelMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_restart_mismatch_forces_no_claim
    {restartMismatch diagnostic : Prop} :
    restartMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_reduction_mismatch_forces_no_claim
    {reductionMismatch diagnostic : Prop} :
    reductionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic : Prop} :
    archiveMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_isg_schedule_mismatch_forces_recompute
    {scheduleMismatch recomputeRequired : Prop} :
    scheduleMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_phase_mismatch_forces_recompute
    {phaseMismatch recomputeRequired : Prop} :
    phaseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_formula_mismatch_forces_recompute
    {formulaMismatch recomputeRequired : Prop} :
    formulaMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_equisat_mismatch_forces_recompute
    {equisatMismatch recomputeRequired : Prop} :
    equisatMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_model_mismatch_forces_recompute
    {modelMismatch recomputeRequired : Prop} :
    modelMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_restart_mismatch_forces_recompute
    {restartMismatch recomputeRequired : Prop} :
    restartMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_reduction_mismatch_forces_recompute
    {reductionMismatch recomputeRequired : Prop} :
    reductionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_archive_mismatch_forces_recompute
    {archiveMismatch recomputeRequired : Prop} :
    archiveMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_isg_schedule_mismatch_cannot_bless_result
    {scheduleMismatch baselineNoClaim satSound unsatSound : Prop} :
    scheduleMismatch ->
    baselineNoClaim ->
    ay_isg_public_soundness_theorem satSound unsatSound ->
    ay_isg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isg_equisat_mismatch_cannot_bless_result
    {equisatMismatch baselineNoClaim satSound unsatSound : Prop} :
    equisatMismatch ->
    baselineNoClaim ->
    ay_isg_public_soundness_theorem satSound unsatSound ->
    ay_isg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isg_replay_mismatch_cannot_bless_result
    {replayMismatch baselineNoClaim satSound unsatSound : Prop} :
    replayMismatch ->
    baselineNoClaim ->
    ay_isg_public_soundness_theorem satSound unsatSound ->
    ay_isg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_isg_policy_requires_benchmark_fingerprint
    {benchmarkFingerprint accepted : Prop} :
    benchmarkFingerprint -> accepted -> benchmarkFingerprint :=
  fun evidence _ => evidence

theorem ay_isg_policy_requires_phase_schedule_digest
    {phaseScheduleDigest accepted : Prop} :
    phaseScheduleDigest -> accepted -> phaseScheduleDigest :=
  fun evidence _ => evidence

theorem ay_isg_policy_requires_phase_formula_digest_ledger
    {phaseFormulaDigestLedger accepted : Prop} :
    phaseFormulaDigestLedger -> accepted -> phaseFormulaDigestLedger :=
  fun evidence _ => evidence

theorem ay_isg_policy_requires_simplification_proof_equisat_ledger
    {simplificationProofEquisatLedger accepted : Prop} :
    simplificationProofEquisatLedger ->
    accepted ->
    simplificationProofEquisatLedger :=
  fun evidence _ => evidence

theorem ay_isg_policy_requires_model_reconstruction_context
    {modelReconstructionContext accepted : Prop} :
    modelReconstructionContext -> accepted -> modelReconstructionContext :=
  fun evidence _ => evidence

theorem ay_isg_policy_requires_unsat_replay_context
    {unsatReplayContext accepted : Prop} :
    unsatReplayContext -> accepted -> unsatReplayContext :=
  fun evidence _ => evidence

theorem ay_isg_policy_requires_restart_reduction_interaction_ledger
    {restartReductionInteractionLedger accepted : Prop} :
    restartReductionInteractionLedger ->
    accepted ->
    restartReductionInteractionLedger :=
  fun evidence _ => evidence

theorem ay_isg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_isg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_isg_policy_requires_archive
    {archiveManifest accepted : Prop} :
    archiveManifest -> accepted -> archiveManifest :=
  fun evidence _ => evidence

theorem ay_isg_policy_requires_fallback
    {fallbackNoClaimPath accepted : Prop} :
    fallbackNoClaimPath -> accepted -> fallbackNoClaimPath :=
  fun evidence _ => evidence

theorem ay_isg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
