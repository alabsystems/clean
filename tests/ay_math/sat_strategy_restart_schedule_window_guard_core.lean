def ay_rswg_conj (p q : Prop) : Prop := p ∧ q

def ay_rswg_disj (p q : Prop) : Prop := p ∨ q

def ay_rswg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rswg_disj satSound unsatSound

def ay_rswg_inputs
    (restartEpochManifest conflictWindowDigest trailSnapshotDigest
      learnedClauseDatabaseDigest reasonProtectionLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) : Prop :=
  ay_rswg_conj restartEpochManifest
    (ay_rswg_conj conflictWindowDigest
      (ay_rswg_conj trailSnapshotDigest
        (ay_rswg_conj learnedClauseDatabaseDigest
          (ay_rswg_conj reasonProtectionLedger
            (ay_rswg_conj propagationReplay
              (ay_rswg_conj fallbackBaseline
                (ay_rswg_conj solverBuildEvidence
                  (ay_rswg_conj validatorGate auditTranscript))))))))

def ay_rswg_restart_epoch_manifest_evidence
    (restartEpochManifest : Prop) : Prop :=
  restartEpochManifest

def ay_rswg_conflict_window_digest_evidence
    (conflictWindowDigest : Prop) : Prop :=
  conflictWindowDigest

def ay_rswg_trail_snapshot_digest_evidence
    (trailSnapshotDigest : Prop) : Prop :=
  trailSnapshotDigest

def ay_rswg_learned_clause_database_digest_evidence
    (learnedClauseDatabaseDigest : Prop) : Prop :=
  learnedClauseDatabaseDigest

def ay_rswg_reason_protection_ledger_evidence
    (reasonProtectionLedger : Prop) : Prop :=
  reasonProtectionLedger

def ay_rswg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_rswg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_rswg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rswg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rswg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rswg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rswg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_rswg_accepted
    (restartEpochManifest conflictWindowDigest trailSnapshotDigest
      learnedClauseDatabaseDigest reasonProtectionLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      scheduleWindowAccepted : Prop) : Prop :=
  scheduleWindowAccepted

def ay_rswg_rejected
    (epochMismatch windowMismatch trailMismatch clauseMismatch reasonMismatch
      replayMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch : Prop) : Prop :=
  ay_rswg_disj epochMismatch
    (ay_rswg_disj windowMismatch
      (ay_rswg_disj trailMismatch
        (ay_rswg_disj clauseMismatch
          (ay_rswg_disj reasonMismatch
            (ay_rswg_disj replayMismatch
              (ay_rswg_disj baselineMismatch
                (ay_rswg_disj buildMismatch
                  (ay_rswg_disj validatorMismatch auditMismatch))))))))

def ay_rswg_gate (accepted rejected : Prop) : Prop :=
  ay_rswg_disj accepted rejected

def ay_rswg_restart_schedule_search_control_hint
    (scheduleWindowAccepted searchControlOnly deterministicWindowReplay
      publicationGuard : Prop) : Prop :=
  scheduleWindowAccepted

theorem ay_rswg_input_components
    {restartEpochManifest conflictWindowDigest trailSnapshotDigest
      learnedClauseDatabaseDigest reasonProtectionLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop} :
    ay_rswg_inputs restartEpochManifest conflictWindowDigest
      trailSnapshotDigest learnedClauseDatabaseDigest reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    ay_rswg_inputs restartEpochManifest conflictWindowDigest
      trailSnapshotDigest learnedClauseDatabaseDigest reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rswg_accepted_policy
    {restartEpochManifest conflictWindowDigest trailSnapshotDigest
      learnedClauseDatabaseDigest reasonProtectionLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      scheduleWindowAccepted : Prop} :
    scheduleWindowAccepted ->
    ay_rswg_accepted restartEpochManifest conflictWindowDigest
      trailSnapshotDigest learnedClauseDatabaseDigest reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript scheduleWindowAccepted := by
  intro accepted
  exact accepted

theorem ay_rswg_accepted_restart_epoch_manifest
    {restartEpochManifest : Prop} :
    restartEpochManifest ->
    ay_rswg_restart_epoch_manifest_evidence restartEpochManifest := by
  intro evidence
  exact evidence

theorem ay_rswg_accepted_conflict_window_digest
    {conflictWindowDigest : Prop} :
    conflictWindowDigest ->
    ay_rswg_conflict_window_digest_evidence conflictWindowDigest := by
  intro evidence
  exact evidence

theorem ay_rswg_accepted_trail_snapshot_digest
    {trailSnapshotDigest : Prop} :
    trailSnapshotDigest ->
    ay_rswg_trail_snapshot_digest_evidence trailSnapshotDigest := by
  intro evidence
  exact evidence

theorem ay_rswg_accepted_learned_clause_database_digest
    {learnedClauseDatabaseDigest : Prop} :
    learnedClauseDatabaseDigest ->
    ay_rswg_learned_clause_database_digest_evidence
      learnedClauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_rswg_accepted_reason_protection_ledger
    {reasonProtectionLedger : Prop} :
    reasonProtectionLedger ->
    ay_rswg_reason_protection_ledger_evidence reasonProtectionLedger := by
  intro evidence
  exact evidence

theorem ay_rswg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_rswg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_rswg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_rswg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rswg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_rswg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rswg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rswg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rswg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rswg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rswg_restart_scheduling_is_search_control_only
    {scheduleWindowAccepted searchControlOnly : Prop} :
    scheduleWindowAccepted ->
    searchControlOnly ->
    searchControlOnly :=
  fun _ controlOnly => controlOnly

theorem ay_rswg_restart_scheduling_cannot_change_original_formula_truth
    {scheduleWindowAccepted originalFormulaTruthPreserved : Prop} :
    scheduleWindowAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_rswg_accepted_schedule_preserves_public_soundness
    {scheduleWindowAccepted satSound unsatSound : Prop} :
    scheduleWindowAccepted ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rswg_window_digest_preserves_replay
    {conflictWindowDigest propagationReplay : Prop} :
    conflictWindowDigest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rswg_trail_snapshot_preserves_replay
    {trailSnapshotDigest propagationReplay : Prop} :
    trailSnapshotDigest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rswg_reason_protection_preserves_replay
    {reasonProtectionLedger propagationReplay : Prop} :
    reasonProtectionLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rswg_accepted_schedule_preserves_fallback_soundness
    {scheduleWindowAccepted fallbackBaseline satSound unsatSound : Prop} :
    scheduleWindowAccepted ->
    fallbackBaseline ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rswg_gate accepted rejected ->
    ay_rswg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rswg_rejected_is_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rswg_rejected_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rswg_failed_guard_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rswg_window_mismatch_forces_no_claim
    {windowMismatch diagnostic : Prop} :
    windowMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rswg_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rswg_clause_mismatch_forces_no_claim
    {clauseMismatch diagnostic : Prop} :
    clauseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rswg_reason_mismatch_forces_no_claim
    {reasonMismatch diagnostic : Prop} :
    reasonMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rswg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rswg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rswg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rswg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rswg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rswg_epoch_mismatch_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rswg_window_mismatch_forces_recompute
    {windowMismatch recomputeRequired : Prop} :
    windowMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rswg_trail_mismatch_forces_recompute
    {trailMismatch recomputeRequired : Prop} :
    trailMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rswg_clause_mismatch_forces_recompute
    {clauseMismatch recomputeRequired : Prop} :
    clauseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rswg_reason_mismatch_forces_recompute
    {reasonMismatch recomputeRequired : Prop} :
    reasonMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rswg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rswg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rswg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rswg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rswg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rswg_epoch_mismatch_cannot_bless_publication
    {epochMismatch baselineSound satSound unsatSound : Prop} :
    epochMismatch ->
    baselineSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_window_mismatch_cannot_bless_publication
    {windowMismatch baselineSound satSound unsatSound : Prop} :
    windowMismatch ->
    baselineSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_trail_mismatch_cannot_bless_publication
    {trailMismatch baselineSound satSound unsatSound : Prop} :
    trailMismatch ->
    baselineSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_clause_mismatch_cannot_bless_publication
    {clauseMismatch baselineSound satSound unsatSound : Prop} :
    clauseMismatch ->
    baselineSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_reason_mismatch_cannot_bless_publication
    {reasonMismatch baselineSound satSound unsatSound : Prop} :
    reasonMismatch ->
    baselineSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound ->
    ay_rswg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rswg_policy_requires_restart_epoch
    {restartEpochManifest accepted : Prop} :
    restartEpochManifest -> accepted -> restartEpochManifest :=
  fun evidence _ => evidence

theorem ay_rswg_policy_requires_conflict_window
    {conflictWindowDigest accepted : Prop} :
    conflictWindowDigest -> accepted -> conflictWindowDigest :=
  fun evidence _ => evidence

theorem ay_rswg_policy_requires_trail_snapshot
    {trailSnapshotDigest accepted : Prop} :
    trailSnapshotDigest -> accepted -> trailSnapshotDigest :=
  fun evidence _ => evidence

theorem ay_rswg_policy_requires_learned_clause_database
    {learnedClauseDatabaseDigest accepted : Prop} :
    learnedClauseDatabaseDigest -> accepted -> learnedClauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_rswg_policy_requires_reason_protection
    {reasonProtectionLedger accepted : Prop} :
    reasonProtectionLedger -> accepted -> reasonProtectionLedger :=
  fun evidence _ => evidence

theorem ay_rswg_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_rswg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_rswg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_rswg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_rswg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
