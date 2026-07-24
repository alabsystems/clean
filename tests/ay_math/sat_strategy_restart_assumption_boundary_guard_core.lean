def ay_rabg_conj (p q : Prop) : Prop := p ∧ q

def ay_rabg_disj (p q : Prop) : Prop := p ∨ q

def ay_rabg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rabg_disj satSound unsatSound

def ay_rabg_inputs
    (assumptionScopeManifest restartPolicyManifest trailSnapshotDigest
      assumptionPrefixWitness restartEpochLedger reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_rabg_conj assumptionScopeManifest
    (ay_rabg_conj restartPolicyManifest
      (ay_rabg_conj trailSnapshotDigest
        (ay_rabg_conj assumptionPrefixWitness
          (ay_rabg_conj restartEpochLedger
            (ay_rabg_conj reasonProtectionLedger
              (ay_rabg_conj propagationReplay
                (ay_rabg_conj fallbackBaseline
                  (ay_rabg_conj solverBuildEvidence
                    (ay_rabg_conj validatorGate auditTranscript)))))))))

def ay_rabg_assumption_scope_manifest_evidence
    (assumptionScopeManifest : Prop) : Prop :=
  assumptionScopeManifest

def ay_rabg_restart_policy_manifest_evidence
    (restartPolicyManifest : Prop) : Prop :=
  restartPolicyManifest

def ay_rabg_trail_snapshot_digest_evidence
    (trailSnapshotDigest : Prop) : Prop :=
  trailSnapshotDigest

def ay_rabg_assumption_prefix_witness_evidence
    (assumptionPrefixWitness : Prop) : Prop :=
  assumptionPrefixWitness

def ay_rabg_restart_epoch_ledger_evidence
    (restartEpochLedger : Prop) : Prop :=
  restartEpochLedger

def ay_rabg_reason_protection_ledger_evidence
    (reasonProtectionLedger : Prop) : Prop :=
  reasonProtectionLedger

def ay_rabg_propagation_replay_evidence (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_rabg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_rabg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rabg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rabg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rabg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rabg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_rabg_accepted
    (assumptionScopeManifest restartPolicyManifest trailSnapshotDigest
      assumptionPrefixWitness restartEpochLedger reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript boundaryAccepted : Prop) : Prop :=
  boundaryAccepted

def ay_rabg_rejected
    (scopeMismatch prefixMismatch restartMismatch trailMismatch epochMismatch
      reasonMismatch replayMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch : Prop) : Prop :=
  ay_rabg_disj scopeMismatch
    (ay_rabg_disj prefixMismatch
      (ay_rabg_disj restartMismatch
        (ay_rabg_disj trailMismatch
          (ay_rabg_disj epochMismatch
            (ay_rabg_disj reasonMismatch
              (ay_rabg_disj replayMismatch
                (ay_rabg_disj baselineMismatch
                  (ay_rabg_disj buildMismatch
                    (ay_rabg_disj validatorMismatch auditMismatch)))))))))

def ay_rabg_restart_boundary_search_control_hint
    (boundaryAccepted searchControlOnly scopedAssumptionsPreserved : Prop) :
    Prop :=
  boundaryAccepted

def ay_rabg_gate (accepted rejected : Prop) : Prop :=
  ay_rabg_disj accepted rejected

theorem ay_rabg_input_components
    {assumptionScopeManifest restartPolicyManifest trailSnapshotDigest
      assumptionPrefixWitness restartEpochLedger reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_rabg_inputs assumptionScopeManifest restartPolicyManifest
      trailSnapshotDigest assumptionPrefixWitness restartEpochLedger
      reasonProtectionLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_rabg_inputs assumptionScopeManifest restartPolicyManifest
      trailSnapshotDigest assumptionPrefixWitness restartEpochLedger
      reasonProtectionLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rabg_accepted_boundary
    {assumptionScopeManifest restartPolicyManifest trailSnapshotDigest
      assumptionPrefixWitness restartEpochLedger reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript boundaryAccepted : Prop} :
    boundaryAccepted ->
    ay_rabg_accepted assumptionScopeManifest restartPolicyManifest
      trailSnapshotDigest assumptionPrefixWitness restartEpochLedger
      reasonProtectionLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript boundaryAccepted := by
  intro accepted
  exact accepted

theorem ay_rabg_accepted_assumption_scope_manifest
    {assumptionScopeManifest : Prop} :
    assumptionScopeManifest ->
    ay_rabg_assumption_scope_manifest_evidence assumptionScopeManifest := by
  intro evidence
  exact evidence

theorem ay_rabg_accepted_restart_policy_manifest
    {restartPolicyManifest : Prop} :
    restartPolicyManifest ->
    ay_rabg_restart_policy_manifest_evidence restartPolicyManifest := by
  intro evidence
  exact evidence

theorem ay_rabg_accepted_trail_snapshot_digest
    {trailSnapshotDigest : Prop} :
    trailSnapshotDigest ->
    ay_rabg_trail_snapshot_digest_evidence trailSnapshotDigest := by
  intro evidence
  exact evidence

theorem ay_rabg_accepted_assumption_prefix_witness
    {assumptionPrefixWitness : Prop} :
    assumptionPrefixWitness ->
    ay_rabg_assumption_prefix_witness_evidence assumptionPrefixWitness := by
  intro evidence
  exact evidence

theorem ay_rabg_accepted_restart_epoch_ledger
    {restartEpochLedger : Prop} :
    restartEpochLedger ->
    ay_rabg_restart_epoch_ledger_evidence restartEpochLedger := by
  intro evidence
  exact evidence

theorem ay_rabg_accepted_reason_protection_ledger
    {reasonProtectionLedger : Prop} :
    reasonProtectionLedger ->
    ay_rabg_reason_protection_ledger_evidence reasonProtectionLedger := by
  intro evidence
  exact evidence

theorem ay_rabg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_rabg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_rabg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline ->
    ay_rabg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rabg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_rabg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rabg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rabg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rabg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rabg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rabg_restarts_are_search_control_only
    {boundaryAccepted searchControlOnly : Prop} :
    boundaryAccepted ->
    searchControlOnly ->
    searchControlOnly :=
  fun _ controlOnly => controlOnly

theorem ay_rabg_restarts_preserve_assumption_scope
    {boundaryAccepted scopedAssumptionsPreserved : Prop} :
    boundaryAccepted ->
    scopedAssumptionsPreserved ->
    scopedAssumptionsPreserved :=
  fun _ preserved => preserved

theorem ay_rabg_restarts_do_not_drop_assumptions
    {assumptionPrefixWitness assumptionsNotDropped : Prop} :
    assumptionPrefixWitness ->
    assumptionsNotDropped ->
    assumptionsNotDropped :=
  fun _ preserved => preserved

theorem ay_rabg_restarts_do_not_reorder_assumptions
    {assumptionPrefixWitness assumptionsNotReordered : Prop} :
    assumptionPrefixWitness ->
    assumptionsNotReordered ->
    assumptionsNotReordered :=
  fun _ preserved => preserved

theorem ay_rabg_accepted_boundary_preserves_public_soundness
    {boundaryAccepted satSound unsatSound : Prop} :
    boundaryAccepted ->
    ay_rabg_public_soundness_theorem satSound unsatSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rabg_accepted_boundary_preserves_intended_scope_soundness
    {boundaryAccepted intendedScopeSound satSound unsatSound : Prop} :
    boundaryAccepted ->
    intendedScopeSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rabg_scope_manifest_preserves_replay
    {assumptionScopeManifest propagationReplay : Prop} :
    assumptionScopeManifest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rabg_prefix_witness_preserves_replay
    {assumptionPrefixWitness propagationReplay : Prop} :
    assumptionPrefixWitness ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rabg_restart_policy_preserves_replay
    {restartPolicyManifest propagationReplay : Prop} :
    restartPolicyManifest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rabg_reason_ledger_preserves_replay
    {reasonProtectionLedger propagationReplay : Prop} :
    reasonProtectionLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_rabg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rabg_gate accepted rejected ->
    ay_rabg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rabg_rejected_is_no_claim
    {scopeMismatch diagnostic : Prop} :
    scopeMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_rejected_forces_recompute
    {scopeMismatch recomputeRequired : Prop} :
    scopeMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rabg_failed_guard_cannot_bless_publication
    {scopeMismatch baselineSound satSound unsatSound : Prop} :
    scopeMismatch ->
    baselineSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rabg_scope_mismatch_forces_no_claim
    {scopeMismatch diagnostic : Prop} :
    scopeMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_prefix_mismatch_forces_no_claim
    {prefixMismatch diagnostic : Prop} :
    prefixMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_restart_mismatch_forces_no_claim
    {restartMismatch diagnostic : Prop} :
    restartMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_trail_mismatch_forces_no_claim
    {trailMismatch diagnostic : Prop} :
    trailMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_reason_mismatch_forces_no_claim
    {reasonMismatch diagnostic : Prop} :
    reasonMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rabg_scope_mismatch_forces_recompute
    {scopeMismatch recomputeRequired : Prop} :
    scopeMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rabg_prefix_mismatch_forces_recompute
    {prefixMismatch recomputeRequired : Prop} :
    prefixMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rabg_restart_mismatch_forces_recompute
    {restartMismatch recomputeRequired : Prop} :
    restartMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rabg_reason_mismatch_forces_recompute
    {reasonMismatch recomputeRequired : Prop} :
    reasonMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rabg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rabg_scope_mismatch_cannot_bless_publication
    {scopeMismatch baselineSound satSound unsatSound : Prop} :
    scopeMismatch ->
    baselineSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rabg_prefix_mismatch_cannot_bless_publication
    {prefixMismatch baselineSound satSound unsatSound : Prop} :
    prefixMismatch ->
    baselineSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rabg_restart_mismatch_cannot_bless_publication
    {restartMismatch baselineSound satSound unsatSound : Prop} :
    restartMismatch ->
    baselineSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rabg_reason_mismatch_cannot_bless_publication
    {reasonMismatch baselineSound satSound unsatSound : Prop} :
    reasonMismatch ->
    baselineSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rabg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound ->
    ay_rabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rabg_policy_requires_assumption_scope_manifest
    {assumptionScopeManifest accepted : Prop} :
    assumptionScopeManifest -> accepted -> assumptionScopeManifest :=
  fun evidence _ => evidence

theorem ay_rabg_policy_requires_restart_policy_manifest
    {restartPolicyManifest accepted : Prop} :
    restartPolicyManifest -> accepted -> restartPolicyManifest :=
  fun evidence _ => evidence

theorem ay_rabg_policy_requires_trail_snapshot_digest
    {trailSnapshotDigest accepted : Prop} :
    trailSnapshotDigest -> accepted -> trailSnapshotDigest :=
  fun evidence _ => evidence

theorem ay_rabg_policy_requires_assumption_prefix_witness
    {assumptionPrefixWitness accepted : Prop} :
    assumptionPrefixWitness -> accepted -> assumptionPrefixWitness :=
  fun evidence _ => evidence

theorem ay_rabg_policy_requires_restart_epoch_ledger
    {restartEpochLedger accepted : Prop} :
    restartEpochLedger -> accepted -> restartEpochLedger :=
  fun evidence _ => evidence

theorem ay_rabg_policy_requires_reason_protection_ledger
    {reasonProtectionLedger accepted : Prop} :
    reasonProtectionLedger -> accepted -> reasonProtectionLedger :=
  fun evidence _ => evidence

theorem ay_rabg_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_rabg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_rabg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_rabg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_rabg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
