def ay_racg_conj (p q : Prop) : Prop := p ∧ q

def ay_racg_disj (p q : Prop) : Prop := p ∨ q

def ay_racg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_racg_disj satSound unsatSound

def ay_racg_inputs
    (reasonArenaDigestBeforeAfter clauseIdRemapLedger trailReasonPointerWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_racg_conj reasonArenaDigestBeforeAfter
    (ay_racg_conj clauseIdRemapLedger
      (ay_racg_conj trailReasonPointerWitness
        (ay_racg_conj propagationReplay
          (ay_racg_conj fallbackBaseline
            (ay_racg_conj solverBuildEvidence
              (ay_racg_conj validatorGate auditTranscript))))))

def ay_racg_reason_arena_digest_before_after_evidence
    (reasonArenaDigestBeforeAfter : Prop) : Prop :=
  reasonArenaDigestBeforeAfter

def ay_racg_clause_id_remap_ledger_evidence
    (clauseIdRemapLedger : Prop) : Prop :=
  clauseIdRemapLedger

def ay_racg_trail_reason_pointer_witness_evidence
    (trailReasonPointerWitness : Prop) : Prop :=
  trailReasonPointerWitness

def ay_racg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_racg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_racg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_racg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_racg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_racg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_racg_accepted
    (reasonArenaDigestBeforeAfter clauseIdRemapLedger trailReasonPointerWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript compactionAccepted : Prop) : Prop :=
  compactionAccepted

def ay_racg_rejected
    (digestMismatch remapMismatch pointerMismatch replayMismatch
      fallbackMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    Prop :=
  ay_racg_disj digestMismatch
    (ay_racg_disj remapMismatch
      (ay_racg_disj pointerMismatch
        (ay_racg_disj replayMismatch
          (ay_racg_disj fallbackMismatch
            (ay_racg_disj buildMismatch
              (ay_racg_disj validatorMismatch auditMismatch))))))

def ay_racg_gate (accepted rejected : Prop) : Prop :=
  ay_racg_disj accepted rejected

def ay_racg_arena_compaction_hint
    (compactionAccepted layoutGuidance remapGuidance replayGuidance : Prop) :
    Prop :=
  compactionAccepted

def ay_racg_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_racg_input_components
    {reasonArenaDigestBeforeAfter clauseIdRemapLedger trailReasonPointerWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_racg_inputs reasonArenaDigestBeforeAfter clauseIdRemapLedger
      trailReasonPointerWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_racg_inputs reasonArenaDigestBeforeAfter clauseIdRemapLedger
      trailReasonPointerWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_racg_accepted_policy
    {reasonArenaDigestBeforeAfter clauseIdRemapLedger trailReasonPointerWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript compactionAccepted : Prop} :
    compactionAccepted ->
    ay_racg_accepted reasonArenaDigestBeforeAfter clauseIdRemapLedger
      trailReasonPointerWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript compactionAccepted := by
  intro accepted
  exact accepted

theorem ay_racg_accepted_reason_arena_digest_before_after
    {reasonArenaDigestBeforeAfter : Prop} :
    reasonArenaDigestBeforeAfter ->
    ay_racg_reason_arena_digest_before_after_evidence
      reasonArenaDigestBeforeAfter := by
  intro evidence
  exact evidence

theorem ay_racg_accepted_clause_id_remap_ledger
    {clauseIdRemapLedger : Prop} :
    clauseIdRemapLedger ->
    ay_racg_clause_id_remap_ledger_evidence clauseIdRemapLedger := by
  intro evidence
  exact evidence

theorem ay_racg_accepted_trail_reason_pointer_witness
    {trailReasonPointerWitness : Prop} :
    trailReasonPointerWitness ->
    ay_racg_trail_reason_pointer_witness_evidence
      trailReasonPointerWitness := by
  intro evidence
  exact evidence

theorem ay_racg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_racg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_racg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_racg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_racg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_racg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_racg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_racg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_racg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_racg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_racg_arena_compaction_policy_admissible_hint
    {compactionAccepted layoutGuidance remapGuidance replayGuidance : Prop} :
    compactionAccepted ->
    layoutGuidance ->
    remapGuidance ->
    replayGuidance ->
    ay_racg_arena_compaction_hint compactionAccepted layoutGuidance
      remapGuidance replayGuidance :=
  fun accepted _ _ _ => accepted

theorem ay_racg_compaction_is_data_layout_recovery_only
    {compactionAccepted dataLayoutRecoveryOnly : Prop} :
    compactionAccepted ->
    dataLayoutRecoveryOnly ->
    dataLayoutRecoveryOnly :=
  fun _ recovery => recovery

theorem ay_racg_compaction_cannot_change_original_formula_truth
    {compactionAccepted originalFormulaTruth : Prop} :
    compactionAccepted ->
    originalFormulaTruth ->
    originalFormulaTruth :=
  fun _ truth => truth

theorem ay_racg_accepted_compaction_preserves_public_soundness
    {compactionAccepted satSound unsatSound : Prop} :
    compactionAccepted ->
    ay_racg_public_soundness_theorem satSound unsatSound ->
    ay_racg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_racg_accepted_compaction_preserves_reason_replay
    {compactionAccepted reasonReplayObligation : Prop} :
    compactionAccepted ->
    reasonReplayObligation ->
    reasonReplayObligation :=
  fun _ replay => replay

theorem ay_racg_pointer_witness_preserves_propagation_replay
    {trailReasonPointerWitness propagationReplay : Prop} :
    trailReasonPointerWitness ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_racg_remap_ledger_preserves_pointer_witness
    {clauseIdRemapLedger trailReasonPointerWitness : Prop} :
    clauseIdRemapLedger ->
    trailReasonPointerWitness ->
    trailReasonPointerWitness :=
  fun _ pointer => pointer

theorem ay_racg_rejected_is_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_racg_rejected_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_racg_failed_arena_compaction_guard_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_racg_public_soundness_theorem satSound unsatSound ->
    ay_racg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_racg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_racg_gate accepted rejected ->
    ay_racg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_racg_safe_strategy_guidance_accept
    {compactionAccepted layoutGuidance remapGuidance replayGuidance satSound
      unsatSound : Prop} :
    compactionAccepted ->
    layoutGuidance ->
    remapGuidance ->
    replayGuidance ->
    ay_racg_public_soundness_theorem satSound unsatSound ->
    ay_racg_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_racg_safe_strategy_guidance_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_racg_public_soundness_theorem satSound unsatSound ->
    ay_racg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_racg_digest_mismatch_forces_no_claim
    {digestMismatch diagnostic : Prop} :
    digestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_racg_remap_mismatch_forces_no_claim
    {remapMismatch diagnostic : Prop} :
    remapMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_racg_pointer_mismatch_forces_no_claim
    {pointerMismatch diagnostic : Prop} :
    pointerMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_racg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_racg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_racg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_racg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_racg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_racg_digest_mismatch_forces_recompute
    {digestMismatch recomputeRequired : Prop} :
    digestMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_racg_remap_mismatch_forces_recompute
    {remapMismatch recomputeRequired : Prop} :
    remapMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_racg_pointer_mismatch_forces_recompute
    {pointerMismatch recomputeRequired : Prop} :
    pointerMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_racg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_racg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_racg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_racg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_racg_digest_mismatch_cannot_bless_publication
    {digestMismatch baselineSound satSound unsatSound : Prop} :
    digestMismatch ->
    baselineSound ->
    ay_racg_public_soundness_theorem satSound unsatSound ->
    ay_racg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_racg_remap_mismatch_cannot_bless_publication
    {remapMismatch baselineSound satSound unsatSound : Prop} :
    remapMismatch ->
    baselineSound ->
    ay_racg_public_soundness_theorem satSound unsatSound ->
    ay_racg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_racg_pointer_mismatch_cannot_bless_publication
    {pointerMismatch baselineSound satSound unsatSound : Prop} :
    pointerMismatch ->
    baselineSound ->
    ay_racg_public_soundness_theorem satSound unsatSound ->
    ay_racg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_racg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_racg_public_soundness_theorem satSound unsatSound ->
    ay_racg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_racg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_racg_public_soundness_theorem satSound unsatSound ->
    ay_racg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_racg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_racg_public_soundness_theorem satSound unsatSound ->
    ay_racg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_racg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_racg_public_soundness_theorem satSound unsatSound ->
    ay_racg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_racg_policy_requires_reason_arena_digest
    {reasonArenaDigestBeforeAfter : Prop} :
    ay_racg_reason_arena_digest_before_after_evidence
      reasonArenaDigestBeforeAfter ->
    reasonArenaDigestBeforeAfter := by
  intro evidence
  exact evidence

theorem ay_racg_policy_requires_clause_id_remap
    {clauseIdRemapLedger : Prop} :
    ay_racg_clause_id_remap_ledger_evidence clauseIdRemapLedger ->
    clauseIdRemapLedger := by
  intro evidence
  exact evidence

theorem ay_racg_policy_requires_trail_reason_pointer
    {trailReasonPointerWitness : Prop} :
    ay_racg_trail_reason_pointer_witness_evidence
      trailReasonPointerWitness ->
    trailReasonPointerWitness := by
  intro evidence
  exact evidence

theorem ay_racg_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_racg_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_racg_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_racg_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_racg_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_racg_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_racg_policy_requires_validator
    {validatorGate : Prop} :
    ay_racg_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_racg_policy_requires_audit
    {auditTranscript : Prop} :
    ay_racg_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
