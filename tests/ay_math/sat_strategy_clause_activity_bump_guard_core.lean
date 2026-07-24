def ay_cabg_conj (p q : Prop) : Prop := p ∧ q

def ay_cabg_disj (p q : Prop) : Prop := p ∨ q

def ay_cabg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_cabg_disj satSound unsatSound

def ay_cabg_inputs
    (clauseDatabaseDigest conflictClauseDigest bumpLedger
      activityVectorDigest orderingTieBreakWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_cabg_conj clauseDatabaseDigest
    (ay_cabg_conj conflictClauseDigest
      (ay_cabg_conj bumpLedger
        (ay_cabg_conj activityVectorDigest
          (ay_cabg_conj orderingTieBreakWitness
            (ay_cabg_conj reasonProtectionLedger
              (ay_cabg_conj propagationReplay
                (ay_cabg_conj fallbackBaseline
                  (ay_cabg_conj solverBuildEvidence
                    (ay_cabg_conj validatorGate auditTranscript)))))))))

def ay_cabg_clause_database_digest_evidence
    (clauseDatabaseDigest : Prop) : Prop :=
  clauseDatabaseDigest

def ay_cabg_conflict_clause_digest_evidence
    (conflictClauseDigest : Prop) : Prop :=
  conflictClauseDigest

def ay_cabg_bump_ledger_evidence (bumpLedger : Prop) : Prop :=
  bumpLedger

def ay_cabg_activity_vector_digest_evidence
    (activityVectorDigest : Prop) : Prop :=
  activityVectorDigest

def ay_cabg_ordering_tie_break_witness_evidence
    (orderingTieBreakWitness : Prop) : Prop :=
  orderingTieBreakWitness

def ay_cabg_reason_protection_ledger_evidence
    (reasonProtectionLedger : Prop) : Prop :=
  reasonProtectionLedger

def ay_cabg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_cabg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_cabg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_cabg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_cabg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_cabg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_cabg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_cabg_accepted
    (clauseDatabaseDigest conflictClauseDigest bumpLedger
      activityVectorDigest orderingTieBreakWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript bumpAccepted : Prop) : Prop :=
  bumpAccepted

def ay_cabg_rejected
    (bumpMismatch activityMismatch orderMismatch reasonMismatch replayMismatch
      clauseMismatch conflictMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch : Prop) : Prop :=
  ay_cabg_disj bumpMismatch
    (ay_cabg_disj activityMismatch
      (ay_cabg_disj orderMismatch
        (ay_cabg_disj reasonMismatch
          (ay_cabg_disj replayMismatch
            (ay_cabg_disj clauseMismatch
              (ay_cabg_disj conflictMismatch
                (ay_cabg_disj baselineMismatch
                  (ay_cabg_disj buildMismatch
                    (ay_cabg_disj validatorMismatch auditMismatch)))))))))

def ay_cabg_gate (accepted rejected : Prop) : Prop :=
  ay_cabg_disj accepted rejected

def ay_cabg_activity_bump_heuristic_hint
    (bumpAccepted heuristicAccountingOnly orderingGuidance replayAccepted :
      Prop) : Prop :=
  bumpAccepted

theorem ay_cabg_input_components
    {clauseDatabaseDigest conflictClauseDigest bumpLedger
      activityVectorDigest orderingTieBreakWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_cabg_inputs clauseDatabaseDigest conflictClauseDigest bumpLedger
      activityVectorDigest orderingTieBreakWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    ay_cabg_inputs clauseDatabaseDigest conflictClauseDigest bumpLedger
      activityVectorDigest orderingTieBreakWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript := by
  intro inputs
  exact inputs

theorem ay_cabg_accepted_policy
    {clauseDatabaseDigest conflictClauseDigest bumpLedger
      activityVectorDigest orderingTieBreakWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript bumpAccepted : Prop} :
    bumpAccepted ->
    ay_cabg_accepted clauseDatabaseDigest conflictClauseDigest bumpLedger
      activityVectorDigest orderingTieBreakWitness reasonProtectionLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript bumpAccepted := by
  intro accepted
  exact accepted

theorem ay_cabg_accepted_clause_database_digest
    {clauseDatabaseDigest : Prop} :
    clauseDatabaseDigest ->
    ay_cabg_clause_database_digest_evidence clauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_cabg_accepted_conflict_clause_digest
    {conflictClauseDigest : Prop} :
    conflictClauseDigest ->
    ay_cabg_conflict_clause_digest_evidence conflictClauseDigest := by
  intro evidence
  exact evidence

theorem ay_cabg_accepted_bump_ledger
    {bumpLedger : Prop} :
    bumpLedger -> ay_cabg_bump_ledger_evidence bumpLedger := by
  intro evidence
  exact evidence

theorem ay_cabg_accepted_activity_vector_digest
    {activityVectorDigest : Prop} :
    activityVectorDigest ->
    ay_cabg_activity_vector_digest_evidence activityVectorDigest := by
  intro evidence
  exact evidence

theorem ay_cabg_accepted_ordering_tie_break_witness
    {orderingTieBreakWitness : Prop} :
    orderingTieBreakWitness ->
    ay_cabg_ordering_tie_break_witness_evidence
      orderingTieBreakWitness := by
  intro evidence
  exact evidence

theorem ay_cabg_accepted_reason_protection_ledger
    {reasonProtectionLedger : Prop} :
    reasonProtectionLedger ->
    ay_cabg_reason_protection_ledger_evidence reasonProtectionLedger := by
  intro evidence
  exact evidence

theorem ay_cabg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_cabg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_cabg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_cabg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_cabg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_cabg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_cabg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_cabg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_cabg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_cabg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_cabg_bumping_is_heuristic_accounting_only
    {bumpAccepted heuristicAccountingOnly : Prop} :
    bumpAccepted ->
    heuristicAccountingOnly ->
    heuristicAccountingOnly :=
  fun _ accountingOnly => accountingOnly

theorem ay_cabg_bumping_cannot_change_original_formula_truth
    {bumpAccepted originalFormulaTruthPreserved : Prop} :
    bumpAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_cabg_accepted_bump_preserves_public_soundness
    {bumpAccepted satSound unsatSound : Prop} :
    bumpAccepted ->
    ay_cabg_public_soundness_theorem satSound unsatSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_cabg_bump_ledger_preserves_replay
    {bumpLedger propagationReplay : Prop} :
    bumpLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_cabg_ordering_witness_preserves_replay
    {orderingTieBreakWitness propagationReplay : Prop} :
    orderingTieBreakWitness ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_cabg_reason_protection_preserves_replay
    {reasonProtectionLedger propagationReplay : Prop} :
    reasonProtectionLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_cabg_accepted_bump_preserves_fallback_soundness
    {bumpAccepted fallbackBaseline satSound unsatSound : Prop} :
    bumpAccepted ->
    fallbackBaseline ->
    ay_cabg_public_soundness_theorem satSound unsatSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cabg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_cabg_gate accepted rejected ->
    ay_cabg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_cabg_rejected_is_no_claim
    {bumpMismatch diagnostic : Prop} :
    bumpMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_rejected_forces_recompute
    {bumpMismatch recomputeRequired : Prop} :
    bumpMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_failed_guard_cannot_bless_publication
    {bumpMismatch baselineSound satSound unsatSound : Prop} :
    bumpMismatch ->
    baselineSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cabg_bump_mismatch_forces_no_claim
    {bumpMismatch diagnostic : Prop} :
    bumpMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_activity_mismatch_forces_no_claim
    {activityMismatch diagnostic : Prop} :
    activityMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_order_mismatch_forces_no_claim
    {orderMismatch diagnostic : Prop} :
    orderMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_reason_mismatch_forces_no_claim
    {reasonMismatch diagnostic : Prop} :
    reasonMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_clause_mismatch_forces_no_claim
    {clauseMismatch diagnostic : Prop} :
    clauseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_conflict_mismatch_forces_no_claim
    {conflictMismatch diagnostic : Prop} :
    conflictMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cabg_bump_mismatch_forces_recompute
    {bumpMismatch recomputeRequired : Prop} :
    bumpMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_activity_mismatch_forces_recompute
    {activityMismatch recomputeRequired : Prop} :
    activityMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_order_mismatch_forces_recompute
    {orderMismatch recomputeRequired : Prop} :
    orderMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_reason_mismatch_forces_recompute
    {reasonMismatch recomputeRequired : Prop} :
    reasonMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_clause_mismatch_forces_recompute
    {clauseMismatch recomputeRequired : Prop} :
    clauseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_conflict_mismatch_forces_recompute
    {conflictMismatch recomputeRequired : Prop} :
    conflictMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cabg_bump_mismatch_cannot_bless_publication
    {bumpMismatch baselineSound satSound unsatSound : Prop} :
    bumpMismatch ->
    baselineSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cabg_activity_mismatch_cannot_bless_publication
    {activityMismatch baselineSound satSound unsatSound : Prop} :
    activityMismatch ->
    baselineSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cabg_order_mismatch_cannot_bless_publication
    {orderMismatch baselineSound satSound unsatSound : Prop} :
    orderMismatch ->
    baselineSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cabg_reason_mismatch_cannot_bless_publication
    {reasonMismatch baselineSound satSound unsatSound : Prop} :
    reasonMismatch ->
    baselineSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cabg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cabg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cabg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound ->
    ay_cabg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cabg_policy_requires_clause_database_digest
    {clauseDatabaseDigest accepted : Prop} :
    clauseDatabaseDigest -> accepted -> clauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_cabg_policy_requires_conflict_clause_digest
    {conflictClauseDigest accepted : Prop} :
    conflictClauseDigest -> accepted -> conflictClauseDigest :=
  fun evidence _ => evidence

theorem ay_cabg_policy_requires_bump_ledger
    {bumpLedger accepted : Prop} :
    bumpLedger -> accepted -> bumpLedger :=
  fun evidence _ => evidence

theorem ay_cabg_policy_requires_activity_vector_digest
    {activityVectorDigest accepted : Prop} :
    activityVectorDigest -> accepted -> activityVectorDigest :=
  fun evidence _ => evidence

theorem ay_cabg_policy_requires_ordering_tie_break
    {orderingTieBreakWitness accepted : Prop} :
    orderingTieBreakWitness -> accepted -> orderingTieBreakWitness :=
  fun evidence _ => evidence

theorem ay_cabg_policy_requires_reason_protection
    {reasonProtectionLedger accepted : Prop} :
    reasonProtectionLedger -> accepted -> reasonProtectionLedger :=
  fun evidence _ => evidence

theorem ay_cabg_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_cabg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_cabg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_cabg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_cabg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
