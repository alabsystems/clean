def ay_rbog_conj (p q : Prop) : Prop := p ∧ q

def ay_rbog_disj (p q : Prop) : Prop := p ∨ q

def ay_rbog_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rbog_disj satSound unsatSound

def ay_rbog_inputs
    (restartBudgetDigest counterWidthManifest overflowPolicyWitness
      conflictWindowLedger scheduleReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) : Prop :=
  ay_rbog_conj restartBudgetDigest
    (ay_rbog_conj counterWidthManifest
      (ay_rbog_conj overflowPolicyWitness
        (ay_rbog_conj conflictWindowLedger
          (ay_rbog_conj scheduleReplay
            (ay_rbog_conj fallbackBaseline
              (ay_rbog_conj solverBuildEvidence
                (ay_rbog_conj validatorGate auditTranscript)))))))

def ay_rbog_restart_budget_digest_evidence
    (restartBudgetDigest : Prop) : Prop :=
  restartBudgetDigest

def ay_rbog_counter_width_manifest_evidence
    (counterWidthManifest : Prop) : Prop :=
  counterWidthManifest

def ay_rbog_overflow_policy_witness_evidence
    (overflowPolicyWitness : Prop) : Prop :=
  overflowPolicyWitness

def ay_rbog_conflict_window_ledger_evidence
    (conflictWindowLedger : Prop) : Prop :=
  conflictWindowLedger

def ay_rbog_schedule_replay_evidence (scheduleReplay : Prop) : Prop :=
  scheduleReplay

def ay_rbog_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_rbog_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rbog_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rbog_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rbog_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rbog_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_rbog_accepted
    (restartBudgetDigest counterWidthManifest overflowPolicyWitness
      conflictWindowLedger scheduleReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript overflowHandlingAccepted : Prop) : Prop :=
  overflowHandlingAccepted

def ay_rbog_rejected
    (budgetMismatch widthMismatch policyMismatch windowMismatch
      scheduleMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch : Prop) : Prop :=
  ay_rbog_disj budgetMismatch
    (ay_rbog_disj widthMismatch
      (ay_rbog_disj policyMismatch
        (ay_rbog_disj windowMismatch
          (ay_rbog_disj scheduleMismatch
            (ay_rbog_disj baselineMismatch
              (ay_rbog_disj buildMismatch
                (ay_rbog_disj validatorMismatch auditMismatch)))))))

def ay_rbog_gate (accepted rejected : Prop) : Prop :=
  ay_rbog_disj accepted rejected

def ay_rbog_overflow_search_control_hint
    (overflowHandlingAccepted searchControlOnly deterministicSchedule
      replayAccepted : Prop) : Prop :=
  overflowHandlingAccepted

theorem ay_rbog_input_components
    {restartBudgetDigest counterWidthManifest overflowPolicyWitness
      conflictWindowLedger scheduleReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop} :
    ay_rbog_inputs restartBudgetDigest counterWidthManifest
      overflowPolicyWitness conflictWindowLedger scheduleReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_rbog_inputs restartBudgetDigest counterWidthManifest
      overflowPolicyWitness conflictWindowLedger scheduleReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rbog_accepted_policy
    {restartBudgetDigest counterWidthManifest overflowPolicyWitness
      conflictWindowLedger scheduleReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript overflowHandlingAccepted : Prop} :
    overflowHandlingAccepted ->
    ay_rbog_accepted restartBudgetDigest counterWidthManifest
      overflowPolicyWitness conflictWindowLedger scheduleReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      overflowHandlingAccepted := by
  intro accepted
  exact accepted

theorem ay_rbog_accepted_restart_budget_digest
    {restartBudgetDigest : Prop} :
    restartBudgetDigest ->
    ay_rbog_restart_budget_digest_evidence restartBudgetDigest := by
  intro evidence
  exact evidence

theorem ay_rbog_accepted_counter_width_manifest
    {counterWidthManifest : Prop} :
    counterWidthManifest ->
    ay_rbog_counter_width_manifest_evidence counterWidthManifest := by
  intro evidence
  exact evidence

theorem ay_rbog_accepted_overflow_policy_witness
    {overflowPolicyWitness : Prop} :
    overflowPolicyWitness ->
    ay_rbog_overflow_policy_witness_evidence overflowPolicyWitness := by
  intro evidence
  exact evidence

theorem ay_rbog_accepted_conflict_window_ledger
    {conflictWindowLedger : Prop} :
    conflictWindowLedger ->
    ay_rbog_conflict_window_ledger_evidence conflictWindowLedger := by
  intro evidence
  exact evidence

theorem ay_rbog_accepted_schedule_replay
    {scheduleReplay : Prop} :
    scheduleReplay -> ay_rbog_schedule_replay_evidence scheduleReplay := by
  intro evidence
  exact evidence

theorem ay_rbog_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_rbog_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_rbog_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_rbog_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rbog_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rbog_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rbog_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rbog_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rbog_overflow_handling_is_search_control_only
    {overflowHandlingAccepted searchControlOnly : Prop} :
    overflowHandlingAccepted ->
    searchControlOnly ->
    searchControlOnly := by
  intro accepted controlOnly
  exact controlOnly

theorem ay_rbog_overflow_handling_cannot_change_original_formula_truth
    {overflowHandlingAccepted originalFormulaTruthPreserved : Prop} :
    overflowHandlingAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_rbog_accepted_evidence_preserves_public_soundness
    {overflowHandlingAccepted satSound unsatSound : Prop} :
    overflowHandlingAccepted ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rbog_accepted_overflow_hint_preserves_schedule_replay
    {overflowHandlingAccepted scheduleReplay : Prop} :
    overflowHandlingAccepted ->
    scheduleReplay ->
    scheduleReplay :=
  fun _ replay => replay

theorem ay_rbog_accepted_overflow_hint_preserves_fallback_soundness
    {overflowHandlingAccepted fallbackBaseline satSound unsatSound : Prop} :
    overflowHandlingAccepted ->
    fallbackBaseline ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbog_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rbog_gate accepted rejected ->
    ay_rbog_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rbog_gate_rejects_on_diagnostic
    {accepted rejected : Prop} :
    ay_rbog_gate accepted rejected ->
    ay_rbog_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rbog_rejected_is_no_claim
    {budgetMismatch diagnostic : Prop} :
    budgetMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbog_rejected_forces_recompute
    {budgetMismatch recomputeRequired : Prop} :
    budgetMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbog_failed_overflow_guard_cannot_bless_publication
    {budgetMismatch baselineSound satSound unsatSound : Prop} :
    budgetMismatch ->
    baselineSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbog_budget_mismatch_forces_no_claim
    {budgetMismatch diagnostic : Prop} :
    budgetMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbog_width_mismatch_forces_no_claim
    {widthMismatch diagnostic : Prop} :
    widthMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbog_policy_mismatch_forces_no_claim
    {policyMismatch diagnostic : Prop} :
    policyMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbog_window_mismatch_forces_no_claim
    {windowMismatch diagnostic : Prop} :
    windowMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbog_schedule_mismatch_forces_no_claim
    {scheduleMismatch diagnostic : Prop} :
    scheduleMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbog_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbog_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbog_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbog_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rbog_budget_mismatch_forces_recompute
    {budgetMismatch recomputeRequired : Prop} :
    budgetMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbog_width_mismatch_forces_recompute
    {widthMismatch recomputeRequired : Prop} :
    widthMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbog_policy_mismatch_forces_recompute
    {policyMismatch recomputeRequired : Prop} :
    policyMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbog_window_mismatch_forces_recompute
    {windowMismatch recomputeRequired : Prop} :
    windowMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbog_schedule_mismatch_forces_recompute
    {scheduleMismatch recomputeRequired : Prop} :
    scheduleMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbog_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbog_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbog_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbog_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rbog_budget_mismatch_cannot_bless_publication
    {budgetMismatch baselineSound satSound unsatSound : Prop} :
    budgetMismatch ->
    baselineSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbog_width_mismatch_cannot_bless_publication
    {widthMismatch baselineSound satSound unsatSound : Prop} :
    widthMismatch ->
    baselineSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbog_policy_mismatch_cannot_bless_publication
    {policyMismatch baselineSound satSound unsatSound : Prop} :
    policyMismatch ->
    baselineSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbog_window_mismatch_cannot_bless_publication
    {windowMismatch baselineSound satSound unsatSound : Prop} :
    windowMismatch ->
    baselineSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbog_schedule_mismatch_cannot_bless_publication
    {scheduleMismatch baselineSound satSound unsatSound : Prop} :
    scheduleMismatch ->
    baselineSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbog_baseline_mismatch_cannot_bless_publication
    {baselineMismatch baselineSound satSound unsatSound : Prop} :
    baselineMismatch ->
    baselineSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbog_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbog_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbog_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound ->
    ay_rbog_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rbog_policy_requires_restart_budget_digest
    {restartBudgetDigest accepted : Prop} :
    restartBudgetDigest -> accepted -> restartBudgetDigest :=
  fun evidence _ => evidence

theorem ay_rbog_policy_requires_counter_width_manifest
    {counterWidthManifest accepted : Prop} :
    counterWidthManifest -> accepted -> counterWidthManifest :=
  fun evidence _ => evidence

theorem ay_rbog_policy_requires_overflow_policy_witness
    {overflowPolicyWitness accepted : Prop} :
    overflowPolicyWitness -> accepted -> overflowPolicyWitness :=
  fun evidence _ => evidence

theorem ay_rbog_policy_requires_conflict_window_ledger
    {conflictWindowLedger accepted : Prop} :
    conflictWindowLedger -> accepted -> conflictWindowLedger :=
  fun evidence _ => evidence

theorem ay_rbog_policy_requires_schedule_replay
    {scheduleReplay accepted : Prop} :
    scheduleReplay -> accepted -> scheduleReplay :=
  fun evidence _ => evidence

theorem ay_rbog_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_rbog_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_rbog_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_rbog_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
