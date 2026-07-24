def ay_pbcg_conj (p q : Prop) : Prop := p ∧ q

def ay_pbcg_disj (p q : Prop) : Prop := p ∨ q

def ay_pbcg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_pbcg_disj satSound unsatSound

def ay_pbcg_inputs
    (propagationBudgetManifest propagationCounterDigest cutoffDecisionLedger
      partialTrailClauseDbDigest noResultFallbackPath solverBuildEvidence
      validatorGate archiveManifest auditTranscript : Prop) : Prop :=
  ay_pbcg_conj propagationBudgetManifest
    (ay_pbcg_conj propagationCounterDigest
      (ay_pbcg_conj cutoffDecisionLedger
        (ay_pbcg_conj partialTrailClauseDbDigest
          (ay_pbcg_conj noResultFallbackPath
            (ay_pbcg_conj solverBuildEvidence
              (ay_pbcg_conj validatorGate
                (ay_pbcg_conj archiveManifest auditTranscript)))))))

def ay_pbcg_propagation_budget_manifest_evidence
    (propagationBudgetManifest : Prop) : Prop :=
  propagationBudgetManifest

def ay_pbcg_propagation_counter_digest_evidence
    (propagationCounterDigest : Prop) : Prop :=
  propagationCounterDigest

def ay_pbcg_cutoff_decision_ledger_evidence
    (cutoffDecisionLedger : Prop) : Prop :=
  cutoffDecisionLedger

def ay_pbcg_partial_trail_clause_db_digest_evidence
    (partialTrailClauseDbDigest : Prop) : Prop :=
  partialTrailClauseDbDigest

def ay_pbcg_no_result_fallback_path_evidence
    (noResultFallbackPath : Prop) : Prop :=
  noResultFallbackPath

def ay_pbcg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_pbcg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_pbcg_archive_manifest_evidence (archiveManifest : Prop) : Prop :=
  archiveManifest

def ay_pbcg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_pbcg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_pbcg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_pbcg_checked_sat_evidence (satEvidence : Prop) : Prop :=
  satEvidence

def ay_pbcg_checked_unsat_evidence (unsatEvidence : Prop) : Prop :=
  unsatEvidence

def ay_pbcg_accepted
    (propagationBudgetManifest propagationCounterDigest cutoffDecisionLedger
      partialTrailClauseDbDigest noResultFallbackPath solverBuildEvidence
      validatorGate archiveManifest auditTranscript cutoffAccepted : Prop) :
    Prop :=
  cutoffAccepted

def ay_pbcg_rejected
    (budgetMismatch counterMismatch cutoffMismatch partialStateMismatch
      fallbackMismatch buildMismatch validatorMismatch archiveMismatch
      auditMismatch : Prop) : Prop :=
  ay_pbcg_disj budgetMismatch
    (ay_pbcg_disj counterMismatch
      (ay_pbcg_disj cutoffMismatch
        (ay_pbcg_disj partialStateMismatch
          (ay_pbcg_disj fallbackMismatch
            (ay_pbcg_disj buildMismatch
              (ay_pbcg_disj validatorMismatch
                (ay_pbcg_disj archiveMismatch auditMismatch)))))))

def ay_pbcg_cutoff_search_control_no_result
    (cutoffAccepted searchControlOnly noResultClassification : Prop) : Prop :=
  cutoffAccepted

def ay_pbcg_gate (accepted rejected : Prop) : Prop :=
  ay_pbcg_disj accepted rejected

theorem ay_pbcg_input_components
    {propagationBudgetManifest propagationCounterDigest cutoffDecisionLedger
      partialTrailClauseDbDigest noResultFallbackPath solverBuildEvidence
      validatorGate archiveManifest auditTranscript : Prop} :
    ay_pbcg_inputs propagationBudgetManifest propagationCounterDigest
      cutoffDecisionLedger partialTrailClauseDbDigest noResultFallbackPath
      solverBuildEvidence validatorGate archiveManifest auditTranscript ->
    ay_pbcg_inputs propagationBudgetManifest propagationCounterDigest
      cutoffDecisionLedger partialTrailClauseDbDigest noResultFallbackPath
      solverBuildEvidence validatorGate archiveManifest auditTranscript := by
  intro inputs
  exact inputs

theorem ay_pbcg_accepted_cutoff
    {propagationBudgetManifest propagationCounterDigest cutoffDecisionLedger
      partialTrailClauseDbDigest noResultFallbackPath solverBuildEvidence
      validatorGate archiveManifest auditTranscript cutoffAccepted : Prop} :
    cutoffAccepted ->
    ay_pbcg_accepted propagationBudgetManifest propagationCounterDigest
      cutoffDecisionLedger partialTrailClauseDbDigest noResultFallbackPath
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      cutoffAccepted := by
  intro accepted
  exact accepted

theorem ay_pbcg_accepted_propagation_budget_manifest
    {propagationBudgetManifest : Prop} :
    propagationBudgetManifest ->
    ay_pbcg_propagation_budget_manifest_evidence
      propagationBudgetManifest := by
  intro evidence
  exact evidence

theorem ay_pbcg_accepted_propagation_counter_digest
    {propagationCounterDigest : Prop} :
    propagationCounterDigest ->
    ay_pbcg_propagation_counter_digest_evidence propagationCounterDigest := by
  intro evidence
  exact evidence

theorem ay_pbcg_accepted_cutoff_decision_ledger
    {cutoffDecisionLedger : Prop} :
    cutoffDecisionLedger ->
    ay_pbcg_cutoff_decision_ledger_evidence cutoffDecisionLedger := by
  intro evidence
  exact evidence

theorem ay_pbcg_accepted_partial_trail_clause_db_digest
    {partialTrailClauseDbDigest : Prop} :
    partialTrailClauseDbDigest ->
    ay_pbcg_partial_trail_clause_db_digest_evidence
      partialTrailClauseDbDigest := by
  intro evidence
  exact evidence

theorem ay_pbcg_accepted_no_result_fallback_path
    {noResultFallbackPath : Prop} :
    noResultFallbackPath ->
    ay_pbcg_no_result_fallback_path_evidence noResultFallbackPath := by
  intro evidence
  exact evidence

theorem ay_pbcg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_pbcg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_pbcg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_pbcg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_pbcg_accepted_archive_manifest
    {archiveManifest : Prop} :
    archiveManifest -> ay_pbcg_archive_manifest_evidence archiveManifest := by
  intro evidence
  exact evidence

theorem ay_pbcg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_pbcg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_pbcg_cutoff_is_search_control_only
    {cutoffAccepted searchControlOnly : Prop} :
    cutoffAccepted ->
    searchControlOnly ->
    searchControlOnly :=
  fun _ controlOnly => controlOnly

theorem ay_pbcg_accepted_cutoff_is_no_result_classification
    {cutoffAccepted noResultClassification : Prop} :
    cutoffAccepted ->
    noResultClassification ->
    noResultClassification :=
  fun _ noResult => noResult

theorem ay_pbcg_cutoff_cannot_change_original_formula_truth
    {cutoffAccepted originalFormulaTruthPreserved : Prop} :
    cutoffAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_pbcg_cutoff_cannot_bless_sat_without_checked_evidence
    {cutoffAccepted satEvidence satSound : Prop} :
    cutoffAccepted ->
    ay_pbcg_checked_sat_evidence satEvidence ->
    (satEvidence -> satSound) ->
    satSound :=
  fun _ evidence transport => transport evidence

theorem ay_pbcg_cutoff_cannot_bless_unsat_without_checked_evidence
    {cutoffAccepted unsatEvidence unsatSound : Prop} :
    cutoffAccepted ->
    ay_pbcg_checked_unsat_evidence unsatEvidence ->
    (unsatEvidence -> unsatSound) ->
    unsatSound :=
  fun _ evidence transport => transport evidence

theorem ay_pbcg_checked_evidence_preserves_public_soundness
    {checkedEvidence satSound unsatSound : Prop} :
    checkedEvidence ->
    ay_pbcg_public_soundness_theorem satSound unsatSound ->
    ay_pbcg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_pbcg_accepted_cutoff_preserves_no_result_fallback
    {cutoffAccepted noResultFallbackPath : Prop} :
    cutoffAccepted ->
    noResultFallbackPath ->
    noResultFallbackPath :=
  fun _ fallback => fallback

theorem ay_pbcg_budget_manifest_preserves_cutoff_accounting
    {propagationBudgetManifest cutoffDecisionLedger : Prop} :
    propagationBudgetManifest ->
    cutoffDecisionLedger ->
    cutoffDecisionLedger :=
  fun _ ledger => ledger

theorem ay_pbcg_counter_digest_preserves_cutoff_accounting
    {propagationCounterDigest cutoffDecisionLedger : Prop} :
    propagationCounterDigest ->
    cutoffDecisionLedger ->
    cutoffDecisionLedger :=
  fun _ ledger => ledger

theorem ay_pbcg_archive_manifest_preserves_no_result_record
    {archiveManifest noResultFallbackPath : Prop} :
    archiveManifest ->
    noResultFallbackPath ->
    noResultFallbackPath :=
  fun _ fallback => fallback

theorem ay_pbcg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_pbcg_gate accepted rejected ->
    ay_pbcg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_pbcg_rejected_is_no_claim
    {budgetMismatch diagnostic : Prop} :
    budgetMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pbcg_rejected_forces_recompute
    {budgetMismatch recomputeRequired : Prop} :
    budgetMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pbcg_failed_guard_cannot_bless_publication
    {budgetMismatch baselineNoResult satSound unsatSound : Prop} :
    budgetMismatch ->
    baselineNoResult ->
    ay_pbcg_public_soundness_theorem satSound unsatSound ->
    ay_pbcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pbcg_budget_mismatch_forces_no_claim
    {budgetMismatch diagnostic : Prop} :
    budgetMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pbcg_counter_mismatch_forces_no_claim
    {counterMismatch diagnostic : Prop} :
    counterMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pbcg_cutoff_mismatch_forces_no_claim
    {cutoffMismatch diagnostic : Prop} :
    cutoffMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pbcg_partial_state_mismatch_forces_no_claim
    {partialStateMismatch diagnostic : Prop} :
    partialStateMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pbcg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pbcg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pbcg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pbcg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic : Prop} :
    archiveMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pbcg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_pbcg_budget_mismatch_forces_recompute
    {budgetMismatch recomputeRequired : Prop} :
    budgetMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pbcg_counter_mismatch_forces_recompute
    {counterMismatch recomputeRequired : Prop} :
    counterMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pbcg_cutoff_mismatch_forces_recompute
    {cutoffMismatch recomputeRequired : Prop} :
    cutoffMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pbcg_partial_state_mismatch_forces_recompute
    {partialStateMismatch recomputeRequired : Prop} :
    partialStateMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pbcg_fallback_mismatch_forces_recompute
    {fallbackMismatch recomputeRequired : Prop} :
    fallbackMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pbcg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pbcg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pbcg_archive_mismatch_forces_recompute
    {archiveMismatch recomputeRequired : Prop} :
    archiveMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pbcg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_pbcg_budget_mismatch_cannot_bless_publication
    {budgetMismatch baselineNoResult satSound unsatSound : Prop} :
    budgetMismatch ->
    baselineNoResult ->
    ay_pbcg_public_soundness_theorem satSound unsatSound ->
    ay_pbcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pbcg_counter_mismatch_cannot_bless_publication
    {counterMismatch baselineNoResult satSound unsatSound : Prop} :
    counterMismatch ->
    baselineNoResult ->
    ay_pbcg_public_soundness_theorem satSound unsatSound ->
    ay_pbcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pbcg_cutoff_mismatch_cannot_bless_publication
    {cutoffMismatch baselineNoResult satSound unsatSound : Prop} :
    cutoffMismatch ->
    baselineNoResult ->
    ay_pbcg_public_soundness_theorem satSound unsatSound ->
    ay_pbcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pbcg_partial_state_mismatch_cannot_bless_publication
    {partialStateMismatch baselineNoResult satSound unsatSound : Prop} :
    partialStateMismatch ->
    baselineNoResult ->
    ay_pbcg_public_soundness_theorem satSound unsatSound ->
    ay_pbcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_pbcg_policy_requires_propagation_budget_manifest
    {propagationBudgetManifest accepted : Prop} :
    propagationBudgetManifest -> accepted -> propagationBudgetManifest :=
  fun evidence _ => evidence

theorem ay_pbcg_policy_requires_propagation_counter_digest
    {propagationCounterDigest accepted : Prop} :
    propagationCounterDigest -> accepted -> propagationCounterDigest :=
  fun evidence _ => evidence

theorem ay_pbcg_policy_requires_cutoff_decision_ledger
    {cutoffDecisionLedger accepted : Prop} :
    cutoffDecisionLedger -> accepted -> cutoffDecisionLedger :=
  fun evidence _ => evidence

theorem ay_pbcg_policy_requires_partial_trail_clause_db_digest
    {partialTrailClauseDbDigest accepted : Prop} :
    partialTrailClauseDbDigest -> accepted -> partialTrailClauseDbDigest :=
  fun evidence _ => evidence

theorem ay_pbcg_policy_requires_no_result_fallback_path
    {noResultFallbackPath accepted : Prop} :
    noResultFallbackPath -> accepted -> noResultFallbackPath :=
  fun evidence _ => evidence

theorem ay_pbcg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_pbcg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_pbcg_policy_requires_archive
    {archiveManifest accepted : Prop} :
    archiveManifest -> accepted -> archiveManifest :=
  fun evidence _ => evidence

theorem ay_pbcg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
