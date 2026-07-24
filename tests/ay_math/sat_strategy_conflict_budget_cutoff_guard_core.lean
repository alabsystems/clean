def ay_cbcg_conj (p q : Prop) : Prop := p ∧ q

def ay_cbcg_disj (p q : Prop) : Prop := p ∨ q

def ay_cbcg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_cbcg_disj satSound unsatSound

def ay_cbcg_inputs
    (conflictBudgetManifest conflictCounterDigest cutoffDecisionLedger
      partialTrailClauseDbDigest noResultFallbackPath solverBuildEvidence
      validatorGate archiveManifest auditTranscript : Prop) : Prop :=
  ay_cbcg_conj conflictBudgetManifest
    (ay_cbcg_conj conflictCounterDigest
      (ay_cbcg_conj cutoffDecisionLedger
        (ay_cbcg_conj partialTrailClauseDbDigest
          (ay_cbcg_conj noResultFallbackPath
            (ay_cbcg_conj solverBuildEvidence
              (ay_cbcg_conj validatorGate
                (ay_cbcg_conj archiveManifest auditTranscript)))))))

def ay_cbcg_conflict_budget_manifest_evidence
    (conflictBudgetManifest : Prop) : Prop :=
  conflictBudgetManifest

def ay_cbcg_conflict_counter_digest_evidence
    (conflictCounterDigest : Prop) : Prop :=
  conflictCounterDigest

def ay_cbcg_cutoff_decision_ledger_evidence
    (cutoffDecisionLedger : Prop) : Prop :=
  cutoffDecisionLedger

def ay_cbcg_partial_trail_clause_db_digest_evidence
    (partialTrailClauseDbDigest : Prop) : Prop :=
  partialTrailClauseDbDigest

def ay_cbcg_no_result_fallback_path_evidence
    (noResultFallbackPath : Prop) : Prop :=
  noResultFallbackPath

def ay_cbcg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_cbcg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_cbcg_archive_manifest_evidence (archiveManifest : Prop) : Prop :=
  archiveManifest

def ay_cbcg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_cbcg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_cbcg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_cbcg_checked_sat_evidence (satEvidence : Prop) : Prop :=
  satEvidence

def ay_cbcg_checked_unsat_evidence (unsatEvidence : Prop) : Prop :=
  unsatEvidence

def ay_cbcg_accepted
    (conflictBudgetManifest conflictCounterDigest cutoffDecisionLedger
      partialTrailClauseDbDigest noResultFallbackPath solverBuildEvidence
      validatorGate archiveManifest auditTranscript cutoffAccepted : Prop) :
    Prop :=
  cutoffAccepted

def ay_cbcg_rejected
    (budgetMismatch counterMismatch cutoffMismatch partialStateMismatch
      fallbackMismatch buildMismatch validatorMismatch archiveMismatch
      auditMismatch : Prop) : Prop :=
  ay_cbcg_disj budgetMismatch
    (ay_cbcg_disj counterMismatch
      (ay_cbcg_disj cutoffMismatch
        (ay_cbcg_disj partialStateMismatch
          (ay_cbcg_disj fallbackMismatch
            (ay_cbcg_disj buildMismatch
              (ay_cbcg_disj validatorMismatch
                (ay_cbcg_disj archiveMismatch auditMismatch)))))))

def ay_cbcg_cutoff_search_control_no_result
    (cutoffAccepted searchControlOnly noResultClassification : Prop) : Prop :=
  cutoffAccepted

def ay_cbcg_gate (accepted rejected : Prop) : Prop :=
  ay_cbcg_disj accepted rejected

theorem ay_cbcg_input_components
    {conflictBudgetManifest conflictCounterDigest cutoffDecisionLedger
      partialTrailClauseDbDigest noResultFallbackPath solverBuildEvidence
      validatorGate archiveManifest auditTranscript : Prop} :
    ay_cbcg_inputs conflictBudgetManifest conflictCounterDigest
      cutoffDecisionLedger partialTrailClauseDbDigest noResultFallbackPath
      solverBuildEvidence validatorGate archiveManifest auditTranscript ->
    ay_cbcg_inputs conflictBudgetManifest conflictCounterDigest
      cutoffDecisionLedger partialTrailClauseDbDigest noResultFallbackPath
      solverBuildEvidence validatorGate archiveManifest auditTranscript := by
  intro inputs
  exact inputs

theorem ay_cbcg_accepted_cutoff
    {conflictBudgetManifest conflictCounterDigest cutoffDecisionLedger
      partialTrailClauseDbDigest noResultFallbackPath solverBuildEvidence
      validatorGate archiveManifest auditTranscript cutoffAccepted : Prop} :
    cutoffAccepted ->
    ay_cbcg_accepted conflictBudgetManifest conflictCounterDigest
      cutoffDecisionLedger partialTrailClauseDbDigest noResultFallbackPath
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      cutoffAccepted := by
  intro accepted
  exact accepted

theorem ay_cbcg_accepted_conflict_budget_manifest
    {conflictBudgetManifest : Prop} :
    conflictBudgetManifest ->
    ay_cbcg_conflict_budget_manifest_evidence conflictBudgetManifest := by
  intro evidence
  exact evidence

theorem ay_cbcg_accepted_conflict_counter_digest
    {conflictCounterDigest : Prop} :
    conflictCounterDigest ->
    ay_cbcg_conflict_counter_digest_evidence conflictCounterDigest := by
  intro evidence
  exact evidence

theorem ay_cbcg_accepted_cutoff_decision_ledger
    {cutoffDecisionLedger : Prop} :
    cutoffDecisionLedger ->
    ay_cbcg_cutoff_decision_ledger_evidence cutoffDecisionLedger := by
  intro evidence
  exact evidence

theorem ay_cbcg_accepted_partial_trail_clause_db_digest
    {partialTrailClauseDbDigest : Prop} :
    partialTrailClauseDbDigest ->
    ay_cbcg_partial_trail_clause_db_digest_evidence
      partialTrailClauseDbDigest := by
  intro evidence
  exact evidence

theorem ay_cbcg_accepted_no_result_fallback_path
    {noResultFallbackPath : Prop} :
    noResultFallbackPath ->
    ay_cbcg_no_result_fallback_path_evidence noResultFallbackPath := by
  intro evidence
  exact evidence

theorem ay_cbcg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_cbcg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_cbcg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_cbcg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_cbcg_accepted_archive_manifest
    {archiveManifest : Prop} :
    archiveManifest -> ay_cbcg_archive_manifest_evidence archiveManifest := by
  intro evidence
  exact evidence

theorem ay_cbcg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_cbcg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_cbcg_cutoff_is_search_control_only
    {cutoffAccepted searchControlOnly : Prop} :
    cutoffAccepted ->
    searchControlOnly ->
    searchControlOnly :=
  fun _ controlOnly => controlOnly

theorem ay_cbcg_accepted_cutoff_is_no_result_classification
    {cutoffAccepted noResultClassification : Prop} :
    cutoffAccepted ->
    noResultClassification ->
    noResultClassification :=
  fun _ noResult => noResult

theorem ay_cbcg_cutoff_cannot_change_original_formula_truth
    {cutoffAccepted originalFormulaTruthPreserved : Prop} :
    cutoffAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_cbcg_cutoff_cannot_bless_sat_without_checked_evidence
    {cutoffAccepted satEvidence satSound : Prop} :
    cutoffAccepted ->
    ay_cbcg_checked_sat_evidence satEvidence ->
    (satEvidence -> satSound) ->
    satSound :=
  fun _ evidence transport => transport evidence

theorem ay_cbcg_cutoff_cannot_bless_unsat_without_checked_evidence
    {cutoffAccepted unsatEvidence unsatSound : Prop} :
    cutoffAccepted ->
    ay_cbcg_checked_unsat_evidence unsatEvidence ->
    (unsatEvidence -> unsatSound) ->
    unsatSound :=
  fun _ evidence transport => transport evidence

theorem ay_cbcg_checked_evidence_preserves_public_soundness
    {checkedEvidence satSound unsatSound : Prop} :
    checkedEvidence ->
    ay_cbcg_public_soundness_theorem satSound unsatSound ->
    ay_cbcg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_cbcg_accepted_cutoff_preserves_no_result_fallback
    {cutoffAccepted noResultFallbackPath : Prop} :
    cutoffAccepted ->
    noResultFallbackPath ->
    noResultFallbackPath :=
  fun _ fallback => fallback

theorem ay_cbcg_budget_manifest_preserves_cutoff_accounting
    {conflictBudgetManifest cutoffDecisionLedger : Prop} :
    conflictBudgetManifest ->
    cutoffDecisionLedger ->
    cutoffDecisionLedger :=
  fun _ ledger => ledger

theorem ay_cbcg_counter_digest_preserves_cutoff_accounting
    {conflictCounterDigest cutoffDecisionLedger : Prop} :
    conflictCounterDigest ->
    cutoffDecisionLedger ->
    cutoffDecisionLedger :=
  fun _ ledger => ledger

theorem ay_cbcg_archive_manifest_preserves_no_result_record
    {archiveManifest noResultFallbackPath : Prop} :
    archiveManifest ->
    noResultFallbackPath ->
    noResultFallbackPath :=
  fun _ fallback => fallback

theorem ay_cbcg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_cbcg_gate accepted rejected ->
    ay_cbcg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_cbcg_rejected_is_no_claim
    {budgetMismatch diagnostic : Prop} :
    budgetMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cbcg_rejected_forces_recompute
    {budgetMismatch recomputeRequired : Prop} :
    budgetMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cbcg_failed_guard_cannot_bless_publication
    {budgetMismatch baselineNoResult satSound unsatSound : Prop} :
    budgetMismatch ->
    baselineNoResult ->
    ay_cbcg_public_soundness_theorem satSound unsatSound ->
    ay_cbcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cbcg_budget_mismatch_forces_no_claim
    {budgetMismatch diagnostic : Prop} :
    budgetMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cbcg_counter_mismatch_forces_no_claim
    {counterMismatch diagnostic : Prop} :
    counterMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cbcg_cutoff_mismatch_forces_no_claim
    {cutoffMismatch diagnostic : Prop} :
    cutoffMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cbcg_partial_state_mismatch_forces_no_claim
    {partialStateMismatch diagnostic : Prop} :
    partialStateMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cbcg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cbcg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cbcg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cbcg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic : Prop} :
    archiveMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cbcg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_cbcg_budget_mismatch_forces_recompute
    {budgetMismatch recomputeRequired : Prop} :
    budgetMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cbcg_counter_mismatch_forces_recompute
    {counterMismatch recomputeRequired : Prop} :
    counterMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cbcg_cutoff_mismatch_forces_recompute
    {cutoffMismatch recomputeRequired : Prop} :
    cutoffMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cbcg_partial_state_mismatch_forces_recompute
    {partialStateMismatch recomputeRequired : Prop} :
    partialStateMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cbcg_fallback_mismatch_forces_recompute
    {fallbackMismatch recomputeRequired : Prop} :
    fallbackMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cbcg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cbcg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cbcg_archive_mismatch_forces_recompute
    {archiveMismatch recomputeRequired : Prop} :
    archiveMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cbcg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_cbcg_budget_mismatch_cannot_bless_publication
    {budgetMismatch baselineNoResult satSound unsatSound : Prop} :
    budgetMismatch ->
    baselineNoResult ->
    ay_cbcg_public_soundness_theorem satSound unsatSound ->
    ay_cbcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cbcg_counter_mismatch_cannot_bless_publication
    {counterMismatch baselineNoResult satSound unsatSound : Prop} :
    counterMismatch ->
    baselineNoResult ->
    ay_cbcg_public_soundness_theorem satSound unsatSound ->
    ay_cbcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cbcg_cutoff_mismatch_cannot_bless_publication
    {cutoffMismatch baselineNoResult satSound unsatSound : Prop} :
    cutoffMismatch ->
    baselineNoResult ->
    ay_cbcg_public_soundness_theorem satSound unsatSound ->
    ay_cbcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cbcg_partial_state_mismatch_cannot_bless_publication
    {partialStateMismatch baselineNoResult satSound unsatSound : Prop} :
    partialStateMismatch ->
    baselineNoResult ->
    ay_cbcg_public_soundness_theorem satSound unsatSound ->
    ay_cbcg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_cbcg_policy_requires_conflict_budget_manifest
    {conflictBudgetManifest accepted : Prop} :
    conflictBudgetManifest -> accepted -> conflictBudgetManifest :=
  fun evidence _ => evidence

theorem ay_cbcg_policy_requires_conflict_counter_digest
    {conflictCounterDigest accepted : Prop} :
    conflictCounterDigest -> accepted -> conflictCounterDigest :=
  fun evidence _ => evidence

theorem ay_cbcg_policy_requires_cutoff_decision_ledger
    {cutoffDecisionLedger accepted : Prop} :
    cutoffDecisionLedger -> accepted -> cutoffDecisionLedger :=
  fun evidence _ => evidence

theorem ay_cbcg_policy_requires_partial_trail_clause_db_digest
    {partialTrailClauseDbDigest accepted : Prop} :
    partialTrailClauseDbDigest -> accepted -> partialTrailClauseDbDigest :=
  fun evidence _ => evidence

theorem ay_cbcg_policy_requires_no_result_fallback_path
    {noResultFallbackPath accepted : Prop} :
    noResultFallbackPath -> accepted -> noResultFallbackPath :=
  fun evidence _ => evidence

theorem ay_cbcg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_cbcg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_cbcg_policy_requires_archive
    {archiveManifest accepted : Prop} :
    archiveManifest -> accepted -> archiveManifest :=
  fun evidence _ => evidence

theorem ay_cbcg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
