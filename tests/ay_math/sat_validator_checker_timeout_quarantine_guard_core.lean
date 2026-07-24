-- SAT-COMP validator checker-timeout quarantine guard core.
--
-- Public SAT/UNSAT claims require completed checker evidence and matching
-- timeout budget, benchmark, certificate/model digest, build evidence,
-- archive, fallback baseline, no-claim quarantine, and audit transcript.

def ay_ctqg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ctqg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ctqg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_ctqg_disj satFact (ay_ctqg_disj unsatFact noClaimFact)

def ay_ctqg_checker_contract
    (checkerCompletionEvidence timeoutBudgetManifest benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline noClaimQuarantine auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (checkerCompletionEvidence -> timeoutBudgetManifest ->
      benchmarkFingerprint -> certificateModelArtifactDigest ->
      solverBuildEvidence -> archiveManifest -> fallbackBaseline ->
      noClaimQuarantine -> auditTranscript -> result) ->
    result

def ay_ctqg_sat_publication
    (checkerContract completedCheckerAcceptance modelEvidence originalModel :
      Prop) : Prop :=
  ay_ctqg_conj checkerContract
    (ay_ctqg_conj completedCheckerAcceptance
      (ay_ctqg_conj modelEvidence originalModel))

def ay_ctqg_unsat_publication
    (checkerContract completedCheckerAcceptance proofEvidence
      originalEmptyClause : Prop) : Prop :=
  ay_ctqg_conj checkerContract
    (ay_ctqg_conj completedCheckerAcceptance
      (ay_ctqg_conj proofEvidence originalEmptyClause))

def ay_ctqg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_ctqg_conj reason (ay_ctqg_conj fallbackPath auditTrail)

def ay_ctqg_quarantine
    (reason quarantineState auditTranscript : Prop) : Prop :=
  ay_ctqg_conj reason (ay_ctqg_conj quarantineState auditTranscript)

def ay_ctqg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_ctqg_conj reason
    (ay_ctqg_conj (satFact -> False) (unsatFact -> False))

def ay_ctqg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_ctqg_conj reason
    (ay_ctqg_conj fallbackPath recomputeObligation)

def ay_ctqg_timeout_failure
    (satFact unsatFact reason fallbackPath recomputeObligation
      quarantineState auditTranscript : Prop) : Prop :=
  ay_ctqg_conj
    (ay_ctqg_blocked_publication satFact unsatFact reason)
    (ay_ctqg_conj
      (ay_ctqg_recompute reason fallbackPath recomputeObligation)
      (ay_ctqg_quarantine reason quarantineState auditTranscript))

theorem ay_ctqg_conj_intro (left right : Prop) :
    left -> right -> ay_ctqg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ctqg_conj_left (left right : Prop) :
    ay_ctqg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ctqg_conj_right (left right : Prop) :
    ay_ctqg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ctqg_disj_left (left right : Prop) :
    left -> ay_ctqg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ctqg_disj_right (left right : Prop) :
    right -> ay_ctqg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ctqg_checker_contract_intro
    (checkerCompletionEvidence timeoutBudgetManifest benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline noClaimQuarantine auditTranscript : Prop) :
    checkerCompletionEvidence -> timeoutBudgetManifest ->
    benchmarkFingerprint -> certificateModelArtifactDigest ->
    solverBuildEvidence -> archiveManifest -> fallbackBaseline ->
    noClaimQuarantine -> auditTranscript ->
    ay_ctqg_checker_contract checkerCompletionEvidence timeoutBudgetManifest
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline noClaimQuarantine auditTranscript :=
  fun checkerProof budgetProof fingerprintProof certificateProof buildProof
      archiveProof fallbackProof quarantineProof auditProof result build =>
    build checkerProof budgetProof fingerprintProof certificateProof
      buildProof archiveProof fallbackProof quarantineProof auditProof

theorem ay_ctqg_checker_contract_completion
    (checkerCompletionEvidence timeoutBudgetManifest benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline noClaimQuarantine auditTranscript : Prop) :
    ay_ctqg_checker_contract checkerCompletionEvidence timeoutBudgetManifest
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline noClaimQuarantine auditTranscript ->
    checkerCompletionEvidence :=
  fun contract =>
    contract checkerCompletionEvidence
      (fun checkerProof _budgetProof _fingerprintProof _certificateProof
          _buildProof _archiveProof _fallbackProof _quarantineProof
          _auditProof => checkerProof)

theorem ay_ctqg_checker_contract_budget
    (checkerCompletionEvidence timeoutBudgetManifest benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline noClaimQuarantine auditTranscript : Prop) :
    ay_ctqg_checker_contract checkerCompletionEvidence timeoutBudgetManifest
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline noClaimQuarantine auditTranscript ->
    timeoutBudgetManifest :=
  fun contract =>
    contract timeoutBudgetManifest
      (fun _checkerProof budgetProof _fingerprintProof _certificateProof
          _buildProof _archiveProof _fallbackProof _quarantineProof
          _auditProof => budgetProof)

theorem ay_ctqg_checker_contract_fingerprint
    (checkerCompletionEvidence timeoutBudgetManifest benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline noClaimQuarantine auditTranscript : Prop) :
    ay_ctqg_checker_contract checkerCompletionEvidence timeoutBudgetManifest
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline noClaimQuarantine auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _checkerProof _budgetProof fingerprintProof _certificateProof
          _buildProof _archiveProof _fallbackProof _quarantineProof
          _auditProof => fingerprintProof)

theorem ay_ctqg_checker_contract_certificate_digest
    (checkerCompletionEvidence timeoutBudgetManifest benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline noClaimQuarantine auditTranscript : Prop) :
    ay_ctqg_checker_contract checkerCompletionEvidence timeoutBudgetManifest
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline noClaimQuarantine auditTranscript ->
    certificateModelArtifactDigest :=
  fun contract =>
    contract certificateModelArtifactDigest
      (fun _checkerProof _budgetProof _fingerprintProof certificateProof
          _buildProof _archiveProof _fallbackProof _quarantineProof
          _auditProof => certificateProof)

theorem ay_ctqg_checker_contract_build
    (checkerCompletionEvidence timeoutBudgetManifest benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline noClaimQuarantine auditTranscript : Prop) :
    ay_ctqg_checker_contract checkerCompletionEvidence timeoutBudgetManifest
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline noClaimQuarantine auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _checkerProof _budgetProof _fingerprintProof _certificateProof
          buildProof _archiveProof _fallbackProof _quarantineProof
          _auditProof => buildProof)

theorem ay_ctqg_checker_contract_archive
    (checkerCompletionEvidence timeoutBudgetManifest benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline noClaimQuarantine auditTranscript : Prop) :
    ay_ctqg_checker_contract checkerCompletionEvidence timeoutBudgetManifest
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline noClaimQuarantine auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _checkerProof _budgetProof _fingerprintProof _certificateProof
          _buildProof archiveProof _fallbackProof _quarantineProof
          _auditProof => archiveProof)

theorem ay_ctqg_checker_contract_fallback
    (checkerCompletionEvidence timeoutBudgetManifest benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline noClaimQuarantine auditTranscript : Prop) :
    ay_ctqg_checker_contract checkerCompletionEvidence timeoutBudgetManifest
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline noClaimQuarantine auditTranscript ->
    fallbackBaseline :=
  fun contract =>
    contract fallbackBaseline
      (fun _checkerProof _budgetProof _fingerprintProof _certificateProof
          _buildProof _archiveProof fallbackProof _quarantineProof
          _auditProof => fallbackProof)

theorem ay_ctqg_checker_contract_quarantine
    (checkerCompletionEvidence timeoutBudgetManifest benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline noClaimQuarantine auditTranscript : Prop) :
    ay_ctqg_checker_contract checkerCompletionEvidence timeoutBudgetManifest
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline noClaimQuarantine auditTranscript ->
    noClaimQuarantine :=
  fun contract =>
    contract noClaimQuarantine
      (fun _checkerProof _budgetProof _fingerprintProof _certificateProof
          _buildProof _archiveProof _fallbackProof quarantineProof
          _auditProof => quarantineProof)

theorem ay_ctqg_checker_contract_audit
    (checkerCompletionEvidence timeoutBudgetManifest benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline noClaimQuarantine auditTranscript : Prop) :
    ay_ctqg_checker_contract checkerCompletionEvidence timeoutBudgetManifest
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline noClaimQuarantine auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _checkerProof _budgetProof _fingerprintProof _certificateProof
          _buildProof _archiveProof _fallbackProof _quarantineProof
          auditProof => auditProof)

theorem ay_ctqg_sat_publication_intro
    (checkerContract completedCheckerAcceptance modelEvidence originalModel :
      Prop) :
    checkerContract -> completedCheckerAcceptance -> modelEvidence ->
    originalModel ->
    ay_ctqg_sat_publication checkerContract completedCheckerAcceptance
      modelEvidence originalModel :=
  fun contractProof acceptanceProof modelProof originalProof =>
    ay_ctqg_conj_intro checkerContract
      (ay_ctqg_conj completedCheckerAcceptance
        (ay_ctqg_conj modelEvidence originalModel)) contractProof
      (ay_ctqg_conj_intro completedCheckerAcceptance
        (ay_ctqg_conj modelEvidence originalModel) acceptanceProof
        (ay_ctqg_conj_intro modelEvidence originalModel modelProof
          originalProof))

theorem ay_ctqg_sat_publication_completed_acceptance
    (checkerContract completedCheckerAcceptance modelEvidence originalModel :
      Prop) :
    ay_ctqg_sat_publication checkerContract completedCheckerAcceptance
      modelEvidence originalModel ->
    completedCheckerAcceptance :=
  fun publication =>
    ay_ctqg_conj_left completedCheckerAcceptance
      (ay_ctqg_conj modelEvidence originalModel)
      (ay_ctqg_conj_right checkerContract
        (ay_ctqg_conj completedCheckerAcceptance
          (ay_ctqg_conj modelEvidence originalModel)) publication)

theorem ay_ctqg_sat_publication_original_model
    (checkerContract completedCheckerAcceptance modelEvidence originalModel :
      Prop) :
    ay_ctqg_sat_publication checkerContract completedCheckerAcceptance
      modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_ctqg_conj_right modelEvidence originalModel
      (ay_ctqg_conj_right completedCheckerAcceptance
        (ay_ctqg_conj modelEvidence originalModel)
        (ay_ctqg_conj_right checkerContract
          (ay_ctqg_conj completedCheckerAcceptance
            (ay_ctqg_conj modelEvidence originalModel)) publication))

theorem ay_ctqg_unsat_publication_intro
    (checkerContract completedCheckerAcceptance proofEvidence
      originalEmptyClause : Prop) :
    checkerContract -> completedCheckerAcceptance -> proofEvidence ->
    originalEmptyClause ->
    ay_ctqg_unsat_publication checkerContract completedCheckerAcceptance
      proofEvidence originalEmptyClause :=
  fun contractProof acceptanceProof proofProof emptyProof =>
    ay_ctqg_conj_intro checkerContract
      (ay_ctqg_conj completedCheckerAcceptance
        (ay_ctqg_conj proofEvidence originalEmptyClause)) contractProof
      (ay_ctqg_conj_intro completedCheckerAcceptance
        (ay_ctqg_conj proofEvidence originalEmptyClause) acceptanceProof
        (ay_ctqg_conj_intro proofEvidence originalEmptyClause proofProof
          emptyProof))

theorem ay_ctqg_unsat_publication_completed_acceptance
    (checkerContract completedCheckerAcceptance proofEvidence
      originalEmptyClause : Prop) :
    ay_ctqg_unsat_publication checkerContract completedCheckerAcceptance
      proofEvidence originalEmptyClause ->
    completedCheckerAcceptance :=
  fun publication =>
    ay_ctqg_conj_left completedCheckerAcceptance
      (ay_ctqg_conj proofEvidence originalEmptyClause)
      (ay_ctqg_conj_right checkerContract
        (ay_ctqg_conj completedCheckerAcceptance
          (ay_ctqg_conj proofEvidence originalEmptyClause)) publication)

theorem ay_ctqg_unsat_publication_original_empty_clause
    (checkerContract completedCheckerAcceptance proofEvidence
      originalEmptyClause : Prop) :
    ay_ctqg_unsat_publication checkerContract completedCheckerAcceptance
      proofEvidence originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_ctqg_conj_right proofEvidence originalEmptyClause
      (ay_ctqg_conj_right completedCheckerAcceptance
        (ay_ctqg_conj proofEvidence originalEmptyClause)
        (ay_ctqg_conj_right checkerContract
          (ay_ctqg_conj completedCheckerAcceptance
            (ay_ctqg_conj proofEvidence originalEmptyClause)) publication))

theorem ay_ctqg_completed_checker_sat_passes_publication
    (checkerContract completedCheckerAcceptance modelEvidence originalModel :
      Prop) :
    ay_ctqg_sat_publication checkerContract completedCheckerAcceptance
      modelEvidence originalModel ->
    ay_ctqg_conj completedCheckerAcceptance originalModel :=
  fun publication =>
    ay_ctqg_conj_intro completedCheckerAcceptance originalModel
      (ay_ctqg_sat_publication_completed_acceptance checkerContract
        completedCheckerAcceptance modelEvidence originalModel publication)
      (ay_ctqg_sat_publication_original_model checkerContract
        completedCheckerAcceptance modelEvidence originalModel publication)

theorem ay_ctqg_completed_checker_unsat_passes_publication
    (checkerContract completedCheckerAcceptance proofEvidence
      originalEmptyClause : Prop) :
    ay_ctqg_unsat_publication checkerContract completedCheckerAcceptance
      proofEvidence originalEmptyClause ->
    ay_ctqg_conj completedCheckerAcceptance originalEmptyClause :=
  fun publication =>
    ay_ctqg_conj_intro completedCheckerAcceptance originalEmptyClause
      (ay_ctqg_unsat_publication_completed_acceptance checkerContract
        completedCheckerAcceptance proofEvidence originalEmptyClause
        publication)
      (ay_ctqg_unsat_publication_original_empty_clause checkerContract
        completedCheckerAcceptance proofEvidence originalEmptyClause
        publication)

theorem ay_ctqg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_ctqg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_ctqg_conj_intro reason (ay_ctqg_conj fallbackPath auditTrail)
      reasonProof
      (ay_ctqg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_ctqg_quarantine_intro
    (reason quarantineState auditTranscript : Prop) :
    reason -> quarantineState -> auditTranscript ->
    ay_ctqg_quarantine reason quarantineState auditTranscript :=
  fun reasonProof quarantineProof auditProof =>
    ay_ctqg_conj_intro reason
      (ay_ctqg_conj quarantineState auditTranscript) reasonProof
      (ay_ctqg_conj_intro quarantineState auditTranscript quarantineProof
        auditProof)

theorem ay_ctqg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ctqg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_ctqg_conj_intro reason
      (ay_ctqg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_ctqg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_ctqg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_ctqg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_ctqg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_ctqg_conj_right reason
        (ay_ctqg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_ctqg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_ctqg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_ctqg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_ctqg_conj_right reason
        (ay_ctqg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_ctqg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_ctqg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_ctqg_conj_intro reason
      (ay_ctqg_conj fallbackPath recomputeObligation) reasonProof
      (ay_ctqg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_ctqg_timeout_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation
      quarantineState auditTranscript : Prop) :
    reason -> fallbackPath -> recomputeObligation -> quarantineState ->
    auditTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ctqg_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation quarantineState auditTranscript :=
  fun reasonProof fallbackProof recomputeProof quarantineProof auditProof
      noSat noUnsat =>
    ay_ctqg_conj_intro
      (ay_ctqg_blocked_publication satFact unsatFact reason)
      (ay_ctqg_conj
        (ay_ctqg_recompute reason fallbackPath recomputeObligation)
        (ay_ctqg_quarantine reason quarantineState auditTranscript))
      (ay_ctqg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_ctqg_conj_intro
        (ay_ctqg_recompute reason fallbackPath recomputeObligation)
        (ay_ctqg_quarantine reason quarantineState auditTranscript)
        (ay_ctqg_recompute_intro reason fallbackPath recomputeObligation
          reasonProof fallbackProof recomputeProof)
        (ay_ctqg_quarantine_intro reason quarantineState auditTranscript
          reasonProof quarantineProof auditProof))

theorem ay_ctqg_timeout_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation
      quarantineState auditTranscript : Prop) :
    ay_ctqg_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation quarantineState auditTranscript ->
    satFact -> False :=
  fun failure =>
    ay_ctqg_blocked_publication_no_sat satFact unsatFact reason
      (ay_ctqg_conj_left
        (ay_ctqg_blocked_publication satFact unsatFact reason)
        (ay_ctqg_conj
          (ay_ctqg_recompute reason fallbackPath recomputeObligation)
          (ay_ctqg_quarantine reason quarantineState auditTranscript))
        failure)

theorem ay_ctqg_timeout_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation
      quarantineState auditTranscript : Prop) :
    ay_ctqg_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation quarantineState auditTranscript ->
    unsatFact -> False :=
  fun failure =>
    ay_ctqg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_ctqg_conj_left
        (ay_ctqg_blocked_publication satFact unsatFact reason)
        (ay_ctqg_conj
          (ay_ctqg_recompute reason fallbackPath recomputeObligation)
          (ay_ctqg_quarantine reason quarantineState auditTranscript))
        failure)

theorem ay_ctqg_timeout_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation
      quarantineState auditTranscript : Prop) :
    ay_ctqg_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation quarantineState auditTranscript ->
    ay_ctqg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_ctqg_conj_left
      (ay_ctqg_recompute reason fallbackPath recomputeObligation)
      (ay_ctqg_quarantine reason quarantineState auditTranscript)
      (ay_ctqg_conj_right
        (ay_ctqg_blocked_publication satFact unsatFact reason)
        (ay_ctqg_conj
          (ay_ctqg_recompute reason fallbackPath recomputeObligation)
          (ay_ctqg_quarantine reason quarantineState auditTranscript))
        failure)

theorem ay_ctqg_timeout_failure_quarantine
    (satFact unsatFact reason fallbackPath recomputeObligation
      quarantineState auditTranscript : Prop) :
    ay_ctqg_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation quarantineState auditTranscript ->
    ay_ctqg_quarantine reason quarantineState auditTranscript :=
  fun failure =>
    ay_ctqg_conj_right
      (ay_ctqg_recompute reason fallbackPath recomputeObligation)
      (ay_ctqg_quarantine reason quarantineState auditTranscript)
      (ay_ctqg_conj_right
        (ay_ctqg_blocked_publication satFact unsatFact reason)
        (ay_ctqg_conj
          (ay_ctqg_recompute reason fallbackPath recomputeObligation)
          (ay_ctqg_quarantine reason quarantineState auditTranscript))
        failure)

theorem ay_ctqg_timeout_forces_no_claim
    (satFact unsatFact timeoutReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    timeoutReason -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ctqg_no_claim timeoutReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ctqg_no_claim_intro timeoutReason fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_ctqg_partial_output_forces_no_claim
    (satFact unsatFact partialOutput fallbackPath auditTrail
      recomputeObligation : Prop) :
    partialOutput -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ctqg_no_claim partialOutput fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ctqg_no_claim_intro partialOutput fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_ctqg_stale_budget_forces_no_claim
    (satFact unsatFact staleBudget fallbackPath auditTrail
      recomputeObligation : Prop) :
    staleBudget -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ctqg_no_claim staleBudget fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ctqg_no_claim_intro staleBudget fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_ctqg_benchmark_mismatch_forces_no_claim
    (satFact unsatFact benchmarkMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    benchmarkMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ctqg_no_claim benchmarkMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ctqg_no_claim_intro benchmarkMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ctqg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ctqg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ctqg_no_claim_intro buildMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_ctqg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ctqg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ctqg_no_claim_intro archiveMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_ctqg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivated fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ctqg_no_claim fallbackActivated fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ctqg_no_claim_intro fallbackActivated fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ctqg_failed_timeout_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation
      quarantineState auditTranscript : Prop) :
    ay_ctqg_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation quarantineState auditTranscript ->
    satFact -> False :=
  ay_ctqg_timeout_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation quarantineState auditTranscript

theorem ay_ctqg_failed_timeout_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation
      quarantineState auditTranscript : Prop) :
    ay_ctqg_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation quarantineState auditTranscript ->
    unsatFact -> False :=
  ay_ctqg_timeout_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation quarantineState auditTranscript

theorem ay_ctqg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_ctqg_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_ctqg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_ctqg_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
