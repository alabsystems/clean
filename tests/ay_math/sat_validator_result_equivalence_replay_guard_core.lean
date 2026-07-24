-- SAT-COMP validator result-equivalence replay guard core.
--
-- Public claims are allowed only when internal result, normalized benchmark
-- fingerprint, emitted artifacts, independent checker replay, archive, build
-- evidence, and no-claim fallback path agree.

def ay_verg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_verg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_verg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_verg_disj satFact (ay_verg_disj unsatFact noClaimFact)

def ay_verg_equivalence_contract
    (internalSolverResult normalizedDimacsFingerprint emittedResultArtifact
      certificateModelArtifact independentCheckerTranscript
      normalizedCheckerResult archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) : Prop :=
  forall result : Prop,
    (internalSolverResult -> normalizedDimacsFingerprint ->
      emittedResultArtifact -> certificateModelArtifact ->
      independentCheckerTranscript -> normalizedCheckerResult ->
      archiveManifest -> solverBuildEvidence -> noClaimFallbackPath ->
      result) ->
    result

def ay_verg_sat_publication
    (equivalenceContract modelEvidence originalModel : Prop) : Prop :=
  ay_verg_conj equivalenceContract
    (ay_verg_conj modelEvidence originalModel)

def ay_verg_unsat_publication
    (equivalenceContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_verg_conj equivalenceContract
    (ay_verg_conj proofEvidence originalEmptyClause)

def ay_verg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_verg_conj reason (ay_verg_conj fallbackPath auditTrail)

def ay_verg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_verg_conj reason
    (ay_verg_conj (satFact -> False) (unsatFact -> False))

def ay_verg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_verg_conj reason
    (ay_verg_conj fallbackPath recomputeObligation)

def ay_verg_disagreement_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_verg_conj
    (ay_verg_blocked_publication satFact unsatFact reason)
    (ay_verg_recompute reason fallbackPath recomputeObligation)

theorem ay_verg_conj_intro (left right : Prop) :
    left -> right -> ay_verg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_verg_conj_left (left right : Prop) :
    ay_verg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_verg_conj_right (left right : Prop) :
    ay_verg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_verg_disj_left (left right : Prop) :
    left -> ay_verg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_verg_disj_right (left right : Prop) :
    right -> ay_verg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_verg_equivalence_contract_intro
    (internalSolverResult normalizedDimacsFingerprint emittedResultArtifact
      certificateModelArtifact independentCheckerTranscript
      normalizedCheckerResult archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    internalSolverResult -> normalizedDimacsFingerprint ->
    emittedResultArtifact -> certificateModelArtifact ->
    independentCheckerTranscript -> normalizedCheckerResult ->
    archiveManifest -> solverBuildEvidence -> noClaimFallbackPath ->
    ay_verg_equivalence_contract internalSolverResult
      normalizedDimacsFingerprint emittedResultArtifact certificateModelArtifact
      independentCheckerTranscript normalizedCheckerResult archiveManifest
      solverBuildEvidence noClaimFallbackPath :=
  fun internalProof fingerprintProof emittedProof certificateProof checkerProof
      normalizedProof archiveProof buildProof fallbackProof result build =>
    build internalProof fingerprintProof emittedProof certificateProof
      checkerProof normalizedProof archiveProof buildProof fallbackProof

theorem ay_verg_equivalence_contract_internal
    (internalSolverResult normalizedDimacsFingerprint emittedResultArtifact
      certificateModelArtifact independentCheckerTranscript
      normalizedCheckerResult archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_verg_equivalence_contract internalSolverResult
      normalizedDimacsFingerprint emittedResultArtifact certificateModelArtifact
      independentCheckerTranscript normalizedCheckerResult archiveManifest
      solverBuildEvidence noClaimFallbackPath ->
    internalSolverResult :=
  fun contract =>
    contract internalSolverResult
      (fun internalProof _fingerprintProof _emittedProof _certificateProof
          _checkerProof _normalizedProof _archiveProof _buildProof
          _fallbackProof => internalProof)

theorem ay_verg_equivalence_contract_fingerprint
    (internalSolverResult normalizedDimacsFingerprint emittedResultArtifact
      certificateModelArtifact independentCheckerTranscript
      normalizedCheckerResult archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_verg_equivalence_contract internalSolverResult
      normalizedDimacsFingerprint emittedResultArtifact certificateModelArtifact
      independentCheckerTranscript normalizedCheckerResult archiveManifest
      solverBuildEvidence noClaimFallbackPath ->
    normalizedDimacsFingerprint :=
  fun contract =>
    contract normalizedDimacsFingerprint
      (fun _internalProof fingerprintProof _emittedProof _certificateProof
          _checkerProof _normalizedProof _archiveProof _buildProof
          _fallbackProof => fingerprintProof)

theorem ay_verg_equivalence_contract_emitted
    (internalSolverResult normalizedDimacsFingerprint emittedResultArtifact
      certificateModelArtifact independentCheckerTranscript
      normalizedCheckerResult archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_verg_equivalence_contract internalSolverResult
      normalizedDimacsFingerprint emittedResultArtifact certificateModelArtifact
      independentCheckerTranscript normalizedCheckerResult archiveManifest
      solverBuildEvidence noClaimFallbackPath ->
    emittedResultArtifact :=
  fun contract =>
    contract emittedResultArtifact
      (fun _internalProof _fingerprintProof emittedProof _certificateProof
          _checkerProof _normalizedProof _archiveProof _buildProof
          _fallbackProof => emittedProof)

theorem ay_verg_equivalence_contract_certificate
    (internalSolverResult normalizedDimacsFingerprint emittedResultArtifact
      certificateModelArtifact independentCheckerTranscript
      normalizedCheckerResult archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_verg_equivalence_contract internalSolverResult
      normalizedDimacsFingerprint emittedResultArtifact certificateModelArtifact
      independentCheckerTranscript normalizedCheckerResult archiveManifest
      solverBuildEvidence noClaimFallbackPath ->
    certificateModelArtifact :=
  fun contract =>
    contract certificateModelArtifact
      (fun _internalProof _fingerprintProof _emittedProof certificateProof
          _checkerProof _normalizedProof _archiveProof _buildProof
          _fallbackProof => certificateProof)

theorem ay_verg_equivalence_contract_checker
    (internalSolverResult normalizedDimacsFingerprint emittedResultArtifact
      certificateModelArtifact independentCheckerTranscript
      normalizedCheckerResult archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_verg_equivalence_contract internalSolverResult
      normalizedDimacsFingerprint emittedResultArtifact certificateModelArtifact
      independentCheckerTranscript normalizedCheckerResult archiveManifest
      solverBuildEvidence noClaimFallbackPath ->
    independentCheckerTranscript :=
  fun contract =>
    contract independentCheckerTranscript
      (fun _internalProof _fingerprintProof _emittedProof _certificateProof
          checkerProof _normalizedProof _archiveProof _buildProof
          _fallbackProof => checkerProof)

theorem ay_verg_equivalence_contract_normalized_checker
    (internalSolverResult normalizedDimacsFingerprint emittedResultArtifact
      certificateModelArtifact independentCheckerTranscript
      normalizedCheckerResult archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_verg_equivalence_contract internalSolverResult
      normalizedDimacsFingerprint emittedResultArtifact certificateModelArtifact
      independentCheckerTranscript normalizedCheckerResult archiveManifest
      solverBuildEvidence noClaimFallbackPath ->
    normalizedCheckerResult :=
  fun contract =>
    contract normalizedCheckerResult
      (fun _internalProof _fingerprintProof _emittedProof _certificateProof
          _checkerProof normalizedProof _archiveProof _buildProof
          _fallbackProof => normalizedProof)

theorem ay_verg_equivalence_contract_archive
    (internalSolverResult normalizedDimacsFingerprint emittedResultArtifact
      certificateModelArtifact independentCheckerTranscript
      normalizedCheckerResult archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_verg_equivalence_contract internalSolverResult
      normalizedDimacsFingerprint emittedResultArtifact certificateModelArtifact
      independentCheckerTranscript normalizedCheckerResult archiveManifest
      solverBuildEvidence noClaimFallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _internalProof _fingerprintProof _emittedProof _certificateProof
          _checkerProof _normalizedProof archiveProof _buildProof
          _fallbackProof => archiveProof)

theorem ay_verg_equivalence_contract_build
    (internalSolverResult normalizedDimacsFingerprint emittedResultArtifact
      certificateModelArtifact independentCheckerTranscript
      normalizedCheckerResult archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_verg_equivalence_contract internalSolverResult
      normalizedDimacsFingerprint emittedResultArtifact certificateModelArtifact
      independentCheckerTranscript normalizedCheckerResult archiveManifest
      solverBuildEvidence noClaimFallbackPath ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _internalProof _fingerprintProof _emittedProof _certificateProof
          _checkerProof _normalizedProof _archiveProof buildProof
          _fallbackProof => buildProof)

theorem ay_verg_equivalence_contract_fallback
    (internalSolverResult normalizedDimacsFingerprint emittedResultArtifact
      certificateModelArtifact independentCheckerTranscript
      normalizedCheckerResult archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_verg_equivalence_contract internalSolverResult
      normalizedDimacsFingerprint emittedResultArtifact certificateModelArtifact
      independentCheckerTranscript normalizedCheckerResult archiveManifest
      solverBuildEvidence noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _internalProof _fingerprintProof _emittedProof _certificateProof
          _checkerProof _normalizedProof _archiveProof _buildProof
          fallbackProof => fallbackProof)

theorem ay_verg_sat_publication_intro
    (equivalenceContract modelEvidence originalModel : Prop) :
    equivalenceContract -> modelEvidence -> originalModel ->
    ay_verg_sat_publication equivalenceContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_verg_conj_intro equivalenceContract
      (ay_verg_conj modelEvidence originalModel) contractProof
      (ay_verg_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_verg_sat_publication_original_model
    (equivalenceContract modelEvidence originalModel : Prop) :
    ay_verg_sat_publication equivalenceContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_verg_conj_right modelEvidence originalModel
      (ay_verg_conj_right equivalenceContract
        (ay_verg_conj modelEvidence originalModel) publication)

theorem ay_verg_unsat_publication_intro
    (equivalenceContract proofEvidence originalEmptyClause : Prop) :
    equivalenceContract -> proofEvidence -> originalEmptyClause ->
    ay_verg_unsat_publication equivalenceContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_verg_conj_intro equivalenceContract
      (ay_verg_conj proofEvidence originalEmptyClause) contractProof
      (ay_verg_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_verg_unsat_publication_original_empty_clause
    (equivalenceContract proofEvidence originalEmptyClause : Prop) :
    ay_verg_unsat_publication equivalenceContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_verg_conj_right proofEvidence originalEmptyClause
      (ay_verg_conj_right equivalenceContract
        (ay_verg_conj proofEvidence originalEmptyClause) publication)

theorem ay_verg_accepted_equivalence_sat_sound
    (equivalenceContract modelEvidence originalModel : Prop) :
    ay_verg_sat_publication equivalenceContract modelEvidence originalModel ->
    originalModel :=
  ay_verg_sat_publication_original_model equivalenceContract modelEvidence
    originalModel

theorem ay_verg_accepted_equivalence_unsat_sound
    (equivalenceContract proofEvidence originalEmptyClause : Prop) :
    ay_verg_unsat_publication equivalenceContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_verg_unsat_publication_original_empty_clause equivalenceContract
    proofEvidence originalEmptyClause

theorem ay_verg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_verg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_verg_conj_intro reason (ay_verg_conj fallbackPath auditTrail)
      reasonProof
      (ay_verg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_verg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_verg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_verg_conj_intro reason
      (ay_verg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_verg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_verg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_verg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_verg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_verg_conj_right reason
        (ay_verg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_verg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_verg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_verg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_verg_conj_right reason
        (ay_verg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_verg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_verg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_verg_conj_intro reason
      (ay_verg_conj fallbackPath recomputeObligation) reasonProof
      (ay_verg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_verg_disagreement_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_verg_disagreement_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_verg_conj_intro
      (ay_verg_blocked_publication satFact unsatFact reason)
      (ay_verg_recompute reason fallbackPath recomputeObligation)
      (ay_verg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_verg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_verg_disagreement_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_verg_disagreement_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_verg_blocked_publication_no_sat satFact unsatFact reason
      (ay_verg_conj_left
        (ay_verg_blocked_publication satFact unsatFact reason)
        (ay_verg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_verg_disagreement_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_verg_disagreement_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_verg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_verg_conj_left
        (ay_verg_blocked_publication satFact unsatFact reason)
        (ay_verg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_verg_disagreement_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_verg_disagreement_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_verg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_verg_conj_right
      (ay_verg_blocked_publication satFact unsatFact reason)
      (ay_verg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_verg_disagreement_forces_no_claim
    (satFact unsatFact disagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    disagreement -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_verg_no_claim disagreement fallbackPath auditTrail :=
  fun disagreementProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_verg_no_claim_intro disagreement fallbackPath auditTrail
      disagreementProof fallbackProof auditProof

theorem ay_verg_internal_result_disagreement_blocks_publication
    (satFact unsatFact internalDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    internalDisagreement -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_verg_no_claim internalDisagreement fallbackPath auditTrail :=
  ay_verg_disagreement_forces_no_claim satFact unsatFact internalDisagreement
    fallbackPath auditTrail recomputeObligation

theorem ay_verg_fingerprint_disagreement_blocks_publication
    (satFact unsatFact fingerprintDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintDisagreement -> fallbackPath -> auditTrail ->
    recomputeObligation -> (satFact -> False) -> (unsatFact -> False) ->
    ay_verg_no_claim fingerprintDisagreement fallbackPath auditTrail :=
  ay_verg_disagreement_forces_no_claim satFact unsatFact
    fingerprintDisagreement fallbackPath auditTrail recomputeObligation

theorem ay_verg_emitted_artifact_disagreement_blocks_publication
    (satFact unsatFact emittedDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    emittedDisagreement -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_verg_no_claim emittedDisagreement fallbackPath auditTrail :=
  ay_verg_disagreement_forces_no_claim satFact unsatFact emittedDisagreement
    fallbackPath auditTrail recomputeObligation

theorem ay_verg_certificate_disagreement_blocks_publication
    (satFact unsatFact certificateDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    certificateDisagreement -> fallbackPath -> auditTrail ->
    recomputeObligation -> (satFact -> False) -> (unsatFact -> False) ->
    ay_verg_no_claim certificateDisagreement fallbackPath auditTrail :=
  ay_verg_disagreement_forces_no_claim satFact unsatFact
    certificateDisagreement fallbackPath auditTrail recomputeObligation

theorem ay_verg_checker_disagreement_blocks_publication
    (satFact unsatFact checkerDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerDisagreement -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_verg_no_claim checkerDisagreement fallbackPath auditTrail :=
  ay_verg_disagreement_forces_no_claim satFact unsatFact checkerDisagreement
    fallbackPath auditTrail recomputeObligation

theorem ay_verg_normalized_result_disagreement_blocks_publication
    (satFact unsatFact normalizedDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    normalizedDisagreement -> fallbackPath -> auditTrail ->
    recomputeObligation -> (satFact -> False) -> (unsatFact -> False) ->
    ay_verg_no_claim normalizedDisagreement fallbackPath auditTrail :=
  ay_verg_disagreement_forces_no_claim satFact unsatFact
    normalizedDisagreement fallbackPath auditTrail recomputeObligation

theorem ay_verg_archive_disagreement_blocks_publication
    (satFact unsatFact archiveDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveDisagreement -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_verg_no_claim archiveDisagreement fallbackPath auditTrail :=
  ay_verg_disagreement_forces_no_claim satFact unsatFact archiveDisagreement
    fallbackPath auditTrail recomputeObligation

theorem ay_verg_build_disagreement_blocks_publication
    (satFact unsatFact buildDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildDisagreement -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_verg_no_claim buildDisagreement fallbackPath auditTrail :=
  ay_verg_disagreement_forces_no_claim satFact unsatFact buildDisagreement
    fallbackPath auditTrail recomputeObligation

theorem ay_verg_failed_disagreement_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_verg_disagreement_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_verg_disagreement_failure_blocks_sat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_verg_failed_disagreement_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_verg_disagreement_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_verg_disagreement_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_verg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_verg_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_verg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_verg_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
