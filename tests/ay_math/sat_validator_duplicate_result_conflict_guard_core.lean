-- SAT-COMP validator duplicate-result conflict guard core.
--
-- Public SAT/UNSAT claims are allowed only when duplicate result artifacts,
-- benchmark fingerprints, certificates/models, checker transcripts, archive
-- manifests, solver build evidence, and no-claim fallback agree.

def ay_drcg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_drcg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_drcg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_drcg_disj satFact (ay_drcg_disj unsatFact noClaimFact)

def ay_drcg_duplicate_contract
    (duplicateResultArtifacts benchmarkFingerprints certificateModelArtifacts
      checkerTranscripts archiveManifests solverBuildEvidence
      noClaimFallbackPath : Prop) : Prop :=
  forall result : Prop,
    (duplicateResultArtifacts -> benchmarkFingerprints ->
      certificateModelArtifacts -> checkerTranscripts -> archiveManifests ->
      solverBuildEvidence -> noClaimFallbackPath -> result) ->
    result

def ay_drcg_sat_publication
    (duplicateContract modelEvidence originalModel : Prop) : Prop :=
  ay_drcg_conj duplicateContract
    (ay_drcg_conj modelEvidence originalModel)

def ay_drcg_unsat_publication
    (duplicateContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_drcg_conj duplicateContract
    (ay_drcg_conj proofEvidence originalEmptyClause)

def ay_drcg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_drcg_conj reason (ay_drcg_conj fallbackPath auditTrail)

def ay_drcg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_drcg_conj reason
    (ay_drcg_conj (satFact -> False) (unsatFact -> False))

def ay_drcg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_drcg_conj reason
    (ay_drcg_conj fallbackPath recomputeObligation)

def ay_drcg_conflict_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_drcg_conj
    (ay_drcg_blocked_publication satFact unsatFact reason)
    (ay_drcg_recompute reason fallbackPath recomputeObligation)

theorem ay_drcg_conj_intro (left right : Prop) :
    left -> right -> ay_drcg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_drcg_conj_left (left right : Prop) :
    ay_drcg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_drcg_conj_right (left right : Prop) :
    ay_drcg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_drcg_disj_left (left right : Prop) :
    left -> ay_drcg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_drcg_disj_right (left right : Prop) :
    right -> ay_drcg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_drcg_duplicate_contract_intro
    (duplicateResultArtifacts benchmarkFingerprints certificateModelArtifacts
      checkerTranscripts archiveManifests solverBuildEvidence
      noClaimFallbackPath : Prop) :
    duplicateResultArtifacts -> benchmarkFingerprints ->
    certificateModelArtifacts -> checkerTranscripts -> archiveManifests ->
    solverBuildEvidence -> noClaimFallbackPath ->
    ay_drcg_duplicate_contract duplicateResultArtifacts
      benchmarkFingerprints certificateModelArtifacts checkerTranscripts
      archiveManifests solverBuildEvidence noClaimFallbackPath :=
  fun duplicateProof fingerprintProof certificateProof checkerProof
      archiveProof buildProof fallbackProof result build =>
    build duplicateProof fingerprintProof certificateProof checkerProof
      archiveProof buildProof fallbackProof

theorem ay_drcg_duplicate_contract_artifacts
    (duplicateResultArtifacts benchmarkFingerprints certificateModelArtifacts
      checkerTranscripts archiveManifests solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_drcg_duplicate_contract duplicateResultArtifacts
      benchmarkFingerprints certificateModelArtifacts checkerTranscripts
      archiveManifests solverBuildEvidence noClaimFallbackPath ->
    duplicateResultArtifacts :=
  fun contract =>
    contract duplicateResultArtifacts
      (fun duplicateProof _fingerprintProof _certificateProof _checkerProof
          _archiveProof _buildProof _fallbackProof => duplicateProof)

theorem ay_drcg_duplicate_contract_fingerprints
    (duplicateResultArtifacts benchmarkFingerprints certificateModelArtifacts
      checkerTranscripts archiveManifests solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_drcg_duplicate_contract duplicateResultArtifacts
      benchmarkFingerprints certificateModelArtifacts checkerTranscripts
      archiveManifests solverBuildEvidence noClaimFallbackPath ->
    benchmarkFingerprints :=
  fun contract =>
    contract benchmarkFingerprints
      (fun _duplicateProof fingerprintProof _certificateProof _checkerProof
          _archiveProof _buildProof _fallbackProof => fingerprintProof)

theorem ay_drcg_duplicate_contract_certificates
    (duplicateResultArtifacts benchmarkFingerprints certificateModelArtifacts
      checkerTranscripts archiveManifests solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_drcg_duplicate_contract duplicateResultArtifacts
      benchmarkFingerprints certificateModelArtifacts checkerTranscripts
      archiveManifests solverBuildEvidence noClaimFallbackPath ->
    certificateModelArtifacts :=
  fun contract =>
    contract certificateModelArtifacts
      (fun _duplicateProof _fingerprintProof certificateProof _checkerProof
          _archiveProof _buildProof _fallbackProof => certificateProof)

theorem ay_drcg_duplicate_contract_checkers
    (duplicateResultArtifacts benchmarkFingerprints certificateModelArtifacts
      checkerTranscripts archiveManifests solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_drcg_duplicate_contract duplicateResultArtifacts
      benchmarkFingerprints certificateModelArtifacts checkerTranscripts
      archiveManifests solverBuildEvidence noClaimFallbackPath ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _duplicateProof _fingerprintProof _certificateProof checkerProof
          _archiveProof _buildProof _fallbackProof => checkerProof)

theorem ay_drcg_duplicate_contract_archives
    (duplicateResultArtifacts benchmarkFingerprints certificateModelArtifacts
      checkerTranscripts archiveManifests solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_drcg_duplicate_contract duplicateResultArtifacts
      benchmarkFingerprints certificateModelArtifacts checkerTranscripts
      archiveManifests solverBuildEvidence noClaimFallbackPath ->
    archiveManifests :=
  fun contract =>
    contract archiveManifests
      (fun _duplicateProof _fingerprintProof _certificateProof _checkerProof
          archiveProof _buildProof _fallbackProof => archiveProof)

theorem ay_drcg_duplicate_contract_build
    (duplicateResultArtifacts benchmarkFingerprints certificateModelArtifacts
      checkerTranscripts archiveManifests solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_drcg_duplicate_contract duplicateResultArtifacts
      benchmarkFingerprints certificateModelArtifacts checkerTranscripts
      archiveManifests solverBuildEvidence noClaimFallbackPath ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _duplicateProof _fingerprintProof _certificateProof _checkerProof
          _archiveProof buildProof _fallbackProof => buildProof)

theorem ay_drcg_duplicate_contract_fallback
    (duplicateResultArtifacts benchmarkFingerprints certificateModelArtifacts
      checkerTranscripts archiveManifests solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_drcg_duplicate_contract duplicateResultArtifacts
      benchmarkFingerprints certificateModelArtifacts checkerTranscripts
      archiveManifests solverBuildEvidence noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _duplicateProof _fingerprintProof _certificateProof _checkerProof
          _archiveProof _buildProof fallbackProof => fallbackProof)

theorem ay_drcg_sat_publication_intro
    (duplicateContract modelEvidence originalModel : Prop) :
    duplicateContract -> modelEvidence -> originalModel ->
    ay_drcg_sat_publication duplicateContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_drcg_conj_intro duplicateContract
      (ay_drcg_conj modelEvidence originalModel) contractProof
      (ay_drcg_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_drcg_sat_publication_original_model
    (duplicateContract modelEvidence originalModel : Prop) :
    ay_drcg_sat_publication duplicateContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_drcg_conj_right modelEvidence originalModel
      (ay_drcg_conj_right duplicateContract
        (ay_drcg_conj modelEvidence originalModel) publication)

theorem ay_drcg_unsat_publication_intro
    (duplicateContract proofEvidence originalEmptyClause : Prop) :
    duplicateContract -> proofEvidence -> originalEmptyClause ->
    ay_drcg_unsat_publication duplicateContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_drcg_conj_intro duplicateContract
      (ay_drcg_conj proofEvidence originalEmptyClause) contractProof
      (ay_drcg_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_drcg_unsat_publication_original_empty_clause
    (duplicateContract proofEvidence originalEmptyClause : Prop) :
    ay_drcg_unsat_publication duplicateContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_drcg_conj_right proofEvidence originalEmptyClause
      (ay_drcg_conj_right duplicateContract
        (ay_drcg_conj proofEvidence originalEmptyClause) publication)

theorem ay_drcg_accepted_duplicate_sat_sound
    (duplicateContract modelEvidence originalModel : Prop) :
    ay_drcg_sat_publication duplicateContract modelEvidence originalModel ->
    originalModel :=
  ay_drcg_sat_publication_original_model duplicateContract modelEvidence
    originalModel

theorem ay_drcg_accepted_duplicate_unsat_sound
    (duplicateContract proofEvidence originalEmptyClause : Prop) :
    ay_drcg_unsat_publication duplicateContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_drcg_unsat_publication_original_empty_clause duplicateContract
    proofEvidence originalEmptyClause

theorem ay_drcg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_drcg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_drcg_conj_intro reason (ay_drcg_conj fallbackPath auditTrail)
      reasonProof
      (ay_drcg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_drcg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_drcg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_drcg_conj_intro reason
      (ay_drcg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_drcg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_drcg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_drcg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_drcg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_drcg_conj_right reason
        (ay_drcg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_drcg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_drcg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_drcg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_drcg_conj_right reason
        (ay_drcg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_drcg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_drcg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_drcg_conj_intro reason
      (ay_drcg_conj fallbackPath recomputeObligation) reasonProof
      (ay_drcg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_drcg_conflict_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_drcg_conflict_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_drcg_conj_intro
      (ay_drcg_blocked_publication satFact unsatFact reason)
      (ay_drcg_recompute reason fallbackPath recomputeObligation)
      (ay_drcg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_drcg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_drcg_conflict_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_drcg_conflict_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_drcg_blocked_publication_no_sat satFact unsatFact reason
      (ay_drcg_conj_left
        (ay_drcg_blocked_publication satFact unsatFact reason)
        (ay_drcg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_drcg_conflict_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_drcg_conflict_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_drcg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_drcg_conj_left
        (ay_drcg_blocked_publication satFact unsatFact reason)
        (ay_drcg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_drcg_conflict_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_drcg_conflict_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_drcg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_drcg_conj_right
      (ay_drcg_blocked_publication satFact unsatFact reason)
      (ay_drcg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_drcg_conflicting_duplicate_results_force_no_claim
    (satFact unsatFact duplicateConflict fallbackPath auditTrail
      recomputeObligation : Prop) :
    duplicateConflict -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_drcg_no_claim duplicateConflict fallbackPath auditTrail :=
  fun conflictProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_drcg_no_claim_intro duplicateConflict fallbackPath auditTrail
      conflictProof fallbackProof auditProof

theorem ay_drcg_mismatched_certificates_force_no_claim
    (satFact unsatFact certificateMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    certificateMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_drcg_no_claim certificateMismatch fallbackPath auditTrail :=
  fun mismatchProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_drcg_no_claim_intro certificateMismatch fallbackPath auditTrail
      mismatchProof fallbackProof auditProof

theorem ay_drcg_mismatched_fingerprints_force_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_drcg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun mismatchProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_drcg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      mismatchProof fallbackProof auditProof

theorem ay_drcg_failed_conflict_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_drcg_conflict_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_drcg_conflict_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_drcg_failed_conflict_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_drcg_conflict_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_drcg_conflict_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_drcg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_drcg_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_drcg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_drcg_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
