-- SAT-COMP validator timeout boundary no-claim guard core.
--
-- Timeout or budget-boundary outcomes publish no semantic SAT/UNSAT claim
-- unless all result artifacts were accepted before the boundary.

def ay_vtbg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vtbg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vtbg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vtbg_disj satFact (ay_vtbg_disj unsatFact noClaimFact)

def ay_vtbg_pre_timeout_contract
    (beforeBoundary resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest :
      Prop) : Prop :=
  forall result : Prop,
    (beforeBoundary -> resultArtifact -> certificateModel ->
      checkerTranscript -> benchmarkFingerprint -> buildConfig ->
      archiveManifest -> submissionManifest -> result) ->
    result

def ay_vtbg_sat_publication
    (preTimeoutContract modelEvidence originalModel : Prop) : Prop :=
  ay_vtbg_conj preTimeoutContract
    (ay_vtbg_conj modelEvidence originalModel)

def ay_vtbg_unsat_publication
    (preTimeoutContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vtbg_conj preTimeoutContract
    (ay_vtbg_conj proofEvidence originalEmptyClause)

def ay_vtbg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vtbg_conj reason (ay_vtbg_conj fallbackPath auditTrail)

def ay_vtbg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vtbg_conj reason
    (ay_vtbg_conj (satFact -> False) (unsatFact -> False))

def ay_vtbg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vtbg_conj reason
    (ay_vtbg_conj fallbackPath recomputeObligation)

def ay_vtbg_boundary_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vtbg_conj
    (ay_vtbg_blocked_publication satFact unsatFact reason)
    (ay_vtbg_recompute reason fallbackPath recomputeObligation)

theorem ay_vtbg_conj_intro (left right : Prop) :
    left -> right -> ay_vtbg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vtbg_conj_left (left right : Prop) :
    ay_vtbg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vtbg_conj_right (left right : Prop) :
    ay_vtbg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vtbg_disj_left (left right : Prop) :
    left -> ay_vtbg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vtbg_disj_right (left right : Prop) :
    right -> ay_vtbg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vtbg_pre_timeout_contract_intro
    (beforeBoundary resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest :
      Prop) :
    beforeBoundary -> resultArtifact -> certificateModel ->
    checkerTranscript -> benchmarkFingerprint -> buildConfig ->
    archiveManifest -> submissionManifest ->
    ay_vtbg_pre_timeout_contract beforeBoundary resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint buildConfig
      archiveManifest submissionManifest :=
  fun boundaryProof resultProof certificateProof checkerProof
      fingerprintProof buildProof archiveProof submissionProof result build =>
    build boundaryProof resultProof certificateProof checkerProof
      fingerprintProof buildProof archiveProof submissionProof

theorem ay_vtbg_pre_timeout_contract_boundary
    (beforeBoundary resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest :
      Prop) :
    ay_vtbg_pre_timeout_contract beforeBoundary resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint buildConfig
      archiveManifest submissionManifest ->
    beforeBoundary :=
  fun contract =>
    contract beforeBoundary
      (fun boundaryProof _resultProof _certificateProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _submissionProof =>
        boundaryProof)

theorem ay_vtbg_pre_timeout_contract_result_artifact
    (beforeBoundary resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest :
      Prop) :
    ay_vtbg_pre_timeout_contract beforeBoundary resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint buildConfig
      archiveManifest submissionManifest ->
    resultArtifact :=
  fun contract =>
    contract resultArtifact
      (fun _boundaryProof resultProof _certificateProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _submissionProof =>
        resultProof)

theorem ay_vtbg_pre_timeout_contract_certificate_model
    (beforeBoundary resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest :
      Prop) :
    ay_vtbg_pre_timeout_contract beforeBoundary resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint buildConfig
      archiveManifest submissionManifest ->
    certificateModel :=
  fun contract =>
    contract certificateModel
      (fun _boundaryProof _resultProof certificateProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _submissionProof =>
        certificateProof)

theorem ay_vtbg_pre_timeout_contract_checker
    (beforeBoundary resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest :
      Prop) :
    ay_vtbg_pre_timeout_contract beforeBoundary resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint buildConfig
      archiveManifest submissionManifest ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _boundaryProof _resultProof _certificateProof checkerProof
          _fingerprintProof _buildProof _archiveProof _submissionProof =>
        checkerProof)

theorem ay_vtbg_pre_timeout_contract_fingerprint
    (beforeBoundary resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest :
      Prop) :
    ay_vtbg_pre_timeout_contract beforeBoundary resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint buildConfig
      archiveManifest submissionManifest ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _boundaryProof _resultProof _certificateProof _checkerProof
          fingerprintProof _buildProof _archiveProof _submissionProof =>
        fingerprintProof)

theorem ay_vtbg_pre_timeout_contract_build
    (beforeBoundary resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest :
      Prop) :
    ay_vtbg_pre_timeout_contract beforeBoundary resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint buildConfig
      archiveManifest submissionManifest ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _boundaryProof _resultProof _certificateProof _checkerProof
          _fingerprintProof buildProof _archiveProof _submissionProof =>
        buildProof)

theorem ay_vtbg_pre_timeout_contract_archive
    (beforeBoundary resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest :
      Prop) :
    ay_vtbg_pre_timeout_contract beforeBoundary resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint buildConfig
      archiveManifest submissionManifest ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _boundaryProof _resultProof _certificateProof _checkerProof
          _fingerprintProof _buildProof archiveProof _submissionProof =>
        archiveProof)

theorem ay_vtbg_pre_timeout_contract_submission
    (beforeBoundary resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest :
      Prop) :
    ay_vtbg_pre_timeout_contract beforeBoundary resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint buildConfig
      archiveManifest submissionManifest ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun _boundaryProof _resultProof _certificateProof _checkerProof
          _fingerprintProof _buildProof _archiveProof submissionProof =>
        submissionProof)

theorem ay_vtbg_sat_publication_intro
    (preTimeoutContract modelEvidence originalModel : Prop) :
    preTimeoutContract -> modelEvidence -> originalModel ->
    ay_vtbg_sat_publication preTimeoutContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vtbg_conj_intro preTimeoutContract
      (ay_vtbg_conj modelEvidence originalModel) contractProof
      (ay_vtbg_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vtbg_sat_publication_original_model
    (preTimeoutContract modelEvidence originalModel : Prop) :
    ay_vtbg_sat_publication preTimeoutContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vtbg_conj_right modelEvidence originalModel
      (ay_vtbg_conj_right preTimeoutContract
        (ay_vtbg_conj modelEvidence originalModel) publication)

theorem ay_vtbg_unsat_publication_intro
    (preTimeoutContract proofEvidence originalEmptyClause : Prop) :
    preTimeoutContract -> proofEvidence -> originalEmptyClause ->
    ay_vtbg_unsat_publication preTimeoutContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vtbg_conj_intro preTimeoutContract
      (ay_vtbg_conj proofEvidence originalEmptyClause) contractProof
      (ay_vtbg_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vtbg_unsat_publication_original_empty_clause
    (preTimeoutContract proofEvidence originalEmptyClause : Prop) :
    ay_vtbg_unsat_publication preTimeoutContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vtbg_conj_right proofEvidence originalEmptyClause
      (ay_vtbg_conj_right preTimeoutContract
        (ay_vtbg_conj proofEvidence originalEmptyClause) publication)

theorem ay_vtbg_accepted_pre_timeout_sat_sound
    (preTimeoutContract modelEvidence originalModel : Prop) :
    ay_vtbg_sat_publication preTimeoutContract modelEvidence originalModel ->
    originalModel :=
  ay_vtbg_sat_publication_original_model preTimeoutContract modelEvidence
    originalModel

theorem ay_vtbg_accepted_pre_timeout_unsat_sound
    (preTimeoutContract proofEvidence originalEmptyClause : Prop) :
    ay_vtbg_unsat_publication preTimeoutContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_vtbg_unsat_publication_original_empty_clause preTimeoutContract
    proofEvidence originalEmptyClause

theorem ay_vtbg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vtbg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vtbg_conj_intro reason (ay_vtbg_conj fallbackPath auditTrail)
      reasonProof
      (ay_vtbg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_vtbg_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vtbg_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vtbg_conj_left reason (ay_vtbg_conj fallbackPath auditTrail)
      noClaim

theorem ay_vtbg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vtbg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_vtbg_conj_intro reason
      (ay_vtbg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_vtbg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_vtbg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vtbg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vtbg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_vtbg_conj_right reason
        (ay_vtbg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vtbg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vtbg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vtbg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_vtbg_conj_right reason
        (ay_vtbg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vtbg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vtbg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vtbg_conj_intro reason
      (ay_vtbg_conj fallbackPath recomputeObligation) reasonProof
      (ay_vtbg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_vtbg_boundary_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtbg_boundary_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_vtbg_conj_intro
      (ay_vtbg_blocked_publication satFact unsatFact reason)
      (ay_vtbg_recompute reason fallbackPath recomputeObligation)
      (ay_vtbg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_vtbg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vtbg_boundary_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vtbg_boundary_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vtbg_blocked_publication_no_sat satFact unsatFact reason
      (ay_vtbg_conj_left
        (ay_vtbg_blocked_publication satFact unsatFact reason)
        (ay_vtbg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vtbg_boundary_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vtbg_boundary_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vtbg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vtbg_conj_left
        (ay_vtbg_blocked_publication satFact unsatFact reason)
        (ay_vtbg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vtbg_boundary_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vtbg_boundary_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vtbg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vtbg_conj_right
      (ay_vtbg_blocked_publication satFact unsatFact reason)
      (ay_vtbg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vtbg_timeout_boundary_forces_no_claim
    (satFact unsatFact timeoutBoundary fallbackPath auditTrail
      recomputeObligation : Prop) :
    timeoutBoundary -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtbg_no_claim timeoutBoundary fallbackPath auditTrail :=
  fun boundaryProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_vtbg_no_claim_intro timeoutBoundary fallbackPath auditTrail
      boundaryProof fallbackProof auditProof

theorem ay_vtbg_incomplete_artifact_forces_no_claim
    (satFact unsatFact incompleteArtifact fallbackPath auditTrail
      recomputeObligation : Prop) :
    incompleteArtifact -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtbg_no_claim incompleteArtifact fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vtbg_no_claim_intro incompleteArtifact fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vtbg_missing_checker_forces_no_claim
    (satFact unsatFact missingChecker fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingChecker -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtbg_no_claim missingChecker fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vtbg_no_claim_intro missingChecker fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vtbg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtbg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vtbg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vtbg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtbg_no_claim buildMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vtbg_no_claim_intro buildMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vtbg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtbg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vtbg_no_claim_intro archiveMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vtbg_submission_mismatch_forces_no_claim
    (satFact unsatFact submissionMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    submissionMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtbg_no_claim submissionMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vtbg_no_claim_intro submissionMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vtbg_failed_boundary_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vtbg_boundary_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vtbg_boundary_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vtbg_failed_boundary_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vtbg_boundary_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vtbg_boundary_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
