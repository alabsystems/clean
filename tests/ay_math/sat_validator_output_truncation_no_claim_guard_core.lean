-- SAT-COMP validator output-truncation no-claim guard core.
--
-- Public SAT/UNSAT claims are allowed only when solver artifacts,
-- output-length/truncation manifests, checker replay, benchmark identity,
-- archive/build evidence, and no-claim fallback agree.

def ay_trng_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_trng_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_trng_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_trng_disj satFact (ay_trng_disj unsatFact noClaimFact)

def ay_trng_output_contract
    (solverResultArtifact outputTruncationManifest certificateModelArtifact
      checkerTranscript benchmarkFingerprint archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) : Prop :=
  forall result : Prop,
    (solverResultArtifact -> outputTruncationManifest ->
      certificateModelArtifact -> checkerTranscript -> benchmarkFingerprint ->
      archiveManifest -> solverBuildEvidence -> noClaimFallbackPath ->
      result) ->
    result

def ay_trng_sat_publication
    (outputContract modelEvidence originalModel : Prop) : Prop :=
  ay_trng_conj outputContract
    (ay_trng_conj modelEvidence originalModel)

def ay_trng_unsat_publication
    (outputContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_trng_conj outputContract
    (ay_trng_conj proofEvidence originalEmptyClause)

def ay_trng_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_trng_conj reason (ay_trng_conj fallbackPath auditTrail)

def ay_trng_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_trng_conj reason
    (ay_trng_conj (satFact -> False) (unsatFact -> False))

def ay_trng_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_trng_conj reason
    (ay_trng_conj fallbackPath recomputeObligation)

def ay_trng_output_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_trng_conj
    (ay_trng_blocked_publication satFact unsatFact reason)
    (ay_trng_recompute reason fallbackPath recomputeObligation)

theorem ay_trng_conj_intro (left right : Prop) :
    left -> right -> ay_trng_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_trng_conj_left (left right : Prop) :
    ay_trng_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_trng_conj_right (left right : Prop) :
    ay_trng_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_trng_disj_left (left right : Prop) :
    left -> ay_trng_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_trng_disj_right (left right : Prop) :
    right -> ay_trng_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_trng_output_contract_intro
    (solverResultArtifact outputTruncationManifest certificateModelArtifact
      checkerTranscript benchmarkFingerprint archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    solverResultArtifact -> outputTruncationManifest ->
    certificateModelArtifact -> checkerTranscript -> benchmarkFingerprint ->
    archiveManifest -> solverBuildEvidence -> noClaimFallbackPath ->
    ay_trng_output_contract solverResultArtifact outputTruncationManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath :=
  fun artifactProof outputProof certificateProof checkerProof fingerprintProof
      archiveProof buildProof fallbackProof result build =>
    build artifactProof outputProof certificateProof checkerProof
      fingerprintProof archiveProof buildProof fallbackProof

theorem ay_trng_output_contract_artifact
    (solverResultArtifact outputTruncationManifest certificateModelArtifact
      checkerTranscript benchmarkFingerprint archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_trng_output_contract solverResultArtifact outputTruncationManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    solverResultArtifact :=
  fun contract =>
    contract solverResultArtifact
      (fun artifactProof _outputProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        artifactProof)

theorem ay_trng_output_contract_manifest
    (solverResultArtifact outputTruncationManifest certificateModelArtifact
      checkerTranscript benchmarkFingerprint archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_trng_output_contract solverResultArtifact outputTruncationManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    outputTruncationManifest :=
  fun contract =>
    contract outputTruncationManifest
      (fun _artifactProof outputProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        outputProof)

theorem ay_trng_output_contract_certificate
    (solverResultArtifact outputTruncationManifest certificateModelArtifact
      checkerTranscript benchmarkFingerprint archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_trng_output_contract solverResultArtifact outputTruncationManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    certificateModelArtifact :=
  fun contract =>
    contract certificateModelArtifact
      (fun _artifactProof _outputProof certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        certificateProof)

theorem ay_trng_output_contract_checker
    (solverResultArtifact outputTruncationManifest certificateModelArtifact
      checkerTranscript benchmarkFingerprint archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_trng_output_contract solverResultArtifact outputTruncationManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _artifactProof _outputProof _certificateProof checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        checkerProof)

theorem ay_trng_output_contract_fingerprint
    (solverResultArtifact outputTruncationManifest certificateModelArtifact
      checkerTranscript benchmarkFingerprint archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_trng_output_contract solverResultArtifact outputTruncationManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _artifactProof _outputProof _certificateProof _checkerProof
          fingerprintProof _archiveProof _buildProof _fallbackProof =>
        fingerprintProof)

theorem ay_trng_output_contract_archive
    (solverResultArtifact outputTruncationManifest certificateModelArtifact
      checkerTranscript benchmarkFingerprint archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_trng_output_contract solverResultArtifact outputTruncationManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _artifactProof _outputProof _certificateProof _checkerProof
          _fingerprintProof archiveProof _buildProof _fallbackProof =>
        archiveProof)

theorem ay_trng_output_contract_build
    (solverResultArtifact outputTruncationManifest certificateModelArtifact
      checkerTranscript benchmarkFingerprint archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_trng_output_contract solverResultArtifact outputTruncationManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _artifactProof _outputProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof buildProof _fallbackProof =>
        buildProof)

theorem ay_trng_output_contract_fallback
    (solverResultArtifact outputTruncationManifest certificateModelArtifact
      checkerTranscript benchmarkFingerprint archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_trng_output_contract solverResultArtifact outputTruncationManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _artifactProof _outputProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof fallbackProof =>
        fallbackProof)

theorem ay_trng_sat_publication_intro
    (outputContract modelEvidence originalModel : Prop) :
    outputContract -> modelEvidence -> originalModel ->
    ay_trng_sat_publication outputContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_trng_conj_intro outputContract
      (ay_trng_conj modelEvidence originalModel) contractProof
      (ay_trng_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_trng_sat_publication_original_model
    (outputContract modelEvidence originalModel : Prop) :
    ay_trng_sat_publication outputContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_trng_conj_right modelEvidence originalModel
      (ay_trng_conj_right outputContract
        (ay_trng_conj modelEvidence originalModel) publication)

theorem ay_trng_unsat_publication_intro
    (outputContract proofEvidence originalEmptyClause : Prop) :
    outputContract -> proofEvidence -> originalEmptyClause ->
    ay_trng_unsat_publication outputContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_trng_conj_intro outputContract
      (ay_trng_conj proofEvidence originalEmptyClause) contractProof
      (ay_trng_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_trng_unsat_publication_original_empty_clause
    (outputContract proofEvidence originalEmptyClause : Prop) :
    ay_trng_unsat_publication outputContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_trng_conj_right proofEvidence originalEmptyClause
      (ay_trng_conj_right outputContract
        (ay_trng_conj proofEvidence originalEmptyClause) publication)

theorem ay_trng_accepted_output_contract_sat_sound
    (outputContract modelEvidence originalModel : Prop) :
    ay_trng_sat_publication outputContract modelEvidence originalModel ->
    originalModel :=
  ay_trng_sat_publication_original_model outputContract modelEvidence
    originalModel

theorem ay_trng_accepted_output_contract_unsat_sound
    (outputContract proofEvidence originalEmptyClause : Prop) :
    ay_trng_unsat_publication outputContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_trng_unsat_publication_original_empty_clause outputContract proofEvidence
    originalEmptyClause

theorem ay_trng_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_trng_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_trng_conj_intro reason (ay_trng_conj fallbackPath auditTrail)
      reasonProof
      (ay_trng_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_trng_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_trng_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_trng_conj_intro reason
      (ay_trng_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_trng_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_trng_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_trng_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_trng_conj_left (satFact -> False) (unsatFact -> False)
      (ay_trng_conj_right reason
        (ay_trng_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_trng_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_trng_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_trng_conj_right (satFact -> False) (unsatFact -> False)
      (ay_trng_conj_right reason
        (ay_trng_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_trng_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_trng_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_trng_conj_intro reason
      (ay_trng_conj fallbackPath recomputeObligation) reasonProof
      (ay_trng_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_trng_output_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_trng_output_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_trng_conj_intro
      (ay_trng_blocked_publication satFact unsatFact reason)
      (ay_trng_recompute reason fallbackPath recomputeObligation)
      (ay_trng_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_trng_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_trng_output_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_trng_output_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_trng_blocked_publication_no_sat satFact unsatFact reason
      (ay_trng_conj_left
        (ay_trng_blocked_publication satFact unsatFact reason)
        (ay_trng_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_trng_output_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_trng_output_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_trng_blocked_publication_no_unsat satFact unsatFact reason
      (ay_trng_conj_left
        (ay_trng_blocked_publication satFact unsatFact reason)
        (ay_trng_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_trng_output_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_trng_output_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_trng_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_trng_conj_right
      (ay_trng_blocked_publication satFact unsatFact reason)
      (ay_trng_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_trng_truncated_output_forces_no_claim
    (satFact unsatFact truncatedOutput fallbackPath auditTrail
      recomputeObligation : Prop) :
    truncatedOutput -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_trng_no_claim truncatedOutput fallbackPath auditTrail :=
  fun truncProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_trng_no_claim_intro truncatedOutput fallbackPath auditTrail truncProof
      fallbackProof auditProof

theorem ay_trng_corrupt_output_forces_no_claim
    (satFact unsatFact corruptOutput fallbackPath auditTrail
      recomputeObligation : Prop) :
    corruptOutput -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_trng_no_claim corruptOutput fallbackPath auditTrail :=
  fun corruptProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_trng_no_claim_intro corruptOutput fallbackPath auditTrail corruptProof
      fallbackProof auditProof

theorem ay_trng_incomplete_output_forces_no_claim
    (satFact unsatFact incompleteOutput fallbackPath auditTrail
      recomputeObligation : Prop) :
    incompleteOutput -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_trng_no_claim incompleteOutput fallbackPath auditTrail :=
  fun incompleteProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_trng_no_claim_intro incompleteOutput fallbackPath auditTrail
      incompleteProof fallbackProof auditProof

theorem ay_trng_failed_output_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_trng_output_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_trng_output_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_trng_failed_output_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_trng_output_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_trng_output_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_trng_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_trng_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_trng_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_trng_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
