-- SAT-COMP validator log-digest no-claim guard core.
--
-- Public SAT/UNSAT claims are allowed only when solver log digest, result
-- artifact, certificate/model artifact, checker transcript, benchmark
-- fingerprint, archive manifest, solver build evidence, and no-claim fallback
-- agree.

def ay_ldng_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ldng_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ldng_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_ldng_disj satFact (ay_ldng_disj unsatFact noClaimFact)

def ay_ldng_log_contract
    (solverLogDigest resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) : Prop :=
  forall result : Prop,
    (solverLogDigest -> resultArtifact -> certificateModelArtifact ->
      checkerTranscript -> benchmarkFingerprint -> archiveManifest ->
      solverBuildEvidence -> noClaimFallbackPath -> result) ->
    result

def ay_ldng_sat_publication
    (logContract modelEvidence originalModel : Prop) : Prop :=
  ay_ldng_conj logContract
    (ay_ldng_conj modelEvidence originalModel)

def ay_ldng_unsat_publication
    (logContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_ldng_conj logContract
    (ay_ldng_conj proofEvidence originalEmptyClause)

def ay_ldng_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_ldng_conj reason (ay_ldng_conj fallbackPath auditTrail)

def ay_ldng_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_ldng_conj reason
    (ay_ldng_conj (satFact -> False) (unsatFact -> False))

def ay_ldng_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_ldng_conj reason
    (ay_ldng_conj fallbackPath recomputeObligation)

def ay_ldng_log_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_ldng_conj
    (ay_ldng_blocked_publication satFact unsatFact reason)
    (ay_ldng_recompute reason fallbackPath recomputeObligation)

theorem ay_ldng_conj_intro (left right : Prop) :
    left -> right -> ay_ldng_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ldng_conj_left (left right : Prop) :
    ay_ldng_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ldng_conj_right (left right : Prop) :
    ay_ldng_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ldng_disj_left (left right : Prop) :
    left -> ay_ldng_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ldng_disj_right (left right : Prop) :
    right -> ay_ldng_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ldng_log_contract_intro
    (solverLogDigest resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    solverLogDigest -> resultArtifact -> certificateModelArtifact ->
    checkerTranscript -> benchmarkFingerprint -> archiveManifest ->
    solverBuildEvidence -> noClaimFallbackPath ->
    ay_ldng_log_contract solverLogDigest resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath :=
  fun logProof artifactProof certificateProof checkerProof fingerprintProof
      archiveProof buildProof fallbackProof result build =>
    build logProof artifactProof certificateProof checkerProof
      fingerprintProof archiveProof buildProof fallbackProof

theorem ay_ldng_log_contract_log_digest
    (solverLogDigest resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ldng_log_contract solverLogDigest resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    solverLogDigest :=
  fun contract =>
    contract solverLogDigest
      (fun logProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        logProof)

theorem ay_ldng_log_contract_result_artifact
    (solverLogDigest resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ldng_log_contract solverLogDigest resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    resultArtifact :=
  fun contract =>
    contract resultArtifact
      (fun _logProof artifactProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        artifactProof)

theorem ay_ldng_log_contract_certificate
    (solverLogDigest resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ldng_log_contract solverLogDigest resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    certificateModelArtifact :=
  fun contract =>
    contract certificateModelArtifact
      (fun _logProof _artifactProof certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        certificateProof)

theorem ay_ldng_log_contract_checker
    (solverLogDigest resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ldng_log_contract solverLogDigest resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _logProof _artifactProof _certificateProof checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        checkerProof)

theorem ay_ldng_log_contract_fingerprint
    (solverLogDigest resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ldng_log_contract solverLogDigest resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _logProof _artifactProof _certificateProof _checkerProof
          fingerprintProof _archiveProof _buildProof _fallbackProof =>
        fingerprintProof)

theorem ay_ldng_log_contract_archive
    (solverLogDigest resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ldng_log_contract solverLogDigest resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _logProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof archiveProof _buildProof _fallbackProof =>
        archiveProof)

theorem ay_ldng_log_contract_build
    (solverLogDigest resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ldng_log_contract solverLogDigest resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _logProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof buildProof _fallbackProof =>
        buildProof)

theorem ay_ldng_log_contract_fallback
    (solverLogDigest resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ldng_log_contract solverLogDigest resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _logProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof fallbackProof =>
        fallbackProof)

theorem ay_ldng_sat_publication_intro
    (logContract modelEvidence originalModel : Prop) :
    logContract -> modelEvidence -> originalModel ->
    ay_ldng_sat_publication logContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_ldng_conj_intro logContract
      (ay_ldng_conj modelEvidence originalModel) contractProof
      (ay_ldng_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_ldng_sat_publication_original_model
    (logContract modelEvidence originalModel : Prop) :
    ay_ldng_sat_publication logContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_ldng_conj_right modelEvidence originalModel
      (ay_ldng_conj_right logContract
        (ay_ldng_conj modelEvidence originalModel) publication)

theorem ay_ldng_unsat_publication_intro
    (logContract proofEvidence originalEmptyClause : Prop) :
    logContract -> proofEvidence -> originalEmptyClause ->
    ay_ldng_unsat_publication logContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_ldng_conj_intro logContract
      (ay_ldng_conj proofEvidence originalEmptyClause) contractProof
      (ay_ldng_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_ldng_unsat_publication_original_empty_clause
    (logContract proofEvidence originalEmptyClause : Prop) :
    ay_ldng_unsat_publication logContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_ldng_conj_right proofEvidence originalEmptyClause
      (ay_ldng_conj_right logContract
        (ay_ldng_conj proofEvidence originalEmptyClause) publication)

theorem ay_ldng_accepted_log_contract_sat_sound
    (logContract modelEvidence originalModel : Prop) :
    ay_ldng_sat_publication logContract modelEvidence originalModel ->
    originalModel :=
  ay_ldng_sat_publication_original_model logContract modelEvidence
    originalModel

theorem ay_ldng_accepted_log_contract_unsat_sound
    (logContract proofEvidence originalEmptyClause : Prop) :
    ay_ldng_unsat_publication logContract proofEvidence originalEmptyClause ->
    originalEmptyClause :=
  ay_ldng_unsat_publication_original_empty_clause logContract proofEvidence
    originalEmptyClause

theorem ay_ldng_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_ldng_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_ldng_conj_intro reason (ay_ldng_conj fallbackPath auditTrail)
      reasonProof
      (ay_ldng_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_ldng_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ldng_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_ldng_conj_intro reason
      (ay_ldng_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_ldng_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_ldng_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_ldng_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_ldng_conj_left (satFact -> False) (unsatFact -> False)
      (ay_ldng_conj_right reason
        (ay_ldng_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_ldng_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_ldng_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_ldng_conj_right (satFact -> False) (unsatFact -> False)
      (ay_ldng_conj_right reason
        (ay_ldng_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_ldng_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_ldng_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_ldng_conj_intro reason
      (ay_ldng_conj fallbackPath recomputeObligation) reasonProof
      (ay_ldng_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_ldng_log_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ldng_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_ldng_conj_intro
      (ay_ldng_blocked_publication satFact unsatFact reason)
      (ay_ldng_recompute reason fallbackPath recomputeObligation)
      (ay_ldng_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_ldng_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_ldng_log_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ldng_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_ldng_blocked_publication_no_sat satFact unsatFact reason
      (ay_ldng_conj_left
        (ay_ldng_blocked_publication satFact unsatFact reason)
        (ay_ldng_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ldng_log_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ldng_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_ldng_blocked_publication_no_unsat satFact unsatFact reason
      (ay_ldng_conj_left
        (ay_ldng_blocked_publication satFact unsatFact reason)
        (ay_ldng_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ldng_log_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ldng_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_ldng_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_ldng_conj_right
      (ay_ldng_blocked_publication satFact unsatFact reason)
      (ay_ldng_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_ldng_missing_log_digest_forces_no_claim
    (satFact unsatFact missingLogDigest fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingLogDigest -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ldng_no_claim missingLogDigest fallbackPath auditTrail :=
  fun missingProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ldng_no_claim_intro missingLogDigest fallbackPath auditTrail
      missingProof fallbackProof auditProof

theorem ay_ldng_truncated_log_digest_forces_no_claim
    (satFact unsatFact truncatedLogDigest fallbackPath auditTrail
      recomputeObligation : Prop) :
    truncatedLogDigest -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ldng_no_claim truncatedLogDigest fallbackPath auditTrail :=
  fun truncProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ldng_no_claim_intro truncatedLogDigest fallbackPath auditTrail
      truncProof fallbackProof auditProof

theorem ay_ldng_tampered_log_digest_forces_no_claim
    (satFact unsatFact tamperedLogDigest fallbackPath auditTrail
      recomputeObligation : Prop) :
    tamperedLogDigest -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ldng_no_claim tamperedLogDigest fallbackPath auditTrail :=
  fun tamperProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ldng_no_claim_intro tamperedLogDigest fallbackPath auditTrail
      tamperProof fallbackProof auditProof

theorem ay_ldng_artifact_disagreement_forces_no_claim
    (satFact unsatFact artifactDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    artifactDisagreement -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ldng_no_claim artifactDisagreement fallbackPath auditTrail :=
  fun disagreementProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ldng_no_claim_intro artifactDisagreement fallbackPath auditTrail
      disagreementProof fallbackProof auditProof

theorem ay_ldng_checker_disagreement_forces_no_claim
    (satFact unsatFact checkerDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerDisagreement -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ldng_no_claim checkerDisagreement fallbackPath auditTrail :=
  fun disagreementProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ldng_no_claim_intro checkerDisagreement fallbackPath auditTrail
      disagreementProof fallbackProof auditProof

theorem ay_ldng_failed_log_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ldng_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_ldng_log_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_ldng_failed_log_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ldng_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_ldng_log_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_ldng_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_ldng_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_ldng_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_ldng_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
