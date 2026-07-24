-- SAT-COMP validator stale-artifact no-claim guard core.
--
-- Public SAT/UNSAT claims are allowed only when artifact timestamp/digest,
-- benchmark fingerprint, certificate/model artifact, checker transcript,
-- archive manifest, solver build evidence, and no-claim fallback agree.

def ay_stag_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_stag_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_stag_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_stag_disj satFact (ay_stag_disj unsatFact noClaimFact)

def ay_stag_fresh_artifact_contract
    (resultArtifactTimestampDigest benchmarkFingerprint
      certificateModelArtifact checkerTranscript archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) : Prop :=
  forall result : Prop,
    (resultArtifactTimestampDigest -> benchmarkFingerprint ->
      certificateModelArtifact -> checkerTranscript -> archiveManifest ->
      solverBuildEvidence -> noClaimFallbackPath -> result) ->
    result

def ay_stag_sat_publication
    (freshContract modelEvidence originalModel : Prop) : Prop :=
  ay_stag_conj freshContract
    (ay_stag_conj modelEvidence originalModel)

def ay_stag_unsat_publication
    (freshContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_stag_conj freshContract
    (ay_stag_conj proofEvidence originalEmptyClause)

def ay_stag_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_stag_conj reason (ay_stag_conj fallbackPath auditTrail)

def ay_stag_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_stag_conj reason
    (ay_stag_conj (satFact -> False) (unsatFact -> False))

def ay_stag_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_stag_conj reason
    (ay_stag_conj fallbackPath recomputeObligation)

def ay_stag_stale_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_stag_conj
    (ay_stag_blocked_publication satFact unsatFact reason)
    (ay_stag_recompute reason fallbackPath recomputeObligation)

theorem ay_stag_conj_intro (left right : Prop) :
    left -> right -> ay_stag_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_stag_conj_left (left right : Prop) :
    ay_stag_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_stag_conj_right (left right : Prop) :
    ay_stag_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_stag_disj_left (left right : Prop) :
    left -> ay_stag_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_stag_disj_right (left right : Prop) :
    right -> ay_stag_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_stag_fresh_artifact_contract_intro
    (resultArtifactTimestampDigest benchmarkFingerprint
      certificateModelArtifact checkerTranscript archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    resultArtifactTimestampDigest -> benchmarkFingerprint ->
    certificateModelArtifact -> checkerTranscript -> archiveManifest ->
    solverBuildEvidence -> noClaimFallbackPath ->
    ay_stag_fresh_artifact_contract resultArtifactTimestampDigest
      benchmarkFingerprint certificateModelArtifact checkerTranscript
      archiveManifest solverBuildEvidence noClaimFallbackPath :=
  fun artifactProof fingerprintProof certificateProof checkerProof
      archiveProof buildProof fallbackProof result build =>
    build artifactProof fingerprintProof certificateProof checkerProof
      archiveProof buildProof fallbackProof

theorem ay_stag_fresh_artifact_contract_artifact
    (resultArtifactTimestampDigest benchmarkFingerprint
      certificateModelArtifact checkerTranscript archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_stag_fresh_artifact_contract resultArtifactTimestampDigest
      benchmarkFingerprint certificateModelArtifact checkerTranscript
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    resultArtifactTimestampDigest :=
  fun contract =>
    contract resultArtifactTimestampDigest
      (fun artifactProof _fingerprintProof _certificateProof _checkerProof
          _archiveProof _buildProof _fallbackProof => artifactProof)

theorem ay_stag_fresh_artifact_contract_fingerprint
    (resultArtifactTimestampDigest benchmarkFingerprint
      certificateModelArtifact checkerTranscript archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_stag_fresh_artifact_contract resultArtifactTimestampDigest
      benchmarkFingerprint certificateModelArtifact checkerTranscript
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _artifactProof fingerprintProof _certificateProof _checkerProof
          _archiveProof _buildProof _fallbackProof => fingerprintProof)

theorem ay_stag_fresh_artifact_contract_certificate
    (resultArtifactTimestampDigest benchmarkFingerprint
      certificateModelArtifact checkerTranscript archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_stag_fresh_artifact_contract resultArtifactTimestampDigest
      benchmarkFingerprint certificateModelArtifact checkerTranscript
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    certificateModelArtifact :=
  fun contract =>
    contract certificateModelArtifact
      (fun _artifactProof _fingerprintProof certificateProof _checkerProof
          _archiveProof _buildProof _fallbackProof => certificateProof)

theorem ay_stag_fresh_artifact_contract_checker
    (resultArtifactTimestampDigest benchmarkFingerprint
      certificateModelArtifact checkerTranscript archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_stag_fresh_artifact_contract resultArtifactTimestampDigest
      benchmarkFingerprint certificateModelArtifact checkerTranscript
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _artifactProof _fingerprintProof _certificateProof checkerProof
          _archiveProof _buildProof _fallbackProof => checkerProof)

theorem ay_stag_fresh_artifact_contract_archive
    (resultArtifactTimestampDigest benchmarkFingerprint
      certificateModelArtifact checkerTranscript archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_stag_fresh_artifact_contract resultArtifactTimestampDigest
      benchmarkFingerprint certificateModelArtifact checkerTranscript
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _artifactProof _fingerprintProof _certificateProof _checkerProof
          archiveProof _buildProof _fallbackProof => archiveProof)

theorem ay_stag_fresh_artifact_contract_build
    (resultArtifactTimestampDigest benchmarkFingerprint
      certificateModelArtifact checkerTranscript archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_stag_fresh_artifact_contract resultArtifactTimestampDigest
      benchmarkFingerprint certificateModelArtifact checkerTranscript
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _artifactProof _fingerprintProof _certificateProof _checkerProof
          _archiveProof buildProof _fallbackProof => buildProof)

theorem ay_stag_fresh_artifact_contract_fallback
    (resultArtifactTimestampDigest benchmarkFingerprint
      certificateModelArtifact checkerTranscript archiveManifest
      solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_stag_fresh_artifact_contract resultArtifactTimestampDigest
      benchmarkFingerprint certificateModelArtifact checkerTranscript
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _artifactProof _fingerprintProof _certificateProof _checkerProof
          _archiveProof _buildProof fallbackProof => fallbackProof)

theorem ay_stag_sat_publication_intro
    (freshContract modelEvidence originalModel : Prop) :
    freshContract -> modelEvidence -> originalModel ->
    ay_stag_sat_publication freshContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_stag_conj_intro freshContract
      (ay_stag_conj modelEvidence originalModel) contractProof
      (ay_stag_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_stag_sat_publication_original_model
    (freshContract modelEvidence originalModel : Prop) :
    ay_stag_sat_publication freshContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_stag_conj_right modelEvidence originalModel
      (ay_stag_conj_right freshContract
        (ay_stag_conj modelEvidence originalModel) publication)

theorem ay_stag_unsat_publication_intro
    (freshContract proofEvidence originalEmptyClause : Prop) :
    freshContract -> proofEvidence -> originalEmptyClause ->
    ay_stag_unsat_publication freshContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_stag_conj_intro freshContract
      (ay_stag_conj proofEvidence originalEmptyClause) contractProof
      (ay_stag_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_stag_unsat_publication_original_empty_clause
    (freshContract proofEvidence originalEmptyClause : Prop) :
    ay_stag_unsat_publication freshContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_stag_conj_right proofEvidence originalEmptyClause
      (ay_stag_conj_right freshContract
        (ay_stag_conj proofEvidence originalEmptyClause) publication)

theorem ay_stag_accepted_fresh_artifact_sat_sound
    (freshContract modelEvidence originalModel : Prop) :
    ay_stag_sat_publication freshContract modelEvidence originalModel ->
    originalModel :=
  ay_stag_sat_publication_original_model freshContract modelEvidence
    originalModel

theorem ay_stag_accepted_fresh_artifact_unsat_sound
    (freshContract proofEvidence originalEmptyClause : Prop) :
    ay_stag_unsat_publication freshContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_stag_unsat_publication_original_empty_clause freshContract proofEvidence
    originalEmptyClause

theorem ay_stag_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_stag_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_stag_conj_intro reason (ay_stag_conj fallbackPath auditTrail)
      reasonProof
      (ay_stag_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_stag_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_stag_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_stag_conj_intro reason
      (ay_stag_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_stag_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_stag_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_stag_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_stag_conj_left (satFact -> False) (unsatFact -> False)
      (ay_stag_conj_right reason
        (ay_stag_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_stag_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_stag_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_stag_conj_right (satFact -> False) (unsatFact -> False)
      (ay_stag_conj_right reason
        (ay_stag_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_stag_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_stag_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_stag_conj_intro reason
      (ay_stag_conj fallbackPath recomputeObligation) reasonProof
      (ay_stag_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_stag_stale_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_stag_stale_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_stag_conj_intro
      (ay_stag_blocked_publication satFact unsatFact reason)
      (ay_stag_recompute reason fallbackPath recomputeObligation)
      (ay_stag_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_stag_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_stag_stale_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_stag_stale_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_stag_blocked_publication_no_sat satFact unsatFact reason
      (ay_stag_conj_left
        (ay_stag_blocked_publication satFact unsatFact reason)
        (ay_stag_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_stag_stale_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_stag_stale_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_stag_blocked_publication_no_unsat satFact unsatFact reason
      (ay_stag_conj_left
        (ay_stag_blocked_publication satFact unsatFact reason)
        (ay_stag_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_stag_stale_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_stag_stale_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_stag_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_stag_conj_right
      (ay_stag_blocked_publication satFact unsatFact reason)
      (ay_stag_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_stag_stale_artifact_forces_no_claim
    (satFact unsatFact staleArtifact fallbackPath auditTrail
      recomputeObligation : Prop) :
    staleArtifact -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_stag_no_claim staleArtifact fallbackPath auditTrail :=
  fun staleProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_stag_no_claim_intro staleArtifact fallbackPath auditTrail staleProof
      fallbackProof auditProof

theorem ay_stag_stale_certificate_forces_no_claim
    (satFact unsatFact staleCertificate fallbackPath auditTrail
      recomputeObligation : Prop) :
    staleCertificate -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_stag_no_claim staleCertificate fallbackPath auditTrail :=
  fun staleProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_stag_no_claim_intro staleCertificate fallbackPath auditTrail
      staleProof fallbackProof auditProof

theorem ay_stag_stale_checker_forces_no_claim
    (satFact unsatFact staleChecker fallbackPath auditTrail
      recomputeObligation : Prop) :
    staleChecker -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_stag_no_claim staleChecker fallbackPath auditTrail :=
  fun staleProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_stag_no_claim_intro staleChecker fallbackPath auditTrail staleProof
      fallbackProof auditProof

theorem ay_stag_stale_benchmark_forces_no_claim
    (satFact unsatFact staleBenchmark fallbackPath auditTrail
      recomputeObligation : Prop) :
    staleBenchmark -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_stag_no_claim staleBenchmark fallbackPath auditTrail :=
  fun staleProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_stag_no_claim_intro staleBenchmark fallbackPath auditTrail staleProof
      fallbackProof auditProof

theorem ay_stag_failed_stale_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_stag_stale_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_stag_stale_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_stag_failed_stale_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_stag_stale_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_stag_stale_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_stag_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_stag_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_stag_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_stag_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
