-- SAT-COMP validator artifact path canonicalization guard core.
--
-- Public SAT/UNSAT claims require archive evidence, canonical artifact paths,
-- path-normalization evidence, symlink/escape exclusion, artifact digest,
-- checker transcript, benchmark fingerprint, solver build evidence, fallback,
-- and audit transcript to agree.

def ay_apcg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_apcg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_apcg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_apcg_disj satFact (ay_apcg_disj unsatFact noClaimFact)

def ay_apcg_path_contract
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (archiveManifest -> canonicalArtifactPathMap ->
      pathNormalizationWitness -> symlinkEscapeExclusionWitness ->
      modelProofArtifactDigest -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> fallbackNoClaimPath -> auditTranscript ->
      result) ->
    result

def ay_apcg_sat_publication
    (pathContract intendedArchivedArtifact checkedModel originalModel :
      Prop) : Prop :=
  ay_apcg_conj pathContract
    (ay_apcg_conj intendedArchivedArtifact
      (ay_apcg_conj checkedModel originalModel))

def ay_apcg_unsat_publication
    (pathContract intendedArchivedArtifact checkedProof originalEmptyClause :
      Prop) : Prop :=
  ay_apcg_conj pathContract
    (ay_apcg_conj intendedArchivedArtifact
      (ay_apcg_conj checkedProof originalEmptyClause))

def ay_apcg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_apcg_conj reason (ay_apcg_conj fallbackPath auditTrail)

def ay_apcg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_apcg_conj reason
    (ay_apcg_conj (satFact -> False) (unsatFact -> False))

def ay_apcg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_apcg_conj reason
    (ay_apcg_conj fallbackPath recomputeObligation)

def ay_apcg_path_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_apcg_conj
    (ay_apcg_blocked_publication satFact unsatFact reason)
    (ay_apcg_recompute reason fallbackPath recomputeObligation)

theorem ay_apcg_conj_intro (left right : Prop) :
    left -> right -> ay_apcg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_apcg_conj_left (left right : Prop) :
    ay_apcg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_apcg_conj_right (left right : Prop) :
    ay_apcg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_apcg_disj_left (left right : Prop) :
    left -> ay_apcg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_apcg_disj_right (left right : Prop) :
    right -> ay_apcg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_apcg_path_contract_intro
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    archiveManifest -> canonicalArtifactPathMap -> pathNormalizationWitness ->
    symlinkEscapeExclusionWitness -> modelProofArtifactDigest ->
    checkerTranscript -> benchmarkFingerprint -> solverBuildEvidence ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_apcg_path_contract archiveManifest canonicalArtifactPathMap
      pathNormalizationWitness symlinkEscapeExclusionWitness
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript :=
  fun archiveProof pathProof normalizationProof exclusionProof artifactProof
      checkerProof fingerprintProof buildProof fallbackProof auditProof result
      build =>
    build archiveProof pathProof normalizationProof exclusionProof
      artifactProof checkerProof fingerprintProof buildProof fallbackProof
      auditProof

theorem ay_apcg_contract_archive
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apcg_path_contract archiveManifest canonicalArtifactPathMap
      pathNormalizationWitness symlinkEscapeExclusionWitness
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun archiveProof _pathProof _normalizationProof _exclusionProof
          _artifactProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_apcg_contract_path_map
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apcg_path_contract archiveManifest canonicalArtifactPathMap
      pathNormalizationWitness symlinkEscapeExclusionWitness
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript ->
    canonicalArtifactPathMap :=
  fun contract =>
    contract canonicalArtifactPathMap
      (fun _archiveProof pathProof _normalizationProof _exclusionProof
          _artifactProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => pathProof)

theorem ay_apcg_contract_normalization
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apcg_path_contract archiveManifest canonicalArtifactPathMap
      pathNormalizationWitness symlinkEscapeExclusionWitness
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript ->
    pathNormalizationWitness :=
  fun contract =>
    contract pathNormalizationWitness
      (fun _archiveProof _pathProof normalizationProof _exclusionProof
          _artifactProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => normalizationProof)

theorem ay_apcg_contract_symlink_exclusion
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apcg_path_contract archiveManifest canonicalArtifactPathMap
      pathNormalizationWitness symlinkEscapeExclusionWitness
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript ->
    symlinkEscapeExclusionWitness :=
  fun contract =>
    contract symlinkEscapeExclusionWitness
      (fun _archiveProof _pathProof _normalizationProof exclusionProof
          _artifactProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => exclusionProof)

theorem ay_apcg_contract_artifact
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apcg_path_contract archiveManifest canonicalArtifactPathMap
      pathNormalizationWitness symlinkEscapeExclusionWitness
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _archiveProof _pathProof _normalizationProof _exclusionProof
          artifactProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => artifactProof)

theorem ay_apcg_contract_checker
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apcg_path_contract archiveManifest canonicalArtifactPathMap
      pathNormalizationWitness symlinkEscapeExclusionWitness
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _archiveProof _pathProof _normalizationProof _exclusionProof
          _artifactProof checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => checkerProof)

theorem ay_apcg_contract_fingerprint
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apcg_path_contract archiveManifest canonicalArtifactPathMap
      pathNormalizationWitness symlinkEscapeExclusionWitness
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _archiveProof _pathProof _normalizationProof _exclusionProof
          _artifactProof _checkerProof fingerprintProof _buildProof
          _fallbackProof _auditProof => fingerprintProof)

theorem ay_apcg_contract_build
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apcg_path_contract archiveManifest canonicalArtifactPathMap
      pathNormalizationWitness symlinkEscapeExclusionWitness
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _archiveProof _pathProof _normalizationProof _exclusionProof
          _artifactProof _checkerProof _fingerprintProof buildProof
          _fallbackProof _auditProof => buildProof)

theorem ay_apcg_contract_fallback
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apcg_path_contract archiveManifest canonicalArtifactPathMap
      pathNormalizationWitness symlinkEscapeExclusionWitness
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _archiveProof _pathProof _normalizationProof _exclusionProof
          _artifactProof _checkerProof _fingerprintProof _buildProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_apcg_contract_audit
    (archiveManifest canonicalArtifactPathMap pathNormalizationWitness
      symlinkEscapeExclusionWitness modelProofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apcg_path_contract archiveManifest canonicalArtifactPathMap
      pathNormalizationWitness symlinkEscapeExclusionWitness
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _archiveProof _pathProof _normalizationProof _exclusionProof
          _artifactProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof auditProof => auditProof)

theorem ay_apcg_sat_publication_intro
    (pathContract intendedArchivedArtifact checkedModel originalModel :
      Prop) :
    pathContract -> intendedArchivedArtifact -> checkedModel ->
    originalModel ->
    ay_apcg_sat_publication pathContract intendedArchivedArtifact
      checkedModel originalModel :=
  fun contractProof artifactProof modelProof originalProof =>
    ay_apcg_conj_intro pathContract
      (ay_apcg_conj intendedArchivedArtifact
        (ay_apcg_conj checkedModel originalModel))
      contractProof
      (ay_apcg_conj_intro intendedArchivedArtifact
        (ay_apcg_conj checkedModel originalModel)
        artifactProof
        (ay_apcg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_apcg_unsat_publication_intro
    (pathContract intendedArchivedArtifact checkedProof originalEmptyClause :
      Prop) :
    pathContract -> intendedArchivedArtifact -> checkedProof ->
    originalEmptyClause ->
    ay_apcg_unsat_publication pathContract intendedArchivedArtifact
      checkedProof originalEmptyClause :=
  fun contractProof artifactProof proofProof originalProof =>
    ay_apcg_conj_intro pathContract
      (ay_apcg_conj intendedArchivedArtifact
        (ay_apcg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_apcg_conj_intro intendedArchivedArtifact
        (ay_apcg_conj checkedProof originalEmptyClause)
        artifactProof
        (ay_apcg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_apcg_sat_publication_original_model
    (pathContract intendedArchivedArtifact checkedModel originalModel :
      Prop) :
    ay_apcg_sat_publication pathContract intendedArchivedArtifact checkedModel
      originalModel ->
    originalModel :=
  fun publication =>
    ay_apcg_conj_right checkedModel originalModel
      (ay_apcg_conj_right intendedArchivedArtifact
        (ay_apcg_conj checkedModel originalModel)
        (ay_apcg_conj_right pathContract
          (ay_apcg_conj intendedArchivedArtifact
            (ay_apcg_conj checkedModel originalModel))
          publication))

theorem ay_apcg_unsat_publication_original_empty_clause
    (pathContract intendedArchivedArtifact checkedProof originalEmptyClause :
      Prop) :
    ay_apcg_unsat_publication pathContract intendedArchivedArtifact
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_apcg_conj_right checkedProof originalEmptyClause
      (ay_apcg_conj_right intendedArchivedArtifact
        (ay_apcg_conj checkedProof originalEmptyClause)
        (ay_apcg_conj_right pathContract
          (ay_apcg_conj intendedArchivedArtifact
            (ay_apcg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_apcg_accepted_canonicalization_ties_sat_to_artifact
    (pathContract intendedArchivedArtifact checkedModel originalModel :
      Prop) :
    ay_apcg_sat_publication pathContract intendedArchivedArtifact checkedModel
      originalModel ->
    ay_apcg_public_result originalModel False False :=
  fun publication =>
    ay_apcg_disj_left originalModel (ay_apcg_disj False False)
      (ay_apcg_sat_publication_original_model pathContract
        intendedArchivedArtifact checkedModel originalModel publication)

theorem ay_apcg_accepted_canonicalization_ties_unsat_to_artifact
    (pathContract intendedArchivedArtifact checkedProof originalEmptyClause :
      Prop) :
    ay_apcg_unsat_publication pathContract intendedArchivedArtifact
      checkedProof originalEmptyClause ->
    ay_apcg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_apcg_disj_right False (ay_apcg_disj originalEmptyClause False)
      (ay_apcg_disj_left originalEmptyClause False
        (ay_apcg_unsat_publication_original_empty_clause pathContract
          intendedArchivedArtifact checkedProof originalEmptyClause
          publication))

theorem ay_apcg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_apcg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_apcg_conj_intro reason (ay_apcg_conj fallbackPath auditTrail)
      reasonProof
      (ay_apcg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_apcg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_apcg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_apcg_conj_intro reason
      (ay_apcg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_apcg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_apcg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_apcg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_apcg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_apcg_conj_right reason
        (ay_apcg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_apcg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_apcg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_apcg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_apcg_conj_right reason
        (ay_apcg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_apcg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_apcg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_apcg_conj_intro reason
      (ay_apcg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_apcg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_apcg_path_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_apcg_blocked_publication satFact unsatFact reason ->
    ay_apcg_recompute reason fallbackPath recomputeObligation ->
    ay_apcg_path_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_apcg_conj_intro
      (ay_apcg_blocked_publication satFact unsatFact reason)
      (ay_apcg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_apcg_path_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_apcg_path_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_apcg_blocked_publication_no_sat satFact unsatFact reason
      (ay_apcg_conj_left
        (ay_apcg_blocked_publication satFact unsatFact reason)
        (ay_apcg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_apcg_path_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_apcg_path_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_apcg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_apcg_conj_left
        (ay_apcg_blocked_publication satFact unsatFact reason)
        (ay_apcg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_apcg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apcg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_apcg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_apcg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apcg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_apcg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apcg_path_mismatch_forces_no_claim
    (satFact unsatFact pathMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    pathMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apcg_no_claim pathMismatch fallbackPath auditTrail :=
  ay_apcg_mismatch_forces_no_claim satFact unsatFact pathMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apcg_normalization_mismatch_forces_no_claim
    (satFact unsatFact normalizationMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    normalizationMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apcg_no_claim normalizationMismatch fallbackPath auditTrail :=
  ay_apcg_mismatch_forces_no_claim satFact unsatFact normalizationMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apcg_symlink_mismatch_forces_no_claim
    (satFact unsatFact symlinkMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    symlinkMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apcg_no_claim symlinkMismatch fallbackPath auditTrail :=
  ay_apcg_mismatch_forces_no_claim satFact unsatFact symlinkMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apcg_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    digestMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apcg_no_claim digestMismatch fallbackPath auditTrail :=
  ay_apcg_mismatch_forces_no_claim satFact unsatFact digestMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apcg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apcg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_apcg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apcg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apcg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_apcg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apcg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apcg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_apcg_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apcg_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apcg_no_claim auditMismatch fallbackPath auditTrail :=
  ay_apcg_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apcg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_apcg_path_failure satFact unsatFact fallbackActivation fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_apcg_path_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_apcg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_apcg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_apcg_failed_path_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_apcg_path_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_apcg_path_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_apcg_failed_path_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_apcg_path_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_apcg_path_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_apcg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_apcg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_apcg_conj_left reason (ay_apcg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_apcg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_apcg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_apcg_conj_left reason (ay_apcg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
