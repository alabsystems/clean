-- SAT-COMP validator filesystem case-sensitivity guard core.
--
-- Public SAT/UNSAT claims require archive evidence, canonical paths,
-- filesystem case policy, artifact digest, checker transcript, benchmark
-- fingerprint, solver build evidence, fallback, and audit transcript to agree.

def ay_fscg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_fscg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_fscg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_fscg_disj satFact (ay_fscg_disj unsatFact noClaimFact)

def ay_fscg_filesystem_case_contract
    (archiveManifest canonicalPathMap filesystemCasePolicyWitness
      artifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (archiveManifest -> canonicalPathMap -> filesystemCasePolicyWitness ->
      artifactDigest -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> fallbackNoClaimPath -> auditTranscript ->
      result) ->
    result

def ay_fscg_sat_publication
    (caseContract intendedArtifact checkedModel originalModel : Prop) :
    Prop :=
  ay_fscg_conj caseContract
    (ay_fscg_conj intendedArtifact
      (ay_fscg_conj checkedModel originalModel))

def ay_fscg_unsat_publication
    (caseContract intendedArtifact checkedProof originalEmptyClause : Prop) :
    Prop :=
  ay_fscg_conj caseContract
    (ay_fscg_conj intendedArtifact
      (ay_fscg_conj checkedProof originalEmptyClause))

def ay_fscg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_fscg_conj reason (ay_fscg_conj fallbackPath auditTrail)

def ay_fscg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_fscg_conj reason
    (ay_fscg_conj (satFact -> False) (unsatFact -> False))

def ay_fscg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_fscg_conj reason
    (ay_fscg_conj fallbackPath recomputeObligation)

def ay_fscg_case_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_fscg_conj
    (ay_fscg_blocked_publication satFact unsatFact reason)
    (ay_fscg_recompute reason fallbackPath recomputeObligation)

theorem ay_fscg_conj_intro (left right : Prop) :
    left -> right -> ay_fscg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_fscg_conj_left (left right : Prop) :
    ay_fscg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_fscg_conj_right (left right : Prop) :
    ay_fscg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_fscg_disj_left (left right : Prop) :
    left -> ay_fscg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_fscg_disj_right (left right : Prop) :
    right -> ay_fscg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_fscg_filesystem_case_contract_intro
    (archiveManifest canonicalPathMap filesystemCasePolicyWitness
      artifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    archiveManifest -> canonicalPathMap -> filesystemCasePolicyWitness ->
    artifactDigest -> checkerTranscript -> benchmarkFingerprint ->
    solverBuildEvidence -> fallbackNoClaimPath -> auditTranscript ->
    ay_fscg_filesystem_case_contract archiveManifest canonicalPathMap
      filesystemCasePolicyWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript :=
  fun archiveProof pathProof caseProof artifactProof checkerProof
      fingerprintProof buildProof fallbackProof auditProof result build =>
    build archiveProof pathProof caseProof artifactProof checkerProof
      fingerprintProof buildProof fallbackProof auditProof

theorem ay_fscg_contract_archive
    (archiveManifest canonicalPathMap filesystemCasePolicyWitness
      artifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_fscg_filesystem_case_contract archiveManifest canonicalPathMap
      filesystemCasePolicyWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun archiveProof _pathProof _caseProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _fallbackProof _auditProof =>
        archiveProof)

theorem ay_fscg_contract_path
    (archiveManifest canonicalPathMap filesystemCasePolicyWitness
      artifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_fscg_filesystem_case_contract archiveManifest canonicalPathMap
      filesystemCasePolicyWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    canonicalPathMap :=
  fun contract =>
    contract canonicalPathMap
      (fun _archiveProof pathProof _caseProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _fallbackProof _auditProof =>
        pathProof)

theorem ay_fscg_contract_case_policy
    (archiveManifest canonicalPathMap filesystemCasePolicyWitness
      artifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_fscg_filesystem_case_contract archiveManifest canonicalPathMap
      filesystemCasePolicyWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    filesystemCasePolicyWitness :=
  fun contract =>
    contract filesystemCasePolicyWitness
      (fun _archiveProof _pathProof caseProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _fallbackProof _auditProof =>
        caseProof)

theorem ay_fscg_contract_artifact
    (archiveManifest canonicalPathMap filesystemCasePolicyWitness
      artifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_fscg_filesystem_case_contract archiveManifest canonicalPathMap
      filesystemCasePolicyWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    artifactDigest :=
  fun contract =>
    contract artifactDigest
      (fun _archiveProof _pathProof _caseProof artifactProof _checkerProof
          _fingerprintProof _buildProof _fallbackProof _auditProof =>
        artifactProof)

theorem ay_fscg_contract_checker
    (archiveManifest canonicalPathMap filesystemCasePolicyWitness
      artifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_fscg_filesystem_case_contract archiveManifest canonicalPathMap
      filesystemCasePolicyWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _archiveProof _pathProof _caseProof _artifactProof checkerProof
          _fingerprintProof _buildProof _fallbackProof _auditProof =>
        checkerProof)

theorem ay_fscg_contract_fingerprint
    (archiveManifest canonicalPathMap filesystemCasePolicyWitness
      artifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_fscg_filesystem_case_contract archiveManifest canonicalPathMap
      filesystemCasePolicyWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _archiveProof _pathProof _caseProof _artifactProof _checkerProof
          fingerprintProof _buildProof _fallbackProof _auditProof =>
        fingerprintProof)

theorem ay_fscg_contract_build
    (archiveManifest canonicalPathMap filesystemCasePolicyWitness
      artifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_fscg_filesystem_case_contract archiveManifest canonicalPathMap
      filesystemCasePolicyWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _archiveProof _pathProof _caseProof _artifactProof _checkerProof
          _fingerprintProof buildProof _fallbackProof _auditProof =>
        buildProof)

theorem ay_fscg_contract_fallback
    (archiveManifest canonicalPathMap filesystemCasePolicyWitness
      artifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_fscg_filesystem_case_contract archiveManifest canonicalPathMap
      filesystemCasePolicyWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _archiveProof _pathProof _caseProof _artifactProof _checkerProof
          _fingerprintProof _buildProof fallbackProof _auditProof =>
        fallbackProof)

theorem ay_fscg_contract_audit
    (archiveManifest canonicalPathMap filesystemCasePolicyWitness
      artifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_fscg_filesystem_case_contract archiveManifest canonicalPathMap
      filesystemCasePolicyWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _archiveProof _pathProof _caseProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _fallbackProof auditProof =>
        auditProof)

theorem ay_fscg_sat_publication_intro
    (caseContract intendedArtifact checkedModel originalModel : Prop) :
    caseContract -> intendedArtifact -> checkedModel -> originalModel ->
    ay_fscg_sat_publication caseContract intendedArtifact checkedModel
      originalModel :=
  fun contractProof artifactProof modelProof originalProof =>
    ay_fscg_conj_intro caseContract
      (ay_fscg_conj intendedArtifact
        (ay_fscg_conj checkedModel originalModel))
      contractProof
      (ay_fscg_conj_intro intendedArtifact
        (ay_fscg_conj checkedModel originalModel)
        artifactProof
        (ay_fscg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_fscg_unsat_publication_intro
    (caseContract intendedArtifact checkedProof originalEmptyClause : Prop) :
    caseContract -> intendedArtifact -> checkedProof -> originalEmptyClause ->
    ay_fscg_unsat_publication caseContract intendedArtifact checkedProof
      originalEmptyClause :=
  fun contractProof artifactProof proofProof originalProof =>
    ay_fscg_conj_intro caseContract
      (ay_fscg_conj intendedArtifact
        (ay_fscg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_fscg_conj_intro intendedArtifact
        (ay_fscg_conj checkedProof originalEmptyClause)
        artifactProof
        (ay_fscg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_fscg_sat_publication_original_model
    (caseContract intendedArtifact checkedModel originalModel : Prop) :
    ay_fscg_sat_publication caseContract intendedArtifact checkedModel
      originalModel ->
    originalModel :=
  fun publication =>
    ay_fscg_conj_right checkedModel originalModel
      (ay_fscg_conj_right intendedArtifact
        (ay_fscg_conj checkedModel originalModel)
        (ay_fscg_conj_right caseContract
          (ay_fscg_conj intendedArtifact
            (ay_fscg_conj checkedModel originalModel))
          publication))

theorem ay_fscg_unsat_publication_original_empty_clause
    (caseContract intendedArtifact checkedProof originalEmptyClause : Prop) :
    ay_fscg_unsat_publication caseContract intendedArtifact checkedProof
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_fscg_conj_right checkedProof originalEmptyClause
      (ay_fscg_conj_right intendedArtifact
        (ay_fscg_conj checkedProof originalEmptyClause)
        (ay_fscg_conj_right caseContract
          (ay_fscg_conj intendedArtifact
            (ay_fscg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_fscg_accepted_case_ties_sat_to_intended_artifact
    (caseContract intendedArtifact checkedModel originalModel : Prop) :
    ay_fscg_sat_publication caseContract intendedArtifact checkedModel
      originalModel ->
    ay_fscg_public_result originalModel False False :=
  fun publication =>
    ay_fscg_disj_left originalModel (ay_fscg_disj False False)
      (ay_fscg_sat_publication_original_model caseContract intendedArtifact
        checkedModel originalModel publication)

theorem ay_fscg_accepted_case_ties_unsat_to_intended_artifact
    (caseContract intendedArtifact checkedProof originalEmptyClause : Prop) :
    ay_fscg_unsat_publication caseContract intendedArtifact checkedProof
      originalEmptyClause ->
    ay_fscg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_fscg_disj_right False (ay_fscg_disj originalEmptyClause False)
      (ay_fscg_disj_left originalEmptyClause False
        (ay_fscg_unsat_publication_original_empty_clause caseContract
          intendedArtifact checkedProof originalEmptyClause publication))

theorem ay_fscg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_fscg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_fscg_conj_intro reason (ay_fscg_conj fallbackPath auditTrail)
      reasonProof
      (ay_fscg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_fscg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_fscg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_fscg_conj_intro reason
      (ay_fscg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_fscg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_fscg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_fscg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_fscg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_fscg_conj_right reason
        (ay_fscg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_fscg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_fscg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_fscg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_fscg_conj_right reason
        (ay_fscg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_fscg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_fscg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_fscg_conj_intro reason
      (ay_fscg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_fscg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_fscg_case_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_fscg_blocked_publication satFact unsatFact reason ->
    ay_fscg_recompute reason fallbackPath recomputeObligation ->
    ay_fscg_case_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_fscg_conj_intro
      (ay_fscg_blocked_publication satFact unsatFact reason)
      (ay_fscg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_fscg_case_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_fscg_case_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_fscg_blocked_publication_no_sat satFact unsatFact reason
      (ay_fscg_conj_left
        (ay_fscg_blocked_publication satFact unsatFact reason)
        (ay_fscg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_fscg_case_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_fscg_case_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_fscg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_fscg_conj_left
        (ay_fscg_blocked_publication satFact unsatFact reason)
        (ay_fscg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_fscg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_fscg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_fscg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_fscg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_fscg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_fscg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_fscg_path_mismatch_forces_no_claim
    (satFact unsatFact pathMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    pathMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_fscg_no_claim pathMismatch fallbackPath auditTrail :=
  ay_fscg_mismatch_forces_no_claim satFact unsatFact pathMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_fscg_case_mismatch_forces_no_claim
    (satFact unsatFact caseMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    caseMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_fscg_no_claim caseMismatch fallbackPath auditTrail :=
  ay_fscg_mismatch_forces_no_claim satFact unsatFact caseMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_fscg_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    digestMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_fscg_no_claim digestMismatch fallbackPath auditTrail :=
  ay_fscg_mismatch_forces_no_claim satFact unsatFact digestMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_fscg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_fscg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_fscg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_fscg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_fscg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_fscg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_fscg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_fscg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_fscg_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_fscg_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_fscg_no_claim auditMismatch fallbackPath auditTrail :=
  ay_fscg_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_fscg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_fscg_case_failure satFact unsatFact fallbackActivation fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_fscg_case_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_fscg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_fscg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_fscg_failed_case_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_fscg_case_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_fscg_case_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_fscg_failed_case_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_fscg_case_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_fscg_case_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_fscg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_fscg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_fscg_conj_left reason (ay_fscg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_fscg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_fscg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_fscg_conj_left reason (ay_fscg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
