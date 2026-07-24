-- SAT-COMP validator archive extraction sandbox guard core.
--
-- Public SAT/UNSAT claims require archive manifest, normalized path ledger,
-- no-path-traversal witness, extracted artifact digest, checker transcript,
-- benchmark fingerprint, solver build evidence, no-claim fallback, and audit
-- transcript to agree.

def ay_aesg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_aesg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_aesg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_aesg_disj satFact (ay_aesg_disj unsatFact noClaimFact)

def ay_aesg_sandbox_contract
    (archiveManifest normalizedPathLedger noPathTraversalWitness
      extractedArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence noClaimFallback auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (archiveManifest -> normalizedPathLedger -> noPathTraversalWitness ->
      extractedArtifactDigest -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> noClaimFallback -> auditTranscript -> result) ->
    result

def ay_aesg_sat_publication
    (sandboxContract acceptedSandboxExtraction modelEvidence originalModel :
      Prop) : Prop :=
  ay_aesg_conj sandboxContract
    (ay_aesg_conj acceptedSandboxExtraction
      (ay_aesg_conj modelEvidence originalModel))

def ay_aesg_unsat_publication
    (sandboxContract acceptedSandboxExtraction proofEvidence
      originalEmptyClause : Prop) : Prop :=
  ay_aesg_conj sandboxContract
    (ay_aesg_conj acceptedSandboxExtraction
      (ay_aesg_conj proofEvidence originalEmptyClause))

def ay_aesg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_aesg_conj reason (ay_aesg_conj fallbackPath auditTrail)

def ay_aesg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_aesg_conj reason
    (ay_aesg_conj (satFact -> False) (unsatFact -> False))

def ay_aesg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_aesg_conj reason
    (ay_aesg_conj fallbackPath recomputeObligation)

def ay_aesg_sandbox_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_aesg_conj
    (ay_aesg_blocked_publication satFact unsatFact reason)
    (ay_aesg_recompute reason fallbackPath recomputeObligation)

theorem ay_aesg_conj_intro (left right : Prop) :
    left -> right -> ay_aesg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_aesg_conj_left (left right : Prop) :
    ay_aesg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_aesg_conj_right (left right : Prop) :
    ay_aesg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_aesg_disj_left (left right : Prop) :
    left -> ay_aesg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_aesg_disj_right (left right : Prop) :
    right -> ay_aesg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_aesg_sandbox_contract_intro
    (archiveManifest normalizedPathLedger noPathTraversalWitness
      extractedArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence noClaimFallback auditTranscript : Prop) :
    archiveManifest -> normalizedPathLedger -> noPathTraversalWitness ->
    extractedArtifactDigest -> checkerTranscript -> benchmarkFingerprint ->
    solverBuildEvidence -> noClaimFallback -> auditTranscript ->
    ay_aesg_sandbox_contract archiveManifest normalizedPathLedger
      noPathTraversalWitness extractedArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence noClaimFallback
      auditTranscript :=
  fun archiveProof ledgerProof traversalProof digestProof checkerProof
      fingerprintProof buildProof fallbackProof auditProof result build =>
    build archiveProof ledgerProof traversalProof digestProof checkerProof
      fingerprintProof buildProof fallbackProof auditProof

theorem ay_aesg_sandbox_contract_archive
    (archiveManifest normalizedPathLedger noPathTraversalWitness
      extractedArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence noClaimFallback auditTranscript : Prop) :
    ay_aesg_sandbox_contract archiveManifest normalizedPathLedger
      noPathTraversalWitness extractedArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence noClaimFallback
      auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun archiveProof _ledgerProof _traversalProof _digestProof
          _checkerProof _fingerprintProof _buildProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_aesg_sandbox_contract_ledger
    (archiveManifest normalizedPathLedger noPathTraversalWitness
      extractedArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence noClaimFallback auditTranscript : Prop) :
    ay_aesg_sandbox_contract archiveManifest normalizedPathLedger
      noPathTraversalWitness extractedArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence noClaimFallback
      auditTranscript ->
    normalizedPathLedger :=
  fun contract =>
    contract normalizedPathLedger
      (fun _archiveProof ledgerProof _traversalProof _digestProof
          _checkerProof _fingerprintProof _buildProof _fallbackProof
          _auditProof => ledgerProof)

theorem ay_aesg_sandbox_contract_no_traversal
    (archiveManifest normalizedPathLedger noPathTraversalWitness
      extractedArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence noClaimFallback auditTranscript : Prop) :
    ay_aesg_sandbox_contract archiveManifest normalizedPathLedger
      noPathTraversalWitness extractedArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence noClaimFallback
      auditTranscript ->
    noPathTraversalWitness :=
  fun contract =>
    contract noPathTraversalWitness
      (fun _archiveProof _ledgerProof traversalProof _digestProof
          _checkerProof _fingerprintProof _buildProof _fallbackProof
          _auditProof => traversalProof)

theorem ay_aesg_sandbox_contract_digest
    (archiveManifest normalizedPathLedger noPathTraversalWitness
      extractedArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence noClaimFallback auditTranscript : Prop) :
    ay_aesg_sandbox_contract archiveManifest normalizedPathLedger
      noPathTraversalWitness extractedArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence noClaimFallback
      auditTranscript ->
    extractedArtifactDigest :=
  fun contract =>
    contract extractedArtifactDigest
      (fun _archiveProof _ledgerProof _traversalProof digestProof
          _checkerProof _fingerprintProof _buildProof _fallbackProof
          _auditProof => digestProof)

theorem ay_aesg_sandbox_contract_checker
    (archiveManifest normalizedPathLedger noPathTraversalWitness
      extractedArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence noClaimFallback auditTranscript : Prop) :
    ay_aesg_sandbox_contract archiveManifest normalizedPathLedger
      noPathTraversalWitness extractedArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence noClaimFallback
      auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _archiveProof _ledgerProof _traversalProof _digestProof
          checkerProof _fingerprintProof _buildProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_aesg_sandbox_contract_fingerprint
    (archiveManifest normalizedPathLedger noPathTraversalWitness
      extractedArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence noClaimFallback auditTranscript : Prop) :
    ay_aesg_sandbox_contract archiveManifest normalizedPathLedger
      noPathTraversalWitness extractedArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence noClaimFallback
      auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _archiveProof _ledgerProof _traversalProof _digestProof
          _checkerProof fingerprintProof _buildProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_aesg_sandbox_contract_build
    (archiveManifest normalizedPathLedger noPathTraversalWitness
      extractedArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence noClaimFallback auditTranscript : Prop) :
    ay_aesg_sandbox_contract archiveManifest normalizedPathLedger
      noPathTraversalWitness extractedArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence noClaimFallback
      auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _archiveProof _ledgerProof _traversalProof _digestProof
          _checkerProof _fingerprintProof buildProof _fallbackProof
          _auditProof => buildProof)

theorem ay_aesg_sandbox_contract_fallback
    (archiveManifest normalizedPathLedger noPathTraversalWitness
      extractedArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence noClaimFallback auditTranscript : Prop) :
    ay_aesg_sandbox_contract archiveManifest normalizedPathLedger
      noPathTraversalWitness extractedArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence noClaimFallback
      auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _archiveProof _ledgerProof _traversalProof _digestProof
          _checkerProof _fingerprintProof _buildProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_aesg_sandbox_contract_audit
    (archiveManifest normalizedPathLedger noPathTraversalWitness
      extractedArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence noClaimFallback auditTranscript : Prop) :
    ay_aesg_sandbox_contract archiveManifest normalizedPathLedger
      noPathTraversalWitness extractedArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence noClaimFallback
      auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _archiveProof _ledgerProof _traversalProof _digestProof
          _checkerProof _fingerprintProof _buildProof _fallbackProof
          auditProof => auditProof)

theorem ay_aesg_sat_publication_intro
    (sandboxContract acceptedSandboxExtraction modelEvidence originalModel :
      Prop) :
    sandboxContract -> acceptedSandboxExtraction -> modelEvidence ->
    originalModel ->
    ay_aesg_sat_publication sandboxContract acceptedSandboxExtraction
      modelEvidence originalModel :=
  fun contractProof extractionProof modelProof originalProof =>
    ay_aesg_conj_intro sandboxContract
      (ay_aesg_conj acceptedSandboxExtraction
        (ay_aesg_conj modelEvidence originalModel)) contractProof
      (ay_aesg_conj_intro acceptedSandboxExtraction
        (ay_aesg_conj modelEvidence originalModel) extractionProof
        (ay_aesg_conj_intro modelEvidence originalModel modelProof
          originalProof))

theorem ay_aesg_sat_publication_extraction
    (sandboxContract acceptedSandboxExtraction modelEvidence originalModel :
      Prop) :
    ay_aesg_sat_publication sandboxContract acceptedSandboxExtraction
      modelEvidence originalModel ->
    acceptedSandboxExtraction :=
  fun publication =>
    ay_aesg_conj_left acceptedSandboxExtraction
      (ay_aesg_conj modelEvidence originalModel)
      (ay_aesg_conj_right sandboxContract
        (ay_aesg_conj acceptedSandboxExtraction
          (ay_aesg_conj modelEvidence originalModel)) publication)

theorem ay_aesg_sat_publication_original_model
    (sandboxContract acceptedSandboxExtraction modelEvidence originalModel :
      Prop) :
    ay_aesg_sat_publication sandboxContract acceptedSandboxExtraction
      modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_aesg_conj_right modelEvidence originalModel
      (ay_aesg_conj_right acceptedSandboxExtraction
        (ay_aesg_conj modelEvidence originalModel)
        (ay_aesg_conj_right sandboxContract
          (ay_aesg_conj acceptedSandboxExtraction
            (ay_aesg_conj modelEvidence originalModel)) publication))

theorem ay_aesg_unsat_publication_intro
    (sandboxContract acceptedSandboxExtraction proofEvidence
      originalEmptyClause : Prop) :
    sandboxContract -> acceptedSandboxExtraction -> proofEvidence ->
    originalEmptyClause ->
    ay_aesg_unsat_publication sandboxContract acceptedSandboxExtraction
      proofEvidence originalEmptyClause :=
  fun contractProof extractionProof proofProof emptyProof =>
    ay_aesg_conj_intro sandboxContract
      (ay_aesg_conj acceptedSandboxExtraction
        (ay_aesg_conj proofEvidence originalEmptyClause)) contractProof
      (ay_aesg_conj_intro acceptedSandboxExtraction
        (ay_aesg_conj proofEvidence originalEmptyClause) extractionProof
        (ay_aesg_conj_intro proofEvidence originalEmptyClause proofProof
          emptyProof))

theorem ay_aesg_unsat_publication_extraction
    (sandboxContract acceptedSandboxExtraction proofEvidence
      originalEmptyClause : Prop) :
    ay_aesg_unsat_publication sandboxContract acceptedSandboxExtraction
      proofEvidence originalEmptyClause ->
    acceptedSandboxExtraction :=
  fun publication =>
    ay_aesg_conj_left acceptedSandboxExtraction
      (ay_aesg_conj proofEvidence originalEmptyClause)
      (ay_aesg_conj_right sandboxContract
        (ay_aesg_conj acceptedSandboxExtraction
          (ay_aesg_conj proofEvidence originalEmptyClause)) publication)

theorem ay_aesg_unsat_publication_original_empty_clause
    (sandboxContract acceptedSandboxExtraction proofEvidence
      originalEmptyClause : Prop) :
    ay_aesg_unsat_publication sandboxContract acceptedSandboxExtraction
      proofEvidence originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_aesg_conj_right proofEvidence originalEmptyClause
      (ay_aesg_conj_right acceptedSandboxExtraction
        (ay_aesg_conj proofEvidence originalEmptyClause)
        (ay_aesg_conj_right sandboxContract
          (ay_aesg_conj acceptedSandboxExtraction
            (ay_aesg_conj proofEvidence originalEmptyClause)) publication))

theorem ay_aesg_accepted_extraction_sat_passes_publication
    (sandboxContract acceptedSandboxExtraction modelEvidence originalModel :
      Prop) :
    ay_aesg_sat_publication sandboxContract acceptedSandboxExtraction
      modelEvidence originalModel ->
    ay_aesg_conj acceptedSandboxExtraction originalModel :=
  fun publication =>
    ay_aesg_conj_intro acceptedSandboxExtraction originalModel
      (ay_aesg_sat_publication_extraction sandboxContract
        acceptedSandboxExtraction modelEvidence originalModel publication)
      (ay_aesg_sat_publication_original_model sandboxContract
        acceptedSandboxExtraction modelEvidence originalModel publication)

theorem ay_aesg_accepted_extraction_unsat_passes_publication
    (sandboxContract acceptedSandboxExtraction proofEvidence
      originalEmptyClause : Prop) :
    ay_aesg_unsat_publication sandboxContract acceptedSandboxExtraction
      proofEvidence originalEmptyClause ->
    ay_aesg_conj acceptedSandboxExtraction originalEmptyClause :=
  fun publication =>
    ay_aesg_conj_intro acceptedSandboxExtraction originalEmptyClause
      (ay_aesg_unsat_publication_extraction sandboxContract
        acceptedSandboxExtraction proofEvidence originalEmptyClause
        publication)
      (ay_aesg_unsat_publication_original_empty_clause sandboxContract
        acceptedSandboxExtraction proofEvidence originalEmptyClause
        publication)

theorem ay_aesg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_aesg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_aesg_conj_intro reason (ay_aesg_conj fallbackPath auditTrail)
      reasonProof
      (ay_aesg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_aesg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_aesg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_aesg_conj_intro reason
      (ay_aesg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_aesg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_aesg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_aesg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_aesg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_aesg_conj_right reason
        (ay_aesg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_aesg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_aesg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_aesg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_aesg_conj_right reason
        (ay_aesg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_aesg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_aesg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_aesg_conj_intro reason
      (ay_aesg_conj fallbackPath recomputeObligation) reasonProof
      (ay_aesg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_aesg_sandbox_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_aesg_sandbox_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_aesg_conj_intro
      (ay_aesg_blocked_publication satFact unsatFact reason)
      (ay_aesg_recompute reason fallbackPath recomputeObligation)
      (ay_aesg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_aesg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_aesg_sandbox_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_aesg_sandbox_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_aesg_blocked_publication_no_sat satFact unsatFact reason
      (ay_aesg_conj_left
        (ay_aesg_blocked_publication satFact unsatFact reason)
        (ay_aesg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_aesg_sandbox_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_aesg_sandbox_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_aesg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_aesg_conj_left
        (ay_aesg_blocked_publication satFact unsatFact reason)
        (ay_aesg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_aesg_sandbox_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_aesg_sandbox_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_aesg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_aesg_conj_right
      (ay_aesg_blocked_publication satFact unsatFact reason)
      (ay_aesg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_aesg_path_traversal_forces_no_claim
    (satFact unsatFact pathTraversal fallbackPath auditTrail
      recomputeObligation : Prop) :
    pathTraversal -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_aesg_no_claim pathTraversal fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_aesg_no_claim_intro pathTraversal fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_aesg_duplicate_normalized_paths_force_no_claim
    (satFact unsatFact duplicatePaths fallbackPath auditTrail
      recomputeObligation : Prop) :
    duplicatePaths -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_aesg_no_claim duplicatePaths fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_aesg_no_claim_intro duplicatePaths fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_aesg_missing_artifact_forces_no_claim
    (satFact unsatFact missingArtifact fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingArtifact -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_aesg_no_claim missingArtifact fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_aesg_no_claim_intro missingArtifact fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_aesg_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    digestMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_aesg_no_claim digestMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_aesg_no_claim_intro digestMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_aesg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_aesg_no_claim checkerMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_aesg_no_claim_intro checkerMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_aesg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_aesg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_aesg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_aesg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_aesg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_aesg_no_claim_intro buildMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_aesg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_aesg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_aesg_no_claim_intro archiveMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_aesg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivated fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_aesg_no_claim fallbackActivated fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_aesg_no_claim_intro fallbackActivated fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_aesg_failed_sandbox_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_aesg_sandbox_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_aesg_sandbox_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_aesg_failed_sandbox_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_aesg_sandbox_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_aesg_sandbox_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_aesg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_aesg_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_aesg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_aesg_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
