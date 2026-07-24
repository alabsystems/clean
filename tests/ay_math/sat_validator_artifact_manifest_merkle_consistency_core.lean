-- SAT-COMP validator artifact manifest Merkle consistency core.
--
-- Sequential-main result artifacts may be published only when archive
-- manifest, Merkle root, artifact digests, solver stdout/stderr digests,
-- certificate/model digest, benchmark fingerprint, checker transcript, build
-- configuration, submission manifest, and fallback/no-claim path agree.

def ay_vamm_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vamm_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vamm_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vamm_disj satFact (ay_vamm_disj unsatFact noClaimFact)

def ay_vamm_merkle_manifest_contract
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) : Prop :=
  forall result : Prop,
    (archiveManifest -> merkleRoot -> artifactDigests ->
      stdoutStderrDigests -> certificateOrModelDigest ->
      benchmarkFingerprint -> checkerTranscript -> buildConfiguration ->
      submissionManifest -> fallbackPath -> result) ->
    result

def ay_vamm_sat_publication
    (merkleContract modelEvidence originalModel : Prop) : Prop :=
  ay_vamm_conj merkleContract
    (ay_vamm_conj modelEvidence originalModel)

def ay_vamm_unsat_publication
    (merkleContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vamm_conj merkleContract
    (ay_vamm_conj proofEvidence originalEmptyClause)

def ay_vamm_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vamm_conj reason (ay_vamm_conj fallbackPath auditTrail)

def ay_vamm_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vamm_conj reason
    (ay_vamm_conj (satFact -> False) (unsatFact -> False))

def ay_vamm_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vamm_conj reason
    (ay_vamm_conj fallbackPath recomputeObligation)

def ay_vamm_merkle_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vamm_conj
    (ay_vamm_blocked_publication satFact unsatFact reason)
    (ay_vamm_recompute reason fallbackPath recomputeObligation)

theorem ay_vamm_conj_intro (left right : Prop) :
    left -> right -> ay_vamm_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vamm_conj_left (left right : Prop) :
    ay_vamm_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vamm_conj_right (left right : Prop) :
    ay_vamm_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vamm_disj_left (left right : Prop) :
    left -> ay_vamm_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vamm_disj_right (left right : Prop) :
    right -> ay_vamm_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vamm_merkle_manifest_contract_intro
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) :
    archiveManifest -> merkleRoot -> artifactDigests ->
    stdoutStderrDigests -> certificateOrModelDigest ->
    benchmarkFingerprint -> checkerTranscript -> buildConfiguration ->
    submissionManifest -> fallbackPath ->
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath :=
  fun archiveProof rootProof artifactProof logProof certificateProof
      fingerprintProof checkerProof buildProof submissionProof fallbackProof
      result build =>
    build archiveProof rootProof artifactProof logProof certificateProof
      fingerprintProof checkerProof buildProof submissionProof fallbackProof

theorem ay_vamm_merkle_manifest_contract_archive
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun archiveProof _rootProof _artifactProof _logProof
          _certificateProof _fingerprintProof _checkerProof _buildProof
          _submissionProof _fallbackProof => archiveProof)

theorem ay_vamm_merkle_manifest_contract_root
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    merkleRoot :=
  fun contract =>
    contract merkleRoot
      (fun _archiveProof rootProof _artifactProof _logProof
          _certificateProof _fingerprintProof _checkerProof _buildProof
          _submissionProof _fallbackProof => rootProof)

theorem ay_vamm_merkle_manifest_contract_artifacts
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    artifactDigests :=
  fun contract =>
    contract artifactDigests
      (fun _archiveProof _rootProof artifactProof _logProof
          _certificateProof _fingerprintProof _checkerProof _buildProof
          _submissionProof _fallbackProof => artifactProof)

theorem ay_vamm_merkle_manifest_contract_logs
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    stdoutStderrDigests :=
  fun contract =>
    contract stdoutStderrDigests
      (fun _archiveProof _rootProof _artifactProof logProof
          _certificateProof _fingerprintProof _checkerProof _buildProof
          _submissionProof _fallbackProof => logProof)

theorem ay_vamm_merkle_manifest_contract_certificate
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    certificateOrModelDigest :=
  fun contract =>
    contract certificateOrModelDigest
      (fun _archiveProof _rootProof _artifactProof _logProof
          certificateProof _fingerprintProof _checkerProof _buildProof
          _submissionProof _fallbackProof => certificateProof)

theorem ay_vamm_merkle_manifest_contract_fingerprint
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _archiveProof _rootProof _artifactProof _logProof
          _certificateProof fingerprintProof _checkerProof _buildProof
          _submissionProof _fallbackProof => fingerprintProof)

theorem ay_vamm_merkle_manifest_contract_checker
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _archiveProof _rootProof _artifactProof _logProof
          _certificateProof _fingerprintProof checkerProof _buildProof
          _submissionProof _fallbackProof => checkerProof)

theorem ay_vamm_merkle_manifest_contract_build
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    buildConfiguration :=
  fun contract =>
    contract buildConfiguration
      (fun _archiveProof _rootProof _artifactProof _logProof
          _certificateProof _fingerprintProof _checkerProof buildProof
          _submissionProof _fallbackProof => buildProof)

theorem ay_vamm_merkle_manifest_contract_submission
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun _archiveProof _rootProof _artifactProof _logProof
          _certificateProof _fingerprintProof _checkerProof _buildProof
          submissionProof _fallbackProof => submissionProof)

theorem ay_vamm_merkle_manifest_contract_fallback
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    fallbackPath :=
  fun contract =>
    contract fallbackPath
      (fun _archiveProof _rootProof _artifactProof _logProof
          _certificateProof _fingerprintProof _checkerProof _buildProof
          _submissionProof fallbackProof => fallbackProof)

theorem ay_vamm_sat_publication_intro
    (merkleContract modelEvidence originalModel : Prop) :
    merkleContract -> modelEvidence -> originalModel ->
    ay_vamm_sat_publication merkleContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vamm_conj_intro merkleContract
      (ay_vamm_conj modelEvidence originalModel)
      contractProof
      (ay_vamm_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vamm_sat_publication_original_model
    (merkleContract modelEvidence originalModel : Prop) :
    ay_vamm_sat_publication merkleContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vamm_conj_right merkleContract
      (ay_vamm_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vamm_unsat_publication_intro
    (merkleContract proofEvidence originalEmptyClause : Prop) :
    merkleContract -> proofEvidence -> originalEmptyClause ->
    ay_vamm_unsat_publication merkleContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vamm_conj_intro merkleContract
      (ay_vamm_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vamm_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vamm_unsat_publication_original_empty_clause
    (merkleContract proofEvidence originalEmptyClause : Prop) :
    ay_vamm_unsat_publication merkleContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vamm_conj_right merkleContract
      (ay_vamm_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vamm_accepted_merkle_manifest_sat_sound
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath modelEvidence
      originalModel : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vamm_accepted_merkle_manifest_unsat_sound
    (archiveManifest merkleRoot artifactDigests stdoutStderrDigests
      certificateOrModelDigest benchmarkFingerprint checkerTranscript
      buildConfiguration submissionManifest fallbackPath proofEvidence
      originalEmptyClause : Prop) :
    ay_vamm_merkle_manifest_contract archiveManifest merkleRoot
      artifactDigests stdoutStderrDigests certificateOrModelDigest
      benchmarkFingerprint checkerTranscript buildConfiguration
      submissionManifest fallbackPath ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vamm_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vamm_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vamm_conj_intro reason
      (ay_vamm_conj fallbackPath auditTrail)
      reasonProof
      (ay_vamm_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_vamm_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vamm_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vamm_conj_left reason
      (ay_vamm_conj fallbackPath auditTrail)
      noClaim

theorem ay_vamm_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vamm_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vamm_conj_intro reason
      (ay_vamm_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vamm_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vamm_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vamm_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vamm_conj_right reason
      (ay_vamm_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vamm_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vamm_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vamm_conj_right reason
      (ay_vamm_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vamm_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vamm_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vamm_conj_intro reason
      (ay_vamm_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_vamm_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vamm_merkle_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vamm_merkle_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vamm_conj_intro
      (ay_vamm_blocked_publication satFact unsatFact reason)
      (ay_vamm_recompute reason fallbackPath recomputeObligation)
      (ay_vamm_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vamm_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vamm_merkle_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vamm_merkle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vamm_blocked_publication_no_sat satFact unsatFact reason
      (ay_vamm_conj_left
        (ay_vamm_blocked_publication satFact unsatFact reason)
        (ay_vamm_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vamm_merkle_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vamm_merkle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vamm_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vamm_conj_left
        (ay_vamm_blocked_publication satFact unsatFact reason)
        (ay_vamm_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vamm_merkle_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vamm_merkle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vamm_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vamm_conj_right
      (ay_vamm_blocked_publication satFact unsatFact reason)
      (ay_vamm_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vamm_root_mismatch_forces_no_claim
    (satFact unsatFact rootMismatch fallbackPath recomputeObligation : Prop) :
    rootMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vamm_merkle_failure satFact unsatFact rootMismatch fallbackPath
      recomputeObligation :=
  ay_vamm_merkle_failure_intro satFact unsatFact rootMismatch fallbackPath
    recomputeObligation

theorem ay_vamm_artifact_mismatch_forces_no_claim
    (satFact unsatFact artifactMismatch fallbackPath
      recomputeObligation : Prop) :
    artifactMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vamm_merkle_failure satFact unsatFact artifactMismatch fallbackPath
      recomputeObligation :=
  ay_vamm_merkle_failure_intro satFact unsatFact artifactMismatch
    fallbackPath recomputeObligation

theorem ay_vamm_log_mismatch_forces_no_claim
    (satFact unsatFact logMismatch fallbackPath recomputeObligation : Prop) :
    logMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vamm_merkle_failure satFact unsatFact logMismatch fallbackPath
      recomputeObligation :=
  ay_vamm_merkle_failure_intro satFact unsatFact logMismatch fallbackPath
    recomputeObligation

theorem ay_vamm_certificate_mismatch_forces_no_claim
    (satFact unsatFact certificateMismatch fallbackPath
      recomputeObligation : Prop) :
    certificateMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vamm_merkle_failure satFact unsatFact certificateMismatch fallbackPath
      recomputeObligation :=
  ay_vamm_merkle_failure_intro satFact unsatFact certificateMismatch
    fallbackPath recomputeObligation

theorem ay_vamm_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath
      recomputeObligation : Prop) :
    fingerprintMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vamm_merkle_failure satFact unsatFact fingerprintMismatch
      fallbackPath recomputeObligation :=
  ay_vamm_merkle_failure_intro satFact unsatFact fingerprintMismatch
    fallbackPath recomputeObligation

theorem ay_vamm_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath
      recomputeObligation : Prop) :
    checkerMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vamm_merkle_failure satFact unsatFact checkerMismatch fallbackPath
      recomputeObligation :=
  ay_vamm_merkle_failure_intro satFact unsatFact checkerMismatch fallbackPath
    recomputeObligation

theorem ay_vamm_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath recomputeObligation : Prop) :
    buildMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vamm_merkle_failure satFact unsatFact buildMismatch fallbackPath
      recomputeObligation :=
  ay_vamm_merkle_failure_intro satFact unsatFact buildMismatch fallbackPath
    recomputeObligation

theorem ay_vamm_submission_mismatch_forces_no_claim
    (satFact unsatFact submissionMismatch fallbackPath
      recomputeObligation : Prop) :
    submissionMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vamm_merkle_failure satFact unsatFact submissionMismatch fallbackPath
      recomputeObligation :=
  ay_vamm_merkle_failure_intro satFact unsatFact submissionMismatch
    fallbackPath recomputeObligation

theorem ay_vamm_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation : Prop) :
    archiveMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vamm_merkle_failure satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation :=
  ay_vamm_merkle_failure_intro satFact unsatFact archiveMismatch fallbackPath
    recomputeObligation

theorem ay_vamm_failed_merkle_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vamm_merkle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vamm_merkle_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vamm_failed_merkle_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vamm_merkle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vamm_merkle_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
