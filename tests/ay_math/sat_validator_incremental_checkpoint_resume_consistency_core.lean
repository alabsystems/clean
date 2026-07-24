-- SAT-COMP validator incremental checkpoint/resume consistency core.
--
-- Resumed sequential-main solver outputs may be published only when checkpoint
-- manifest, resume seed/digest, trail/proof/model artifact digest, result JSON,
-- benchmark fingerprint, checker transcript, build configuration, archive
-- manifest, and submission manifest agree.

def ay_vcrc_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vcrc_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vcrc_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vcrc_disj satFact (ay_vcrc_disj unsatFact noClaimFact)

def ay_vcrc_resume_contract
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) : Prop :=
  forall result : Prop,
    (checkpointManifest -> resumeSeedDigest ->
      trailProofModelArtifactDigest -> resultJson -> benchmarkFingerprint ->
      checkerTranscript -> buildConfiguration -> archiveManifest ->
      submissionManifest -> result) ->
    result

def ay_vcrc_sat_publication
    (resumeContract modelEvidence originalModel : Prop) : Prop :=
  ay_vcrc_conj resumeContract
    (ay_vcrc_conj modelEvidence originalModel)

def ay_vcrc_unsat_publication
    (resumeContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vcrc_conj resumeContract
    (ay_vcrc_conj proofEvidence originalEmptyClause)

def ay_vcrc_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vcrc_conj reason (ay_vcrc_conj fallbackPath auditTrail)

def ay_vcrc_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vcrc_conj reason
    (ay_vcrc_conj (satFact -> False) (unsatFact -> False))

def ay_vcrc_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vcrc_conj reason
    (ay_vcrc_conj fallbackPath recomputeObligation)

def ay_vcrc_resume_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vcrc_conj
    (ay_vcrc_blocked_publication satFact unsatFact reason)
    (ay_vcrc_recompute reason fallbackPath recomputeObligation)

theorem ay_vcrc_conj_intro (left right : Prop) :
    left -> right -> ay_vcrc_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcrc_conj_left (left right : Prop) :
    ay_vcrc_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcrc_conj_right (left right : Prop) :
    ay_vcrc_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcrc_disj_left (left right : Prop) :
    left -> ay_vcrc_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vcrc_disj_right (left right : Prop) :
    right -> ay_vcrc_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcrc_resume_contract_intro
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    checkpointManifest -> resumeSeedDigest ->
    trailProofModelArtifactDigest -> resultJson -> benchmarkFingerprint ->
    checkerTranscript -> buildConfiguration -> archiveManifest ->
    submissionManifest ->
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest :=
  fun checkpointProof resumeProof artifactProof jsonProof fingerprintProof
      checkerProof buildProof archiveProof submissionProof result build =>
    build checkpointProof resumeProof artifactProof jsonProof fingerprintProof
      checkerProof buildProof archiveProof submissionProof

theorem ay_vcrc_resume_contract_checkpoint
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    checkpointManifest :=
  fun contract =>
    contract checkpointManifest
      (fun checkpointProof _resumeProof _artifactProof _jsonProof
          _fingerprintProof _checkerProof _buildProof _archiveProof
          _submissionProof => checkpointProof)

theorem ay_vcrc_resume_contract_resume_seed_digest
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    resumeSeedDigest :=
  fun contract =>
    contract resumeSeedDigest
      (fun _checkpointProof resumeProof _artifactProof _jsonProof
          _fingerprintProof _checkerProof _buildProof _archiveProof
          _submissionProof => resumeProof)

theorem ay_vcrc_resume_contract_artifact_digest
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    trailProofModelArtifactDigest :=
  fun contract =>
    contract trailProofModelArtifactDigest
      (fun _checkpointProof _resumeProof artifactProof _jsonProof
          _fingerprintProof _checkerProof _buildProof _archiveProof
          _submissionProof => artifactProof)

theorem ay_vcrc_resume_contract_result_json
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    resultJson :=
  fun contract =>
    contract resultJson
      (fun _checkpointProof _resumeProof _artifactProof jsonProof
          _fingerprintProof _checkerProof _buildProof _archiveProof
          _submissionProof => jsonProof)

theorem ay_vcrc_resume_contract_fingerprint
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _checkpointProof _resumeProof _artifactProof _jsonProof
          fingerprintProof _checkerProof _buildProof _archiveProof
          _submissionProof => fingerprintProof)

theorem ay_vcrc_resume_contract_checker
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _checkpointProof _resumeProof _artifactProof _jsonProof
          _fingerprintProof checkerProof _buildProof _archiveProof
          _submissionProof => checkerProof)

theorem ay_vcrc_resume_contract_build
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    buildConfiguration :=
  fun contract =>
    contract buildConfiguration
      (fun _checkpointProof _resumeProof _artifactProof _jsonProof
          _fingerprintProof _checkerProof buildProof _archiveProof
          _submissionProof => buildProof)

theorem ay_vcrc_resume_contract_archive
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _checkpointProof _resumeProof _artifactProof _jsonProof
          _fingerprintProof _checkerProof _buildProof archiveProof
          _submissionProof => archiveProof)

theorem ay_vcrc_resume_contract_submission
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun _checkpointProof _resumeProof _artifactProof _jsonProof
          _fingerprintProof _checkerProof _buildProof _archiveProof
          submissionProof => submissionProof)

theorem ay_vcrc_sat_publication_intro
    (resumeContract modelEvidence originalModel : Prop) :
    resumeContract -> modelEvidence -> originalModel ->
    ay_vcrc_sat_publication resumeContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vcrc_conj_intro resumeContract
      (ay_vcrc_conj modelEvidence originalModel)
      contractProof
      (ay_vcrc_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vcrc_sat_publication_original_model
    (resumeContract modelEvidence originalModel : Prop) :
    ay_vcrc_sat_publication resumeContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vcrc_conj_right resumeContract
      (ay_vcrc_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vcrc_unsat_publication_intro
    (resumeContract proofEvidence originalEmptyClause : Prop) :
    resumeContract -> proofEvidence -> originalEmptyClause ->
    ay_vcrc_unsat_publication resumeContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vcrc_conj_intro resumeContract
      (ay_vcrc_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vcrc_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vcrc_unsat_publication_original_empty_clause
    (resumeContract proofEvidence originalEmptyClause : Prop) :
    ay_vcrc_unsat_publication resumeContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vcrc_conj_right resumeContract
      (ay_vcrc_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vcrc_accepted_resume_sat_sound
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest modelEvidence originalModel : Prop) :
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vcrc_accepted_resume_unsat_sound
    (checkpointManifest resumeSeedDigest trailProofModelArtifactDigest
      resultJson benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest proofEvidence originalEmptyClause :
      Prop) :
    ay_vcrc_resume_contract checkpointManifest resumeSeedDigest
      trailProofModelArtifactDigest resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vcrc_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vcrc_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vcrc_conj_intro reason
      (ay_vcrc_conj fallbackPath auditTrail)
      reasonProof
      (ay_vcrc_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_vcrc_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vcrc_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vcrc_conj_left reason
      (ay_vcrc_conj fallbackPath auditTrail)
      noClaim

theorem ay_vcrc_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vcrc_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vcrc_conj_intro reason
      (ay_vcrc_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vcrc_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vcrc_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vcrc_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vcrc_conj_right reason
      (ay_vcrc_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vcrc_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vcrc_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vcrc_conj_right reason
      (ay_vcrc_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vcrc_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vcrc_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vcrc_conj_intro reason
      (ay_vcrc_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_vcrc_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vcrc_resume_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcrc_resume_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vcrc_conj_intro
      (ay_vcrc_blocked_publication satFact unsatFact reason)
      (ay_vcrc_recompute reason fallbackPath recomputeObligation)
      (ay_vcrc_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vcrc_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vcrc_resume_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcrc_resume_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vcrc_blocked_publication_no_sat satFact unsatFact reason
      (ay_vcrc_conj_left
        (ay_vcrc_blocked_publication satFact unsatFact reason)
        (ay_vcrc_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vcrc_resume_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcrc_resume_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vcrc_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vcrc_conj_left
        (ay_vcrc_blocked_publication satFact unsatFact reason)
        (ay_vcrc_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vcrc_resume_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcrc_resume_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vcrc_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vcrc_conj_right
      (ay_vcrc_blocked_publication satFact unsatFact reason)
      (ay_vcrc_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vcrc_checkpoint_mismatch_forces_no_claim
    (satFact unsatFact checkpointMismatch fallbackPath
      recomputeObligation : Prop) :
    checkpointMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcrc_resume_failure satFact unsatFact checkpointMismatch fallbackPath
      recomputeObligation :=
  ay_vcrc_resume_failure_intro satFact unsatFact checkpointMismatch
    fallbackPath recomputeObligation

theorem ay_vcrc_resume_mismatch_forces_no_claim
    (satFact unsatFact resumeMismatch fallbackPath
      recomputeObligation : Prop) :
    resumeMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcrc_resume_failure satFact unsatFact resumeMismatch fallbackPath
      recomputeObligation :=
  ay_vcrc_resume_failure_intro satFact unsatFact resumeMismatch fallbackPath
    recomputeObligation

theorem ay_vcrc_artifact_mismatch_forces_no_claim
    (satFact unsatFact artifactMismatch fallbackPath
      recomputeObligation : Prop) :
    artifactMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcrc_resume_failure satFact unsatFact artifactMismatch fallbackPath
      recomputeObligation :=
  ay_vcrc_resume_failure_intro satFact unsatFact artifactMismatch
    fallbackPath recomputeObligation

theorem ay_vcrc_json_mismatch_forces_no_claim
    (satFact unsatFact jsonMismatch fallbackPath recomputeObligation : Prop) :
    jsonMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcrc_resume_failure satFact unsatFact jsonMismatch fallbackPath
      recomputeObligation :=
  ay_vcrc_resume_failure_intro satFact unsatFact jsonMismatch fallbackPath
    recomputeObligation

theorem ay_vcrc_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath
      recomputeObligation : Prop) :
    fingerprintMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcrc_resume_failure satFact unsatFact fingerprintMismatch
      fallbackPath recomputeObligation :=
  ay_vcrc_resume_failure_intro satFact unsatFact fingerprintMismatch
    fallbackPath recomputeObligation

theorem ay_vcrc_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath
      recomputeObligation : Prop) :
    checkerMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcrc_resume_failure satFact unsatFact checkerMismatch fallbackPath
      recomputeObligation :=
  ay_vcrc_resume_failure_intro satFact unsatFact checkerMismatch fallbackPath
    recomputeObligation

theorem ay_vcrc_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath recomputeObligation : Prop) :
    buildMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcrc_resume_failure satFact unsatFact buildMismatch fallbackPath
      recomputeObligation :=
  ay_vcrc_resume_failure_intro satFact unsatFact buildMismatch fallbackPath
    recomputeObligation

theorem ay_vcrc_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation : Prop) :
    archiveMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcrc_resume_failure satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation :=
  ay_vcrc_resume_failure_intro satFact unsatFact archiveMismatch fallbackPath
    recomputeObligation

theorem ay_vcrc_submission_mismatch_forces_no_claim
    (satFact unsatFact submissionMismatch fallbackPath
      recomputeObligation : Prop) :
    submissionMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcrc_resume_failure satFact unsatFact submissionMismatch fallbackPath
      recomputeObligation :=
  ay_vcrc_resume_failure_intro satFact unsatFact submissionMismatch
    fallbackPath recomputeObligation

theorem ay_vcrc_failed_resume_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcrc_resume_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vcrc_resume_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vcrc_failed_resume_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcrc_resume_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vcrc_resume_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
