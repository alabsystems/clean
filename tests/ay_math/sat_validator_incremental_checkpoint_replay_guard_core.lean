-- SAT-COMP validator incremental checkpoint replay guard core.
--
-- Checkpoint/resume public claims are allowed only when checkpoint manifest,
-- resume transcript, binary/config identity, benchmark, artifacts, checker,
-- archive, and no-claim fallback path agree.

def ay_vckp_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vckp_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vckp_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vckp_disj satFact (ay_vckp_disj unsatFact noClaimFact)

def ay_vckp_checkpoint_contract
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) : Prop :=
  forall result : Prop,
    (checkpointManifest -> resumeTranscript -> solverBinaryHash ->
      configurationDigest -> benchmarkFingerprint -> resultArtifact ->
      certificateModel -> checkerTranscript -> archiveManifest ->
      noClaimFallbackPath -> result) ->
    result

def ay_vckp_sat_publication
    (checkpointContract modelEvidence originalModel : Prop) : Prop :=
  ay_vckp_conj checkpointContract
    (ay_vckp_conj modelEvidence originalModel)

def ay_vckp_unsat_publication
    (checkpointContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vckp_conj checkpointContract
    (ay_vckp_conj proofEvidence originalEmptyClause)

def ay_vckp_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vckp_conj reason (ay_vckp_conj fallbackPath auditTrail)

def ay_vckp_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vckp_conj reason
    (ay_vckp_conj (satFact -> False) (unsatFact -> False))

def ay_vckp_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vckp_conj reason
    (ay_vckp_conj fallbackPath recomputeObligation)

def ay_vckp_checkpoint_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vckp_conj
    (ay_vckp_blocked_publication satFact unsatFact reason)
    (ay_vckp_recompute reason fallbackPath recomputeObligation)

theorem ay_vckp_conj_intro (left right : Prop) :
    left -> right -> ay_vckp_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vckp_conj_left (left right : Prop) :
    ay_vckp_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vckp_conj_right (left right : Prop) :
    ay_vckp_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vckp_disj_left (left right : Prop) :
    left -> ay_vckp_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vckp_disj_right (left right : Prop) :
    right -> ay_vckp_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vckp_checkpoint_contract_intro
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) :
    checkpointManifest -> resumeTranscript -> solverBinaryHash ->
    configurationDigest -> benchmarkFingerprint -> resultArtifact ->
    certificateModel -> checkerTranscript -> archiveManifest ->
    noClaimFallbackPath ->
    ay_vckp_checkpoint_contract checkpointManifest resumeTranscript
      solverBinaryHash configurationDigest benchmarkFingerprint
      resultArtifact certificateModel checkerTranscript archiveManifest
      noClaimFallbackPath :=
  fun checkpointProof resumeProof binaryProof configProof fingerprintProof
      artifactProof certificateProof checkerProof archiveProof fallbackProof
      result build =>
    build checkpointProof resumeProof binaryProof configProof fingerprintProof
      artifactProof certificateProof checkerProof archiveProof fallbackProof

theorem ay_vckp_checkpoint_contract_checkpoint
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) :
    ay_vckp_checkpoint_contract checkpointManifest resumeTranscript
      solverBinaryHash configurationDigest benchmarkFingerprint
      resultArtifact certificateModel checkerTranscript archiveManifest
      noClaimFallbackPath ->
    checkpointManifest :=
  fun contract =>
    contract checkpointManifest
      (fun checkpointProof _resumeProof _binaryProof _configProof
          _fingerprintProof _artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => checkpointProof)

theorem ay_vckp_checkpoint_contract_resume
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) :
    ay_vckp_checkpoint_contract checkpointManifest resumeTranscript
      solverBinaryHash configurationDigest benchmarkFingerprint
      resultArtifact certificateModel checkerTranscript archiveManifest
      noClaimFallbackPath ->
    resumeTranscript :=
  fun contract =>
    contract resumeTranscript
      (fun _checkpointProof resumeProof _binaryProof _configProof
          _fingerprintProof _artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => resumeProof)

theorem ay_vckp_checkpoint_contract_binary
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) :
    ay_vckp_checkpoint_contract checkpointManifest resumeTranscript
      solverBinaryHash configurationDigest benchmarkFingerprint
      resultArtifact certificateModel checkerTranscript archiveManifest
      noClaimFallbackPath ->
    solverBinaryHash :=
  fun contract =>
    contract solverBinaryHash
      (fun _checkpointProof _resumeProof binaryProof _configProof
          _fingerprintProof _artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => binaryProof)

theorem ay_vckp_checkpoint_contract_config
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) :
    ay_vckp_checkpoint_contract checkpointManifest resumeTranscript
      solverBinaryHash configurationDigest benchmarkFingerprint
      resultArtifact certificateModel checkerTranscript archiveManifest
      noClaimFallbackPath ->
    configurationDigest :=
  fun contract =>
    contract configurationDigest
      (fun _checkpointProof _resumeProof _binaryProof configProof
          _fingerprintProof _artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => configProof)

theorem ay_vckp_checkpoint_contract_fingerprint
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) :
    ay_vckp_checkpoint_contract checkpointManifest resumeTranscript
      solverBinaryHash configurationDigest benchmarkFingerprint
      resultArtifact certificateModel checkerTranscript archiveManifest
      noClaimFallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _checkpointProof _resumeProof _binaryProof _configProof
          fingerprintProof _artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => fingerprintProof)

theorem ay_vckp_checkpoint_contract_result_artifact
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) :
    ay_vckp_checkpoint_contract checkpointManifest resumeTranscript
      solverBinaryHash configurationDigest benchmarkFingerprint
      resultArtifact certificateModel checkerTranscript archiveManifest
      noClaimFallbackPath ->
    resultArtifact :=
  fun contract =>
    contract resultArtifact
      (fun _checkpointProof _resumeProof _binaryProof _configProof
          _fingerprintProof artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => artifactProof)

theorem ay_vckp_checkpoint_contract_certificate_model
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) :
    ay_vckp_checkpoint_contract checkpointManifest resumeTranscript
      solverBinaryHash configurationDigest benchmarkFingerprint
      resultArtifact certificateModel checkerTranscript archiveManifest
      noClaimFallbackPath ->
    certificateModel :=
  fun contract =>
    contract certificateModel
      (fun _checkpointProof _resumeProof _binaryProof _configProof
          _fingerprintProof _artifactProof certificateProof _checkerProof
          _archiveProof _fallbackProof => certificateProof)

theorem ay_vckp_checkpoint_contract_checker
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) :
    ay_vckp_checkpoint_contract checkpointManifest resumeTranscript
      solverBinaryHash configurationDigest benchmarkFingerprint
      resultArtifact certificateModel checkerTranscript archiveManifest
      noClaimFallbackPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _checkpointProof _resumeProof _binaryProof _configProof
          _fingerprintProof _artifactProof _certificateProof checkerProof
          _archiveProof _fallbackProof => checkerProof)

theorem ay_vckp_checkpoint_contract_archive
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) :
    ay_vckp_checkpoint_contract checkpointManifest resumeTranscript
      solverBinaryHash configurationDigest benchmarkFingerprint
      resultArtifact certificateModel checkerTranscript archiveManifest
      noClaimFallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _checkpointProof _resumeProof _binaryProof _configProof
          _fingerprintProof _artifactProof _certificateProof _checkerProof
          archiveProof _fallbackProof => archiveProof)

theorem ay_vckp_checkpoint_contract_fallback
    (checkpointManifest resumeTranscript solverBinaryHash configurationDigest
      benchmarkFingerprint resultArtifact certificateModel checkerTranscript
      archiveManifest noClaimFallbackPath : Prop) :
    ay_vckp_checkpoint_contract checkpointManifest resumeTranscript
      solverBinaryHash configurationDigest benchmarkFingerprint
      resultArtifact certificateModel checkerTranscript archiveManifest
      noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _checkpointProof _resumeProof _binaryProof _configProof
          _fingerprintProof _artifactProof _certificateProof _checkerProof
          _archiveProof fallbackProof => fallbackProof)

theorem ay_vckp_sat_publication_intro
    (checkpointContract modelEvidence originalModel : Prop) :
    checkpointContract -> modelEvidence -> originalModel ->
    ay_vckp_sat_publication checkpointContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vckp_conj_intro checkpointContract
      (ay_vckp_conj modelEvidence originalModel) contractProof
      (ay_vckp_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vckp_sat_publication_original_model
    (checkpointContract modelEvidence originalModel : Prop) :
    ay_vckp_sat_publication checkpointContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vckp_conj_right modelEvidence originalModel
      (ay_vckp_conj_right checkpointContract
        (ay_vckp_conj modelEvidence originalModel) publication)

theorem ay_vckp_unsat_publication_intro
    (checkpointContract proofEvidence originalEmptyClause : Prop) :
    checkpointContract -> proofEvidence -> originalEmptyClause ->
    ay_vckp_unsat_publication checkpointContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vckp_conj_intro checkpointContract
      (ay_vckp_conj proofEvidence originalEmptyClause) contractProof
      (ay_vckp_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vckp_unsat_publication_original_empty_clause
    (checkpointContract proofEvidence originalEmptyClause : Prop) :
    ay_vckp_unsat_publication checkpointContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vckp_conj_right proofEvidence originalEmptyClause
      (ay_vckp_conj_right checkpointContract
        (ay_vckp_conj proofEvidence originalEmptyClause) publication)

theorem ay_vckp_accepted_checkpoint_sat_sound
    (checkpointContract modelEvidence originalModel : Prop) :
    ay_vckp_sat_publication checkpointContract modelEvidence originalModel ->
    originalModel :=
  ay_vckp_sat_publication_original_model checkpointContract modelEvidence
    originalModel

theorem ay_vckp_accepted_checkpoint_unsat_sound
    (checkpointContract proofEvidence originalEmptyClause : Prop) :
    ay_vckp_unsat_publication checkpointContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_vckp_unsat_publication_original_empty_clause checkpointContract
    proofEvidence originalEmptyClause

theorem ay_vckp_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vckp_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vckp_conj_intro reason (ay_vckp_conj fallbackPath auditTrail)
      reasonProof
      (ay_vckp_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_vckp_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_vckp_conj_intro reason
      (ay_vckp_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_vckp_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_vckp_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vckp_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vckp_conj_left (satFact -> False) (unsatFact -> False)
      (ay_vckp_conj_right reason
        (ay_vckp_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vckp_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vckp_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vckp_conj_right (satFact -> False) (unsatFact -> False)
      (ay_vckp_conj_right reason
        (ay_vckp_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vckp_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vckp_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vckp_conj_intro reason
      (ay_vckp_conj fallbackPath recomputeObligation) reasonProof
      (ay_vckp_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_vckp_checkpoint_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_checkpoint_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_vckp_conj_intro
      (ay_vckp_blocked_publication satFact unsatFact reason)
      (ay_vckp_recompute reason fallbackPath recomputeObligation)
      (ay_vckp_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_vckp_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vckp_checkpoint_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vckp_checkpoint_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vckp_blocked_publication_no_sat satFact unsatFact reason
      (ay_vckp_conj_left
        (ay_vckp_blocked_publication satFact unsatFact reason)
        (ay_vckp_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vckp_checkpoint_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vckp_checkpoint_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vckp_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vckp_conj_left
        (ay_vckp_blocked_publication satFact unsatFact reason)
        (ay_vckp_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vckp_checkpoint_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vckp_checkpoint_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vckp_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vckp_conj_right
      (ay_vckp_blocked_publication satFact unsatFact reason)
      (ay_vckp_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vckp_mismatch_forces_no_claim
    (satFact unsatFact mismatch fallbackPath auditTrail recomputeObligation :
      Prop) :
    mismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_no_claim mismatch fallbackPath auditTrail :=
  fun mismatchProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_vckp_no_claim_intro mismatch fallbackPath auditTrail mismatchProof
      fallbackProof auditProof

theorem ay_vckp_checkpoint_mismatch_blocks_publication
    (satFact unsatFact checkpointMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkpointMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_no_claim checkpointMismatch fallbackPath auditTrail :=
  ay_vckp_mismatch_forces_no_claim satFact unsatFact checkpointMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vckp_resume_mismatch_blocks_publication
    (satFact unsatFact resumeMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    resumeMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_no_claim resumeMismatch fallbackPath auditTrail :=
  ay_vckp_mismatch_forces_no_claim satFact unsatFact resumeMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vckp_binary_mismatch_blocks_publication
    (satFact unsatFact binaryMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    binaryMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_no_claim binaryMismatch fallbackPath auditTrail :=
  ay_vckp_mismatch_forces_no_claim satFact unsatFact binaryMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vckp_config_mismatch_blocks_publication
    (satFact unsatFact configMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    configMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_no_claim configMismatch fallbackPath auditTrail :=
  ay_vckp_mismatch_forces_no_claim satFact unsatFact configMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vckp_benchmark_mismatch_blocks_publication
    (satFact unsatFact benchmarkMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    benchmarkMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_no_claim benchmarkMismatch fallbackPath auditTrail :=
  ay_vckp_mismatch_forces_no_claim satFact unsatFact benchmarkMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vckp_artifact_mismatch_blocks_publication
    (satFact unsatFact artifactMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_vckp_mismatch_forces_no_claim satFact unsatFact artifactMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vckp_certificate_mismatch_blocks_publication
    (satFact unsatFact certificateMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    certificateMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_no_claim certificateMismatch fallbackPath auditTrail :=
  ay_vckp_mismatch_forces_no_claim satFact unsatFact certificateMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vckp_checker_mismatch_blocks_publication
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_vckp_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vckp_archive_mismatch_blocks_publication
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vckp_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_vckp_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vckp_failed_checkpoint_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vckp_checkpoint_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vckp_checkpoint_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vckp_failed_checkpoint_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vckp_checkpoint_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vckp_checkpoint_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vckp_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_vckp_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_vckp_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_vckp_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
