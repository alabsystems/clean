-- SAT-COMP validator submission exit-code consensus core.
--
-- Sequential-main public publication requires agreement between solver exit
-- code, stdout result line, certificate/model artifact, result JSON, benchmark
-- fingerprint, checker transcript, build configuration, archive manifest, and
-- submission manifest.

def ay_vsec_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vsec_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vsec_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vsec_disj satFact (ay_vsec_disj unsatFact noClaimFact)

def ay_vsec_consensus_contract
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) : Prop :=
  forall result : Prop,
    (solverExitCode -> stdoutResultLine -> certificateOrModelArtifact ->
      resultJson -> benchmarkFingerprint -> checkerTranscript ->
      buildConfiguration -> archiveManifest -> submissionManifest -> result) ->
    result

def ay_vsec_sat_publication
    (consensusContract modelEvidence originalModel : Prop) : Prop :=
  ay_vsec_conj consensusContract
    (ay_vsec_conj modelEvidence originalModel)

def ay_vsec_unsat_publication
    (consensusContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vsec_conj consensusContract
    (ay_vsec_conj proofEvidence originalEmptyClause)

def ay_vsec_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vsec_conj reason (ay_vsec_conj fallbackPath auditTrail)

def ay_vsec_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vsec_conj reason
    (ay_vsec_conj (satFact -> False) (unsatFact -> False))

def ay_vsec_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vsec_conj reason
    (ay_vsec_conj fallbackPath recomputeObligation)

def ay_vsec_consensus_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vsec_conj
    (ay_vsec_blocked_publication satFact unsatFact reason)
    (ay_vsec_recompute reason fallbackPath recomputeObligation)

theorem ay_vsec_conj_intro (left right : Prop) :
    left -> right -> ay_vsec_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vsec_conj_left (left right : Prop) :
    ay_vsec_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vsec_conj_right (left right : Prop) :
    ay_vsec_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vsec_disj_left (left right : Prop) :
    left -> ay_vsec_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vsec_disj_right (left right : Prop) :
    right -> ay_vsec_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vsec_consensus_contract_intro
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    solverExitCode -> stdoutResultLine -> certificateOrModelArtifact ->
    resultJson -> benchmarkFingerprint -> checkerTranscript ->
    buildConfiguration -> archiveManifest -> submissionManifest ->
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest :=
  fun exitProof lineProof artifactProof jsonProof fingerprintProof
      checkerProof buildProof archiveProof submissionProof result build =>
    build exitProof lineProof artifactProof jsonProof fingerprintProof
      checkerProof buildProof archiveProof submissionProof

theorem ay_vsec_consensus_contract_exit_code
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    solverExitCode :=
  fun contract =>
    contract solverExitCode
      (fun exitProof _lineProof _artifactProof _jsonProof _fingerprintProof
          _checkerProof _buildProof _archiveProof _submissionProof =>
        exitProof)

theorem ay_vsec_consensus_contract_result_line
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    stdoutResultLine :=
  fun contract =>
    contract stdoutResultLine
      (fun _exitProof lineProof _artifactProof _jsonProof _fingerprintProof
          _checkerProof _buildProof _archiveProof _submissionProof =>
        lineProof)

theorem ay_vsec_consensus_contract_artifact
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    certificateOrModelArtifact :=
  fun contract =>
    contract certificateOrModelArtifact
      (fun _exitProof _lineProof artifactProof _jsonProof _fingerprintProof
          _checkerProof _buildProof _archiveProof _submissionProof =>
        artifactProof)

theorem ay_vsec_consensus_contract_result_json
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    resultJson :=
  fun contract =>
    contract resultJson
      (fun _exitProof _lineProof _artifactProof jsonProof _fingerprintProof
          _checkerProof _buildProof _archiveProof _submissionProof =>
        jsonProof)

theorem ay_vsec_consensus_contract_fingerprint
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _exitProof _lineProof _artifactProof _jsonProof fingerprintProof
          _checkerProof _buildProof _archiveProof _submissionProof =>
        fingerprintProof)

theorem ay_vsec_consensus_contract_checker_transcript
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _exitProof _lineProof _artifactProof _jsonProof _fingerprintProof
          checkerProof _buildProof _archiveProof _submissionProof =>
        checkerProof)

theorem ay_vsec_consensus_contract_build
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    buildConfiguration :=
  fun contract =>
    contract buildConfiguration
      (fun _exitProof _lineProof _artifactProof _jsonProof _fingerprintProof
          _checkerProof buildProof _archiveProof _submissionProof =>
        buildProof)

theorem ay_vsec_consensus_contract_archive_manifest
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _exitProof _lineProof _artifactProof _jsonProof _fingerprintProof
          _checkerProof _buildProof archiveProof _submissionProof =>
        archiveProof)

theorem ay_vsec_consensus_contract_submission_manifest
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest : Prop) :
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun _exitProof _lineProof _artifactProof _jsonProof _fingerprintProof
          _checkerProof _buildProof _archiveProof submissionProof =>
        submissionProof)

theorem ay_vsec_sat_publication_intro
    (consensusContract modelEvidence originalModel : Prop) :
    consensusContract -> modelEvidence -> originalModel ->
    ay_vsec_sat_publication consensusContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vsec_conj_intro consensusContract
      (ay_vsec_conj modelEvidence originalModel)
      contractProof
      (ay_vsec_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vsec_sat_publication_original_model
    (consensusContract modelEvidence originalModel : Prop) :
    ay_vsec_sat_publication consensusContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vsec_conj_right consensusContract
      (ay_vsec_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vsec_unsat_publication_intro
    (consensusContract proofEvidence originalEmptyClause : Prop) :
    consensusContract -> proofEvidence -> originalEmptyClause ->
    ay_vsec_unsat_publication consensusContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vsec_conj_intro consensusContract
      (ay_vsec_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vsec_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vsec_unsat_publication_original_empty_clause
    (consensusContract proofEvidence originalEmptyClause : Prop) :
    ay_vsec_unsat_publication consensusContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vsec_conj_right consensusContract
      (ay_vsec_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vsec_accepted_consensus_sat_sound
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest modelEvidence originalModel : Prop) :
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vsec_accepted_consensus_unsat_sound
    (solverExitCode stdoutResultLine certificateOrModelArtifact resultJson
      benchmarkFingerprint checkerTranscript buildConfiguration
      archiveManifest submissionManifest proofEvidence originalEmptyClause :
      Prop) :
    ay_vsec_consensus_contract solverExitCode stdoutResultLine
      certificateOrModelArtifact resultJson benchmarkFingerprint
      checkerTranscript buildConfiguration archiveManifest
      submissionManifest ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vsec_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vsec_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vsec_conj_intro reason
      (ay_vsec_conj fallbackPath auditTrail)
      reasonProof
      (ay_vsec_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_vsec_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vsec_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vsec_conj_left reason
      (ay_vsec_conj fallbackPath auditTrail)
      noClaim

theorem ay_vsec_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vsec_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vsec_conj_intro reason
      (ay_vsec_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vsec_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vsec_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vsec_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vsec_conj_right reason
      (ay_vsec_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vsec_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vsec_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vsec_conj_right reason
      (ay_vsec_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vsec_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vsec_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vsec_conj_intro reason
      (ay_vsec_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_vsec_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vsec_consensus_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsec_consensus_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vsec_conj_intro
      (ay_vsec_blocked_publication satFact unsatFact reason)
      (ay_vsec_recompute reason fallbackPath recomputeObligation)
      (ay_vsec_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vsec_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vsec_consensus_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsec_consensus_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vsec_blocked_publication_no_sat satFact unsatFact reason
      (ay_vsec_conj_left
        (ay_vsec_blocked_publication satFact unsatFact reason)
        (ay_vsec_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsec_consensus_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsec_consensus_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vsec_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vsec_conj_left
        (ay_vsec_blocked_publication satFact unsatFact reason)
        (ay_vsec_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsec_consensus_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsec_consensus_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vsec_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vsec_conj_right
      (ay_vsec_blocked_publication satFact unsatFact reason)
      (ay_vsec_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vsec_exit_code_mismatch_forces_no_claim
    (satFact unsatFact exitCodeMismatch fallbackPath
      recomputeObligation : Prop) :
    exitCodeMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsec_consensus_failure satFact unsatFact exitCodeMismatch fallbackPath
      recomputeObligation :=
  ay_vsec_consensus_failure_intro satFact unsatFact exitCodeMismatch
    fallbackPath recomputeObligation

theorem ay_vsec_result_line_mismatch_forces_no_claim
    (satFact unsatFact resultLineMismatch fallbackPath
      recomputeObligation : Prop) :
    resultLineMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsec_consensus_failure satFact unsatFact resultLineMismatch
      fallbackPath recomputeObligation :=
  ay_vsec_consensus_failure_intro satFact unsatFact resultLineMismatch
    fallbackPath recomputeObligation

theorem ay_vsec_certificate_mismatch_forces_no_claim
    (satFact unsatFact certificateMismatch fallbackPath
      recomputeObligation : Prop) :
    certificateMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsec_consensus_failure satFact unsatFact certificateMismatch
      fallbackPath recomputeObligation :=
  ay_vsec_consensus_failure_intro satFact unsatFact certificateMismatch
    fallbackPath recomputeObligation

theorem ay_vsec_json_mismatch_forces_no_claim
    (satFact unsatFact jsonMismatch fallbackPath recomputeObligation : Prop) :
    jsonMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsec_consensus_failure satFact unsatFact jsonMismatch fallbackPath
      recomputeObligation :=
  ay_vsec_consensus_failure_intro satFact unsatFact jsonMismatch fallbackPath
    recomputeObligation

theorem ay_vsec_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath
      recomputeObligation : Prop) :
    fingerprintMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsec_consensus_failure satFact unsatFact fingerprintMismatch
      fallbackPath recomputeObligation :=
  ay_vsec_consensus_failure_intro satFact unsatFact fingerprintMismatch
    fallbackPath recomputeObligation

theorem ay_vsec_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath
      recomputeObligation : Prop) :
    checkerMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsec_consensus_failure satFact unsatFact checkerMismatch fallbackPath
      recomputeObligation :=
  ay_vsec_consensus_failure_intro satFact unsatFact checkerMismatch
    fallbackPath recomputeObligation

theorem ay_vsec_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath recomputeObligation : Prop) :
    buildMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsec_consensus_failure satFact unsatFact buildMismatch fallbackPath
      recomputeObligation :=
  ay_vsec_consensus_failure_intro satFact unsatFact buildMismatch fallbackPath
    recomputeObligation

theorem ay_vsec_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation : Prop) :
    archiveMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsec_consensus_failure satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation :=
  ay_vsec_consensus_failure_intro satFact unsatFact archiveMismatch
    fallbackPath recomputeObligation

theorem ay_vsec_submission_mismatch_forces_no_claim
    (satFact unsatFact submissionMismatch fallbackPath
      recomputeObligation : Prop) :
    submissionMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsec_consensus_failure satFact unsatFact submissionMismatch
      fallbackPath recomputeObligation :=
  ay_vsec_consensus_failure_intro satFact unsatFact submissionMismatch
    fallbackPath recomputeObligation

theorem ay_vsec_failed_consensus_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsec_consensus_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vsec_consensus_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vsec_failed_consensus_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsec_consensus_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vsec_consensus_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation
