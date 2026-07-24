-- SAT-COMP validator result JSON/schema manifest core.
--
-- Machine-readable result JSON may publish SAT/UNSAT only when schema version,
-- solver exit code, stdout/stderr digests, result artifacts, checker
-- transcripts, formula fingerprint, build config, archive manifest, and
-- fallback path agree.

def ay_vrjs_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrjs_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vrjs_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vrjs_disj satFact (ay_vrjs_disj unsatFact noClaimFact)

def ay_vrjs_json_manifest_contract
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) : Prop :=
  forall result : Prop,
    (schemaVersion -> solverExitCode -> stdoutStderrDigests ->
      resultArtifacts -> checkerTranscripts -> formulaFingerprint ->
      buildConfig -> archiveManifest -> fallbackPath -> result) ->
    result

def ay_vrjs_sat_publication
    (jsonContract modelEvidence originalModel : Prop) : Prop :=
  ay_vrjs_conj jsonContract
    (ay_vrjs_conj modelEvidence originalModel)

def ay_vrjs_unsat_publication
    (jsonContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vrjs_conj jsonContract
    (ay_vrjs_conj proofEvidence originalEmptyClause)

def ay_vrjs_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vrjs_conj reason (ay_vrjs_conj fallbackPath auditTrail)

def ay_vrjs_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vrjs_conj reason
    (ay_vrjs_conj (satFact -> False) (unsatFact -> False))

def ay_vrjs_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vrjs_conj reason
    (ay_vrjs_conj fallbackPath recomputeObligation)

def ay_vrjs_json_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vrjs_conj
    (ay_vrjs_blocked_publication satFact unsatFact reason)
    (ay_vrjs_recompute reason fallbackPath recomputeObligation)

theorem ay_vrjs_conj_intro (left right : Prop) :
    left -> right -> ay_vrjs_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrjs_conj_left (left right : Prop) :
    ay_vrjs_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrjs_conj_right (left right : Prop) :
    ay_vrjs_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrjs_disj_left (left right : Prop) :
    left -> ay_vrjs_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vrjs_disj_right (left right : Prop) :
    right -> ay_vrjs_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrjs_json_manifest_contract_intro
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    schemaVersion -> solverExitCode -> stdoutStderrDigests ->
    resultArtifacts -> checkerTranscripts -> formulaFingerprint ->
    buildConfig -> archiveManifest -> fallbackPath ->
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath :=
  fun schemaProof exitProof digestProof artifactProof transcriptProof
      fingerprintProof buildProof archiveProof fallbackProof result build =>
    build schemaProof exitProof digestProof artifactProof transcriptProof
      fingerprintProof buildProof archiveProof fallbackProof

theorem ay_vrjs_json_manifest_contract_schema_version
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath ->
    schemaVersion :=
  fun contract =>
    contract schemaVersion
      (fun schemaProof _exitProof _digestProof _artifactProof
          _transcriptProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof => schemaProof)

theorem ay_vrjs_json_manifest_contract_exit_code
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath ->
    solverExitCode :=
  fun contract =>
    contract solverExitCode
      (fun _schemaProof exitProof _digestProof _artifactProof
          _transcriptProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof => exitProof)

theorem ay_vrjs_json_manifest_contract_stdout_stderr_digests
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath ->
    stdoutStderrDigests :=
  fun contract =>
    contract stdoutStderrDigests
      (fun _schemaProof _exitProof digestProof _artifactProof
          _transcriptProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof => digestProof)

theorem ay_vrjs_json_manifest_contract_artifacts
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath ->
    resultArtifacts :=
  fun contract =>
    contract resultArtifacts
      (fun _schemaProof _exitProof _digestProof artifactProof
          _transcriptProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof => artifactProof)

theorem ay_vrjs_json_manifest_contract_transcripts
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _schemaProof _exitProof _digestProof _artifactProof
          transcriptProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof => transcriptProof)

theorem ay_vrjs_json_manifest_contract_fingerprint
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath ->
    formulaFingerprint :=
  fun contract =>
    contract formulaFingerprint
      (fun _schemaProof _exitProof _digestProof _artifactProof
          _transcriptProof fingerprintProof _buildProof _archiveProof
          _fallbackProof => fingerprintProof)

theorem ay_vrjs_json_manifest_contract_build_config
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _schemaProof _exitProof _digestProof _artifactProof
          _transcriptProof _fingerprintProof buildProof _archiveProof
          _fallbackProof => buildProof)

theorem ay_vrjs_json_manifest_contract_archive_manifest
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _schemaProof _exitProof _digestProof _artifactProof
          _transcriptProof _fingerprintProof _buildProof archiveProof
          _fallbackProof => archiveProof)

theorem ay_vrjs_json_manifest_contract_fallback_path
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath ->
    fallbackPath :=
  fun contract =>
    contract fallbackPath
      (fun _schemaProof _exitProof _digestProof _artifactProof
          _transcriptProof _fingerprintProof _buildProof _archiveProof
          fallbackProof => fallbackProof)

theorem ay_vrjs_sat_publication_intro
    (jsonContract modelEvidence originalModel : Prop) :
    jsonContract -> modelEvidence -> originalModel ->
    ay_vrjs_sat_publication jsonContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vrjs_conj_intro jsonContract
      (ay_vrjs_conj modelEvidence originalModel)
      contractProof
      (ay_vrjs_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vrjs_sat_publication_original_model
    (jsonContract modelEvidence originalModel : Prop) :
    ay_vrjs_sat_publication jsonContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vrjs_conj_right jsonContract
      (ay_vrjs_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vrjs_unsat_publication_intro
    (jsonContract proofEvidence originalEmptyClause : Prop) :
    jsonContract -> proofEvidence -> originalEmptyClause ->
    ay_vrjs_unsat_publication jsonContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vrjs_conj_intro jsonContract
      (ay_vrjs_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vrjs_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vrjs_unsat_publication_original_empty_clause
    (jsonContract proofEvidence originalEmptyClause : Prop) :
    ay_vrjs_unsat_publication jsonContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vrjs_conj_right jsonContract
      (ay_vrjs_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vrjs_accepted_json_manifest_sat_sound
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath modelEvidence originalModel : Prop) :
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vrjs_accepted_json_manifest_unsat_sound
    (schemaVersion solverExitCode stdoutStderrDigests resultArtifacts
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath proofEvidence originalEmptyClause : Prop) :
    ay_vrjs_json_manifest_contract schemaVersion solverExitCode
      stdoutStderrDigests resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest fallbackPath ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vrjs_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vrjs_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vrjs_conj_intro reason
      (ay_vrjs_conj fallbackPath auditTrail)
      reasonProof
      (ay_vrjs_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_vrjs_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vrjs_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vrjs_conj_left reason
      (ay_vrjs_conj fallbackPath auditTrail)
      noClaim

theorem ay_vrjs_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vrjs_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vrjs_conj_intro reason
      (ay_vrjs_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vrjs_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vrjs_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vrjs_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vrjs_conj_right reason
      (ay_vrjs_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vrjs_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vrjs_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vrjs_conj_right reason
      (ay_vrjs_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vrjs_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vrjs_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vrjs_conj_intro reason
      (ay_vrjs_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_vrjs_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vrjs_json_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrjs_json_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vrjs_conj_intro
      (ay_vrjs_blocked_publication satFact unsatFact reason)
      (ay_vrjs_recompute reason fallbackPath recomputeObligation)
      (ay_vrjs_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vrjs_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vrjs_json_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrjs_json_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vrjs_blocked_publication_no_sat satFact unsatFact reason
      (ay_vrjs_conj_left
        (ay_vrjs_blocked_publication satFact unsatFact reason)
        (ay_vrjs_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vrjs_json_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrjs_json_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vrjs_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vrjs_conj_left
        (ay_vrjs_blocked_publication satFact unsatFact reason)
        (ay_vrjs_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vrjs_json_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrjs_json_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vrjs_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vrjs_conj_right
      (ay_vrjs_blocked_publication satFact unsatFact reason)
      (ay_vrjs_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vrjs_schema_drift_forces_no_claim
    (satFact unsatFact schemaDrift fallbackPath recomputeObligation : Prop) :
    schemaDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrjs_json_failure satFact unsatFact schemaDrift fallbackPath
      recomputeObligation :=
  ay_vrjs_json_failure_intro satFact unsatFact schemaDrift fallbackPath
    recomputeObligation

theorem ay_vrjs_missing_required_field_forces_no_claim
    (satFact unsatFact missingRequiredField fallbackPath
      recomputeObligation : Prop) :
    missingRequiredField -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrjs_json_failure satFact unsatFact missingRequiredField fallbackPath
      recomputeObligation :=
  ay_vrjs_json_failure_intro satFact unsatFact missingRequiredField
    fallbackPath recomputeObligation

theorem ay_vrjs_exit_mismatch_forces_no_claim
    (satFact unsatFact exitMismatch fallbackPath recomputeObligation : Prop) :
    exitMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrjs_json_failure satFact unsatFact exitMismatch fallbackPath
      recomputeObligation :=
  ay_vrjs_json_failure_intro satFact unsatFact exitMismatch fallbackPath
    recomputeObligation

theorem ay_vrjs_digest_drift_forces_no_claim
    (satFact unsatFact digestDrift fallbackPath recomputeObligation : Prop) :
    digestDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrjs_json_failure satFact unsatFact digestDrift fallbackPath
      recomputeObligation :=
  ay_vrjs_json_failure_intro satFact unsatFact digestDrift fallbackPath
    recomputeObligation

theorem ay_vrjs_artifact_drift_forces_no_claim
    (satFact unsatFact artifactDrift fallbackPath recomputeObligation : Prop) :
    artifactDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrjs_json_failure satFact unsatFact artifactDrift fallbackPath
      recomputeObligation :=
  ay_vrjs_json_failure_intro satFact unsatFact artifactDrift fallbackPath
    recomputeObligation

theorem ay_vrjs_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackPath
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrjs_json_failure satFact unsatFact missingTranscript fallbackPath
      recomputeObligation :=
  ay_vrjs_json_failure_intro satFact unsatFact missingTranscript fallbackPath
    recomputeObligation

theorem ay_vrjs_fingerprint_drift_forces_no_claim
    (satFact unsatFact fingerprintDrift fallbackPath
      recomputeObligation : Prop) :
    fingerprintDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrjs_json_failure satFact unsatFact fingerprintDrift fallbackPath
      recomputeObligation :=
  ay_vrjs_json_failure_intro satFact unsatFact fingerprintDrift fallbackPath
    recomputeObligation

theorem ay_vrjs_build_drift_forces_no_claim
    (satFact unsatFact buildDrift fallbackPath recomputeObligation : Prop) :
    buildDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrjs_json_failure satFact unsatFact buildDrift fallbackPath
      recomputeObligation :=
  ay_vrjs_json_failure_intro satFact unsatFact buildDrift fallbackPath
    recomputeObligation

theorem ay_vrjs_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation : Prop) :
    archiveMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrjs_json_failure satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation :=
  ay_vrjs_json_failure_intro satFact unsatFact archiveMismatch fallbackPath
    recomputeObligation

theorem ay_vrjs_failed_json_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrjs_json_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vrjs_json_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vrjs_failed_json_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrjs_json_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vrjs_json_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
