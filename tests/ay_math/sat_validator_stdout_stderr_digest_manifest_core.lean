-- SAT-COMP validator stdout/stderr digest manifest core.
--
-- Public solver results may rely on stdout/stderr logs only when log digests,
-- solver exit code, output line, artifact digests, checker transcripts,
-- formula fingerprint, build config, archive manifest, and fallback path agree.

def ay_vsdm_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vsdm_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vsdm_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vsdm_disj satFact (ay_vsdm_disj unsatFact noClaimFact)

def ay_vsdm_log_manifest_contract
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) : Prop :=
  forall result : Prop,
    (stdoutDigest -> stderrDigest -> solverExitCode -> outputLine ->
      artifactDigests -> checkerTranscripts -> formulaFingerprint ->
      buildConfig -> archiveManifest -> fallbackPath -> result) ->
    result

def ay_vsdm_sat_publication
    (logContract modelEvidence originalModel : Prop) : Prop :=
  ay_vsdm_conj logContract
    (ay_vsdm_conj modelEvidence originalModel)

def ay_vsdm_unsat_publication
    (logContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vsdm_conj logContract
    (ay_vsdm_conj proofEvidence originalEmptyClause)

def ay_vsdm_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vsdm_conj reason (ay_vsdm_conj fallbackPath auditTrail)

def ay_vsdm_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vsdm_conj reason
    (ay_vsdm_conj (satFact -> False) (unsatFact -> False))

def ay_vsdm_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vsdm_conj reason
    (ay_vsdm_conj fallbackPath recomputeObligation)

def ay_vsdm_log_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vsdm_conj
    (ay_vsdm_blocked_publication satFact unsatFact reason)
    (ay_vsdm_recompute reason fallbackPath recomputeObligation)

theorem ay_vsdm_conj_intro (left right : Prop) :
    left -> right -> ay_vsdm_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vsdm_conj_left (left right : Prop) :
    ay_vsdm_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vsdm_conj_right (left right : Prop) :
    ay_vsdm_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vsdm_disj_left (left right : Prop) :
    left -> ay_vsdm_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vsdm_disj_right (left right : Prop) :
    right -> ay_vsdm_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vsdm_log_manifest_contract_intro
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    stdoutDigest -> stderrDigest -> solverExitCode -> outputLine ->
    artifactDigests -> checkerTranscripts -> formulaFingerprint ->
    buildConfig -> archiveManifest -> fallbackPath ->
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath :=
  fun stdoutProof stderrProof exitProof outputProof artifactProof
      transcriptProof fingerprintProof buildProof archiveProof fallbackProof
      result build =>
    build stdoutProof stderrProof exitProof outputProof artifactProof
      transcriptProof fingerprintProof buildProof archiveProof fallbackProof

theorem ay_vsdm_log_manifest_contract_stdout_digest
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    stdoutDigest :=
  fun contract =>
    contract stdoutDigest
      (fun stdoutProof _stderrProof _exitProof _outputProof _artifactProof
          _transcriptProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof => stdoutProof)

theorem ay_vsdm_log_manifest_contract_stderr_digest
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    stderrDigest :=
  fun contract =>
    contract stderrDigest
      (fun _stdoutProof stderrProof _exitProof _outputProof _artifactProof
          _transcriptProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof => stderrProof)

theorem ay_vsdm_log_manifest_contract_exit_code
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    solverExitCode :=
  fun contract =>
    contract solverExitCode
      (fun _stdoutProof _stderrProof exitProof _outputProof _artifactProof
          _transcriptProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof => exitProof)

theorem ay_vsdm_log_manifest_contract_output_line
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    outputLine :=
  fun contract =>
    contract outputLine
      (fun _stdoutProof _stderrProof _exitProof outputProof _artifactProof
          _transcriptProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof => outputProof)

theorem ay_vsdm_log_manifest_contract_artifact_digests
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    artifactDigests :=
  fun contract =>
    contract artifactDigests
      (fun _stdoutProof _stderrProof _exitProof _outputProof artifactProof
          _transcriptProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof => artifactProof)

theorem ay_vsdm_log_manifest_contract_transcripts
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _stdoutProof _stderrProof _exitProof _outputProof _artifactProof
          transcriptProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof => transcriptProof)

theorem ay_vsdm_log_manifest_contract_fingerprint
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    formulaFingerprint :=
  fun contract =>
    contract formulaFingerprint
      (fun _stdoutProof _stderrProof _exitProof _outputProof _artifactProof
          _transcriptProof fingerprintProof _buildProof _archiveProof
          _fallbackProof => fingerprintProof)

theorem ay_vsdm_log_manifest_contract_build_config
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _stdoutProof _stderrProof _exitProof _outputProof _artifactProof
          _transcriptProof _fingerprintProof buildProof _archiveProof
          _fallbackProof => buildProof)

theorem ay_vsdm_log_manifest_contract_archive_manifest
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _stdoutProof _stderrProof _exitProof _outputProof _artifactProof
          _transcriptProof _fingerprintProof _buildProof archiveProof
          _fallbackProof => archiveProof)

theorem ay_vsdm_log_manifest_contract_fallback_path
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    fallbackPath :=
  fun contract =>
    contract fallbackPath
      (fun _stdoutProof _stderrProof _exitProof _outputProof _artifactProof
          _transcriptProof _fingerprintProof _buildProof _archiveProof
          fallbackProof => fallbackProof)

theorem ay_vsdm_sat_publication_intro
    (logContract modelEvidence originalModel : Prop) :
    logContract -> modelEvidence -> originalModel ->
    ay_vsdm_sat_publication logContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vsdm_conj_intro logContract
      (ay_vsdm_conj modelEvidence originalModel)
      contractProof
      (ay_vsdm_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vsdm_sat_publication_original_model
    (logContract modelEvidence originalModel : Prop) :
    ay_vsdm_sat_publication logContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vsdm_conj_right logContract
      (ay_vsdm_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vsdm_unsat_publication_intro
    (logContract proofEvidence originalEmptyClause : Prop) :
    logContract -> proofEvidence -> originalEmptyClause ->
    ay_vsdm_unsat_publication logContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vsdm_conj_intro logContract
      (ay_vsdm_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vsdm_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vsdm_unsat_publication_original_empty_clause
    (logContract proofEvidence originalEmptyClause : Prop) :
    ay_vsdm_unsat_publication logContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vsdm_conj_right logContract
      (ay_vsdm_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vsdm_accepted_log_manifest_sat_sound
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath modelEvidence originalModel : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vsdm_accepted_log_manifest_unsat_sound
    (stdoutDigest stderrDigest solverExitCode outputLine artifactDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath proofEvidence originalEmptyClause : Prop) :
    ay_vsdm_log_manifest_contract stdoutDigest stderrDigest solverExitCode
      outputLine artifactDigests checkerTranscripts formulaFingerprint
      buildConfig archiveManifest fallbackPath ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vsdm_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vsdm_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vsdm_conj_intro reason
      (ay_vsdm_conj fallbackPath auditTrail)
      reasonProof
      (ay_vsdm_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_vsdm_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vsdm_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vsdm_conj_left reason
      (ay_vsdm_conj fallbackPath auditTrail)
      noClaim

theorem ay_vsdm_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vsdm_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vsdm_conj_intro reason
      (ay_vsdm_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vsdm_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vsdm_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vsdm_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vsdm_conj_right reason
      (ay_vsdm_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vsdm_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vsdm_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vsdm_conj_right reason
      (ay_vsdm_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vsdm_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vsdm_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vsdm_conj_intro reason
      (ay_vsdm_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_vsdm_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vsdm_log_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsdm_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vsdm_conj_intro
      (ay_vsdm_blocked_publication satFact unsatFact reason)
      (ay_vsdm_recompute reason fallbackPath recomputeObligation)
      (ay_vsdm_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vsdm_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vsdm_log_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsdm_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vsdm_blocked_publication_no_sat satFact unsatFact reason
      (ay_vsdm_conj_left
        (ay_vsdm_blocked_publication satFact unsatFact reason)
        (ay_vsdm_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsdm_log_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsdm_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vsdm_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vsdm_conj_left
        (ay_vsdm_blocked_publication satFact unsatFact reason)
        (ay_vsdm_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsdm_log_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsdm_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vsdm_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vsdm_conj_right
      (ay_vsdm_blocked_publication satFact unsatFact reason)
      (ay_vsdm_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vsdm_log_truncation_forces_no_claim
    (satFact unsatFact logTruncation fallbackPath
      recomputeObligation : Prop) :
    logTruncation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsdm_log_failure satFact unsatFact logTruncation fallbackPath
      recomputeObligation :=
  ay_vsdm_log_failure_intro satFact unsatFact logTruncation fallbackPath
    recomputeObligation

theorem ay_vsdm_digest_drift_forces_no_claim
    (satFact unsatFact digestDrift fallbackPath recomputeObligation : Prop) :
    digestDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsdm_log_failure satFact unsatFact digestDrift fallbackPath
      recomputeObligation :=
  ay_vsdm_log_failure_intro satFact unsatFact digestDrift fallbackPath
    recomputeObligation

theorem ay_vsdm_output_conflict_forces_no_claim
    (satFact unsatFact outputConflict fallbackPath
      recomputeObligation : Prop) :
    outputConflict -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsdm_log_failure satFact unsatFact outputConflict fallbackPath
      recomputeObligation :=
  ay_vsdm_log_failure_intro satFact unsatFact outputConflict fallbackPath
    recomputeObligation

theorem ay_vsdm_stale_artifact_forces_no_claim
    (satFact unsatFact staleArtifact fallbackPath
      recomputeObligation : Prop) :
    staleArtifact -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsdm_log_failure satFact unsatFact staleArtifact fallbackPath
      recomputeObligation :=
  ay_vsdm_log_failure_intro satFact unsatFact staleArtifact fallbackPath
    recomputeObligation

theorem ay_vsdm_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackPath
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsdm_log_failure satFact unsatFact missingTranscript fallbackPath
      recomputeObligation :=
  ay_vsdm_log_failure_intro satFact unsatFact missingTranscript fallbackPath
    recomputeObligation

theorem ay_vsdm_fingerprint_drift_forces_no_claim
    (satFact unsatFact fingerprintDrift fallbackPath
      recomputeObligation : Prop) :
    fingerprintDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsdm_log_failure satFact unsatFact fingerprintDrift fallbackPath
      recomputeObligation :=
  ay_vsdm_log_failure_intro satFact unsatFact fingerprintDrift fallbackPath
    recomputeObligation

theorem ay_vsdm_build_drift_forces_no_claim
    (satFact unsatFact buildDrift fallbackPath recomputeObligation : Prop) :
    buildDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsdm_log_failure satFact unsatFact buildDrift fallbackPath
      recomputeObligation :=
  ay_vsdm_log_failure_intro satFact unsatFact buildDrift fallbackPath
    recomputeObligation

theorem ay_vsdm_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation : Prop) :
    archiveMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsdm_log_failure satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation :=
  ay_vsdm_log_failure_intro satFact unsatFact archiveMismatch fallbackPath
    recomputeObligation

theorem ay_vsdm_failed_log_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsdm_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vsdm_log_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vsdm_failed_log_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsdm_log_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vsdm_log_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
