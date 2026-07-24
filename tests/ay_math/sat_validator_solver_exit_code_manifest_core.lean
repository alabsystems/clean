-- SAT-COMP validator solver exit-code manifest core.
--
-- Sequential-main solver exit codes may publish SAT/UNSAT only when the
-- output line, result artifacts, checker transcripts, formula fingerprint,
-- build config, archive/metadata manifests, and fallback/no-claim path agree.

def ay_vsem_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vsem_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vsem_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vsem_disj satFact (ay_vsem_disj unsatFact noClaimFact)

def ay_vsem_exit_manifest_contract
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath : Prop) : Prop :=
  forall result : Prop,
    (solverExitCode -> outputLine -> resultArtifacts -> checkerTranscripts ->
      formulaFingerprint -> buildConfig -> archiveManifest ->
      metadataManifest -> fallbackPath -> result) ->
    result

def ay_vsem_sat_publication
    (exitContract modelEvidence originalModel : Prop) : Prop :=
  ay_vsem_conj exitContract
    (ay_vsem_conj modelEvidence originalModel)

def ay_vsem_unsat_publication
    (exitContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vsem_conj exitContract
    (ay_vsem_conj proofEvidence originalEmptyClause)

def ay_vsem_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vsem_conj reason (ay_vsem_conj fallbackPath auditTrail)

def ay_vsem_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vsem_conj reason
    (ay_vsem_conj (satFact -> False) (unsatFact -> False))

def ay_vsem_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vsem_conj reason
    (ay_vsem_conj fallbackPath recomputeObligation)

def ay_vsem_exit_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vsem_conj
    (ay_vsem_blocked_publication satFact unsatFact reason)
    (ay_vsem_recompute reason fallbackPath recomputeObligation)

theorem ay_vsem_conj_intro (left right : Prop) :
    left -> right -> ay_vsem_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vsem_conj_left (left right : Prop) :
    ay_vsem_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vsem_conj_right (left right : Prop) :
    ay_vsem_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vsem_disj_left (left right : Prop) :
    left -> ay_vsem_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vsem_disj_right (left right : Prop) :
    right -> ay_vsem_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vsem_exit_manifest_contract_intro
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath : Prop) :
    solverExitCode -> outputLine -> resultArtifacts -> checkerTranscripts ->
    formulaFingerprint -> buildConfig -> archiveManifest ->
    metadataManifest -> fallbackPath ->
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath :=
  fun exitProof outputProof artifactProof transcriptProof fingerprintProof
      buildProof archiveProof metadataProof fallbackProof result build =>
    build exitProof outputProof artifactProof transcriptProof fingerprintProof
      buildProof archiveProof metadataProof fallbackProof

theorem ay_vsem_exit_manifest_contract_exit_code
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath : Prop) :
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath ->
    solverExitCode :=
  fun contract =>
    contract solverExitCode
      (fun exitProof _outputProof _artifactProof _transcriptProof
          _fingerprintProof _buildProof _archiveProof _metadataProof
          _fallbackProof => exitProof)

theorem ay_vsem_exit_manifest_contract_output_line
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath : Prop) :
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath ->
    outputLine :=
  fun contract =>
    contract outputLine
      (fun _exitProof outputProof _artifactProof _transcriptProof
          _fingerprintProof _buildProof _archiveProof _metadataProof
          _fallbackProof => outputProof)

theorem ay_vsem_exit_manifest_contract_artifacts
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath : Prop) :
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath ->
    resultArtifacts :=
  fun contract =>
    contract resultArtifacts
      (fun _exitProof _outputProof artifactProof _transcriptProof
          _fingerprintProof _buildProof _archiveProof _metadataProof
          _fallbackProof => artifactProof)

theorem ay_vsem_exit_manifest_contract_transcripts
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath : Prop) :
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _exitProof _outputProof _artifactProof transcriptProof
          _fingerprintProof _buildProof _archiveProof _metadataProof
          _fallbackProof => transcriptProof)

theorem ay_vsem_exit_manifest_contract_fingerprint
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath : Prop) :
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath ->
    formulaFingerprint :=
  fun contract =>
    contract formulaFingerprint
      (fun _exitProof _outputProof _artifactProof _transcriptProof
          fingerprintProof _buildProof _archiveProof _metadataProof
          _fallbackProof => fingerprintProof)

theorem ay_vsem_exit_manifest_contract_build_config
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath : Prop) :
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _exitProof _outputProof _artifactProof _transcriptProof
          _fingerprintProof buildProof _archiveProof _metadataProof
          _fallbackProof => buildProof)

theorem ay_vsem_exit_manifest_contract_archive_manifest
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath : Prop) :
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _exitProof _outputProof _artifactProof _transcriptProof
          _fingerprintProof _buildProof archiveProof _metadataProof
          _fallbackProof => archiveProof)

theorem ay_vsem_exit_manifest_contract_metadata_manifest
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath : Prop) :
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath ->
    metadataManifest :=
  fun contract =>
    contract metadataManifest
      (fun _exitProof _outputProof _artifactProof _transcriptProof
          _fingerprintProof _buildProof _archiveProof metadataProof
          _fallbackProof => metadataProof)

theorem ay_vsem_exit_manifest_contract_fallback_path
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath : Prop) :
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath ->
    fallbackPath :=
  fun contract =>
    contract fallbackPath
      (fun _exitProof _outputProof _artifactProof _transcriptProof
          _fingerprintProof _buildProof _archiveProof _metadataProof
          fallbackProof => fallbackProof)

theorem ay_vsem_sat_publication_intro
    (exitContract modelEvidence originalModel : Prop) :
    exitContract -> modelEvidence -> originalModel ->
    ay_vsem_sat_publication exitContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vsem_conj_intro exitContract
      (ay_vsem_conj modelEvidence originalModel)
      contractProof
      (ay_vsem_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vsem_sat_publication_original_model
    (exitContract modelEvidence originalModel : Prop) :
    ay_vsem_sat_publication exitContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vsem_conj_right exitContract
      (ay_vsem_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vsem_unsat_publication_intro
    (exitContract proofEvidence originalEmptyClause : Prop) :
    exitContract -> proofEvidence -> originalEmptyClause ->
    ay_vsem_unsat_publication exitContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vsem_conj_intro exitContract
      (ay_vsem_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vsem_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vsem_unsat_publication_original_empty_clause
    (exitContract proofEvidence originalEmptyClause : Prop) :
    ay_vsem_unsat_publication exitContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vsem_conj_right exitContract
      (ay_vsem_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vsem_accepted_exit_manifest_sat_sound
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath modelEvidence originalModel : Prop) :
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vsem_accepted_exit_manifest_unsat_sound
    (solverExitCode outputLine resultArtifacts checkerTranscripts
      formulaFingerprint buildConfig archiveManifest metadataManifest
      fallbackPath proofEvidence originalEmptyClause : Prop) :
    ay_vsem_exit_manifest_contract solverExitCode outputLine
      resultArtifacts checkerTranscripts formulaFingerprint buildConfig
      archiveManifest metadataManifest fallbackPath ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vsem_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vsem_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vsem_conj_intro reason
      (ay_vsem_conj fallbackPath auditTrail)
      reasonProof
      (ay_vsem_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_vsem_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vsem_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vsem_conj_left reason
      (ay_vsem_conj fallbackPath auditTrail)
      noClaim

theorem ay_vsem_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vsem_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vsem_conj_intro reason
      (ay_vsem_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vsem_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vsem_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vsem_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vsem_conj_right reason
      (ay_vsem_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vsem_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vsem_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vsem_conj_right reason
      (ay_vsem_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vsem_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vsem_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vsem_conj_intro reason
      (ay_vsem_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_vsem_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vsem_exit_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsem_exit_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vsem_conj_intro
      (ay_vsem_blocked_publication satFact unsatFact reason)
      (ay_vsem_recompute reason fallbackPath recomputeObligation)
      (ay_vsem_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vsem_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vsem_exit_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsem_exit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vsem_blocked_publication_no_sat satFact unsatFact reason
      (ay_vsem_conj_left
        (ay_vsem_blocked_publication satFact unsatFact reason)
        (ay_vsem_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsem_exit_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsem_exit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vsem_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vsem_conj_left
        (ay_vsem_blocked_publication satFact unsatFact reason)
        (ay_vsem_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsem_exit_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsem_exit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vsem_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vsem_conj_right
      (ay_vsem_blocked_publication satFact unsatFact reason)
      (ay_vsem_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vsem_exit_code_mismatch_forces_no_claim
    (satFact unsatFact exitCodeMismatch fallbackPath
      recomputeObligation : Prop) :
    exitCodeMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsem_exit_failure satFact unsatFact exitCodeMismatch fallbackPath
      recomputeObligation :=
  ay_vsem_exit_failure_intro satFact unsatFact exitCodeMismatch fallbackPath
    recomputeObligation

theorem ay_vsem_stale_artifacts_forces_no_claim
    (satFact unsatFact staleArtifacts fallbackPath
      recomputeObligation : Prop) :
    staleArtifacts -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsem_exit_failure satFact unsatFact staleArtifacts fallbackPath
      recomputeObligation :=
  ay_vsem_exit_failure_intro satFact unsatFact staleArtifacts fallbackPath
    recomputeObligation

theorem ay_vsem_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackPath
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsem_exit_failure satFact unsatFact missingTranscript fallbackPath
      recomputeObligation :=
  ay_vsem_exit_failure_intro satFact unsatFact missingTranscript fallbackPath
    recomputeObligation

theorem ay_vsem_fingerprint_drift_forces_no_claim
    (satFact unsatFact fingerprintDrift fallbackPath
      recomputeObligation : Prop) :
    fingerprintDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsem_exit_failure satFact unsatFact fingerprintDrift fallbackPath
      recomputeObligation :=
  ay_vsem_exit_failure_intro satFact unsatFact fingerprintDrift fallbackPath
    recomputeObligation

theorem ay_vsem_build_drift_forces_no_claim
    (satFact unsatFact buildDrift fallbackPath recomputeObligation : Prop) :
    buildDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsem_exit_failure satFact unsatFact buildDrift fallbackPath
      recomputeObligation :=
  ay_vsem_exit_failure_intro satFact unsatFact buildDrift fallbackPath
    recomputeObligation

theorem ay_vsem_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation : Prop) :
    archiveMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsem_exit_failure satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation :=
  ay_vsem_exit_failure_intro satFact unsatFact archiveMismatch fallbackPath
    recomputeObligation

theorem ay_vsem_output_conflict_forces_no_claim
    (satFact unsatFact outputConflict fallbackPath
      recomputeObligation : Prop) :
    outputConflict -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsem_exit_failure satFact unsatFact outputConflict fallbackPath
      recomputeObligation :=
  ay_vsem_exit_failure_intro satFact unsatFact outputConflict fallbackPath
    recomputeObligation

theorem ay_vsem_failed_exit_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsem_exit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vsem_exit_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vsem_failed_exit_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsem_exit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vsem_exit_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
