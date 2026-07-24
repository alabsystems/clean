-- SAT-COMP validator competition archive manifest core.
--
-- Archived result directories, logs, model/proof artifacts, checker
-- transcripts, formula fingerprints, build configs, and output lines may
-- support publication only when archive manifest and cross-file digests agree.

def ay_vcam_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vcam_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vcam_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vcam_disj satFact (ay_vcam_disj unsatFact noClaimFact)

def ay_vcam_archive_contract
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) : Prop :=
  forall result : Prop,
    (archiveManifest -> crossFileDigests -> archivedResultDirectories ->
      archivedLogs -> modelOrProofArtifacts -> checkerTranscripts ->
      formulaFingerprints -> buildConfigs -> outputLines ->
      fallbackDiagnostics -> result) ->
    result

def ay_vcam_sat_publication
    (archiveContract modelEvidence originalModel : Prop) : Prop :=
  ay_vcam_conj archiveContract
    (ay_vcam_conj modelEvidence originalModel)

def ay_vcam_unsat_publication
    (archiveContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vcam_conj archiveContract
    (ay_vcam_conj proofEvidence originalEmptyClause)

def ay_vcam_no_claim
    (reason fallbackDiagnostics auditTrail : Prop) : Prop :=
  ay_vcam_conj reason (ay_vcam_conj fallbackDiagnostics auditTrail)

def ay_vcam_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vcam_conj reason
    (ay_vcam_conj (satFact -> False) (unsatFact -> False))

def ay_vcam_recompute
    (reason fallbackDiagnostics recomputeObligation : Prop) : Prop :=
  ay_vcam_conj reason
    (ay_vcam_conj fallbackDiagnostics recomputeObligation)

def ay_vcam_archive_failure
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) : Prop :=
  ay_vcam_conj
    (ay_vcam_blocked_publication satFact unsatFact reason)
    (ay_vcam_recompute reason fallbackDiagnostics recomputeObligation)

theorem ay_vcam_conj_intro (left right : Prop) :
    left -> right -> ay_vcam_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcam_conj_left (left right : Prop) :
    ay_vcam_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcam_conj_right (left right : Prop) :
    ay_vcam_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcam_disj_left (left right : Prop) :
    left -> ay_vcam_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vcam_disj_right (left right : Prop) :
    right -> ay_vcam_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcam_archive_contract_intro
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) :
    archiveManifest -> crossFileDigests -> archivedResultDirectories ->
    archivedLogs -> modelOrProofArtifacts -> checkerTranscripts ->
    formulaFingerprints -> buildConfigs -> outputLines ->
    fallbackDiagnostics ->
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics :=
  fun manifestProof digestProof directoriesProof logsProof artifactsProof
      transcriptsProof fingerprintsProof buildProof outputProof fallbackProof
      result build =>
    build manifestProof digestProof directoriesProof logsProof artifactsProof
      transcriptsProof fingerprintsProof buildProof outputProof fallbackProof

theorem ay_vcam_archive_contract_manifest
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun manifestProof _digestProof _directoriesProof _logsProof
          _artifactsProof _transcriptsProof _fingerprintsProof _buildProof
          _outputProof _fallbackProof => manifestProof)

theorem ay_vcam_archive_contract_cross_file_digests
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    crossFileDigests :=
  fun contract =>
    contract crossFileDigests
      (fun _manifestProof digestProof _directoriesProof _logsProof
          _artifactsProof _transcriptsProof _fingerprintsProof _buildProof
          _outputProof _fallbackProof => digestProof)

theorem ay_vcam_archive_contract_result_directories
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    archivedResultDirectories :=
  fun contract =>
    contract archivedResultDirectories
      (fun _manifestProof _digestProof directoriesProof _logsProof
          _artifactsProof _transcriptsProof _fingerprintsProof _buildProof
          _outputProof _fallbackProof => directoriesProof)

theorem ay_vcam_archive_contract_logs
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    archivedLogs :=
  fun contract =>
    contract archivedLogs
      (fun _manifestProof _digestProof _directoriesProof logsProof
          _artifactsProof _transcriptsProof _fingerprintsProof _buildProof
          _outputProof _fallbackProof => logsProof)

theorem ay_vcam_archive_contract_artifacts
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    modelOrProofArtifacts :=
  fun contract =>
    contract modelOrProofArtifacts
      (fun _manifestProof _digestProof _directoriesProof _logsProof
          artifactsProof _transcriptsProof _fingerprintsProof _buildProof
          _outputProof _fallbackProof => artifactsProof)

theorem ay_vcam_archive_contract_transcripts
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _manifestProof _digestProof _directoriesProof _logsProof
          _artifactsProof transcriptsProof _fingerprintsProof _buildProof
          _outputProof _fallbackProof => transcriptsProof)

theorem ay_vcam_archive_contract_fingerprints
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    formulaFingerprints :=
  fun contract =>
    contract formulaFingerprints
      (fun _manifestProof _digestProof _directoriesProof _logsProof
          _artifactsProof _transcriptsProof fingerprintsProof _buildProof
          _outputProof _fallbackProof => fingerprintsProof)

theorem ay_vcam_archive_contract_build_configs
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    buildConfigs :=
  fun contract =>
    contract buildConfigs
      (fun _manifestProof _digestProof _directoriesProof _logsProof
          _artifactsProof _transcriptsProof _fingerprintsProof buildProof
          _outputProof _fallbackProof => buildProof)

theorem ay_vcam_archive_contract_output_lines
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    outputLines :=
  fun contract =>
    contract outputLines
      (fun _manifestProof _digestProof _directoriesProof _logsProof
          _artifactsProof _transcriptsProof _fingerprintsProof _buildProof
          outputProof _fallbackProof => outputProof)

theorem ay_vcam_archive_contract_fallback
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    fallbackDiagnostics :=
  fun contract =>
    contract fallbackDiagnostics
      (fun _manifestProof _digestProof _directoriesProof _logsProof
          _artifactsProof _transcriptsProof _fingerprintsProof _buildProof
          _outputProof fallbackProof => fallbackProof)

theorem ay_vcam_sat_publication_intro
    (archiveContract modelEvidence originalModel : Prop) :
    archiveContract -> modelEvidence -> originalModel ->
    ay_vcam_sat_publication archiveContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vcam_conj_intro archiveContract
      (ay_vcam_conj modelEvidence originalModel)
      contractProof
      (ay_vcam_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vcam_sat_publication_original_model
    (archiveContract modelEvidence originalModel : Prop) :
    ay_vcam_sat_publication archiveContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vcam_conj_right archiveContract
      (ay_vcam_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vcam_unsat_publication_intro
    (archiveContract proofEvidence originalEmptyClause : Prop) :
    archiveContract -> proofEvidence -> originalEmptyClause ->
    ay_vcam_unsat_publication archiveContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vcam_conj_intro archiveContract
      (ay_vcam_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vcam_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vcam_unsat_publication_original_empty_clause
    (archiveContract proofEvidence originalEmptyClause : Prop) :
    ay_vcam_unsat_publication archiveContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vcam_conj_right archiveContract
      (ay_vcam_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vcam_accepted_archive_sat_sound
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics modelEvidence originalModel : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vcam_accepted_archive_unsat_sound
    (archiveManifest crossFileDigests archivedResultDirectories archivedLogs
      modelOrProofArtifacts checkerTranscripts formulaFingerprints buildConfigs
      outputLines fallbackDiagnostics proofEvidence
      originalEmptyClause : Prop) :
    ay_vcam_archive_contract archiveManifest crossFileDigests
      archivedResultDirectories archivedLogs modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs outputLines
      fallbackDiagnostics ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vcam_no_claim_intro
    (reason fallbackDiagnostics auditTrail : Prop) :
    reason -> fallbackDiagnostics -> auditTrail ->
    ay_vcam_no_claim reason fallbackDiagnostics auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vcam_conj_intro reason
      (ay_vcam_conj fallbackDiagnostics auditTrail)
      reasonProof
      (ay_vcam_conj_intro fallbackDiagnostics auditTrail
        fallbackProof auditProof)

theorem ay_vcam_no_claim_reason
    (reason fallbackDiagnostics auditTrail : Prop) :
    ay_vcam_no_claim reason fallbackDiagnostics auditTrail -> reason :=
  fun noClaim =>
    ay_vcam_conj_left reason
      (ay_vcam_conj fallbackDiagnostics auditTrail)
      noClaim

theorem ay_vcam_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vcam_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vcam_conj_intro reason
      (ay_vcam_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vcam_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vcam_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vcam_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vcam_conj_right reason
      (ay_vcam_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vcam_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vcam_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vcam_conj_right reason
      (ay_vcam_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vcam_recompute_intro
    (reason fallbackDiagnostics recomputeObligation : Prop) :
    reason -> fallbackDiagnostics -> recomputeObligation ->
    ay_vcam_recompute reason fallbackDiagnostics recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vcam_conj_intro reason
      (ay_vcam_conj fallbackDiagnostics recomputeObligation)
      reasonProof
      (ay_vcam_conj_intro fallbackDiagnostics recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vcam_archive_failure_intro
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcam_archive_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vcam_conj_intro
      (ay_vcam_blocked_publication satFact unsatFact reason)
      (ay_vcam_recompute reason fallbackDiagnostics recomputeObligation)
      (ay_vcam_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vcam_recompute_intro reason fallbackDiagnostics recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vcam_archive_failure_blocks_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcam_archive_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vcam_blocked_publication_no_sat satFact unsatFact reason
      (ay_vcam_conj_left
        (ay_vcam_blocked_publication satFact unsatFact reason)
        (ay_vcam_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vcam_archive_failure_blocks_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcam_archive_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vcam_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vcam_conj_left
        (ay_vcam_blocked_publication satFact unsatFact reason)
        (ay_vcam_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vcam_archive_failure_recompute
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcam_archive_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    ay_vcam_recompute reason fallbackDiagnostics recomputeObligation :=
  fun failure =>
    ay_vcam_conj_right
      (ay_vcam_blocked_publication satFact unsatFact reason)
      (ay_vcam_recompute reason fallbackDiagnostics recomputeObligation)
      failure

theorem ay_vcam_missing_archived_file_forces_no_claim
    (satFact unsatFact missingArchivedFile fallbackDiagnostics
      recomputeObligation : Prop) :
    missingArchivedFile -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcam_archive_failure satFact unsatFact missingArchivedFile
      fallbackDiagnostics recomputeObligation :=
  ay_vcam_archive_failure_intro satFact unsatFact missingArchivedFile
    fallbackDiagnostics recomputeObligation

theorem ay_vcam_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch fallbackDiagnostics
      recomputeObligation : Prop) :
    digestMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcam_archive_failure satFact unsatFact digestMismatch
      fallbackDiagnostics recomputeObligation :=
  ay_vcam_archive_failure_intro satFact unsatFact digestMismatch
    fallbackDiagnostics recomputeObligation

theorem ay_vcam_stale_fingerprint_forces_no_claim
    (satFact unsatFact staleFingerprint fallbackDiagnostics
      recomputeObligation : Prop) :
    staleFingerprint -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcam_archive_failure satFact unsatFact staleFingerprint
      fallbackDiagnostics recomputeObligation :=
  ay_vcam_archive_failure_intro satFact unsatFact staleFingerprint
    fallbackDiagnostics recomputeObligation

theorem ay_vcam_output_conflict_forces_no_claim
    (satFact unsatFact outputConflict fallbackDiagnostics
      recomputeObligation : Prop) :
    outputConflict -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcam_archive_failure satFact unsatFact outputConflict
      fallbackDiagnostics recomputeObligation :=
  ay_vcam_archive_failure_intro satFact unsatFact outputConflict
    fallbackDiagnostics recomputeObligation

theorem ay_vcam_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackDiagnostics
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcam_archive_failure satFact unsatFact missingTranscript
      fallbackDiagnostics recomputeObligation :=
  ay_vcam_archive_failure_intro satFact unsatFact missingTranscript
    fallbackDiagnostics recomputeObligation

theorem ay_vcam_failed_archive_cannot_bless_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcam_archive_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  ay_vcam_archive_failure_blocks_sat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation

theorem ay_vcam_failed_archive_cannot_bless_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcam_archive_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  ay_vcam_archive_failure_blocks_unsat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation
