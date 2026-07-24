-- SAT-COMP validator run manifest crosscheck core.
--
-- A sequential-main run may publish SAT/UNSAT only when run manifest, solver
-- config, benchmark fingerprint, result JSON, certificate bundle index,
-- stdout/stderr digests, checker transcripts, build config, archive manifest,
-- and fallback path agree.

def ay_vrmc_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrmc_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vrmc_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vrmc_disj satFact (ay_vrmc_disj unsatFact noClaimFact)

def ay_vrmc_run_crosscheck_contract
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) : Prop :=
  forall result : Prop,
    (runManifest -> solverConfig -> benchmarkFingerprint -> resultJson ->
      certificateBundleIndex -> stdoutStderrDigests -> checkerTranscripts ->
      buildConfig -> archiveManifest -> fallbackPath -> result) ->
    result

def ay_vrmc_sat_publication
    (runContract modelEvidence originalModel : Prop) : Prop :=
  ay_vrmc_conj runContract
    (ay_vrmc_conj modelEvidence originalModel)

def ay_vrmc_unsat_publication
    (runContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vrmc_conj runContract
    (ay_vrmc_conj proofEvidence originalEmptyClause)

def ay_vrmc_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vrmc_conj reason (ay_vrmc_conj fallbackPath auditTrail)

def ay_vrmc_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vrmc_conj reason
    (ay_vrmc_conj (satFact -> False) (unsatFact -> False))

def ay_vrmc_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vrmc_conj reason
    (ay_vrmc_conj fallbackPath recomputeObligation)

def ay_vrmc_crosscheck_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vrmc_conj
    (ay_vrmc_blocked_publication satFact unsatFact reason)
    (ay_vrmc_recompute reason fallbackPath recomputeObligation)

theorem ay_vrmc_conj_intro (left right : Prop) :
    left -> right -> ay_vrmc_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrmc_conj_left (left right : Prop) :
    ay_vrmc_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrmc_conj_right (left right : Prop) :
    ay_vrmc_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrmc_disj_left (left right : Prop) :
    left -> ay_vrmc_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vrmc_disj_right (left right : Prop) :
    right -> ay_vrmc_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrmc_run_crosscheck_contract_intro
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) :
    runManifest -> solverConfig -> benchmarkFingerprint -> resultJson ->
    certificateBundleIndex -> stdoutStderrDigests -> checkerTranscripts ->
    buildConfig -> archiveManifest -> fallbackPath ->
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath :=
  fun manifestProof solverConfigProof benchmarkProof jsonProof bundleProof
      logProof transcriptProof buildProof archiveProof fallbackProof result
      build =>
    build manifestProof solverConfigProof benchmarkProof jsonProof bundleProof
      logProof transcriptProof buildProof archiveProof fallbackProof

theorem ay_vrmc_run_crosscheck_contract_run_manifest
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    runManifest :=
  fun contract =>
    contract runManifest
      (fun manifestProof _solverConfigProof _benchmarkProof _jsonProof
          _bundleProof _logProof _transcriptProof _buildProof _archiveProof
          _fallbackProof => manifestProof)

theorem ay_vrmc_run_crosscheck_contract_solver_config
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    solverConfig :=
  fun contract =>
    contract solverConfig
      (fun _manifestProof solverConfigProof _benchmarkProof _jsonProof
          _bundleProof _logProof _transcriptProof _buildProof _archiveProof
          _fallbackProof => solverConfigProof)

theorem ay_vrmc_run_crosscheck_contract_benchmark_fingerprint
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _manifestProof _solverConfigProof benchmarkProof _jsonProof
          _bundleProof _logProof _transcriptProof _buildProof _archiveProof
          _fallbackProof => benchmarkProof)

theorem ay_vrmc_run_crosscheck_contract_result_json
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    resultJson :=
  fun contract =>
    contract resultJson
      (fun _manifestProof _solverConfigProof _benchmarkProof jsonProof
          _bundleProof _logProof _transcriptProof _buildProof _archiveProof
          _fallbackProof => jsonProof)

theorem ay_vrmc_run_crosscheck_contract_bundle_index
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    certificateBundleIndex :=
  fun contract =>
    contract certificateBundleIndex
      (fun _manifestProof _solverConfigProof _benchmarkProof _jsonProof
          bundleProof _logProof _transcriptProof _buildProof _archiveProof
          _fallbackProof => bundleProof)

theorem ay_vrmc_run_crosscheck_contract_log_digests
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    stdoutStderrDigests :=
  fun contract =>
    contract stdoutStderrDigests
      (fun _manifestProof _solverConfigProof _benchmarkProof _jsonProof
          _bundleProof logProof _transcriptProof _buildProof _archiveProof
          _fallbackProof => logProof)

theorem ay_vrmc_run_crosscheck_contract_transcripts
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _manifestProof _solverConfigProof _benchmarkProof _jsonProof
          _bundleProof _logProof transcriptProof _buildProof _archiveProof
          _fallbackProof => transcriptProof)

theorem ay_vrmc_run_crosscheck_contract_build_config
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _manifestProof _solverConfigProof _benchmarkProof _jsonProof
          _bundleProof _logProof _transcriptProof buildProof _archiveProof
          _fallbackProof => buildProof)

theorem ay_vrmc_run_crosscheck_contract_archive_manifest
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _manifestProof _solverConfigProof _benchmarkProof _jsonProof
          _bundleProof _logProof _transcriptProof _buildProof archiveProof
          _fallbackProof => archiveProof)

theorem ay_vrmc_run_crosscheck_contract_fallback_path
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    fallbackPath :=
  fun contract =>
    contract fallbackPath
      (fun _manifestProof _solverConfigProof _benchmarkProof _jsonProof
          _bundleProof _logProof _transcriptProof _buildProof _archiveProof
          fallbackProof => fallbackProof)

theorem ay_vrmc_sat_publication_intro
    (runContract modelEvidence originalModel : Prop) :
    runContract -> modelEvidence -> originalModel ->
    ay_vrmc_sat_publication runContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vrmc_conj_intro runContract
      (ay_vrmc_conj modelEvidence originalModel)
      contractProof
      (ay_vrmc_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vrmc_sat_publication_original_model
    (runContract modelEvidence originalModel : Prop) :
    ay_vrmc_sat_publication runContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vrmc_conj_right runContract
      (ay_vrmc_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vrmc_unsat_publication_intro
    (runContract proofEvidence originalEmptyClause : Prop) :
    runContract -> proofEvidence -> originalEmptyClause ->
    ay_vrmc_unsat_publication runContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vrmc_conj_intro runContract
      (ay_vrmc_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vrmc_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vrmc_unsat_publication_original_empty_clause
    (runContract proofEvidence originalEmptyClause : Prop) :
    ay_vrmc_unsat_publication runContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vrmc_conj_right runContract
      (ay_vrmc_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vrmc_accepted_run_crosscheck_sat_sound
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath modelEvidence originalModel : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vrmc_accepted_run_crosscheck_unsat_sound
    (runManifest solverConfig benchmarkFingerprint resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts buildConfig
      archiveManifest fallbackPath proofEvidence originalEmptyClause : Prop) :
    ay_vrmc_run_crosscheck_contract runManifest solverConfig
      benchmarkFingerprint resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vrmc_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vrmc_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vrmc_conj_intro reason
      (ay_vrmc_conj fallbackPath auditTrail)
      reasonProof
      (ay_vrmc_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_vrmc_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vrmc_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vrmc_conj_left reason
      (ay_vrmc_conj fallbackPath auditTrail)
      noClaim

theorem ay_vrmc_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vrmc_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vrmc_conj_intro reason
      (ay_vrmc_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vrmc_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vrmc_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vrmc_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vrmc_conj_right reason
      (ay_vrmc_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vrmc_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vrmc_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vrmc_conj_right reason
      (ay_vrmc_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vrmc_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vrmc_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vrmc_conj_intro reason
      (ay_vrmc_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_vrmc_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vrmc_crosscheck_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrmc_crosscheck_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vrmc_conj_intro
      (ay_vrmc_blocked_publication satFact unsatFact reason)
      (ay_vrmc_recompute reason fallbackPath recomputeObligation)
      (ay_vrmc_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vrmc_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vrmc_crosscheck_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrmc_crosscheck_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vrmc_blocked_publication_no_sat satFact unsatFact reason
      (ay_vrmc_conj_left
        (ay_vrmc_blocked_publication satFact unsatFact reason)
        (ay_vrmc_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vrmc_crosscheck_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrmc_crosscheck_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vrmc_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vrmc_conj_left
        (ay_vrmc_blocked_publication satFact unsatFact reason)
        (ay_vrmc_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vrmc_crosscheck_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrmc_crosscheck_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vrmc_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vrmc_conj_right
      (ay_vrmc_blocked_publication satFact unsatFact reason)
      (ay_vrmc_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vrmc_manifest_drift_forces_no_claim
    (satFact unsatFact manifestDrift fallbackPath
      recomputeObligation : Prop) :
    manifestDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrmc_crosscheck_failure satFact unsatFact manifestDrift fallbackPath
      recomputeObligation :=
  ay_vrmc_crosscheck_failure_intro satFact unsatFact manifestDrift
    fallbackPath recomputeObligation

theorem ay_vrmc_config_mismatch_forces_no_claim
    (satFact unsatFact configMismatch fallbackPath
      recomputeObligation : Prop) :
    configMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrmc_crosscheck_failure satFact unsatFact configMismatch fallbackPath
      recomputeObligation :=
  ay_vrmc_crosscheck_failure_intro satFact unsatFact configMismatch
    fallbackPath recomputeObligation

theorem ay_vrmc_benchmark_fingerprint_drift_forces_no_claim
    (satFact unsatFact benchmarkFingerprintDrift fallbackPath
      recomputeObligation : Prop) :
    benchmarkFingerprintDrift -> (satFact -> False) ->
    (unsatFact -> False) -> fallbackPath -> recomputeObligation ->
    ay_vrmc_crosscheck_failure satFact unsatFact benchmarkFingerprintDrift
      fallbackPath recomputeObligation :=
  ay_vrmc_crosscheck_failure_intro satFact unsatFact
    benchmarkFingerprintDrift fallbackPath recomputeObligation

theorem ay_vrmc_result_mismatch_forces_no_claim
    (satFact unsatFact resultMismatch fallbackPath
      recomputeObligation : Prop) :
    resultMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrmc_crosscheck_failure satFact unsatFact resultMismatch fallbackPath
      recomputeObligation :=
  ay_vrmc_crosscheck_failure_intro satFact unsatFact resultMismatch
    fallbackPath recomputeObligation

theorem ay_vrmc_bundle_mismatch_forces_no_claim
    (satFact unsatFact bundleMismatch fallbackPath
      recomputeObligation : Prop) :
    bundleMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrmc_crosscheck_failure satFact unsatFact bundleMismatch fallbackPath
      recomputeObligation :=
  ay_vrmc_crosscheck_failure_intro satFact unsatFact bundleMismatch
    fallbackPath recomputeObligation

theorem ay_vrmc_log_digest_drift_forces_no_claim
    (satFact unsatFact logDigestDrift fallbackPath
      recomputeObligation : Prop) :
    logDigestDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrmc_crosscheck_failure satFact unsatFact logDigestDrift fallbackPath
      recomputeObligation :=
  ay_vrmc_crosscheck_failure_intro satFact unsatFact logDigestDrift
    fallbackPath recomputeObligation

theorem ay_vrmc_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackPath
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrmc_crosscheck_failure satFact unsatFact missingTranscript
      fallbackPath recomputeObligation :=
  ay_vrmc_crosscheck_failure_intro satFact unsatFact missingTranscript
    fallbackPath recomputeObligation

theorem ay_vrmc_build_drift_forces_no_claim
    (satFact unsatFact buildDrift fallbackPath recomputeObligation : Prop) :
    buildDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrmc_crosscheck_failure satFact unsatFact buildDrift fallbackPath
      recomputeObligation :=
  ay_vrmc_crosscheck_failure_intro satFact unsatFact buildDrift fallbackPath
    recomputeObligation

theorem ay_vrmc_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation : Prop) :
    archiveMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrmc_crosscheck_failure satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation :=
  ay_vrmc_crosscheck_failure_intro satFact unsatFact archiveMismatch
    fallbackPath recomputeObligation

theorem ay_vrmc_run_ambiguity_forces_no_claim
    (satFact unsatFact runAmbiguity fallbackPath recomputeObligation : Prop) :
    runAmbiguity -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrmc_crosscheck_failure satFact unsatFact runAmbiguity fallbackPath
      recomputeObligation :=
  ay_vrmc_crosscheck_failure_intro satFact unsatFact runAmbiguity
    fallbackPath recomputeObligation

theorem ay_vrmc_failed_crosscheck_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrmc_crosscheck_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vrmc_crosscheck_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vrmc_failed_crosscheck_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrmc_crosscheck_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vrmc_crosscheck_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation
