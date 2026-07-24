-- SAT-COMP validator competition submission manifest core.
--
-- Final sequential-main submission publication may certify SAT/UNSAT only when
-- submission manifest, run manifests, result JSON, certificate bundle index,
-- solver config, benchmark fingerprints, stdout/stderr digests, checker
-- transcripts, build config, archive manifest, and fallback path agree.

def ay_vcsm_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vcsm_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vcsm_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vcsm_disj satFact (ay_vcsm_disj unsatFact noClaimFact)

def ay_vcsm_submission_contract
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    Prop :=
  forall result : Prop,
    (submissionManifest -> runManifests -> resultJson ->
      certificateBundleIndex -> solverConfig -> benchmarkFingerprints ->
      stdoutStderrDigests -> checkerTranscripts -> buildConfig ->
      archiveManifest -> fallbackPath -> result) ->
    result

def ay_vcsm_sat_publication
    (submissionContract modelEvidence originalModel : Prop) : Prop :=
  ay_vcsm_conj submissionContract
    (ay_vcsm_conj modelEvidence originalModel)

def ay_vcsm_unsat_publication
    (submissionContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vcsm_conj submissionContract
    (ay_vcsm_conj proofEvidence originalEmptyClause)

def ay_vcsm_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vcsm_conj reason (ay_vcsm_conj fallbackPath auditTrail)

def ay_vcsm_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vcsm_conj reason
    (ay_vcsm_conj (satFact -> False) (unsatFact -> False))

def ay_vcsm_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vcsm_conj reason
    (ay_vcsm_conj fallbackPath recomputeObligation)

def ay_vcsm_submission_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vcsm_conj
    (ay_vcsm_blocked_publication satFact unsatFact reason)
    (ay_vcsm_recompute reason fallbackPath recomputeObligation)

theorem ay_vcsm_conj_intro (left right : Prop) :
    left -> right -> ay_vcsm_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcsm_conj_left (left right : Prop) :
    ay_vcsm_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcsm_conj_right (left right : Prop) :
    ay_vcsm_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcsm_disj_left (left right : Prop) :
    left -> ay_vcsm_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vcsm_disj_right (left right : Prop) :
    right -> ay_vcsm_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcsm_submission_contract_intro
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    submissionManifest -> runManifests -> resultJson ->
    certificateBundleIndex -> solverConfig -> benchmarkFingerprints ->
    stdoutStderrDigests -> checkerTranscripts -> buildConfig ->
    archiveManifest -> fallbackPath ->
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath :=
  fun submissionProof runProof jsonProof bundleProof solverConfigProof
      benchmarkProof logProof transcriptProof buildProof archiveProof
      fallbackProof result build =>
    build submissionProof runProof jsonProof bundleProof solverConfigProof
      benchmarkProof logProof transcriptProof buildProof archiveProof
      fallbackProof

theorem ay_vcsm_submission_contract_submission_manifest
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun submissionProof _runProof _jsonProof _bundleProof
          _solverConfigProof _benchmarkProof _logProof _transcriptProof
          _buildProof _archiveProof _fallbackProof => submissionProof)

theorem ay_vcsm_submission_contract_run_manifests
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    runManifests :=
  fun contract =>
    contract runManifests
      (fun _submissionProof runProof _jsonProof _bundleProof
          _solverConfigProof _benchmarkProof _logProof _transcriptProof
          _buildProof _archiveProof _fallbackProof => runProof)

theorem ay_vcsm_submission_contract_result_json
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    resultJson :=
  fun contract =>
    contract resultJson
      (fun _submissionProof _runProof jsonProof _bundleProof
          _solverConfigProof _benchmarkProof _logProof _transcriptProof
          _buildProof _archiveProof _fallbackProof => jsonProof)

theorem ay_vcsm_submission_contract_bundle_index
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    certificateBundleIndex :=
  fun contract =>
    contract certificateBundleIndex
      (fun _submissionProof _runProof _jsonProof bundleProof
          _solverConfigProof _benchmarkProof _logProof _transcriptProof
          _buildProof _archiveProof _fallbackProof => bundleProof)

theorem ay_vcsm_submission_contract_solver_config
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    solverConfig :=
  fun contract =>
    contract solverConfig
      (fun _submissionProof _runProof _jsonProof _bundleProof
          solverConfigProof _benchmarkProof _logProof _transcriptProof
          _buildProof _archiveProof _fallbackProof => solverConfigProof)

theorem ay_vcsm_submission_contract_benchmark_fingerprints
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    benchmarkFingerprints :=
  fun contract =>
    contract benchmarkFingerprints
      (fun _submissionProof _runProof _jsonProof _bundleProof
          _solverConfigProof benchmarkProof _logProof _transcriptProof
          _buildProof _archiveProof _fallbackProof => benchmarkProof)

theorem ay_vcsm_submission_contract_log_digests
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    stdoutStderrDigests :=
  fun contract =>
    contract stdoutStderrDigests
      (fun _submissionProof _runProof _jsonProof _bundleProof
          _solverConfigProof _benchmarkProof logProof _transcriptProof
          _buildProof _archiveProof _fallbackProof => logProof)

theorem ay_vcsm_submission_contract_transcripts
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _submissionProof _runProof _jsonProof _bundleProof
          _solverConfigProof _benchmarkProof _logProof transcriptProof
          _buildProof _archiveProof _fallbackProof => transcriptProof)

theorem ay_vcsm_submission_contract_build_config
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _submissionProof _runProof _jsonProof _bundleProof
          _solverConfigProof _benchmarkProof _logProof _transcriptProof
          buildProof _archiveProof _fallbackProof => buildProof)

theorem ay_vcsm_submission_contract_archive_manifest
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _submissionProof _runProof _jsonProof _bundleProof
          _solverConfigProof _benchmarkProof _logProof _transcriptProof
          _buildProof archiveProof _fallbackProof => archiveProof)

theorem ay_vcsm_submission_contract_fallback_path
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    fallbackPath :=
  fun contract =>
    contract fallbackPath
      (fun _submissionProof _runProof _jsonProof _bundleProof
          _solverConfigProof _benchmarkProof _logProof _transcriptProof
          _buildProof _archiveProof fallbackProof => fallbackProof)

theorem ay_vcsm_sat_publication_intro
    (submissionContract modelEvidence originalModel : Prop) :
    submissionContract -> modelEvidence -> originalModel ->
    ay_vcsm_sat_publication submissionContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vcsm_conj_intro submissionContract
      (ay_vcsm_conj modelEvidence originalModel)
      contractProof
      (ay_vcsm_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vcsm_sat_publication_original_model
    (submissionContract modelEvidence originalModel : Prop) :
    ay_vcsm_sat_publication submissionContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vcsm_conj_right submissionContract
      (ay_vcsm_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vcsm_unsat_publication_intro
    (submissionContract proofEvidence originalEmptyClause : Prop) :
    submissionContract -> proofEvidence -> originalEmptyClause ->
    ay_vcsm_unsat_publication submissionContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vcsm_conj_intro submissionContract
      (ay_vcsm_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vcsm_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vcsm_unsat_publication_original_empty_clause
    (submissionContract proofEvidence originalEmptyClause : Prop) :
    ay_vcsm_unsat_publication submissionContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vcsm_conj_right submissionContract
      (ay_vcsm_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vcsm_accepted_submission_sat_sound
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath modelEvidence
      originalModel : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vcsm_accepted_submission_unsat_sound
    (submissionManifest runManifests resultJson certificateBundleIndex
      solverConfig benchmarkFingerprints stdoutStderrDigests
      checkerTranscripts buildConfig archiveManifest fallbackPath proofEvidence
      originalEmptyClause : Prop) :
    ay_vcsm_submission_contract submissionManifest runManifests resultJson
      certificateBundleIndex solverConfig benchmarkFingerprints
      stdoutStderrDigests checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vcsm_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vcsm_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vcsm_conj_intro reason
      (ay_vcsm_conj fallbackPath auditTrail)
      reasonProof
      (ay_vcsm_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_vcsm_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vcsm_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vcsm_conj_left reason
      (ay_vcsm_conj fallbackPath auditTrail)
      noClaim

theorem ay_vcsm_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vcsm_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vcsm_conj_intro reason
      (ay_vcsm_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vcsm_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vcsm_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vcsm_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vcsm_conj_right reason
      (ay_vcsm_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vcsm_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vcsm_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vcsm_conj_right reason
      (ay_vcsm_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vcsm_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vcsm_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vcsm_conj_intro reason
      (ay_vcsm_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_vcsm_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vcsm_submission_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vcsm_conj_intro
      (ay_vcsm_blocked_publication satFact unsatFact reason)
      (ay_vcsm_recompute reason fallbackPath recomputeObligation)
      (ay_vcsm_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vcsm_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vcsm_submission_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcsm_submission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vcsm_blocked_publication_no_sat satFact unsatFact reason
      (ay_vcsm_conj_left
        (ay_vcsm_blocked_publication satFact unsatFact reason)
        (ay_vcsm_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vcsm_submission_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcsm_submission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vcsm_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vcsm_conj_left
        (ay_vcsm_blocked_publication satFact unsatFact reason)
        (ay_vcsm_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vcsm_submission_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcsm_submission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vcsm_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vcsm_conj_right
      (ay_vcsm_blocked_publication satFact unsatFact reason)
      (ay_vcsm_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vcsm_submission_manifest_drift_forces_no_claim
    (satFact unsatFact submissionManifestDrift fallbackPath
      recomputeObligation : Prop) :
    submissionManifestDrift -> (satFact -> False) ->
    (unsatFact -> False) -> fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact submissionManifestDrift
      fallbackPath recomputeObligation :=
  ay_vcsm_submission_failure_intro satFact unsatFact
    submissionManifestDrift fallbackPath recomputeObligation

theorem ay_vcsm_missing_run_forces_no_claim
    (satFact unsatFact missingRun fallbackPath recomputeObligation : Prop) :
    missingRun -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact missingRun fallbackPath
      recomputeObligation :=
  ay_vcsm_submission_failure_intro satFact unsatFact missingRun fallbackPath
    recomputeObligation

theorem ay_vcsm_result_mismatch_forces_no_claim
    (satFact unsatFact resultMismatch fallbackPath
      recomputeObligation : Prop) :
    resultMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact resultMismatch fallbackPath
      recomputeObligation :=
  ay_vcsm_submission_failure_intro satFact unsatFact resultMismatch
    fallbackPath recomputeObligation

theorem ay_vcsm_bundle_mismatch_forces_no_claim
    (satFact unsatFact bundleMismatch fallbackPath
      recomputeObligation : Prop) :
    bundleMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact bundleMismatch fallbackPath
      recomputeObligation :=
  ay_vcsm_submission_failure_intro satFact unsatFact bundleMismatch
    fallbackPath recomputeObligation

theorem ay_vcsm_config_mismatch_forces_no_claim
    (satFact unsatFact configMismatch fallbackPath
      recomputeObligation : Prop) :
    configMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact configMismatch fallbackPath
      recomputeObligation :=
  ay_vcsm_submission_failure_intro satFact unsatFact configMismatch
    fallbackPath recomputeObligation

theorem ay_vcsm_benchmark_drift_forces_no_claim
    (satFact unsatFact benchmarkDrift fallbackPath
      recomputeObligation : Prop) :
    benchmarkDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact benchmarkDrift fallbackPath
      recomputeObligation :=
  ay_vcsm_submission_failure_intro satFact unsatFact benchmarkDrift
    fallbackPath recomputeObligation

theorem ay_vcsm_log_digest_drift_forces_no_claim
    (satFact unsatFact logDigestDrift fallbackPath
      recomputeObligation : Prop) :
    logDigestDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact logDigestDrift fallbackPath
      recomputeObligation :=
  ay_vcsm_submission_failure_intro satFact unsatFact logDigestDrift
    fallbackPath recomputeObligation

theorem ay_vcsm_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackPath
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact missingTranscript
      fallbackPath recomputeObligation :=
  ay_vcsm_submission_failure_intro satFact unsatFact missingTranscript
    fallbackPath recomputeObligation

theorem ay_vcsm_build_drift_forces_no_claim
    (satFact unsatFact buildDrift fallbackPath recomputeObligation : Prop) :
    buildDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact buildDrift fallbackPath
      recomputeObligation :=
  ay_vcsm_submission_failure_intro satFact unsatFact buildDrift fallbackPath
    recomputeObligation

theorem ay_vcsm_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation : Prop) :
    archiveMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation :=
  ay_vcsm_submission_failure_intro satFact unsatFact archiveMismatch
    fallbackPath recomputeObligation

theorem ay_vcsm_duplicate_or_ambiguous_run_forces_no_claim
    (satFact unsatFact duplicateOrAmbiguousRun fallbackPath
      recomputeObligation : Prop) :
    duplicateOrAmbiguousRun -> (satFact -> False) ->
    (unsatFact -> False) -> fallbackPath -> recomputeObligation ->
    ay_vcsm_submission_failure satFact unsatFact duplicateOrAmbiguousRun
      fallbackPath recomputeObligation :=
  ay_vcsm_submission_failure_intro satFact unsatFact duplicateOrAmbiguousRun
    fallbackPath recomputeObligation

theorem ay_vcsm_failed_submission_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcsm_submission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vcsm_submission_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vcsm_failed_submission_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcsm_submission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vcsm_submission_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation
