-- SAT-COMP validator submission replay/audit manifest core.
--
-- Post-run replay audit publication may certify SAT/UNSAT only when
-- submission manifest, replay transcript, audit manifest, run manifests,
-- result JSON, certificate bundle index, benchmark fingerprints, checker
-- transcripts, build config, archive manifest, and fallback path agree.

def ay_vsra_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vsra_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vsra_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vsra_disj satFact (ay_vsra_disj unsatFact noClaimFact)

def ay_vsra_replay_audit_contract
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) : Prop :=
  forall result : Prop,
    (submissionManifest -> replayTranscript -> auditManifest ->
      runManifests -> resultJson -> certificateBundleIndex ->
      benchmarkFingerprints -> checkerTranscripts -> buildConfig ->
      archiveManifest -> fallbackPath -> result) ->
    result

def ay_vsra_sat_publication
    (auditContract modelEvidence originalModel : Prop) : Prop :=
  ay_vsra_conj auditContract
    (ay_vsra_conj modelEvidence originalModel)

def ay_vsra_unsat_publication
    (auditContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vsra_conj auditContract
    (ay_vsra_conj proofEvidence originalEmptyClause)

def ay_vsra_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vsra_conj reason (ay_vsra_conj fallbackPath auditTrail)

def ay_vsra_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vsra_conj reason
    (ay_vsra_conj (satFact -> False) (unsatFact -> False))

def ay_vsra_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vsra_conj reason
    (ay_vsra_conj fallbackPath recomputeObligation)

def ay_vsra_audit_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vsra_conj
    (ay_vsra_blocked_publication satFact unsatFact reason)
    (ay_vsra_recompute reason fallbackPath recomputeObligation)

theorem ay_vsra_conj_intro (left right : Prop) :
    left -> right -> ay_vsra_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vsra_conj_left (left right : Prop) :
    ay_vsra_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vsra_conj_right (left right : Prop) :
    ay_vsra_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vsra_disj_left (left right : Prop) :
    left -> ay_vsra_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vsra_disj_right (left right : Prop) :
    right -> ay_vsra_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vsra_replay_audit_contract_intro
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    submissionManifest -> replayTranscript -> auditManifest ->
    runManifests -> resultJson -> certificateBundleIndex ->
    benchmarkFingerprints -> checkerTranscripts -> buildConfig ->
    archiveManifest -> fallbackPath ->
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath :=
  fun submissionProof replayProof auditProof runProof jsonProof bundleProof
      benchmarkProof checkerProof buildProof archiveProof fallbackProof result
      build =>
    build submissionProof replayProof auditProof runProof jsonProof
      bundleProof benchmarkProof checkerProof buildProof archiveProof
      fallbackProof

theorem ay_vsra_replay_audit_contract_submission_manifest
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun submissionProof _replayProof _auditProof _runProof _jsonProof
          _bundleProof _benchmarkProof _checkerProof _buildProof
          _archiveProof _fallbackProof => submissionProof)

theorem ay_vsra_replay_audit_contract_replay_transcript
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    replayTranscript :=
  fun contract =>
    contract replayTranscript
      (fun _submissionProof replayProof _auditProof _runProof _jsonProof
          _bundleProof _benchmarkProof _checkerProof _buildProof
          _archiveProof _fallbackProof => replayProof)

theorem ay_vsra_replay_audit_contract_audit_manifest
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    auditManifest :=
  fun contract =>
    contract auditManifest
      (fun _submissionProof _replayProof auditProof _runProof _jsonProof
          _bundleProof _benchmarkProof _checkerProof _buildProof
          _archiveProof _fallbackProof => auditProof)

theorem ay_vsra_replay_audit_contract_run_manifests
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    runManifests :=
  fun contract =>
    contract runManifests
      (fun _submissionProof _replayProof _auditProof runProof _jsonProof
          _bundleProof _benchmarkProof _checkerProof _buildProof
          _archiveProof _fallbackProof => runProof)

theorem ay_vsra_replay_audit_contract_result_json
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    resultJson :=
  fun contract =>
    contract resultJson
      (fun _submissionProof _replayProof _auditProof _runProof jsonProof
          _bundleProof _benchmarkProof _checkerProof _buildProof
          _archiveProof _fallbackProof => jsonProof)

theorem ay_vsra_replay_audit_contract_bundle_index
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    certificateBundleIndex :=
  fun contract =>
    contract certificateBundleIndex
      (fun _submissionProof _replayProof _auditProof _runProof _jsonProof
          bundleProof _benchmarkProof _checkerProof _buildProof _archiveProof
          _fallbackProof => bundleProof)

theorem ay_vsra_replay_audit_contract_benchmark_fingerprints
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    benchmarkFingerprints :=
  fun contract =>
    contract benchmarkFingerprints
      (fun _submissionProof _replayProof _auditProof _runProof _jsonProof
          _bundleProof benchmarkProof _checkerProof _buildProof _archiveProof
          _fallbackProof => benchmarkProof)

theorem ay_vsra_replay_audit_contract_checker_transcripts
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _submissionProof _replayProof _auditProof _runProof _jsonProof
          _bundleProof _benchmarkProof checkerProof _buildProof _archiveProof
          _fallbackProof => checkerProof)

theorem ay_vsra_replay_audit_contract_build_config
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _submissionProof _replayProof _auditProof _runProof _jsonProof
          _bundleProof _benchmarkProof _checkerProof buildProof _archiveProof
          _fallbackProof => buildProof)

theorem ay_vsra_replay_audit_contract_archive_manifest
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _submissionProof _replayProof _auditProof _runProof _jsonProof
          _bundleProof _benchmarkProof _checkerProof _buildProof archiveProof
          _fallbackProof => archiveProof)

theorem ay_vsra_replay_audit_contract_fallback_path
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    fallbackPath :=
  fun contract =>
    contract fallbackPath
      (fun _submissionProof _replayProof _auditProof _runProof _jsonProof
          _bundleProof _benchmarkProof _checkerProof _buildProof
          _archiveProof fallbackProof => fallbackProof)

theorem ay_vsra_sat_publication_intro
    (auditContract modelEvidence originalModel : Prop) :
    auditContract -> modelEvidence -> originalModel ->
    ay_vsra_sat_publication auditContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vsra_conj_intro auditContract
      (ay_vsra_conj modelEvidence originalModel)
      contractProof
      (ay_vsra_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vsra_sat_publication_original_model
    (auditContract modelEvidence originalModel : Prop) :
    ay_vsra_sat_publication auditContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vsra_conj_right auditContract
      (ay_vsra_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vsra_unsat_publication_intro
    (auditContract proofEvidence originalEmptyClause : Prop) :
    auditContract -> proofEvidence -> originalEmptyClause ->
    ay_vsra_unsat_publication auditContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vsra_conj_intro auditContract
      (ay_vsra_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vsra_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vsra_unsat_publication_original_empty_clause
    (auditContract proofEvidence originalEmptyClause : Prop) :
    ay_vsra_unsat_publication auditContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vsra_conj_right auditContract
      (ay_vsra_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vsra_accepted_replay_audit_sat_sound
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath modelEvidence originalModel :
      Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vsra_accepted_replay_audit_unsat_sound
    (submissionManifest replayTranscript auditManifest runManifests resultJson
      certificateBundleIndex benchmarkFingerprints checkerTranscripts
      buildConfig archiveManifest fallbackPath proofEvidence
      originalEmptyClause : Prop) :
    ay_vsra_replay_audit_contract submissionManifest replayTranscript
      auditManifest runManifests resultJson certificateBundleIndex
      benchmarkFingerprints checkerTranscripts buildConfig archiveManifest
      fallbackPath ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vsra_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vsra_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vsra_conj_intro reason
      (ay_vsra_conj fallbackPath auditTrail)
      reasonProof
      (ay_vsra_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_vsra_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vsra_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vsra_conj_left reason
      (ay_vsra_conj fallbackPath auditTrail)
      noClaim

theorem ay_vsra_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vsra_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vsra_conj_intro reason
      (ay_vsra_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vsra_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vsra_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vsra_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vsra_conj_right reason
      (ay_vsra_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vsra_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vsra_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vsra_conj_right reason
      (ay_vsra_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vsra_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vsra_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vsra_conj_intro reason
      (ay_vsra_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_vsra_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vsra_audit_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsra_audit_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vsra_conj_intro
      (ay_vsra_blocked_publication satFact unsatFact reason)
      (ay_vsra_recompute reason fallbackPath recomputeObligation)
      (ay_vsra_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vsra_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vsra_audit_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsra_audit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vsra_blocked_publication_no_sat satFact unsatFact reason
      (ay_vsra_conj_left
        (ay_vsra_blocked_publication satFact unsatFact reason)
        (ay_vsra_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsra_audit_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsra_audit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vsra_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vsra_conj_left
        (ay_vsra_blocked_publication satFact unsatFact reason)
        (ay_vsra_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsra_audit_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsra_audit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vsra_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vsra_conj_right
      (ay_vsra_blocked_publication satFact unsatFact reason)
      (ay_vsra_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vsra_replay_drift_forces_no_claim
    (satFact unsatFact replayDrift fallbackPath recomputeObligation : Prop) :
    replayDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsra_audit_failure satFact unsatFact replayDrift fallbackPath
      recomputeObligation :=
  ay_vsra_audit_failure_intro satFact unsatFact replayDrift fallbackPath
    recomputeObligation

theorem ay_vsra_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath recomputeObligation : Prop) :
    auditMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsra_audit_failure satFact unsatFact auditMismatch fallbackPath
      recomputeObligation :=
  ay_vsra_audit_failure_intro satFact unsatFact auditMismatch fallbackPath
    recomputeObligation

theorem ay_vsra_missing_run_forces_no_claim
    (satFact unsatFact missingRun fallbackPath recomputeObligation : Prop) :
    missingRun -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsra_audit_failure satFact unsatFact missingRun fallbackPath
      recomputeObligation :=
  ay_vsra_audit_failure_intro satFact unsatFact missingRun fallbackPath
    recomputeObligation

theorem ay_vsra_result_mismatch_forces_no_claim
    (satFact unsatFact resultMismatch fallbackPath
      recomputeObligation : Prop) :
    resultMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsra_audit_failure satFact unsatFact resultMismatch fallbackPath
      recomputeObligation :=
  ay_vsra_audit_failure_intro satFact unsatFact resultMismatch fallbackPath
    recomputeObligation

theorem ay_vsra_bundle_mismatch_forces_no_claim
    (satFact unsatFact bundleMismatch fallbackPath
      recomputeObligation : Prop) :
    bundleMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsra_audit_failure satFact unsatFact bundleMismatch fallbackPath
      recomputeObligation :=
  ay_vsra_audit_failure_intro satFact unsatFact bundleMismatch fallbackPath
    recomputeObligation

theorem ay_vsra_benchmark_drift_forces_no_claim
    (satFact unsatFact benchmarkDrift fallbackPath
      recomputeObligation : Prop) :
    benchmarkDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsra_audit_failure satFact unsatFact benchmarkDrift fallbackPath
      recomputeObligation :=
  ay_vsra_audit_failure_intro satFact unsatFact benchmarkDrift fallbackPath
    recomputeObligation

theorem ay_vsra_missing_checker_transcript_forces_no_claim
    (satFact unsatFact missingCheckerTranscript fallbackPath
      recomputeObligation : Prop) :
    missingCheckerTranscript -> (satFact -> False) ->
    (unsatFact -> False) -> fallbackPath -> recomputeObligation ->
    ay_vsra_audit_failure satFact unsatFact missingCheckerTranscript
      fallbackPath recomputeObligation :=
  ay_vsra_audit_failure_intro satFact unsatFact missingCheckerTranscript
    fallbackPath recomputeObligation

theorem ay_vsra_build_drift_forces_no_claim
    (satFact unsatFact buildDrift fallbackPath recomputeObligation : Prop) :
    buildDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsra_audit_failure satFact unsatFact buildDrift fallbackPath
      recomputeObligation :=
  ay_vsra_audit_failure_intro satFact unsatFact buildDrift fallbackPath
    recomputeObligation

theorem ay_vsra_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation : Prop) :
    archiveMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsra_audit_failure satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation :=
  ay_vsra_audit_failure_intro satFact unsatFact archiveMismatch fallbackPath
    recomputeObligation

theorem ay_vsra_audit_ambiguity_forces_no_claim
    (satFact unsatFact auditAmbiguity fallbackPath
      recomputeObligation : Prop) :
    auditAmbiguity -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vsra_audit_failure satFact unsatFact auditAmbiguity fallbackPath
      recomputeObligation :=
  ay_vsra_audit_failure_intro satFact unsatFact auditAmbiguity fallbackPath
    recomputeObligation

theorem ay_vsra_failed_audit_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsra_audit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vsra_audit_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vsra_failed_audit_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsra_audit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vsra_audit_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
