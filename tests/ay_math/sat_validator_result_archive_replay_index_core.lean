-- SAT-COMP validator result archive replay index core.
--
-- Archived results may be replayed for SAT/UNSAT publication only when archive
-- replay index, replay transcript, result JSON, certificate bundle index,
-- benchmark fingerprint, checker transcript, build config, archive manifest,
-- and fallback path agree.

def ay_vrai_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrai_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vrai_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vrai_disj satFact (ay_vrai_disj unsatFact noClaimFact)

def ay_vrai_replay_index_contract
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath : Prop) : Prop :=
  forall result : Prop,
    (archiveReplayIndex -> replayTranscript -> resultJson ->
      certificateBundleIndex -> benchmarkFingerprint -> checkerTranscript ->
      buildConfig -> archiveManifest -> fallbackPath -> result) ->
    result

def ay_vrai_sat_publication
    (replayContract modelEvidence originalModel : Prop) : Prop :=
  ay_vrai_conj replayContract
    (ay_vrai_conj modelEvidence originalModel)

def ay_vrai_unsat_publication
    (replayContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vrai_conj replayContract
    (ay_vrai_conj proofEvidence originalEmptyClause)

def ay_vrai_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vrai_conj reason (ay_vrai_conj fallbackPath auditTrail)

def ay_vrai_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vrai_conj reason
    (ay_vrai_conj (satFact -> False) (unsatFact -> False))

def ay_vrai_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vrai_conj reason
    (ay_vrai_conj fallbackPath recomputeObligation)

def ay_vrai_replay_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vrai_conj
    (ay_vrai_blocked_publication satFact unsatFact reason)
    (ay_vrai_recompute reason fallbackPath recomputeObligation)

theorem ay_vrai_conj_intro (left right : Prop) :
    left -> right -> ay_vrai_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrai_conj_left (left right : Prop) :
    ay_vrai_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrai_conj_right (left right : Prop) :
    ay_vrai_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrai_disj_left (left right : Prop) :
    left -> ay_vrai_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vrai_disj_right (left right : Prop) :
    right -> ay_vrai_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrai_replay_index_contract_intro
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath : Prop) :
    archiveReplayIndex -> replayTranscript -> resultJson ->
    certificateBundleIndex -> benchmarkFingerprint -> checkerTranscript ->
    buildConfig -> archiveManifest -> fallbackPath ->
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath :=
  fun indexProof replayProof jsonProof bundleProof benchmarkProof
      checkerProof buildProof archiveProof fallbackProof result build =>
    build indexProof replayProof jsonProof bundleProof benchmarkProof
      checkerProof buildProof archiveProof fallbackProof

theorem ay_vrai_replay_index_contract_index
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath ->
    archiveReplayIndex :=
  fun contract =>
    contract archiveReplayIndex
      (fun indexProof _replayProof _jsonProof _bundleProof _benchmarkProof
          _checkerProof _buildProof _archiveProof _fallbackProof =>
        indexProof)

theorem ay_vrai_replay_index_contract_replay_transcript
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath ->
    replayTranscript :=
  fun contract =>
    contract replayTranscript
      (fun _indexProof replayProof _jsonProof _bundleProof _benchmarkProof
          _checkerProof _buildProof _archiveProof _fallbackProof =>
        replayProof)

theorem ay_vrai_replay_index_contract_result_json
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath ->
    resultJson :=
  fun contract =>
    contract resultJson
      (fun _indexProof _replayProof jsonProof _bundleProof _benchmarkProof
          _checkerProof _buildProof _archiveProof _fallbackProof =>
        jsonProof)

theorem ay_vrai_replay_index_contract_bundle_index
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath ->
    certificateBundleIndex :=
  fun contract =>
    contract certificateBundleIndex
      (fun _indexProof _replayProof _jsonProof bundleProof _benchmarkProof
          _checkerProof _buildProof _archiveProof _fallbackProof =>
        bundleProof)

theorem ay_vrai_replay_index_contract_benchmark
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _indexProof _replayProof _jsonProof _bundleProof benchmarkProof
          _checkerProof _buildProof _archiveProof _fallbackProof =>
        benchmarkProof)

theorem ay_vrai_replay_index_contract_checker_transcript
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _indexProof _replayProof _jsonProof _bundleProof _benchmarkProof
          checkerProof _buildProof _archiveProof _fallbackProof =>
        checkerProof)

theorem ay_vrai_replay_index_contract_build_config
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _indexProof _replayProof _jsonProof _bundleProof _benchmarkProof
          _checkerProof buildProof _archiveProof _fallbackProof =>
        buildProof)

theorem ay_vrai_replay_index_contract_archive_manifest
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _indexProof _replayProof _jsonProof _bundleProof _benchmarkProof
          _checkerProof _buildProof archiveProof _fallbackProof =>
        archiveProof)

theorem ay_vrai_replay_index_contract_fallback_path
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath ->
    fallbackPath :=
  fun contract =>
    contract fallbackPath
      (fun _indexProof _replayProof _jsonProof _bundleProof _benchmarkProof
          _checkerProof _buildProof _archiveProof fallbackProof =>
        fallbackProof)

theorem ay_vrai_sat_publication_intro
    (replayContract modelEvidence originalModel : Prop) :
    replayContract -> modelEvidence -> originalModel ->
    ay_vrai_sat_publication replayContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vrai_conj_intro replayContract
      (ay_vrai_conj modelEvidence originalModel)
      contractProof
      (ay_vrai_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vrai_sat_publication_original_model
    (replayContract modelEvidence originalModel : Prop) :
    ay_vrai_sat_publication replayContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vrai_conj_right replayContract
      (ay_vrai_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vrai_unsat_publication_intro
    (replayContract proofEvidence originalEmptyClause : Prop) :
    replayContract -> proofEvidence -> originalEmptyClause ->
    ay_vrai_unsat_publication replayContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vrai_conj_intro replayContract
      (ay_vrai_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vrai_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vrai_unsat_publication_original_empty_clause
    (replayContract proofEvidence originalEmptyClause : Prop) :
    ay_vrai_unsat_publication replayContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vrai_conj_right replayContract
      (ay_vrai_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vrai_accepted_replay_index_sat_sound
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath modelEvidence originalModel : Prop) :
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vrai_accepted_replay_index_unsat_sound
    (archiveReplayIndex replayTranscript resultJson certificateBundleIndex
      benchmarkFingerprint checkerTranscript buildConfig archiveManifest
      fallbackPath proofEvidence originalEmptyClause : Prop) :
    ay_vrai_replay_index_contract archiveReplayIndex replayTranscript
      resultJson certificateBundleIndex benchmarkFingerprint
      checkerTranscript buildConfig archiveManifest fallbackPath ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vrai_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vrai_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vrai_conj_intro reason
      (ay_vrai_conj fallbackPath auditTrail)
      reasonProof
      (ay_vrai_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_vrai_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vrai_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vrai_conj_left reason
      (ay_vrai_conj fallbackPath auditTrail)
      noClaim

theorem ay_vrai_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vrai_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vrai_conj_intro reason
      (ay_vrai_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vrai_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vrai_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vrai_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vrai_conj_right reason
      (ay_vrai_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vrai_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vrai_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vrai_conj_right reason
      (ay_vrai_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vrai_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vrai_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vrai_conj_intro reason
      (ay_vrai_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_vrai_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vrai_replay_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrai_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vrai_conj_intro
      (ay_vrai_blocked_publication satFact unsatFact reason)
      (ay_vrai_recompute reason fallbackPath recomputeObligation)
      (ay_vrai_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vrai_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vrai_replay_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrai_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vrai_blocked_publication_no_sat satFact unsatFact reason
      (ay_vrai_conj_left
        (ay_vrai_blocked_publication satFact unsatFact reason)
        (ay_vrai_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vrai_replay_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrai_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vrai_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vrai_conj_left
        (ay_vrai_blocked_publication satFact unsatFact reason)
        (ay_vrai_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vrai_replay_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrai_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vrai_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vrai_conj_right
      (ay_vrai_blocked_publication satFact unsatFact reason)
      (ay_vrai_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vrai_replay_index_drift_forces_no_claim
    (satFact unsatFact replayIndexDrift fallbackPath
      recomputeObligation : Prop) :
    replayIndexDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrai_replay_failure satFact unsatFact replayIndexDrift fallbackPath
      recomputeObligation :=
  ay_vrai_replay_failure_intro satFact unsatFact replayIndexDrift
    fallbackPath recomputeObligation

theorem ay_vrai_replay_transcript_mismatch_forces_no_claim
    (satFact unsatFact replayTranscriptMismatch fallbackPath
      recomputeObligation : Prop) :
    replayTranscriptMismatch -> (satFact -> False) ->
    (unsatFact -> False) -> fallbackPath -> recomputeObligation ->
    ay_vrai_replay_failure satFact unsatFact replayTranscriptMismatch
      fallbackPath recomputeObligation :=
  ay_vrai_replay_failure_intro satFact unsatFact replayTranscriptMismatch
    fallbackPath recomputeObligation

theorem ay_vrai_result_mismatch_forces_no_claim
    (satFact unsatFact resultMismatch fallbackPath
      recomputeObligation : Prop) :
    resultMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrai_replay_failure satFact unsatFact resultMismatch fallbackPath
      recomputeObligation :=
  ay_vrai_replay_failure_intro satFact unsatFact resultMismatch fallbackPath
    recomputeObligation

theorem ay_vrai_bundle_mismatch_forces_no_claim
    (satFact unsatFact bundleMismatch fallbackPath
      recomputeObligation : Prop) :
    bundleMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrai_replay_failure satFact unsatFact bundleMismatch fallbackPath
      recomputeObligation :=
  ay_vrai_replay_failure_intro satFact unsatFact bundleMismatch fallbackPath
    recomputeObligation

theorem ay_vrai_benchmark_drift_forces_no_claim
    (satFact unsatFact benchmarkDrift fallbackPath
      recomputeObligation : Prop) :
    benchmarkDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrai_replay_failure satFact unsatFact benchmarkDrift fallbackPath
      recomputeObligation :=
  ay_vrai_replay_failure_intro satFact unsatFact benchmarkDrift fallbackPath
    recomputeObligation

theorem ay_vrai_missing_checker_transcript_forces_no_claim
    (satFact unsatFact missingCheckerTranscript fallbackPath
      recomputeObligation : Prop) :
    missingCheckerTranscript -> (satFact -> False) ->
    (unsatFact -> False) -> fallbackPath -> recomputeObligation ->
    ay_vrai_replay_failure satFact unsatFact missingCheckerTranscript
      fallbackPath recomputeObligation :=
  ay_vrai_replay_failure_intro satFact unsatFact missingCheckerTranscript
    fallbackPath recomputeObligation

theorem ay_vrai_build_drift_forces_no_claim
    (satFact unsatFact buildDrift fallbackPath recomputeObligation : Prop) :
    buildDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrai_replay_failure satFact unsatFact buildDrift fallbackPath
      recomputeObligation :=
  ay_vrai_replay_failure_intro satFact unsatFact buildDrift fallbackPath
    recomputeObligation

theorem ay_vrai_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation : Prop) :
    archiveMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrai_replay_failure satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation :=
  ay_vrai_replay_failure_intro satFact unsatFact archiveMismatch fallbackPath
    recomputeObligation

theorem ay_vrai_replay_ambiguity_forces_no_claim
    (satFact unsatFact replayAmbiguity fallbackPath
      recomputeObligation : Prop) :
    replayAmbiguity -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vrai_replay_failure satFact unsatFact replayAmbiguity fallbackPath
      recomputeObligation :=
  ay_vrai_replay_failure_intro satFact unsatFact replayAmbiguity fallbackPath
    recomputeObligation

theorem ay_vrai_failed_replay_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrai_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vrai_replay_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vrai_failed_replay_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vrai_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vrai_replay_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
