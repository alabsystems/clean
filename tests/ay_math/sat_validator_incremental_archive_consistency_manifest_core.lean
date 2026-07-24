-- SAT-COMP validator incremental archive consistency manifest core.
--
-- Adding sequential-main results to an archive may publish SAT/UNSAT only when
-- prior archive manifest, appended artifact digests, result JSON, certificate
-- bundle index, stdout/stderr digests, checker transcripts, formula
-- fingerprint, build config, and fallback path agree.

def ay_viac_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_viac_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_viac_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_viac_disj satFact (ay_viac_disj unsatFact noClaimFact)

def ay_viac_archive_append_contract
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath : Prop) : Prop :=
  forall result : Prop,
    (previousArchiveManifest -> appendedArtifactDigests -> resultJson ->
      certificateBundleIndex -> stdoutStderrDigests -> checkerTranscripts ->
      formulaFingerprint -> buildConfig -> fallbackPath -> result) ->
    result

def ay_viac_sat_publication
    (appendContract modelEvidence originalModel : Prop) : Prop :=
  ay_viac_conj appendContract
    (ay_viac_conj modelEvidence originalModel)

def ay_viac_unsat_publication
    (appendContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_viac_conj appendContract
    (ay_viac_conj proofEvidence originalEmptyClause)

def ay_viac_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_viac_conj reason (ay_viac_conj fallbackPath auditTrail)

def ay_viac_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_viac_conj reason
    (ay_viac_conj (satFact -> False) (unsatFact -> False))

def ay_viac_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_viac_conj reason
    (ay_viac_conj fallbackPath recomputeObligation)

def ay_viac_archive_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_viac_conj
    (ay_viac_blocked_publication satFact unsatFact reason)
    (ay_viac_recompute reason fallbackPath recomputeObligation)

theorem ay_viac_conj_intro (left right : Prop) :
    left -> right -> ay_viac_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_viac_conj_left (left right : Prop) :
    ay_viac_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_viac_conj_right (left right : Prop) :
    ay_viac_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_viac_disj_left (left right : Prop) :
    left -> ay_viac_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_viac_disj_right (left right : Prop) :
    right -> ay_viac_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_viac_archive_append_contract_intro
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath : Prop) :
    previousArchiveManifest -> appendedArtifactDigests -> resultJson ->
    certificateBundleIndex -> stdoutStderrDigests -> checkerTranscripts ->
    formulaFingerprint -> buildConfig -> fallbackPath ->
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath :=
  fun previousProof digestProof jsonProof indexProof logProof transcriptProof
      fingerprintProof buildProof fallbackProof result build =>
    build previousProof digestProof jsonProof indexProof logProof
      transcriptProof fingerprintProof buildProof fallbackProof

theorem ay_viac_archive_append_contract_previous_manifest
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath : Prop) :
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath ->
    previousArchiveManifest :=
  fun contract =>
    contract previousArchiveManifest
      (fun previousProof _digestProof _jsonProof _indexProof _logProof
          _transcriptProof _fingerprintProof _buildProof _fallbackProof =>
        previousProof)

theorem ay_viac_archive_append_contract_appended_digests
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath : Prop) :
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath ->
    appendedArtifactDigests :=
  fun contract =>
    contract appendedArtifactDigests
      (fun _previousProof digestProof _jsonProof _indexProof _logProof
          _transcriptProof _fingerprintProof _buildProof _fallbackProof =>
        digestProof)

theorem ay_viac_archive_append_contract_result_json
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath : Prop) :
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath ->
    resultJson :=
  fun contract =>
    contract resultJson
      (fun _previousProof _digestProof jsonProof _indexProof _logProof
          _transcriptProof _fingerprintProof _buildProof _fallbackProof =>
        jsonProof)

theorem ay_viac_archive_append_contract_bundle_index
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath : Prop) :
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath ->
    certificateBundleIndex :=
  fun contract =>
    contract certificateBundleIndex
      (fun _previousProof _digestProof _jsonProof indexProof _logProof
          _transcriptProof _fingerprintProof _buildProof _fallbackProof =>
        indexProof)

theorem ay_viac_archive_append_contract_log_digests
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath : Prop) :
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath ->
    stdoutStderrDigests :=
  fun contract =>
    contract stdoutStderrDigests
      (fun _previousProof _digestProof _jsonProof _indexProof logProof
          _transcriptProof _fingerprintProof _buildProof _fallbackProof =>
        logProof)

theorem ay_viac_archive_append_contract_transcripts
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath : Prop) :
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _previousProof _digestProof _jsonProof _indexProof _logProof
          transcriptProof _fingerprintProof _buildProof _fallbackProof =>
        transcriptProof)

theorem ay_viac_archive_append_contract_fingerprint
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath : Prop) :
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath ->
    formulaFingerprint :=
  fun contract =>
    contract formulaFingerprint
      (fun _previousProof _digestProof _jsonProof _indexProof _logProof
          _transcriptProof fingerprintProof _buildProof _fallbackProof =>
        fingerprintProof)

theorem ay_viac_archive_append_contract_build_config
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath : Prop) :
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _previousProof _digestProof _jsonProof _indexProof _logProof
          _transcriptProof _fingerprintProof buildProof _fallbackProof =>
        buildProof)

theorem ay_viac_archive_append_contract_fallback_path
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath : Prop) :
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath ->
    fallbackPath :=
  fun contract =>
    contract fallbackPath
      (fun _previousProof _digestProof _jsonProof _indexProof _logProof
          _transcriptProof _fingerprintProof _buildProof fallbackProof =>
        fallbackProof)

theorem ay_viac_sat_publication_intro
    (appendContract modelEvidence originalModel : Prop) :
    appendContract -> modelEvidence -> originalModel ->
    ay_viac_sat_publication appendContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_viac_conj_intro appendContract
      (ay_viac_conj modelEvidence originalModel)
      contractProof
      (ay_viac_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_viac_sat_publication_original_model
    (appendContract modelEvidence originalModel : Prop) :
    ay_viac_sat_publication appendContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_viac_conj_right appendContract
      (ay_viac_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_viac_unsat_publication_intro
    (appendContract proofEvidence originalEmptyClause : Prop) :
    appendContract -> proofEvidence -> originalEmptyClause ->
    ay_viac_unsat_publication appendContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_viac_conj_intro appendContract
      (ay_viac_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_viac_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_viac_unsat_publication_original_empty_clause
    (appendContract proofEvidence originalEmptyClause : Prop) :
    ay_viac_unsat_publication appendContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_viac_conj_right appendContract
      (ay_viac_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_viac_accepted_archive_append_sat_sound
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath modelEvidence
      originalModel : Prop) :
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_viac_accepted_archive_append_unsat_sound
    (previousArchiveManifest appendedArtifactDigests resultJson
      certificateBundleIndex stdoutStderrDigests checkerTranscripts
      formulaFingerprint buildConfig fallbackPath proofEvidence
      originalEmptyClause : Prop) :
    ay_viac_archive_append_contract previousArchiveManifest
      appendedArtifactDigests resultJson certificateBundleIndex
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      fallbackPath ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_viac_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_viac_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_viac_conj_intro reason
      (ay_viac_conj fallbackPath auditTrail)
      reasonProof
      (ay_viac_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_viac_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_viac_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_viac_conj_left reason
      (ay_viac_conj fallbackPath auditTrail)
      noClaim

theorem ay_viac_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_viac_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_viac_conj_intro reason
      (ay_viac_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_viac_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_viac_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_viac_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_viac_conj_right reason
      (ay_viac_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_viac_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_viac_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_viac_conj_right reason
      (ay_viac_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_viac_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_viac_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_viac_conj_intro reason
      (ay_viac_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_viac_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_viac_archive_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_viac_archive_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_viac_conj_intro
      (ay_viac_blocked_publication satFact unsatFact reason)
      (ay_viac_recompute reason fallbackPath recomputeObligation)
      (ay_viac_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_viac_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_viac_archive_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_viac_archive_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_viac_blocked_publication_no_sat satFact unsatFact reason
      (ay_viac_conj_left
        (ay_viac_blocked_publication satFact unsatFact reason)
        (ay_viac_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_viac_archive_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_viac_archive_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_viac_blocked_publication_no_unsat satFact unsatFact reason
      (ay_viac_conj_left
        (ay_viac_blocked_publication satFact unsatFact reason)
        (ay_viac_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_viac_archive_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_viac_archive_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_viac_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_viac_conj_right
      (ay_viac_blocked_publication satFact unsatFact reason)
      (ay_viac_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_viac_append_drift_forces_no_claim
    (satFact unsatFact appendDrift fallbackPath recomputeObligation : Prop) :
    appendDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_viac_archive_failure satFact unsatFact appendDrift fallbackPath
      recomputeObligation :=
  ay_viac_archive_failure_intro satFact unsatFact appendDrift fallbackPath
    recomputeObligation

theorem ay_viac_prior_manifest_mismatch_forces_no_claim
    (satFact unsatFact priorManifestMismatch fallbackPath
      recomputeObligation : Prop) :
    priorManifestMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_viac_archive_failure satFact unsatFact priorManifestMismatch
      fallbackPath recomputeObligation :=
  ay_viac_archive_failure_intro satFact unsatFact priorManifestMismatch
    fallbackPath recomputeObligation

theorem ay_viac_artifact_digest_drift_forces_no_claim
    (satFact unsatFact artifactDigestDrift fallbackPath
      recomputeObligation : Prop) :
    artifactDigestDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_viac_archive_failure satFact unsatFact artifactDigestDrift
      fallbackPath recomputeObligation :=
  ay_viac_archive_failure_intro satFact unsatFact artifactDigestDrift
    fallbackPath recomputeObligation

theorem ay_viac_result_json_mismatch_forces_no_claim
    (satFact unsatFact resultJsonMismatch fallbackPath
      recomputeObligation : Prop) :
    resultJsonMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_viac_archive_failure satFact unsatFact resultJsonMismatch
      fallbackPath recomputeObligation :=
  ay_viac_archive_failure_intro satFact unsatFact resultJsonMismatch
    fallbackPath recomputeObligation

theorem ay_viac_bundle_index_mismatch_forces_no_claim
    (satFact unsatFact bundleIndexMismatch fallbackPath
      recomputeObligation : Prop) :
    bundleIndexMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_viac_archive_failure satFact unsatFact bundleIndexMismatch
      fallbackPath recomputeObligation :=
  ay_viac_archive_failure_intro satFact unsatFact bundleIndexMismatch
    fallbackPath recomputeObligation

theorem ay_viac_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackPath
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_viac_archive_failure satFact unsatFact missingTranscript fallbackPath
      recomputeObligation :=
  ay_viac_archive_failure_intro satFact unsatFact missingTranscript
    fallbackPath recomputeObligation

theorem ay_viac_fingerprint_drift_forces_no_claim
    (satFact unsatFact fingerprintDrift fallbackPath
      recomputeObligation : Prop) :
    fingerprintDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_viac_archive_failure satFact unsatFact fingerprintDrift fallbackPath
      recomputeObligation :=
  ay_viac_archive_failure_intro satFact unsatFact fingerprintDrift
    fallbackPath recomputeObligation

theorem ay_viac_build_drift_forces_no_claim
    (satFact unsatFact buildDrift fallbackPath recomputeObligation : Prop) :
    buildDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_viac_archive_failure satFact unsatFact buildDrift fallbackPath
      recomputeObligation :=
  ay_viac_archive_failure_intro satFact unsatFact buildDrift fallbackPath
    recomputeObligation

theorem ay_viac_archive_ambiguity_forces_no_claim
    (satFact unsatFact archiveAmbiguity fallbackPath
      recomputeObligation : Prop) :
    archiveAmbiguity -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_viac_archive_failure satFact unsatFact archiveAmbiguity fallbackPath
      recomputeObligation :=
  ay_viac_archive_failure_intro satFact unsatFact archiveAmbiguity
    fallbackPath recomputeObligation

theorem ay_viac_failed_archive_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_viac_archive_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_viac_archive_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_viac_failed_archive_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_viac_archive_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_viac_archive_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
