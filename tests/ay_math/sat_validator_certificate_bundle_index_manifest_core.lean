-- SAT-COMP validator certificate-bundle index manifest core.
--
-- SAT/UNSAT certificates may be published only when bundle index, artifact
-- digests, result JSON, stdout/stderr digests, checker transcripts, formula
-- fingerprint, build config, archive manifest, and fallback path agree.

def ay_vcbi_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vcbi_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vcbi_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vcbi_disj satFact (ay_vcbi_disj unsatFact noClaimFact)

def ay_vcbi_index_manifest_contract
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) : Prop :=
  forall result : Prop,
    (bundleIndex -> artifactDigests -> resultJson -> stdoutStderrDigests ->
      checkerTranscripts -> formulaFingerprint -> buildConfig ->
      archiveManifest -> fallbackPath -> result) ->
    result

def ay_vcbi_sat_publication
    (indexContract modelEvidence originalModel : Prop) : Prop :=
  ay_vcbi_conj indexContract
    (ay_vcbi_conj modelEvidence originalModel)

def ay_vcbi_unsat_publication
    (indexContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vcbi_conj indexContract
    (ay_vcbi_conj proofEvidence originalEmptyClause)

def ay_vcbi_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vcbi_conj reason (ay_vcbi_conj fallbackPath auditTrail)

def ay_vcbi_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vcbi_conj reason
    (ay_vcbi_conj (satFact -> False) (unsatFact -> False))

def ay_vcbi_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vcbi_conj reason
    (ay_vcbi_conj fallbackPath recomputeObligation)

def ay_vcbi_index_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vcbi_conj
    (ay_vcbi_blocked_publication satFact unsatFact reason)
    (ay_vcbi_recompute reason fallbackPath recomputeObligation)

theorem ay_vcbi_conj_intro (left right : Prop) :
    left -> right -> ay_vcbi_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcbi_conj_left (left right : Prop) :
    ay_vcbi_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcbi_conj_right (left right : Prop) :
    ay_vcbi_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcbi_disj_left (left right : Prop) :
    left -> ay_vcbi_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vcbi_disj_right (left right : Prop) :
    right -> ay_vcbi_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcbi_index_manifest_contract_intro
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    bundleIndex -> artifactDigests -> resultJson -> stdoutStderrDigests ->
    checkerTranscripts -> formulaFingerprint -> buildConfig ->
    archiveManifest -> fallbackPath ->
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath :=
  fun indexProof digestProof jsonProof logProof transcriptProof
      fingerprintProof buildProof archiveProof fallbackProof result build =>
    build indexProof digestProof jsonProof logProof transcriptProof
      fingerprintProof buildProof archiveProof fallbackProof

theorem ay_vcbi_index_manifest_contract_bundle_index
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath ->
    bundleIndex :=
  fun contract =>
    contract bundleIndex
      (fun indexProof _digestProof _jsonProof _logProof _transcriptProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof =>
        indexProof)

theorem ay_vcbi_index_manifest_contract_artifact_digests
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath ->
    artifactDigests :=
  fun contract =>
    contract artifactDigests
      (fun _indexProof digestProof _jsonProof _logProof _transcriptProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof =>
        digestProof)

theorem ay_vcbi_index_manifest_contract_result_json
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath ->
    resultJson :=
  fun contract =>
    contract resultJson
      (fun _indexProof _digestProof jsonProof _logProof _transcriptProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof =>
        jsonProof)

theorem ay_vcbi_index_manifest_contract_log_digests
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath ->
    stdoutStderrDigests :=
  fun contract =>
    contract stdoutStderrDigests
      (fun _indexProof _digestProof _jsonProof logProof _transcriptProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof =>
        logProof)

theorem ay_vcbi_index_manifest_contract_transcripts
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _indexProof _digestProof _jsonProof _logProof transcriptProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof =>
        transcriptProof)

theorem ay_vcbi_index_manifest_contract_fingerprint
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath ->
    formulaFingerprint :=
  fun contract =>
    contract formulaFingerprint
      (fun _indexProof _digestProof _jsonProof _logProof _transcriptProof
          fingerprintProof _buildProof _archiveProof _fallbackProof =>
        fingerprintProof)

theorem ay_vcbi_index_manifest_contract_build_config
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _indexProof _digestProof _jsonProof _logProof _transcriptProof
          _fingerprintProof buildProof _archiveProof _fallbackProof =>
        buildProof)

theorem ay_vcbi_index_manifest_contract_archive_manifest
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _indexProof _digestProof _jsonProof _logProof _transcriptProof
          _fingerprintProof _buildProof archiveProof _fallbackProof =>
        archiveProof)

theorem ay_vcbi_index_manifest_contract_fallback_path
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath : Prop) :
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath ->
    fallbackPath :=
  fun contract =>
    contract fallbackPath
      (fun _indexProof _digestProof _jsonProof _logProof _transcriptProof
          _fingerprintProof _buildProof _archiveProof fallbackProof =>
        fallbackProof)

theorem ay_vcbi_sat_publication_intro
    (indexContract modelEvidence originalModel : Prop) :
    indexContract -> modelEvidence -> originalModel ->
    ay_vcbi_sat_publication indexContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vcbi_conj_intro indexContract
      (ay_vcbi_conj modelEvidence originalModel)
      contractProof
      (ay_vcbi_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vcbi_sat_publication_original_model
    (indexContract modelEvidence originalModel : Prop) :
    ay_vcbi_sat_publication indexContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vcbi_conj_right indexContract
      (ay_vcbi_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vcbi_unsat_publication_intro
    (indexContract proofEvidence originalEmptyClause : Prop) :
    indexContract -> proofEvidence -> originalEmptyClause ->
    ay_vcbi_unsat_publication indexContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vcbi_conj_intro indexContract
      (ay_vcbi_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vcbi_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vcbi_unsat_publication_original_empty_clause
    (indexContract proofEvidence originalEmptyClause : Prop) :
    ay_vcbi_unsat_publication indexContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vcbi_conj_right indexContract
      (ay_vcbi_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vcbi_accepted_index_manifest_sat_sound
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath modelEvidence originalModel : Prop) :
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vcbi_accepted_index_manifest_unsat_sound
    (bundleIndex artifactDigests resultJson stdoutStderrDigests
      checkerTranscripts formulaFingerprint buildConfig archiveManifest
      fallbackPath proofEvidence originalEmptyClause : Prop) :
    ay_vcbi_index_manifest_contract bundleIndex artifactDigests resultJson
      stdoutStderrDigests checkerTranscripts formulaFingerprint buildConfig
      archiveManifest fallbackPath ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vcbi_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vcbi_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vcbi_conj_intro reason
      (ay_vcbi_conj fallbackPath auditTrail)
      reasonProof
      (ay_vcbi_conj_intro fallbackPath auditTrail
        fallbackProof auditProof)

theorem ay_vcbi_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vcbi_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vcbi_conj_left reason
      (ay_vcbi_conj fallbackPath auditTrail)
      noClaim

theorem ay_vcbi_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vcbi_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vcbi_conj_intro reason
      (ay_vcbi_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vcbi_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vcbi_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vcbi_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vcbi_conj_right reason
      (ay_vcbi_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vcbi_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vcbi_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vcbi_conj_right reason
      (ay_vcbi_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vcbi_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vcbi_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vcbi_conj_intro reason
      (ay_vcbi_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_vcbi_conj_intro fallbackPath recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vcbi_index_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcbi_index_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vcbi_conj_intro
      (ay_vcbi_blocked_publication satFact unsatFact reason)
      (ay_vcbi_recompute reason fallbackPath recomputeObligation)
      (ay_vcbi_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vcbi_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vcbi_index_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcbi_index_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vcbi_blocked_publication_no_sat satFact unsatFact reason
      (ay_vcbi_conj_left
        (ay_vcbi_blocked_publication satFact unsatFact reason)
        (ay_vcbi_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vcbi_index_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcbi_index_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vcbi_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vcbi_conj_left
        (ay_vcbi_blocked_publication satFact unsatFact reason)
        (ay_vcbi_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vcbi_index_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcbi_index_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vcbi_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vcbi_conj_right
      (ay_vcbi_blocked_publication satFact unsatFact reason)
      (ay_vcbi_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vcbi_missing_bundle_entry_forces_no_claim
    (satFact unsatFact missingBundleEntry fallbackPath
      recomputeObligation : Prop) :
    missingBundleEntry -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcbi_index_failure satFact unsatFact missingBundleEntry fallbackPath
      recomputeObligation :=
  ay_vcbi_index_failure_intro satFact unsatFact missingBundleEntry
    fallbackPath recomputeObligation

theorem ay_vcbi_digest_drift_forces_no_claim
    (satFact unsatFact digestDrift fallbackPath recomputeObligation : Prop) :
    digestDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcbi_index_failure satFact unsatFact digestDrift fallbackPath
      recomputeObligation :=
  ay_vcbi_index_failure_intro satFact unsatFact digestDrift fallbackPath
    recomputeObligation

theorem ay_vcbi_result_json_mismatch_forces_no_claim
    (satFact unsatFact resultJsonMismatch fallbackPath
      recomputeObligation : Prop) :
    resultJsonMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcbi_index_failure satFact unsatFact resultJsonMismatch fallbackPath
      recomputeObligation :=
  ay_vcbi_index_failure_intro satFact unsatFact resultJsonMismatch
    fallbackPath recomputeObligation

theorem ay_vcbi_log_digest_drift_forces_no_claim
    (satFact unsatFact logDigestDrift fallbackPath
      recomputeObligation : Prop) :
    logDigestDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcbi_index_failure satFact unsatFact logDigestDrift fallbackPath
      recomputeObligation :=
  ay_vcbi_index_failure_intro satFact unsatFact logDigestDrift fallbackPath
    recomputeObligation

theorem ay_vcbi_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackPath
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcbi_index_failure satFact unsatFact missingTranscript fallbackPath
      recomputeObligation :=
  ay_vcbi_index_failure_intro satFact unsatFact missingTranscript fallbackPath
    recomputeObligation

theorem ay_vcbi_fingerprint_drift_forces_no_claim
    (satFact unsatFact fingerprintDrift fallbackPath
      recomputeObligation : Prop) :
    fingerprintDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcbi_index_failure satFact unsatFact fingerprintDrift fallbackPath
      recomputeObligation :=
  ay_vcbi_index_failure_intro satFact unsatFact fingerprintDrift fallbackPath
    recomputeObligation

theorem ay_vcbi_build_drift_forces_no_claim
    (satFact unsatFact buildDrift fallbackPath recomputeObligation : Prop) :
    buildDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcbi_index_failure satFact unsatFact buildDrift fallbackPath
      recomputeObligation :=
  ay_vcbi_index_failure_intro satFact unsatFact buildDrift fallbackPath
    recomputeObligation

theorem ay_vcbi_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation : Prop) :
    archiveMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcbi_index_failure satFact unsatFact archiveMismatch fallbackPath
      recomputeObligation :=
  ay_vcbi_index_failure_intro satFact unsatFact archiveMismatch fallbackPath
    recomputeObligation

theorem ay_vcbi_index_ambiguity_forces_no_claim
    (satFact unsatFact indexAmbiguity fallbackPath
      recomputeObligation : Prop) :
    indexAmbiguity -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_vcbi_index_failure satFact unsatFact indexAmbiguity fallbackPath
      recomputeObligation :=
  ay_vcbi_index_failure_intro satFact unsatFact indexAmbiguity fallbackPath
    recomputeObligation

theorem ay_vcbi_failed_index_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcbi_index_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vcbi_index_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vcbi_failed_index_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vcbi_index_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vcbi_index_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
