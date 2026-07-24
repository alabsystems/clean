-- SAT-COMP validator checker-version pin guard core.
--
-- Public SAT/UNSAT claims may rely on a checker only when its binary digest,
-- version manifest, flags, transcript digest, artifact digest, benchmark
-- fingerprint, solver build evidence, archive manifest, fallback path, and
-- audit transcript agree.

def ay_cvpg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cvpg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cvpg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_cvpg_disj satFact (ay_cvpg_disj unsatFact noClaimFact)

def ay_cvpg_pin_contract
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (checkerBinaryDigest -> checkerVersionManifest ->
      checkerFlagManifest -> transcriptDigest -> artifactDigest ->
      benchmarkFingerprint -> solverBuildEvidence -> archiveManifest ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_cvpg_sat_publication
    (pinContract pinnedCheckerAccepts checkedModel originalModel : Prop) :
    Prop :=
  ay_cvpg_conj pinContract
    (ay_cvpg_conj pinnedCheckerAccepts
      (ay_cvpg_conj checkedModel originalModel))

def ay_cvpg_unsat_publication
    (pinContract pinnedCheckerAccepts checkedProof originalEmptyClause : Prop) :
    Prop :=
  ay_cvpg_conj pinContract
    (ay_cvpg_conj pinnedCheckerAccepts
      (ay_cvpg_conj checkedProof originalEmptyClause))

def ay_cvpg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_cvpg_conj reason (ay_cvpg_conj fallbackPath auditTrail)

def ay_cvpg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_cvpg_conj reason
    (ay_cvpg_conj (satFact -> False) (unsatFact -> False))

def ay_cvpg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_cvpg_conj reason
    (ay_cvpg_conj fallbackPath recomputeObligation)

def ay_cvpg_pin_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_cvpg_conj
    (ay_cvpg_blocked_publication satFact unsatFact reason)
    (ay_cvpg_recompute reason fallbackPath recomputeObligation)

theorem ay_cvpg_conj_intro (left right : Prop) :
    left -> right -> ay_cvpg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_cvpg_conj_left (left right : Prop) :
    ay_cvpg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_cvpg_conj_right (left right : Prop) :
    ay_cvpg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_cvpg_disj_left (left right : Prop) :
    left -> ay_cvpg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_cvpg_disj_right (left right : Prop) :
    right -> ay_cvpg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_cvpg_pin_contract_intro
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    checkerBinaryDigest -> checkerVersionManifest ->
    checkerFlagManifest -> transcriptDigest -> artifactDigest ->
    benchmarkFingerprint -> solverBuildEvidence -> archiveManifest ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_cvpg_pin_contract checkerBinaryDigest checkerVersionManifest
      checkerFlagManifest transcriptDigest artifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :=
  fun binaryProof versionProof flagProof transcriptProof artifactProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof result
      build =>
    build binaryProof versionProof flagProof transcriptProof artifactProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof

theorem ay_cvpg_contract_checker_binary
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cvpg_pin_contract checkerBinaryDigest checkerVersionManifest
      checkerFlagManifest transcriptDigest artifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    checkerBinaryDigest :=
  fun contract =>
    contract checkerBinaryDigest
      (fun binaryProof _versionProof _flagProof _transcriptProof
          _artifactProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => binaryProof)

theorem ay_cvpg_contract_checker_version
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cvpg_pin_contract checkerBinaryDigest checkerVersionManifest
      checkerFlagManifest transcriptDigest artifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    checkerVersionManifest :=
  fun contract =>
    contract checkerVersionManifest
      (fun _binaryProof versionProof _flagProof _transcriptProof
          _artifactProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => versionProof)

theorem ay_cvpg_contract_checker_flags
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cvpg_pin_contract checkerBinaryDigest checkerVersionManifest
      checkerFlagManifest transcriptDigest artifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    checkerFlagManifest :=
  fun contract =>
    contract checkerFlagManifest
      (fun _binaryProof _versionProof flagProof _transcriptProof
          _artifactProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => flagProof)

theorem ay_cvpg_contract_transcript
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cvpg_pin_contract checkerBinaryDigest checkerVersionManifest
      checkerFlagManifest transcriptDigest artifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    transcriptDigest :=
  fun contract =>
    contract transcriptDigest
      (fun _binaryProof _versionProof _flagProof transcriptProof
          _artifactProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => transcriptProof)

theorem ay_cvpg_contract_artifact
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cvpg_pin_contract checkerBinaryDigest checkerVersionManifest
      checkerFlagManifest transcriptDigest artifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    artifactDigest :=
  fun contract =>
    contract artifactDigest
      (fun _binaryProof _versionProof _flagProof _transcriptProof
          artifactProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => artifactProof)

theorem ay_cvpg_contract_fingerprint
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cvpg_pin_contract checkerBinaryDigest checkerVersionManifest
      checkerFlagManifest transcriptDigest artifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _binaryProof _versionProof _flagProof _transcriptProof
          _artifactProof fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => fingerprintProof)

theorem ay_cvpg_contract_build
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cvpg_pin_contract checkerBinaryDigest checkerVersionManifest
      checkerFlagManifest transcriptDigest artifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _binaryProof _versionProof _flagProof _transcriptProof
          _artifactProof _fingerprintProof buildProof _archiveProof
          _fallbackProof _auditProof => buildProof)

theorem ay_cvpg_contract_archive
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cvpg_pin_contract checkerBinaryDigest checkerVersionManifest
      checkerFlagManifest transcriptDigest artifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _binaryProof _versionProof _flagProof _transcriptProof
          _artifactProof _fingerprintProof _buildProof archiveProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_cvpg_contract_fallback
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cvpg_pin_contract checkerBinaryDigest checkerVersionManifest
      checkerFlagManifest transcriptDigest artifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _binaryProof _versionProof _flagProof _transcriptProof
          _artifactProof _fingerprintProof _buildProof _archiveProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_cvpg_contract_audit
    (checkerBinaryDigest checkerVersionManifest checkerFlagManifest
      transcriptDigest artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cvpg_pin_contract checkerBinaryDigest checkerVersionManifest
      checkerFlagManifest transcriptDigest artifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _binaryProof _versionProof _flagProof _transcriptProof
          _artifactProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof auditProof => auditProof)

theorem ay_cvpg_sat_publication_intro
    (pinContract pinnedCheckerAccepts checkedModel originalModel : Prop) :
    pinContract -> pinnedCheckerAccepts -> checkedModel -> originalModel ->
    ay_cvpg_sat_publication pinContract pinnedCheckerAccepts checkedModel
      originalModel :=
  fun hcontract haccepts hchecked horiginal =>
    ay_cvpg_conj_intro pinContract
      (ay_cvpg_conj pinnedCheckerAccepts
        (ay_cvpg_conj checkedModel originalModel))
      hcontract
      (ay_cvpg_conj_intro pinnedCheckerAccepts
        (ay_cvpg_conj checkedModel originalModel)
        haccepts
        (ay_cvpg_conj_intro checkedModel originalModel hchecked horiginal))

theorem ay_cvpg_unsat_publication_intro
    (pinContract pinnedCheckerAccepts checkedProof originalEmptyClause : Prop) :
    pinContract -> pinnedCheckerAccepts -> checkedProof ->
    originalEmptyClause ->
    ay_cvpg_unsat_publication pinContract pinnedCheckerAccepts checkedProof
      originalEmptyClause :=
  fun hcontract haccepts hchecked horiginal =>
    ay_cvpg_conj_intro pinContract
      (ay_cvpg_conj pinnedCheckerAccepts
        (ay_cvpg_conj checkedProof originalEmptyClause))
      hcontract
      (ay_cvpg_conj_intro pinnedCheckerAccepts
        (ay_cvpg_conj checkedProof originalEmptyClause)
        haccepts
        (ay_cvpg_conj_intro checkedProof originalEmptyClause hchecked
          horiginal))

theorem ay_cvpg_sat_publication_original_model
    (pinContract pinnedCheckerAccepts checkedModel originalModel : Prop) :
    ay_cvpg_sat_publication pinContract pinnedCheckerAccepts checkedModel
      originalModel ->
    originalModel :=
  fun publication =>
    ay_cvpg_conj_right checkedModel originalModel
      (ay_cvpg_conj_right pinnedCheckerAccepts
        (ay_cvpg_conj checkedModel originalModel)
        (ay_cvpg_conj_right pinContract
          (ay_cvpg_conj pinnedCheckerAccepts
            (ay_cvpg_conj checkedModel originalModel))
          publication))

theorem ay_cvpg_unsat_publication_original_empty_clause
    (pinContract pinnedCheckerAccepts checkedProof originalEmptyClause : Prop) :
    ay_cvpg_unsat_publication pinContract pinnedCheckerAccepts checkedProof
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_cvpg_conj_right checkedProof originalEmptyClause
      (ay_cvpg_conj_right pinnedCheckerAccepts
        (ay_cvpg_conj checkedProof originalEmptyClause)
        (ay_cvpg_conj_right pinContract
          (ay_cvpg_conj pinnedCheckerAccepts
            (ay_cvpg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_cvpg_accepted_pin_preserves_sat_soundness
    (pinContract pinnedCheckerAccepts checkedModel originalModel : Prop) :
    ay_cvpg_sat_publication pinContract pinnedCheckerAccepts checkedModel
      originalModel ->
    originalModel :=
  ay_cvpg_sat_publication_original_model pinContract pinnedCheckerAccepts
    checkedModel originalModel

theorem ay_cvpg_accepted_pin_preserves_unsat_soundness
    (pinContract pinnedCheckerAccepts checkedProof originalEmptyClause : Prop) :
    ay_cvpg_unsat_publication pinContract pinnedCheckerAccepts checkedProof
      originalEmptyClause ->
    originalEmptyClause :=
  ay_cvpg_unsat_publication_original_empty_clause pinContract
    pinnedCheckerAccepts checkedProof originalEmptyClause

theorem ay_cvpg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_cvpg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_cvpg_conj_intro reason (ay_cvpg_conj fallbackPath auditTrail)
      hreason
      (ay_cvpg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_cvpg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_cvpg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_cvpg_conj_intro reason
      (ay_cvpg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_cvpg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_cvpg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_cvpg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_cvpg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_cvpg_conj_right reason
        (ay_cvpg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_cvpg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_cvpg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_cvpg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_cvpg_conj_right reason
        (ay_cvpg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_cvpg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_cvpg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_cvpg_conj_intro reason
      (ay_cvpg_conj fallbackPath recomputeObligation)
      hreason
      (ay_cvpg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_cvpg_pin_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cvpg_blocked_publication satFact unsatFact reason ->
    ay_cvpg_recompute reason fallbackPath recomputeObligation ->
    ay_cvpg_pin_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_cvpg_conj_intro
      (ay_cvpg_blocked_publication satFact unsatFact reason)
      (ay_cvpg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_cvpg_pin_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cvpg_pin_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_cvpg_blocked_publication_no_sat satFact unsatFact reason
      (ay_cvpg_conj_left
        (ay_cvpg_blocked_publication satFact unsatFact reason)
        (ay_cvpg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_cvpg_pin_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cvpg_pin_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_cvpg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_cvpg_conj_left
        (ay_cvpg_blocked_publication satFact unsatFact reason)
        (ay_cvpg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_cvpg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_cvpg_no_claim reason fallbackPath auditTrail :=
  ay_cvpg_no_claim_intro reason fallbackPath auditTrail

theorem ay_cvpg_checker_binary_mismatch_forces_no_claim
    (checkerBinaryMismatch fallbackPath auditTrail : Prop) :
    checkerBinaryMismatch -> fallbackPath -> auditTrail ->
    ay_cvpg_no_claim checkerBinaryMismatch fallbackPath auditTrail :=
  ay_cvpg_mismatch_forces_no_claim checkerBinaryMismatch fallbackPath
    auditTrail

theorem ay_cvpg_checker_version_mismatch_forces_no_claim
    (checkerVersionMismatch fallbackPath auditTrail : Prop) :
    checkerVersionMismatch -> fallbackPath -> auditTrail ->
    ay_cvpg_no_claim checkerVersionMismatch fallbackPath auditTrail :=
  ay_cvpg_mismatch_forces_no_claim checkerVersionMismatch fallbackPath
    auditTrail

theorem ay_cvpg_checker_flag_mismatch_forces_no_claim
    (checkerFlagMismatch fallbackPath auditTrail : Prop) :
    checkerFlagMismatch -> fallbackPath -> auditTrail ->
    ay_cvpg_no_claim checkerFlagMismatch fallbackPath auditTrail :=
  ay_cvpg_mismatch_forces_no_claim checkerFlagMismatch fallbackPath auditTrail

theorem ay_cvpg_transcript_mismatch_forces_no_claim
    (transcriptMismatch fallbackPath auditTrail : Prop) :
    transcriptMismatch -> fallbackPath -> auditTrail ->
    ay_cvpg_no_claim transcriptMismatch fallbackPath auditTrail :=
  ay_cvpg_mismatch_forces_no_claim transcriptMismatch fallbackPath auditTrail

theorem ay_cvpg_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_cvpg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_cvpg_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_cvpg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch fallbackPath auditTrail : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    ay_cvpg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_cvpg_mismatch_forces_no_claim fingerprintMismatch fallbackPath auditTrail

theorem ay_cvpg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_cvpg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_cvpg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_cvpg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_cvpg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_cvpg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_cvpg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_cvpg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_cvpg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_cvpg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cvpg_pin_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_cvpg_pin_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_cvpg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cvpg_pin_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_cvpg_pin_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
