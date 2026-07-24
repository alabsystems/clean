-- SAT-COMP validator stdout/stderr split guard core.
--
-- Public SAT/UNSAT claims require stdout result digest, stderr diagnostic
-- digest, stream ordering policy, parsed result artifact, checker transcript,
-- benchmark fingerprint, solver build evidence, archive manifest, no-claim
-- fallback, and audit transcript to agree.  Stream split failures become
-- no-claim recompute obligations rather than public semantic answers.

def ay_sspg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_sspg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_sspg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_sspg_disj satFact (ay_sspg_disj unsatFact noClaimFact)

def ay_sspg_stream_split_contract
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) : Prop :=
  forall result : Prop,
    (stdoutResultDigest -> stderrDiagnosticDigest -> streamOrderingPolicy ->
      parsedResultArtifact -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> noClaimFallback ->
      auditTranscript -> result) ->
    result

def ay_sspg_sat_publication
    (streamContract acceptedStreamSplit checkedModel originalModel : Prop) :
    Prop :=
  ay_sspg_conj streamContract
    (ay_sspg_conj acceptedStreamSplit
      (ay_sspg_conj checkedModel originalModel))

def ay_sspg_unsat_publication
    (streamContract acceptedStreamSplit checkedProof originalEmptyClause :
      Prop) : Prop :=
  ay_sspg_conj streamContract
    (ay_sspg_conj acceptedStreamSplit
      (ay_sspg_conj checkedProof originalEmptyClause))

def ay_sspg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_sspg_conj reason (ay_sspg_conj fallbackPath auditTrail)

def ay_sspg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_sspg_conj reason
    (ay_sspg_conj (satFact -> False) (unsatFact -> False))

def ay_sspg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_sspg_conj reason
    (ay_sspg_conj fallbackPath recomputeObligation)

def ay_sspg_stream_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_sspg_conj
    (ay_sspg_blocked_publication satFact unsatFact reason)
    (ay_sspg_recompute reason fallbackPath recomputeObligation)

theorem ay_sspg_conj_intro (left right : Prop) :
    left -> right -> ay_sspg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_sspg_conj_left (left right : Prop) :
    ay_sspg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_sspg_conj_right (left right : Prop) :
    ay_sspg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_sspg_disj_left (left right : Prop) :
    left -> ay_sspg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_sspg_disj_right (left right : Prop) :
    right -> ay_sspg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_sspg_stream_split_contract_intro
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    stdoutResultDigest -> stderrDiagnosticDigest -> streamOrderingPolicy ->
    parsedResultArtifact -> checkerTranscript -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> noClaimFallback ->
    auditTranscript ->
    ay_sspg_stream_split_contract stdoutResultDigest
      stderrDiagnosticDigest streamOrderingPolicy parsedResultArtifact
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript :=
  fun stdoutProof stderrProof orderingProof artifactProof checkerProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof result
      build =>
    build stdoutProof stderrProof orderingProof artifactProof checkerProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof

theorem ay_sspg_contract_stdout
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_sspg_stream_split_contract stdoutResultDigest stderrDiagnosticDigest
      streamOrderingPolicy parsedResultArtifact checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest noClaimFallback
      auditTranscript ->
    stdoutResultDigest :=
  fun contract =>
    contract stdoutResultDigest
      (fun stdoutProof _stderrProof _orderingProof _artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => stdoutProof)

theorem ay_sspg_contract_stderr
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_sspg_stream_split_contract stdoutResultDigest stderrDiagnosticDigest
      streamOrderingPolicy parsedResultArtifact checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest noClaimFallback
      auditTranscript ->
    stderrDiagnosticDigest :=
  fun contract =>
    contract stderrDiagnosticDigest
      (fun _stdoutProof stderrProof _orderingProof _artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => stderrProof)

theorem ay_sspg_contract_ordering
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_sspg_stream_split_contract stdoutResultDigest stderrDiagnosticDigest
      streamOrderingPolicy parsedResultArtifact checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest noClaimFallback
      auditTranscript ->
    streamOrderingPolicy :=
  fun contract =>
    contract streamOrderingPolicy
      (fun _stdoutProof _stderrProof orderingProof _artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => orderingProof)

theorem ay_sspg_contract_artifact
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_sspg_stream_split_contract stdoutResultDigest stderrDiagnosticDigest
      streamOrderingPolicy parsedResultArtifact checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest noClaimFallback
      auditTranscript ->
    parsedResultArtifact :=
  fun contract =>
    contract parsedResultArtifact
      (fun _stdoutProof _stderrProof _orderingProof artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => artifactProof)

theorem ay_sspg_contract_checker
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_sspg_stream_split_contract stdoutResultDigest stderrDiagnosticDigest
      streamOrderingPolicy parsedResultArtifact checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest noClaimFallback
      auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _stdoutProof _stderrProof _orderingProof _artifactProof
          checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => checkerProof)

theorem ay_sspg_contract_fingerprint
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_sspg_stream_split_contract stdoutResultDigest stderrDiagnosticDigest
      streamOrderingPolicy parsedResultArtifact checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest noClaimFallback
      auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _stdoutProof _stderrProof _orderingProof _artifactProof
          _checkerProof fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => fingerprintProof)

theorem ay_sspg_contract_build
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_sspg_stream_split_contract stdoutResultDigest stderrDiagnosticDigest
      streamOrderingPolicy parsedResultArtifact checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest noClaimFallback
      auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _stdoutProof _stderrProof _orderingProof _artifactProof
          _checkerProof _fingerprintProof buildProof _archiveProof
          _fallbackProof _auditProof => buildProof)

theorem ay_sspg_contract_archive
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_sspg_stream_split_contract stdoutResultDigest stderrDiagnosticDigest
      streamOrderingPolicy parsedResultArtifact checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest noClaimFallback
      auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _stdoutProof _stderrProof _orderingProof _artifactProof
          _checkerProof _fingerprintProof _buildProof archiveProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_sspg_contract_fallback
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_sspg_stream_split_contract stdoutResultDigest stderrDiagnosticDigest
      streamOrderingPolicy parsedResultArtifact checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest noClaimFallback
      auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _stdoutProof _stderrProof _orderingProof _artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_sspg_contract_audit
    (stdoutResultDigest stderrDiagnosticDigest streamOrderingPolicy
      parsedResultArtifact checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_sspg_stream_split_contract stdoutResultDigest stderrDiagnosticDigest
      streamOrderingPolicy parsedResultArtifact checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest noClaimFallback
      auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _stdoutProof _stderrProof _orderingProof _artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof auditProof => auditProof)

theorem ay_sspg_sat_publication_intro
    (streamContract acceptedStreamSplit checkedModel originalModel : Prop) :
    streamContract -> acceptedStreamSplit -> checkedModel -> originalModel ->
    ay_sspg_sat_publication streamContract acceptedStreamSplit checkedModel
      originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_sspg_conj_intro streamContract
      (ay_sspg_conj acceptedStreamSplit
        (ay_sspg_conj checkedModel originalModel))
      contractProof
      (ay_sspg_conj_intro acceptedStreamSplit
        (ay_sspg_conj checkedModel originalModel)
        acceptedProof
        (ay_sspg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_sspg_sat_publication_stream
    (streamContract acceptedStreamSplit checkedModel originalModel : Prop) :
    ay_sspg_sat_publication streamContract acceptedStreamSplit checkedModel
      originalModel ->
    streamContract :=
  fun publication =>
    ay_sspg_conj_left streamContract
      (ay_sspg_conj acceptedStreamSplit
        (ay_sspg_conj checkedModel originalModel))
      publication

theorem ay_sspg_sat_publication_original_model
    (streamContract acceptedStreamSplit checkedModel originalModel : Prop) :
    ay_sspg_sat_publication streamContract acceptedStreamSplit checkedModel
      originalModel ->
    originalModel :=
  fun publication =>
    ay_sspg_conj_right checkedModel originalModel
      (ay_sspg_conj_right acceptedStreamSplit
        (ay_sspg_conj checkedModel originalModel)
        (ay_sspg_conj_right streamContract
          (ay_sspg_conj acceptedStreamSplit
            (ay_sspg_conj checkedModel originalModel))
          publication))

theorem ay_sspg_unsat_publication_intro
    (streamContract acceptedStreamSplit checkedProof originalEmptyClause :
      Prop) :
    streamContract -> acceptedStreamSplit -> checkedProof ->
    originalEmptyClause ->
    ay_sspg_unsat_publication streamContract acceptedStreamSplit checkedProof
      originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_sspg_conj_intro streamContract
      (ay_sspg_conj acceptedStreamSplit
        (ay_sspg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_sspg_conj_intro acceptedStreamSplit
        (ay_sspg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_sspg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_sspg_unsat_publication_stream
    (streamContract acceptedStreamSplit checkedProof originalEmptyClause :
      Prop) :
    ay_sspg_unsat_publication streamContract acceptedStreamSplit checkedProof
      originalEmptyClause ->
    streamContract :=
  fun publication =>
    ay_sspg_conj_left streamContract
      (ay_sspg_conj acceptedStreamSplit
        (ay_sspg_conj checkedProof originalEmptyClause))
      publication

theorem ay_sspg_unsat_publication_original_empty_clause
    (streamContract acceptedStreamSplit checkedProof originalEmptyClause :
      Prop) :
    ay_sspg_unsat_publication streamContract acceptedStreamSplit checkedProof
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_sspg_conj_right checkedProof originalEmptyClause
      (ay_sspg_conj_right acceptedStreamSplit
        (ay_sspg_conj checkedProof originalEmptyClause)
        (ay_sspg_conj_right streamContract
          (ay_sspg_conj acceptedStreamSplit
            (ay_sspg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_sspg_accepted_stream_sat_passes_publication
    (streamContract acceptedStreamSplit checkedModel originalModel : Prop) :
    ay_sspg_sat_publication streamContract acceptedStreamSplit checkedModel
      originalModel ->
    ay_sspg_public_result originalModel False False :=
  fun publication =>
    ay_sspg_disj_left originalModel (ay_sspg_disj False False)
      (ay_sspg_sat_publication_original_model streamContract
        acceptedStreamSplit checkedModel originalModel publication)

theorem ay_sspg_accepted_stream_unsat_passes_publication
    (streamContract acceptedStreamSplit checkedProof originalEmptyClause :
      Prop) :
    ay_sspg_unsat_publication streamContract acceptedStreamSplit checkedProof
      originalEmptyClause ->
    ay_sspg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_sspg_disj_right False (ay_sspg_disj originalEmptyClause False)
      (ay_sspg_disj_left originalEmptyClause False
        (ay_sspg_unsat_publication_original_empty_clause streamContract
          acceptedStreamSplit checkedProof originalEmptyClause publication))

theorem ay_sspg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_sspg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_sspg_conj_intro reason (ay_sspg_conj fallbackPath auditTrail)
      reasonProof
      (ay_sspg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_sspg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_sspg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_sspg_conj_intro reason
      (ay_sspg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_sspg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_sspg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_sspg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_sspg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_sspg_conj_right reason
        (ay_sspg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_sspg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_sspg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_sspg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_sspg_conj_right reason
        (ay_sspg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_sspg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_sspg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_sspg_conj_intro reason
      (ay_sspg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_sspg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_sspg_stream_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sspg_blocked_publication satFact unsatFact reason ->
    ay_sspg_recompute reason fallbackPath recomputeObligation ->
    ay_sspg_stream_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_sspg_conj_intro
      (ay_sspg_blocked_publication satFact unsatFact reason)
      (ay_sspg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_sspg_stream_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sspg_stream_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_sspg_blocked_publication_no_sat satFact unsatFact reason
      (ay_sspg_conj_left
        (ay_sspg_blocked_publication satFact unsatFact reason)
        (ay_sspg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_sspg_stream_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sspg_stream_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_sspg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_sspg_conj_left
        (ay_sspg_blocked_publication satFact unsatFact reason)
        (ay_sspg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_sspg_stream_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sspg_stream_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_sspg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_sspg_conj_right
      (ay_sspg_blocked_publication satFact unsatFact reason)
      (ay_sspg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_sspg_interleaved_stream_forces_no_claim
    (satFact unsatFact interleavedStream fallbackPath auditTrail
      recomputeObligation : Prop) :
    interleavedStream -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sspg_no_claim interleavedStream fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_sspg_no_claim_intro interleavedStream fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_sspg_truncated_stream_forces_recompute
    (satFact unsatFact truncatedStream fallbackPath recomputeObligation :
      Prop) :
    truncatedStream -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_sspg_stream_failure satFact unsatFact truncatedStream fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_sspg_stream_failure_intro satFact unsatFact truncatedStream
      fallbackPath recomputeObligation
      (ay_sspg_blocked_publication_intro satFact unsatFact truncatedStream
        reasonProof noSat noUnsat)
      (ay_sspg_recompute_intro truncatedStream fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_sspg_misdirected_stream_forces_no_claim
    (satFact unsatFact misdirectedStream fallbackPath auditTrail
      recomputeObligation : Prop) :
    misdirectedStream -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sspg_no_claim misdirectedStream fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_sspg_no_claim_intro misdirectedStream fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_sspg_status_on_stderr_only_forces_no_claim
    (satFact unsatFact statusOnStderrOnly fallbackPath auditTrail
      recomputeObligation : Prop) :
    statusOnStderrOnly -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sspg_no_claim statusOnStderrOnly fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_sspg_no_claim_intro statusOnStderrOnly fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_sspg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sspg_no_claim checkerMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_sspg_no_claim_intro checkerMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_sspg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sspg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_sspg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_sspg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sspg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_sspg_no_claim_intro buildMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_sspg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sspg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_sspg_no_claim_intro archiveMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_sspg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivation fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivation -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sspg_no_claim fallbackActivation fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_sspg_no_claim_intro fallbackActivation fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_sspg_failed_stream_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sspg_stream_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_sspg_stream_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_sspg_failed_stream_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sspg_stream_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_sspg_stream_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_sspg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_sspg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_sspg_conj_left reason (ay_sspg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_sspg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_sspg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_sspg_conj_left reason (ay_sspg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
