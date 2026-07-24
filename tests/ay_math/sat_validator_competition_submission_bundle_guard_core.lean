-- SAT-COMP validator competition submission bundle guard core.
--
-- Sequential-main public claims are allowed only when the competition
-- submission bundle agrees across binary, script, config, benchmark, logs,
-- result artifacts, independent checker evidence, archive, and fallback path.

def ay_vsub_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vsub_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vsub_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vsub_disj satFact (ay_vsub_disj unsatFact noClaimFact)

def ay_vsub_bundle_contract
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) : Prop :=
  forall result : Prop,
    (solverBinaryHash -> runScriptDigest -> configurationManifest ->
      benchmarkFingerprint -> stdoutStderrTranscript -> resultArtifact ->
      certificateModel -> independentCheckerTranscript -> archiveManifest ->
      noClaimFallbackPath -> result) ->
    result

def ay_vsub_sat_publication
    (bundleContract modelEvidence originalModel : Prop) : Prop :=
  ay_vsub_conj bundleContract
    (ay_vsub_conj modelEvidence originalModel)

def ay_vsub_unsat_publication
    (bundleContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vsub_conj bundleContract
    (ay_vsub_conj proofEvidence originalEmptyClause)

def ay_vsub_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vsub_conj reason (ay_vsub_conj fallbackPath auditTrail)

def ay_vsub_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vsub_conj reason
    (ay_vsub_conj (satFact -> False) (unsatFact -> False))

def ay_vsub_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vsub_conj reason
    (ay_vsub_conj fallbackPath recomputeObligation)

def ay_vsub_bundle_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vsub_conj
    (ay_vsub_blocked_publication satFact unsatFact reason)
    (ay_vsub_recompute reason fallbackPath recomputeObligation)

theorem ay_vsub_conj_intro (left right : Prop) :
    left -> right -> ay_vsub_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vsub_conj_left (left right : Prop) :
    ay_vsub_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vsub_conj_right (left right : Prop) :
    ay_vsub_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vsub_disj_left (left right : Prop) :
    left -> ay_vsub_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vsub_disj_right (left right : Prop) :
    right -> ay_vsub_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vsub_bundle_contract_intro
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) :
    solverBinaryHash -> runScriptDigest -> configurationManifest ->
    benchmarkFingerprint -> stdoutStderrTranscript -> resultArtifact ->
    certificateModel -> independentCheckerTranscript -> archiveManifest ->
    noClaimFallbackPath ->
    ay_vsub_bundle_contract solverBinaryHash runScriptDigest
      configurationManifest benchmarkFingerprint stdoutStderrTranscript
      resultArtifact certificateModel independentCheckerTranscript
      archiveManifest noClaimFallbackPath :=
  fun binaryProof scriptProof configProof fingerprintProof transcriptProof
      artifactProof certificateProof checkerProof archiveProof fallbackProof
      result build =>
    build binaryProof scriptProof configProof fingerprintProof transcriptProof
      artifactProof certificateProof checkerProof archiveProof fallbackProof

theorem ay_vsub_bundle_contract_binary
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) :
    ay_vsub_bundle_contract solverBinaryHash runScriptDigest
      configurationManifest benchmarkFingerprint stdoutStderrTranscript
      resultArtifact certificateModel independentCheckerTranscript
      archiveManifest noClaimFallbackPath ->
    solverBinaryHash :=
  fun contract =>
    contract solverBinaryHash
      (fun binaryProof _scriptProof _configProof _fingerprintProof
          _transcriptProof _artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => binaryProof)

theorem ay_vsub_bundle_contract_run_script
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) :
    ay_vsub_bundle_contract solverBinaryHash runScriptDigest
      configurationManifest benchmarkFingerprint stdoutStderrTranscript
      resultArtifact certificateModel independentCheckerTranscript
      archiveManifest noClaimFallbackPath ->
    runScriptDigest :=
  fun contract =>
    contract runScriptDigest
      (fun _binaryProof scriptProof _configProof _fingerprintProof
          _transcriptProof _artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => scriptProof)

theorem ay_vsub_bundle_contract_configuration
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) :
    ay_vsub_bundle_contract solverBinaryHash runScriptDigest
      configurationManifest benchmarkFingerprint stdoutStderrTranscript
      resultArtifact certificateModel independentCheckerTranscript
      archiveManifest noClaimFallbackPath ->
    configurationManifest :=
  fun contract =>
    contract configurationManifest
      (fun _binaryProof _scriptProof configProof _fingerprintProof
          _transcriptProof _artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => configProof)

theorem ay_vsub_bundle_contract_fingerprint
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) :
    ay_vsub_bundle_contract solverBinaryHash runScriptDigest
      configurationManifest benchmarkFingerprint stdoutStderrTranscript
      resultArtifact certificateModel independentCheckerTranscript
      archiveManifest noClaimFallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _binaryProof _scriptProof _configProof fingerprintProof
          _transcriptProof _artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => fingerprintProof)

theorem ay_vsub_bundle_contract_stdout_stderr
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) :
    ay_vsub_bundle_contract solverBinaryHash runScriptDigest
      configurationManifest benchmarkFingerprint stdoutStderrTranscript
      resultArtifact certificateModel independentCheckerTranscript
      archiveManifest noClaimFallbackPath ->
    stdoutStderrTranscript :=
  fun contract =>
    contract stdoutStderrTranscript
      (fun _binaryProof _scriptProof _configProof _fingerprintProof
          transcriptProof _artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => transcriptProof)

theorem ay_vsub_bundle_contract_result_artifact
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) :
    ay_vsub_bundle_contract solverBinaryHash runScriptDigest
      configurationManifest benchmarkFingerprint stdoutStderrTranscript
      resultArtifact certificateModel independentCheckerTranscript
      archiveManifest noClaimFallbackPath ->
    resultArtifact :=
  fun contract =>
    contract resultArtifact
      (fun _binaryProof _scriptProof _configProof _fingerprintProof
          _transcriptProof artifactProof _certificateProof _checkerProof
          _archiveProof _fallbackProof => artifactProof)

theorem ay_vsub_bundle_contract_certificate_model
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) :
    ay_vsub_bundle_contract solverBinaryHash runScriptDigest
      configurationManifest benchmarkFingerprint stdoutStderrTranscript
      resultArtifact certificateModel independentCheckerTranscript
      archiveManifest noClaimFallbackPath ->
    certificateModel :=
  fun contract =>
    contract certificateModel
      (fun _binaryProof _scriptProof _configProof _fingerprintProof
          _transcriptProof _artifactProof certificateProof _checkerProof
          _archiveProof _fallbackProof => certificateProof)

theorem ay_vsub_bundle_contract_checker
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) :
    ay_vsub_bundle_contract solverBinaryHash runScriptDigest
      configurationManifest benchmarkFingerprint stdoutStderrTranscript
      resultArtifact certificateModel independentCheckerTranscript
      archiveManifest noClaimFallbackPath ->
    independentCheckerTranscript :=
  fun contract =>
    contract independentCheckerTranscript
      (fun _binaryProof _scriptProof _configProof _fingerprintProof
          _transcriptProof _artifactProof _certificateProof checkerProof
          _archiveProof _fallbackProof => checkerProof)

theorem ay_vsub_bundle_contract_archive
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) :
    ay_vsub_bundle_contract solverBinaryHash runScriptDigest
      configurationManifest benchmarkFingerprint stdoutStderrTranscript
      resultArtifact certificateModel independentCheckerTranscript
      archiveManifest noClaimFallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _binaryProof _scriptProof _configProof _fingerprintProof
          _transcriptProof _artifactProof _certificateProof _checkerProof
          archiveProof _fallbackProof => archiveProof)

theorem ay_vsub_bundle_contract_fallback
    (solverBinaryHash runScriptDigest configurationManifest
      benchmarkFingerprint stdoutStderrTranscript resultArtifact
      certificateModel independentCheckerTranscript archiveManifest
      noClaimFallbackPath : Prop) :
    ay_vsub_bundle_contract solverBinaryHash runScriptDigest
      configurationManifest benchmarkFingerprint stdoutStderrTranscript
      resultArtifact certificateModel independentCheckerTranscript
      archiveManifest noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _binaryProof _scriptProof _configProof _fingerprintProof
          _transcriptProof _artifactProof _certificateProof _checkerProof
          _archiveProof fallbackProof => fallbackProof)

theorem ay_vsub_sat_publication_intro
    (bundleContract modelEvidence originalModel : Prop) :
    bundleContract -> modelEvidence -> originalModel ->
    ay_vsub_sat_publication bundleContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vsub_conj_intro bundleContract
      (ay_vsub_conj modelEvidence originalModel) contractProof
      (ay_vsub_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vsub_sat_publication_original_model
    (bundleContract modelEvidence originalModel : Prop) :
    ay_vsub_sat_publication bundleContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vsub_conj_right modelEvidence originalModel
      (ay_vsub_conj_right bundleContract
        (ay_vsub_conj modelEvidence originalModel) publication)

theorem ay_vsub_unsat_publication_intro
    (bundleContract proofEvidence originalEmptyClause : Prop) :
    bundleContract -> proofEvidence -> originalEmptyClause ->
    ay_vsub_unsat_publication bundleContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vsub_conj_intro bundleContract
      (ay_vsub_conj proofEvidence originalEmptyClause) contractProof
      (ay_vsub_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vsub_unsat_publication_original_empty_clause
    (bundleContract proofEvidence originalEmptyClause : Prop) :
    ay_vsub_unsat_publication bundleContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vsub_conj_right proofEvidence originalEmptyClause
      (ay_vsub_conj_right bundleContract
        (ay_vsub_conj proofEvidence originalEmptyClause) publication)

theorem ay_vsub_accepted_bundle_sat_sound
    (bundleContract modelEvidence originalModel : Prop) :
    ay_vsub_sat_publication bundleContract modelEvidence originalModel ->
    originalModel :=
  ay_vsub_sat_publication_original_model bundleContract modelEvidence
    originalModel

theorem ay_vsub_accepted_bundle_unsat_sound
    (bundleContract proofEvidence originalEmptyClause : Prop) :
    ay_vsub_unsat_publication bundleContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_vsub_unsat_publication_original_empty_clause bundleContract proofEvidence
    originalEmptyClause

theorem ay_vsub_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vsub_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vsub_conj_intro reason (ay_vsub_conj fallbackPath auditTrail)
      reasonProof
      (ay_vsub_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_vsub_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_vsub_conj_intro reason
      (ay_vsub_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_vsub_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_vsub_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vsub_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vsub_conj_left (satFact -> False) (unsatFact -> False)
      (ay_vsub_conj_right reason
        (ay_vsub_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vsub_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vsub_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vsub_conj_right (satFact -> False) (unsatFact -> False)
      (ay_vsub_conj_right reason
        (ay_vsub_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vsub_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vsub_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vsub_conj_intro reason
      (ay_vsub_conj fallbackPath recomputeObligation) reasonProof
      (ay_vsub_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_vsub_bundle_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_bundle_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_vsub_conj_intro
      (ay_vsub_blocked_publication satFact unsatFact reason)
      (ay_vsub_recompute reason fallbackPath recomputeObligation)
      (ay_vsub_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_vsub_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vsub_bundle_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsub_bundle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vsub_blocked_publication_no_sat satFact unsatFact reason
      (ay_vsub_conj_left
        (ay_vsub_blocked_publication satFact unsatFact reason)
        (ay_vsub_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsub_bundle_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsub_bundle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vsub_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vsub_conj_left
        (ay_vsub_blocked_publication satFact unsatFact reason)
        (ay_vsub_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsub_bundle_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsub_bundle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vsub_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vsub_conj_right
      (ay_vsub_blocked_publication satFact unsatFact reason)
      (ay_vsub_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vsub_mismatch_forces_no_claim
    (satFact unsatFact mismatch fallbackPath auditTrail recomputeObligation :
      Prop) :
    mismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_no_claim mismatch fallbackPath auditTrail :=
  fun mismatchProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_vsub_no_claim_intro mismatch fallbackPath auditTrail mismatchProof
      fallbackProof auditProof

theorem ay_vsub_binary_mismatch_blocks_publication
    (satFact unsatFact binaryMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    binaryMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_no_claim binaryMismatch fallbackPath auditTrail :=
  ay_vsub_mismatch_forces_no_claim satFact unsatFact binaryMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vsub_script_mismatch_blocks_publication
    (satFact unsatFact scriptMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    scriptMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_no_claim scriptMismatch fallbackPath auditTrail :=
  ay_vsub_mismatch_forces_no_claim satFact unsatFact scriptMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vsub_config_mismatch_blocks_publication
    (satFact unsatFact configMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    configMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_no_claim configMismatch fallbackPath auditTrail :=
  ay_vsub_mismatch_forces_no_claim satFact unsatFact configMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vsub_benchmark_mismatch_blocks_publication
    (satFact unsatFact benchmarkMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    benchmarkMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_no_claim benchmarkMismatch fallbackPath auditTrail :=
  ay_vsub_mismatch_forces_no_claim satFact unsatFact benchmarkMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vsub_stdout_stderr_mismatch_blocks_publication
    (satFact unsatFact transcriptMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    transcriptMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_no_claim transcriptMismatch fallbackPath auditTrail :=
  ay_vsub_mismatch_forces_no_claim satFact unsatFact transcriptMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vsub_result_artifact_mismatch_blocks_publication
    (satFact unsatFact artifactMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_vsub_mismatch_forces_no_claim satFact unsatFact artifactMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vsub_certificate_mismatch_blocks_publication
    (satFact unsatFact certificateMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    certificateMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_no_claim certificateMismatch fallbackPath auditTrail :=
  ay_vsub_mismatch_forces_no_claim satFact unsatFact certificateMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vsub_checker_mismatch_blocks_publication
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_vsub_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vsub_archive_mismatch_blocks_publication
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsub_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_vsub_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_vsub_failed_bundle_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsub_bundle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vsub_bundle_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vsub_failed_bundle_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsub_bundle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vsub_bundle_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vsub_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_vsub_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_vsub_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_vsub_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
