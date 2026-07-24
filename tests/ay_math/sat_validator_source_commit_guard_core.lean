-- SAT-COMP validator source-commit/build provenance guard core.
--
-- Public SAT/UNSAT claims are tied to the intended ay source commit, build,
-- binary, configuration, benchmark, output, artifact, checker, archive,
-- fallback, and audit evidence.

def ay_scg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_scg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_scg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_scg_disj satFact (ay_scg_disj unsatFact noClaimFact)

def ay_scg_source_contract
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (sourceCommitDigest -> buildManifest -> solverBinaryDigest ->
      solverConfigurationDigest -> benchmarkFingerprint -> solverOutputDigest ->
      modelProofArtifactDigest -> checkerTranscript -> archiveManifest ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_scg_sat_publication
    (sourceContract sourceBuildBinaryConfigMatch checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_scg_conj sourceContract
    (ay_scg_conj sourceBuildBinaryConfigMatch
      (ay_scg_conj checkedModel originalBenchmarkSat))

def ay_scg_unsat_publication
    (sourceContract sourceBuildBinaryConfigMatch checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_scg_conj sourceContract
    (ay_scg_conj sourceBuildBinaryConfigMatch
      (ay_scg_conj checkedProof originalBenchmarkUnsat))

def ay_scg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_scg_conj reason (ay_scg_conj fallbackPath auditTrail)

def ay_scg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_scg_conj reason
    (ay_scg_conj (satFact -> False) (unsatFact -> False))

def ay_scg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_scg_conj reason
    (ay_scg_conj fallbackPath recomputeObligation)

def ay_scg_source_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_scg_conj
    (ay_scg_blocked_publication satFact unsatFact reason)
    (ay_scg_recompute reason fallbackPath recomputeObligation)

theorem ay_scg_conj_intro (left right : Prop) :
    left -> right -> ay_scg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_scg_conj_left (left right : Prop) :
    ay_scg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_scg_conj_right (left right : Prop) :
    ay_scg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_scg_disj_left (left right : Prop) :
    left -> ay_scg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_scg_disj_right (left right : Prop) :
    right -> ay_scg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_scg_source_contract_intro
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    sourceCommitDigest -> buildManifest -> solverBinaryDigest ->
    solverConfigurationDigest -> benchmarkFingerprint -> solverOutputDigest ->
    modelProofArtifactDigest -> checkerTranscript -> archiveManifest ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript :=
  fun sourceProof buildProof binaryProof configProof benchmarkProof outputProof
      artifactProof checkerProof archiveProof fallbackProof auditProof result
      build =>
    build sourceProof buildProof binaryProof configProof benchmarkProof
      outputProof artifactProof checkerProof archiveProof fallbackProof
      auditProof

theorem ay_scg_contract_source
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    sourceCommitDigest :=
  fun contract =>
    contract sourceCommitDigest
      (fun sourceProof _buildProof _binaryProof _configProof _benchmarkProof
          _outputProof _artifactProof _checkerProof _archiveProof
          _fallbackProof _auditProof => sourceProof)

theorem ay_scg_contract_build
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    buildManifest :=
  fun contract =>
    contract buildManifest
      (fun _sourceProof buildProof _binaryProof _configProof _benchmarkProof
          _outputProof _artifactProof _checkerProof _archiveProof
          _fallbackProof _auditProof => buildProof)

theorem ay_scg_contract_binary
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBinaryDigest :=
  fun contract =>
    contract solverBinaryDigest
      (fun _sourceProof _buildProof binaryProof _configProof _benchmarkProof
          _outputProof _artifactProof _checkerProof _archiveProof
          _fallbackProof _auditProof => binaryProof)

theorem ay_scg_contract_config
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverConfigurationDigest :=
  fun contract =>
    contract solverConfigurationDigest
      (fun _sourceProof _buildProof _binaryProof configProof _benchmarkProof
          _outputProof _artifactProof _checkerProof _archiveProof
          _fallbackProof _auditProof => configProof)

theorem ay_scg_contract_benchmark
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _sourceProof _buildProof _binaryProof _configProof benchmarkProof
          _outputProof _artifactProof _checkerProof _archiveProof
          _fallbackProof _auditProof => benchmarkProof)

theorem ay_scg_contract_output
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverOutputDigest :=
  fun contract =>
    contract solverOutputDigest
      (fun _sourceProof _buildProof _binaryProof _configProof _benchmarkProof
          outputProof _artifactProof _checkerProof _archiveProof
          _fallbackProof _auditProof => outputProof)

theorem ay_scg_contract_artifact
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _sourceProof _buildProof _binaryProof _configProof _benchmarkProof
          _outputProof artifactProof _checkerProof _archiveProof
          _fallbackProof _auditProof => artifactProof)

theorem ay_scg_contract_checker
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _sourceProof _buildProof _binaryProof _configProof _benchmarkProof
          _outputProof _artifactProof checkerProof _archiveProof
          _fallbackProof _auditProof => checkerProof)

theorem ay_scg_contract_archive
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _sourceProof _buildProof _binaryProof _configProof _benchmarkProof
          _outputProof _artifactProof _checkerProof archiveProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_scg_contract_fallback
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _sourceProof _buildProof _binaryProof _configProof _benchmarkProof
          _outputProof _artifactProof _checkerProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_scg_contract_audit
    (sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_scg_source_contract sourceCommitDigest buildManifest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _sourceProof _buildProof _binaryProof _configProof _benchmarkProof
          _outputProof _artifactProof _checkerProof _archiveProof
          _fallbackProof auditProof => auditProof)

theorem ay_scg_sat_publication_intro
    (sourceContract sourceBuildBinaryConfigMatch checkedModel
      originalBenchmarkSat : Prop) :
    sourceContract -> sourceBuildBinaryConfigMatch -> checkedModel ->
    originalBenchmarkSat ->
    ay_scg_sat_publication sourceContract sourceBuildBinaryConfigMatch
      checkedModel originalBenchmarkSat :=
  fun hcontract hmatch hchecked horiginal =>
    ay_scg_conj_intro sourceContract
      (ay_scg_conj sourceBuildBinaryConfigMatch
        (ay_scg_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_scg_conj_intro sourceBuildBinaryConfigMatch
        (ay_scg_conj checkedModel originalBenchmarkSat)
        hmatch
        (ay_scg_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_scg_unsat_publication_intro
    (sourceContract sourceBuildBinaryConfigMatch checkedProof
      originalBenchmarkUnsat : Prop) :
    sourceContract -> sourceBuildBinaryConfigMatch -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_scg_unsat_publication sourceContract sourceBuildBinaryConfigMatch
      checkedProof originalBenchmarkUnsat :=
  fun hcontract hmatch hchecked horiginal =>
    ay_scg_conj_intro sourceContract
      (ay_scg_conj sourceBuildBinaryConfigMatch
        (ay_scg_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_scg_conj_intro sourceBuildBinaryConfigMatch
        (ay_scg_conj checkedProof originalBenchmarkUnsat)
        hmatch
        (ay_scg_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_scg_sat_publication_original_claim
    (sourceContract sourceBuildBinaryConfigMatch checkedModel
      originalBenchmarkSat : Prop) :
    ay_scg_sat_publication sourceContract sourceBuildBinaryConfigMatch
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_scg_conj_right checkedModel originalBenchmarkSat
      (ay_scg_conj_right sourceBuildBinaryConfigMatch
        (ay_scg_conj checkedModel originalBenchmarkSat)
        (ay_scg_conj_right sourceContract
          (ay_scg_conj sourceBuildBinaryConfigMatch
            (ay_scg_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_scg_unsat_publication_original_claim
    (sourceContract sourceBuildBinaryConfigMatch checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_scg_unsat_publication sourceContract sourceBuildBinaryConfigMatch
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_scg_conj_right checkedProof originalBenchmarkUnsat
      (ay_scg_conj_right sourceBuildBinaryConfigMatch
        (ay_scg_conj checkedProof originalBenchmarkUnsat)
        (ay_scg_conj_right sourceContract
          (ay_scg_conj sourceBuildBinaryConfigMatch
            (ay_scg_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_scg_accepted_source_preserves_sat_soundness
    (sourceContract sourceBuildBinaryConfigMatch checkedModel
      originalBenchmarkSat : Prop) :
    ay_scg_sat_publication sourceContract sourceBuildBinaryConfigMatch
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_scg_sat_publication_original_claim sourceContract
    sourceBuildBinaryConfigMatch checkedModel originalBenchmarkSat

theorem ay_scg_accepted_source_preserves_unsat_soundness
    (sourceContract sourceBuildBinaryConfigMatch checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_scg_unsat_publication sourceContract sourceBuildBinaryConfigMatch
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_scg_unsat_publication_original_claim sourceContract
    sourceBuildBinaryConfigMatch checkedProof originalBenchmarkUnsat

theorem ay_scg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_scg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_scg_conj_intro reason (ay_scg_conj fallbackPath auditTrail)
      hreason
      (ay_scg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_scg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_scg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_scg_conj_intro reason
      (ay_scg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_scg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_scg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_scg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_scg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_scg_conj_right reason
        (ay_scg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_scg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_scg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_scg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_scg_conj_right reason
        (ay_scg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_scg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_scg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_scg_conj_intro reason
      (ay_scg_conj fallbackPath recomputeObligation)
      hreason
      (ay_scg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_scg_source_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_scg_blocked_publication satFact unsatFact reason ->
    ay_scg_recompute reason fallbackPath recomputeObligation ->
    ay_scg_source_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_scg_conj_intro
      (ay_scg_blocked_publication satFact unsatFact reason)
      (ay_scg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_scg_source_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_scg_source_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_scg_blocked_publication_no_sat satFact unsatFact reason
      (ay_scg_conj_left
        (ay_scg_blocked_publication satFact unsatFact reason)
        (ay_scg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_scg_source_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_scg_source_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_scg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_scg_conj_left
        (ay_scg_blocked_publication satFact unsatFact reason)
        (ay_scg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_scg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_scg_no_claim reason fallbackPath auditTrail :=
  ay_scg_no_claim_intro reason fallbackPath auditTrail

theorem ay_scg_source_mismatch_forces_no_claim
    (sourceMismatch fallbackPath auditTrail : Prop) :
    sourceMismatch -> fallbackPath -> auditTrail ->
    ay_scg_no_claim sourceMismatch fallbackPath auditTrail :=
  ay_scg_mismatch_forces_no_claim sourceMismatch fallbackPath auditTrail

theorem ay_scg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_scg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_scg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_scg_binary_mismatch_forces_no_claim
    (binaryMismatch fallbackPath auditTrail : Prop) :
    binaryMismatch -> fallbackPath -> auditTrail ->
    ay_scg_no_claim binaryMismatch fallbackPath auditTrail :=
  ay_scg_mismatch_forces_no_claim binaryMismatch fallbackPath auditTrail

theorem ay_scg_config_mismatch_forces_no_claim
    (configMismatch fallbackPath auditTrail : Prop) :
    configMismatch -> fallbackPath -> auditTrail ->
    ay_scg_no_claim configMismatch fallbackPath auditTrail :=
  ay_scg_mismatch_forces_no_claim configMismatch fallbackPath auditTrail

theorem ay_scg_output_mismatch_forces_no_claim
    (outputMismatch fallbackPath auditTrail : Prop) :
    outputMismatch -> fallbackPath -> auditTrail ->
    ay_scg_no_claim outputMismatch fallbackPath auditTrail :=
  ay_scg_mismatch_forces_no_claim outputMismatch fallbackPath auditTrail

theorem ay_scg_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_scg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_scg_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_scg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_scg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_scg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_scg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_scg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_scg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_scg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_scg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_scg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_scg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_scg_source_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_scg_source_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_scg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_scg_source_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_scg_source_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
