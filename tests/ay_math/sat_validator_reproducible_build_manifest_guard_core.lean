-- SAT-COMP validator reproducible-build manifest guard core.
--
-- Public SAT/UNSAT claims are tied to reproducible source, build, toolchain,
-- binary, configuration, benchmark, output, artifact, checker, archive,
-- fallback, and audit evidence.

def ay_rbmg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rbmg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_rbmg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_rbmg_disj satFact (ay_rbmg_disj unsatFact noClaimFact)

def ay_rbmg_build_contract
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (sourceCommitDigest -> buildManifest -> toolchainDigest ->
      solverBinaryDigest -> solverConfigurationDigest ->
      benchmarkFingerprint -> solverOutputDigest -> modelProofArtifactDigest ->
      checkerTranscript -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_rbmg_sat_publication
    (buildContract reproducibleBuildEvidence checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_rbmg_conj buildContract
    (ay_rbmg_conj reproducibleBuildEvidence
      (ay_rbmg_conj checkedModel originalBenchmarkSat))

def ay_rbmg_unsat_publication
    (buildContract reproducibleBuildEvidence checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_rbmg_conj buildContract
    (ay_rbmg_conj reproducibleBuildEvidence
      (ay_rbmg_conj checkedProof originalBenchmarkUnsat))

def ay_rbmg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_rbmg_conj reason (ay_rbmg_conj fallbackPath auditTrail)

def ay_rbmg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_rbmg_conj reason
    (ay_rbmg_conj (satFact -> False) (unsatFact -> False))

def ay_rbmg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_rbmg_conj reason
    (ay_rbmg_conj fallbackPath recomputeObligation)

def ay_rbmg_build_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_rbmg_conj
    (ay_rbmg_blocked_publication satFact unsatFact reason)
    (ay_rbmg_recompute reason fallbackPath recomputeObligation)

theorem ay_rbmg_conj_intro (left right : Prop) :
    left -> right -> ay_rbmg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_rbmg_conj_left (left right : Prop) :
    ay_rbmg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_rbmg_conj_right (left right : Prop) :
    ay_rbmg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_rbmg_disj_left (left right : Prop) :
    left -> ay_rbmg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_rbmg_disj_right (left right : Prop) :
    right -> ay_rbmg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_rbmg_build_contract_intro
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    sourceCommitDigest -> buildManifest -> toolchainDigest ->
    solverBinaryDigest -> solverConfigurationDigest ->
    benchmarkFingerprint -> solverOutputDigest -> modelProofArtifactDigest ->
    checkerTranscript -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript :=
  fun sourceProof buildProof toolchainProof binaryProof configProof
      benchmarkProof outputProof artifactProof checkerProof archiveProof
      fallbackProof auditProof result build =>
    build sourceProof buildProof toolchainProof binaryProof configProof
      benchmarkProof outputProof artifactProof checkerProof archiveProof
      fallbackProof auditProof

theorem ay_rbmg_contract_source
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    sourceCommitDigest :=
  fun contract =>
    contract sourceCommitDigest
      (fun sourceProof _buildProof _toolchainProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => sourceProof)

theorem ay_rbmg_contract_build
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    buildManifest :=
  fun contract =>
    contract buildManifest
      (fun _sourceProof buildProof _toolchainProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => buildProof)

theorem ay_rbmg_contract_toolchain
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    toolchainDigest :=
  fun contract =>
    contract toolchainDigest
      (fun _sourceProof _buildProof toolchainProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => toolchainProof)

theorem ay_rbmg_contract_binary
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBinaryDigest :=
  fun contract =>
    contract solverBinaryDigest
      (fun _sourceProof _buildProof _toolchainProof binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => binaryProof)

theorem ay_rbmg_contract_config
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverConfigurationDigest :=
  fun contract =>
    contract solverConfigurationDigest
      (fun _sourceProof _buildProof _toolchainProof _binaryProof configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => configProof)

theorem ay_rbmg_contract_benchmark
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _sourceProof _buildProof _toolchainProof _binaryProof _configProof
          benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => benchmarkProof)

theorem ay_rbmg_contract_output
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverOutputDigest :=
  fun contract =>
    contract solverOutputDigest
      (fun _sourceProof _buildProof _toolchainProof _binaryProof _configProof
          _benchmarkProof outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => outputProof)

theorem ay_rbmg_contract_artifact
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _sourceProof _buildProof _toolchainProof _binaryProof _configProof
          _benchmarkProof _outputProof artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => artifactProof)

theorem ay_rbmg_contract_checker
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _sourceProof _buildProof _toolchainProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof checkerProof
          _archiveProof _fallbackProof _auditProof => checkerProof)

theorem ay_rbmg_contract_archive
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _sourceProof _buildProof _toolchainProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          archiveProof _fallbackProof _auditProof => archiveProof)

theorem ay_rbmg_contract_fallback
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _sourceProof _buildProof _toolchainProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof fallbackProof _auditProof => fallbackProof)

theorem ay_rbmg_contract_audit
    (sourceCommitDigest buildManifest toolchainDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_build_contract sourceCommitDigest buildManifest toolchainDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _sourceProof _buildProof _toolchainProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof auditProof => auditProof)

theorem ay_rbmg_sat_publication_intro
    (buildContract reproducibleBuildEvidence checkedModel
      originalBenchmarkSat : Prop) :
    buildContract -> reproducibleBuildEvidence -> checkedModel ->
    originalBenchmarkSat ->
    ay_rbmg_sat_publication buildContract reproducibleBuildEvidence
      checkedModel originalBenchmarkSat :=
  fun hcontract hevidence hchecked horiginal =>
    ay_rbmg_conj_intro buildContract
      (ay_rbmg_conj reproducibleBuildEvidence
        (ay_rbmg_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_rbmg_conj_intro reproducibleBuildEvidence
        (ay_rbmg_conj checkedModel originalBenchmarkSat)
        hevidence
        (ay_rbmg_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_rbmg_unsat_publication_intro
    (buildContract reproducibleBuildEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    buildContract -> reproducibleBuildEvidence -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_rbmg_unsat_publication buildContract reproducibleBuildEvidence
      checkedProof originalBenchmarkUnsat :=
  fun hcontract hevidence hchecked horiginal =>
    ay_rbmg_conj_intro buildContract
      (ay_rbmg_conj reproducibleBuildEvidence
        (ay_rbmg_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_rbmg_conj_intro reproducibleBuildEvidence
        (ay_rbmg_conj checkedProof originalBenchmarkUnsat)
        hevidence
        (ay_rbmg_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_rbmg_sat_publication_original_claim
    (buildContract reproducibleBuildEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_rbmg_sat_publication buildContract reproducibleBuildEvidence
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_rbmg_conj_right checkedModel originalBenchmarkSat
      (ay_rbmg_conj_right reproducibleBuildEvidence
        (ay_rbmg_conj checkedModel originalBenchmarkSat)
        (ay_rbmg_conj_right buildContract
          (ay_rbmg_conj reproducibleBuildEvidence
            (ay_rbmg_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_rbmg_unsat_publication_original_claim
    (buildContract reproducibleBuildEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_rbmg_unsat_publication buildContract reproducibleBuildEvidence
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_rbmg_conj_right checkedProof originalBenchmarkUnsat
      (ay_rbmg_conj_right reproducibleBuildEvidence
        (ay_rbmg_conj checkedProof originalBenchmarkUnsat)
        (ay_rbmg_conj_right buildContract
          (ay_rbmg_conj reproducibleBuildEvidence
            (ay_rbmg_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_rbmg_accepted_build_preserves_sat_soundness
    (buildContract reproducibleBuildEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_rbmg_sat_publication buildContract reproducibleBuildEvidence
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_rbmg_sat_publication_original_claim buildContract
    reproducibleBuildEvidence checkedModel originalBenchmarkSat

theorem ay_rbmg_accepted_build_preserves_unsat_soundness
    (buildContract reproducibleBuildEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_rbmg_unsat_publication buildContract reproducibleBuildEvidence
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_rbmg_unsat_publication_original_claim buildContract
    reproducibleBuildEvidence checkedProof originalBenchmarkUnsat

theorem ay_rbmg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_rbmg_conj_intro reason (ay_rbmg_conj fallbackPath auditTrail)
      hreason
      (ay_rbmg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_rbmg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_rbmg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_rbmg_conj_intro reason
      (ay_rbmg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_rbmg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_rbmg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_rbmg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_rbmg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_rbmg_conj_right reason
        (ay_rbmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rbmg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_rbmg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_rbmg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_rbmg_conj_right reason
        (ay_rbmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rbmg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_rbmg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_rbmg_conj_intro reason
      (ay_rbmg_conj fallbackPath recomputeObligation)
      hreason
      (ay_rbmg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_rbmg_build_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rbmg_blocked_publication satFact unsatFact reason ->
    ay_rbmg_recompute reason fallbackPath recomputeObligation ->
    ay_rbmg_build_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_rbmg_conj_intro
      (ay_rbmg_blocked_publication satFact unsatFact reason)
      (ay_rbmg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_rbmg_build_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rbmg_build_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_rbmg_blocked_publication_no_sat satFact unsatFact reason
      (ay_rbmg_conj_left
        (ay_rbmg_blocked_publication satFact unsatFact reason)
        (ay_rbmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rbmg_build_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rbmg_build_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_rbmg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_rbmg_conj_left
        (ay_rbmg_blocked_publication satFact unsatFact reason)
        (ay_rbmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rbmg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim reason fallbackPath auditTrail :=
  ay_rbmg_no_claim_intro reason fallbackPath auditTrail

theorem ay_rbmg_source_mismatch_forces_no_claim
    (sourceMismatch fallbackPath auditTrail : Prop) :
    sourceMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim sourceMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim sourceMismatch fallbackPath auditTrail

theorem ay_rbmg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_rbmg_toolchain_mismatch_forces_no_claim
    (toolchainMismatch fallbackPath auditTrail : Prop) :
    toolchainMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim toolchainMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim toolchainMismatch fallbackPath auditTrail

theorem ay_rbmg_binary_mismatch_forces_no_claim
    (binaryMismatch fallbackPath auditTrail : Prop) :
    binaryMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim binaryMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim binaryMismatch fallbackPath auditTrail

theorem ay_rbmg_config_mismatch_forces_no_claim
    (configMismatch fallbackPath auditTrail : Prop) :
    configMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim configMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim configMismatch fallbackPath auditTrail

theorem ay_rbmg_output_mismatch_forces_no_claim
    (outputMismatch fallbackPath auditTrail : Prop) :
    outputMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim outputMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim outputMismatch fallbackPath auditTrail

theorem ay_rbmg_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_rbmg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_rbmg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_rbmg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_rbmg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_rbmg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_rbmg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rbmg_build_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_rbmg_build_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_rbmg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rbmg_build_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_rbmg_build_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
