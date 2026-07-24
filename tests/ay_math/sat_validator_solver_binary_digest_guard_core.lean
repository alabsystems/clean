-- SAT-COMP validator solver-binary digest guard core.
--
-- Public SAT/UNSAT claims are tied to the intended ay binary, build manifest,
-- solver configuration, benchmark, output, artifact, checker, archive,
-- fallback, and audit evidence.

def ay_sbdg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_sbdg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_sbdg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_sbdg_disj satFact (ay_sbdg_disj unsatFact noClaimFact)

def ay_sbdg_binary_contract
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (solverBinaryDigest -> solverBuildManifest -> solverConfigurationDigest ->
      benchmarkFingerprint -> solverOutputDigest -> modelProofArtifactDigest ->
      checkerTranscript -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_sbdg_sat_publication
    (binaryContract binaryBuildConfigMatch checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_sbdg_conj binaryContract
    (ay_sbdg_conj binaryBuildConfigMatch
      (ay_sbdg_conj checkedModel originalBenchmarkSat))

def ay_sbdg_unsat_publication
    (binaryContract binaryBuildConfigMatch checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_sbdg_conj binaryContract
    (ay_sbdg_conj binaryBuildConfigMatch
      (ay_sbdg_conj checkedProof originalBenchmarkUnsat))

def ay_sbdg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_sbdg_conj reason (ay_sbdg_conj fallbackPath auditTrail)

def ay_sbdg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_sbdg_conj reason
    (ay_sbdg_conj (satFact -> False) (unsatFact -> False))

def ay_sbdg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_sbdg_conj reason
    (ay_sbdg_conj fallbackPath recomputeObligation)

def ay_sbdg_binary_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_sbdg_conj
    (ay_sbdg_blocked_publication satFact unsatFact reason)
    (ay_sbdg_recompute reason fallbackPath recomputeObligation)

theorem ay_sbdg_conj_intro (left right : Prop) :
    left -> right -> ay_sbdg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_sbdg_conj_left (left right : Prop) :
    ay_sbdg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_sbdg_conj_right (left right : Prop) :
    ay_sbdg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_sbdg_disj_left (left right : Prop) :
    left -> ay_sbdg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_sbdg_disj_right (left right : Prop) :
    right -> ay_sbdg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_sbdg_binary_contract_intro
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    solverBinaryDigest -> solverBuildManifest -> solverConfigurationDigest ->
    benchmarkFingerprint -> solverOutputDigest -> modelProofArtifactDigest ->
    checkerTranscript -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_sbdg_binary_contract solverBinaryDigest solverBuildManifest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript :=
  fun binaryProof buildProof configProof benchmarkProof outputProof
      artifactProof checkerProof archiveProof fallbackProof auditProof result
      build =>
    build binaryProof buildProof configProof benchmarkProof outputProof
      artifactProof checkerProof archiveProof fallbackProof auditProof

theorem ay_sbdg_contract_binary
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_sbdg_binary_contract solverBinaryDigest solverBuildManifest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBinaryDigest :=
  fun contract =>
    contract solverBinaryDigest
      (fun binaryProof _buildProof _configProof _benchmarkProof _outputProof
          _artifactProof _checkerProof _archiveProof _fallbackProof
          _auditProof => binaryProof)

theorem ay_sbdg_contract_build
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_sbdg_binary_contract solverBinaryDigest solverBuildManifest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBuildManifest :=
  fun contract =>
    contract solverBuildManifest
      (fun _binaryProof buildProof _configProof _benchmarkProof _outputProof
          _artifactProof _checkerProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_sbdg_contract_config
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_sbdg_binary_contract solverBinaryDigest solverBuildManifest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverConfigurationDigest :=
  fun contract =>
    contract solverConfigurationDigest
      (fun _binaryProof _buildProof configProof _benchmarkProof _outputProof
          _artifactProof _checkerProof _archiveProof _fallbackProof
          _auditProof => configProof)

theorem ay_sbdg_contract_benchmark
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_sbdg_binary_contract solverBinaryDigest solverBuildManifest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _binaryProof _buildProof _configProof benchmarkProof _outputProof
          _artifactProof _checkerProof _archiveProof _fallbackProof
          _auditProof => benchmarkProof)

theorem ay_sbdg_contract_output
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_sbdg_binary_contract solverBinaryDigest solverBuildManifest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverOutputDigest :=
  fun contract =>
    contract solverOutputDigest
      (fun _binaryProof _buildProof _configProof _benchmarkProof outputProof
          _artifactProof _checkerProof _archiveProof _fallbackProof
          _auditProof => outputProof)

theorem ay_sbdg_contract_artifact
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_sbdg_binary_contract solverBinaryDigest solverBuildManifest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _binaryProof _buildProof _configProof _benchmarkProof _outputProof
          artifactProof _checkerProof _archiveProof _fallbackProof
          _auditProof => artifactProof)

theorem ay_sbdg_contract_checker
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_sbdg_binary_contract solverBinaryDigest solverBuildManifest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _binaryProof _buildProof _configProof _benchmarkProof _outputProof
          _artifactProof checkerProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_sbdg_contract_archive
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_sbdg_binary_contract solverBinaryDigest solverBuildManifest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _binaryProof _buildProof _configProof _benchmarkProof _outputProof
          _artifactProof _checkerProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_sbdg_contract_fallback
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_sbdg_binary_contract solverBinaryDigest solverBuildManifest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _binaryProof _buildProof _configProof _benchmarkProof _outputProof
          _artifactProof _checkerProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_sbdg_contract_audit
    (solverBinaryDigest solverBuildManifest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_sbdg_binary_contract solverBinaryDigest solverBuildManifest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _binaryProof _buildProof _configProof _benchmarkProof _outputProof
          _artifactProof _checkerProof _archiveProof _fallbackProof auditProof =>
        auditProof)

theorem ay_sbdg_sat_publication_intro
    (binaryContract binaryBuildConfigMatch checkedModel
      originalBenchmarkSat : Prop) :
    binaryContract -> binaryBuildConfigMatch -> checkedModel ->
    originalBenchmarkSat ->
    ay_sbdg_sat_publication binaryContract binaryBuildConfigMatch
      checkedModel originalBenchmarkSat :=
  fun hcontract hmatch hchecked horiginal =>
    ay_sbdg_conj_intro binaryContract
      (ay_sbdg_conj binaryBuildConfigMatch
        (ay_sbdg_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_sbdg_conj_intro binaryBuildConfigMatch
        (ay_sbdg_conj checkedModel originalBenchmarkSat)
        hmatch
        (ay_sbdg_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_sbdg_unsat_publication_intro
    (binaryContract binaryBuildConfigMatch checkedProof
      originalBenchmarkUnsat : Prop) :
    binaryContract -> binaryBuildConfigMatch -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_sbdg_unsat_publication binaryContract binaryBuildConfigMatch
      checkedProof originalBenchmarkUnsat :=
  fun hcontract hmatch hchecked horiginal =>
    ay_sbdg_conj_intro binaryContract
      (ay_sbdg_conj binaryBuildConfigMatch
        (ay_sbdg_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_sbdg_conj_intro binaryBuildConfigMatch
        (ay_sbdg_conj checkedProof originalBenchmarkUnsat)
        hmatch
        (ay_sbdg_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_sbdg_sat_publication_original_claim
    (binaryContract binaryBuildConfigMatch checkedModel
      originalBenchmarkSat : Prop) :
    ay_sbdg_sat_publication binaryContract binaryBuildConfigMatch
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_sbdg_conj_right checkedModel originalBenchmarkSat
      (ay_sbdg_conj_right binaryBuildConfigMatch
        (ay_sbdg_conj checkedModel originalBenchmarkSat)
        (ay_sbdg_conj_right binaryContract
          (ay_sbdg_conj binaryBuildConfigMatch
            (ay_sbdg_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_sbdg_unsat_publication_original_claim
    (binaryContract binaryBuildConfigMatch checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_sbdg_unsat_publication binaryContract binaryBuildConfigMatch
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_sbdg_conj_right checkedProof originalBenchmarkUnsat
      (ay_sbdg_conj_right binaryBuildConfigMatch
        (ay_sbdg_conj checkedProof originalBenchmarkUnsat)
        (ay_sbdg_conj_right binaryContract
          (ay_sbdg_conj binaryBuildConfigMatch
            (ay_sbdg_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_sbdg_accepted_binary_preserves_sat_soundness
    (binaryContract binaryBuildConfigMatch checkedModel
      originalBenchmarkSat : Prop) :
    ay_sbdg_sat_publication binaryContract binaryBuildConfigMatch
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_sbdg_sat_publication_original_claim binaryContract binaryBuildConfigMatch
    checkedModel originalBenchmarkSat

theorem ay_sbdg_accepted_binary_preserves_unsat_soundness
    (binaryContract binaryBuildConfigMatch checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_sbdg_unsat_publication binaryContract binaryBuildConfigMatch
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_sbdg_unsat_publication_original_claim binaryContract
    binaryBuildConfigMatch checkedProof originalBenchmarkUnsat

theorem ay_sbdg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_sbdg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_sbdg_conj_intro reason (ay_sbdg_conj fallbackPath auditTrail)
      hreason
      (ay_sbdg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_sbdg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_sbdg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_sbdg_conj_intro reason
      (ay_sbdg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_sbdg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_sbdg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_sbdg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_sbdg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_sbdg_conj_right reason
        (ay_sbdg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_sbdg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_sbdg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_sbdg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_sbdg_conj_right reason
        (ay_sbdg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_sbdg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_sbdg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_sbdg_conj_intro reason
      (ay_sbdg_conj fallbackPath recomputeObligation)
      hreason
      (ay_sbdg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_sbdg_binary_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sbdg_blocked_publication satFact unsatFact reason ->
    ay_sbdg_recompute reason fallbackPath recomputeObligation ->
    ay_sbdg_binary_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_sbdg_conj_intro
      (ay_sbdg_blocked_publication satFact unsatFact reason)
      (ay_sbdg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_sbdg_binary_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sbdg_binary_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_sbdg_blocked_publication_no_sat satFact unsatFact reason
      (ay_sbdg_conj_left
        (ay_sbdg_blocked_publication satFact unsatFact reason)
        (ay_sbdg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_sbdg_binary_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sbdg_binary_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_sbdg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_sbdg_conj_left
        (ay_sbdg_blocked_publication satFact unsatFact reason)
        (ay_sbdg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_sbdg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_sbdg_no_claim reason fallbackPath auditTrail :=
  ay_sbdg_no_claim_intro reason fallbackPath auditTrail

theorem ay_sbdg_binary_mismatch_forces_no_claim
    (binaryMismatch fallbackPath auditTrail : Prop) :
    binaryMismatch -> fallbackPath -> auditTrail ->
    ay_sbdg_no_claim binaryMismatch fallbackPath auditTrail :=
  ay_sbdg_mismatch_forces_no_claim binaryMismatch fallbackPath auditTrail

theorem ay_sbdg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_sbdg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_sbdg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_sbdg_config_mismatch_forces_no_claim
    (configMismatch fallbackPath auditTrail : Prop) :
    configMismatch -> fallbackPath -> auditTrail ->
    ay_sbdg_no_claim configMismatch fallbackPath auditTrail :=
  ay_sbdg_mismatch_forces_no_claim configMismatch fallbackPath auditTrail

theorem ay_sbdg_output_mismatch_forces_no_claim
    (outputMismatch fallbackPath auditTrail : Prop) :
    outputMismatch -> fallbackPath -> auditTrail ->
    ay_sbdg_no_claim outputMismatch fallbackPath auditTrail :=
  ay_sbdg_mismatch_forces_no_claim outputMismatch fallbackPath auditTrail

theorem ay_sbdg_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_sbdg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_sbdg_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_sbdg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_sbdg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_sbdg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_sbdg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_sbdg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_sbdg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_sbdg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_sbdg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_sbdg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_sbdg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sbdg_binary_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_sbdg_binary_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_sbdg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sbdg_binary_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_sbdg_binary_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
