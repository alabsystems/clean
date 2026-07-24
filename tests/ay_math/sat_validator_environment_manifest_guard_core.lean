-- SAT-COMP validator execution-environment manifest guard core.
--
-- Public SAT/UNSAT claims are tied to the intended environment, runtime,
-- binary, configuration, benchmark, output, artifact, checker, archive,
-- fallback, and audit evidence.

def ay_envg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_envg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_envg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_envg_disj satFact (ay_envg_disj unsatFact noClaimFact)

def ay_envg_environment_contract
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (environmentManifest -> osRuntimeDigest -> solverBinaryDigest ->
      solverConfigurationDigest -> benchmarkFingerprint -> solverOutputDigest ->
      modelProofArtifactDigest -> checkerTranscript -> archiveManifest ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_envg_sat_publication
    (environmentContract environmentConfigEvidence checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_envg_conj environmentContract
    (ay_envg_conj environmentConfigEvidence
      (ay_envg_conj checkedModel originalBenchmarkSat))

def ay_envg_unsat_publication
    (environmentContract environmentConfigEvidence checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_envg_conj environmentContract
    (ay_envg_conj environmentConfigEvidence
      (ay_envg_conj checkedProof originalBenchmarkUnsat))

def ay_envg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_envg_conj reason (ay_envg_conj fallbackPath auditTrail)

def ay_envg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_envg_conj reason
    (ay_envg_conj (satFact -> False) (unsatFact -> False))

def ay_envg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_envg_conj reason
    (ay_envg_conj fallbackPath recomputeObligation)

def ay_envg_environment_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_envg_conj
    (ay_envg_blocked_publication satFact unsatFact reason)
    (ay_envg_recompute reason fallbackPath recomputeObligation)

theorem ay_envg_conj_intro (left right : Prop) :
    left -> right -> ay_envg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_envg_conj_left (left right : Prop) :
    ay_envg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_envg_conj_right (left right : Prop) :
    ay_envg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_envg_disj_left (left right : Prop) :
    left -> ay_envg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_envg_disj_right (left right : Prop) :
    right -> ay_envg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_envg_environment_contract_intro
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    environmentManifest -> osRuntimeDigest -> solverBinaryDigest ->
    solverConfigurationDigest -> benchmarkFingerprint -> solverOutputDigest ->
    modelProofArtifactDigest -> checkerTranscript -> archiveManifest ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript :=
  fun environmentProof runtimeProof binaryProof configProof benchmarkProof
      outputProof artifactProof checkerProof archiveProof fallbackProof
      auditProof result build =>
    build environmentProof runtimeProof binaryProof configProof benchmarkProof
      outputProof artifactProof checkerProof archiveProof fallbackProof
      auditProof

theorem ay_envg_contract_environment
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    environmentManifest :=
  fun contract =>
    contract environmentManifest
      (fun environmentProof _runtimeProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => environmentProof)

theorem ay_envg_contract_runtime
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    osRuntimeDigest :=
  fun contract =>
    contract osRuntimeDigest
      (fun _environmentProof runtimeProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => runtimeProof)

theorem ay_envg_contract_binary
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBinaryDigest :=
  fun contract =>
    contract solverBinaryDigest
      (fun _environmentProof _runtimeProof binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => binaryProof)

theorem ay_envg_contract_config
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverConfigurationDigest :=
  fun contract =>
    contract solverConfigurationDigest
      (fun _environmentProof _runtimeProof _binaryProof configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => configProof)

theorem ay_envg_contract_benchmark
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _environmentProof _runtimeProof _binaryProof _configProof
          benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => benchmarkProof)

theorem ay_envg_contract_output
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverOutputDigest :=
  fun contract =>
    contract solverOutputDigest
      (fun _environmentProof _runtimeProof _binaryProof _configProof
          _benchmarkProof outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => outputProof)

theorem ay_envg_contract_artifact
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _environmentProof _runtimeProof _binaryProof _configProof
          _benchmarkProof _outputProof artifactProof _checkerProof
          _archiveProof _fallbackProof _auditProof => artifactProof)

theorem ay_envg_contract_checker
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _environmentProof _runtimeProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof checkerProof
          _archiveProof _fallbackProof _auditProof => checkerProof)

theorem ay_envg_contract_archive
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _environmentProof _runtimeProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          archiveProof _fallbackProof _auditProof => archiveProof)

theorem ay_envg_contract_fallback
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _environmentProof _runtimeProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof fallbackProof _auditProof => fallbackProof)

theorem ay_envg_contract_audit
    (environmentManifest osRuntimeDigest solverBinaryDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_envg_environment_contract environmentManifest osRuntimeDigest
      solverBinaryDigest solverConfigurationDigest benchmarkFingerprint
      solverOutputDigest modelProofArtifactDigest checkerTranscript
      archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _environmentProof _runtimeProof _binaryProof _configProof
          _benchmarkProof _outputProof _artifactProof _checkerProof
          _archiveProof _fallbackProof auditProof => auditProof)

theorem ay_envg_sat_publication_intro
    (environmentContract environmentConfigEvidence checkedModel
      originalBenchmarkSat : Prop) :
    environmentContract -> environmentConfigEvidence -> checkedModel ->
    originalBenchmarkSat ->
    ay_envg_sat_publication environmentContract environmentConfigEvidence
      checkedModel originalBenchmarkSat :=
  fun hcontract hevidence hchecked horiginal =>
    ay_envg_conj_intro environmentContract
      (ay_envg_conj environmentConfigEvidence
        (ay_envg_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_envg_conj_intro environmentConfigEvidence
        (ay_envg_conj checkedModel originalBenchmarkSat)
        hevidence
        (ay_envg_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_envg_unsat_publication_intro
    (environmentContract environmentConfigEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    environmentContract -> environmentConfigEvidence -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_envg_unsat_publication environmentContract environmentConfigEvidence
      checkedProof originalBenchmarkUnsat :=
  fun hcontract hevidence hchecked horiginal =>
    ay_envg_conj_intro environmentContract
      (ay_envg_conj environmentConfigEvidence
        (ay_envg_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_envg_conj_intro environmentConfigEvidence
        (ay_envg_conj checkedProof originalBenchmarkUnsat)
        hevidence
        (ay_envg_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_envg_sat_publication_original_claim
    (environmentContract environmentConfigEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_envg_sat_publication environmentContract environmentConfigEvidence
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_envg_conj_right checkedModel originalBenchmarkSat
      (ay_envg_conj_right environmentConfigEvidence
        (ay_envg_conj checkedModel originalBenchmarkSat)
        (ay_envg_conj_right environmentContract
          (ay_envg_conj environmentConfigEvidence
            (ay_envg_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_envg_unsat_publication_original_claim
    (environmentContract environmentConfigEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_envg_unsat_publication environmentContract environmentConfigEvidence
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_envg_conj_right checkedProof originalBenchmarkUnsat
      (ay_envg_conj_right environmentConfigEvidence
        (ay_envg_conj checkedProof originalBenchmarkUnsat)
        (ay_envg_conj_right environmentContract
          (ay_envg_conj environmentConfigEvidence
            (ay_envg_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_envg_accepted_environment_preserves_sat_soundness
    (environmentContract environmentConfigEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_envg_sat_publication environmentContract environmentConfigEvidence
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_envg_sat_publication_original_claim environmentContract
    environmentConfigEvidence checkedModel originalBenchmarkSat

theorem ay_envg_accepted_environment_preserves_unsat_soundness
    (environmentContract environmentConfigEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_envg_unsat_publication environmentContract environmentConfigEvidence
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_envg_unsat_publication_original_claim environmentContract
    environmentConfigEvidence checkedProof originalBenchmarkUnsat

theorem ay_envg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_envg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_envg_conj_intro reason (ay_envg_conj fallbackPath auditTrail)
      hreason
      (ay_envg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_envg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_envg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_envg_conj_intro reason
      (ay_envg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_envg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_envg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_envg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_envg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_envg_conj_right reason
        (ay_envg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_envg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_envg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_envg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_envg_conj_right reason
        (ay_envg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_envg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_envg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_envg_conj_intro reason
      (ay_envg_conj fallbackPath recomputeObligation)
      hreason
      (ay_envg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_envg_environment_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_envg_blocked_publication satFact unsatFact reason ->
    ay_envg_recompute reason fallbackPath recomputeObligation ->
    ay_envg_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_envg_conj_intro
      (ay_envg_blocked_publication satFact unsatFact reason)
      (ay_envg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_envg_environment_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_envg_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_envg_blocked_publication_no_sat satFact unsatFact reason
      (ay_envg_conj_left
        (ay_envg_blocked_publication satFact unsatFact reason)
        (ay_envg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_envg_environment_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_envg_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_envg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_envg_conj_left
        (ay_envg_blocked_publication satFact unsatFact reason)
        (ay_envg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_envg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_envg_no_claim reason fallbackPath auditTrail :=
  ay_envg_no_claim_intro reason fallbackPath auditTrail

theorem ay_envg_environment_mismatch_forces_no_claim
    (environmentMismatch fallbackPath auditTrail : Prop) :
    environmentMismatch -> fallbackPath -> auditTrail ->
    ay_envg_no_claim environmentMismatch fallbackPath auditTrail :=
  ay_envg_mismatch_forces_no_claim environmentMismatch fallbackPath auditTrail

theorem ay_envg_runtime_mismatch_forces_no_claim
    (runtimeMismatch fallbackPath auditTrail : Prop) :
    runtimeMismatch -> fallbackPath -> auditTrail ->
    ay_envg_no_claim runtimeMismatch fallbackPath auditTrail :=
  ay_envg_mismatch_forces_no_claim runtimeMismatch fallbackPath auditTrail

theorem ay_envg_binary_mismatch_forces_no_claim
    (binaryMismatch fallbackPath auditTrail : Prop) :
    binaryMismatch -> fallbackPath -> auditTrail ->
    ay_envg_no_claim binaryMismatch fallbackPath auditTrail :=
  ay_envg_mismatch_forces_no_claim binaryMismatch fallbackPath auditTrail

theorem ay_envg_config_mismatch_forces_no_claim
    (configMismatch fallbackPath auditTrail : Prop) :
    configMismatch -> fallbackPath -> auditTrail ->
    ay_envg_no_claim configMismatch fallbackPath auditTrail :=
  ay_envg_mismatch_forces_no_claim configMismatch fallbackPath auditTrail

theorem ay_envg_output_mismatch_forces_no_claim
    (outputMismatch fallbackPath auditTrail : Prop) :
    outputMismatch -> fallbackPath -> auditTrail ->
    ay_envg_no_claim outputMismatch fallbackPath auditTrail :=
  ay_envg_mismatch_forces_no_claim outputMismatch fallbackPath auditTrail

theorem ay_envg_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_envg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_envg_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_envg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_envg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_envg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_envg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_envg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_envg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_envg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_envg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_envg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_envg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_envg_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_envg_environment_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_envg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_envg_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_envg_environment_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation
