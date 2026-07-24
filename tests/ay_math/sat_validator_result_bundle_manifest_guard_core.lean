-- SAT-COMP validator result-bundle manifest guard core.
--
-- Public SAT/UNSAT claims are tied to a coherent result bundle rather than
-- loose artifacts. Solver output alone is insufficient: publication requires
-- independent checked evidence for the original benchmark.

def ay_rbmg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rbmg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_rbmg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_rbmg_disj satFact (ay_rbmg_disj unsatFact noClaimFact)

def ay_rbmg_bundle_contract
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint -> solverBinaryDigest -> solverBuildManifest ->
      solverConfigDigest -> solverOutputDigest -> modelProofArtifactDigest ->
      checkerTranscript -> archiveBundleManifest -> environmentManifest ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_rbmg_sat_publication
    (bundleContract coherentBundle independentValidation checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_rbmg_conj bundleContract
    (ay_rbmg_conj coherentBundle
      (ay_rbmg_conj independentValidation
        (ay_rbmg_conj checkedModel originalBenchmarkSat)))

def ay_rbmg_unsat_publication
    (bundleContract coherentBundle independentValidation checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_rbmg_conj bundleContract
    (ay_rbmg_conj coherentBundle
      (ay_rbmg_conj independentValidation
        (ay_rbmg_conj checkedProof originalBenchmarkUnsat)))

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

def ay_rbmg_bundle_failure
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

theorem ay_rbmg_bundle_contract_intro
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    benchmarkFingerprint -> solverBinaryDigest -> solverBuildManifest ->
    solverConfigDigest -> solverOutputDigest -> modelProofArtifactDigest ->
    checkerTranscript -> archiveBundleManifest -> environmentManifest ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript :=
  fun benchmarkProof binaryProof buildProof configProof outputProof
      artifactProof checkerProof archiveProof environmentProof fallbackProof
      auditProof result build =>
    build benchmarkProof binaryProof buildProof configProof outputProof
      artifactProof checkerProof archiveProof environmentProof fallbackProof
      auditProof

theorem ay_rbmg_contract_benchmark
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun benchmarkProof _binaryProof _buildProof _configProof _outputProof
          _artifactProof _checkerProof _archiveProof _environmentProof
          _fallbackProof _auditProof => benchmarkProof)

theorem ay_rbmg_contract_binary
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript ->
    solverBinaryDigest :=
  fun contract =>
    contract solverBinaryDigest
      (fun _benchmarkProof binaryProof _buildProof _configProof _outputProof
          _artifactProof _checkerProof _archiveProof _environmentProof
          _fallbackProof _auditProof => binaryProof)

theorem ay_rbmg_contract_build
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript ->
    solverBuildManifest :=
  fun contract =>
    contract solverBuildManifest
      (fun _benchmarkProof _binaryProof buildProof _configProof _outputProof
          _artifactProof _checkerProof _archiveProof _environmentProof
          _fallbackProof _auditProof => buildProof)

theorem ay_rbmg_contract_config
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript ->
    solverConfigDigest :=
  fun contract =>
    contract solverConfigDigest
      (fun _benchmarkProof _binaryProof _buildProof configProof _outputProof
          _artifactProof _checkerProof _archiveProof _environmentProof
          _fallbackProof _auditProof => configProof)

theorem ay_rbmg_contract_output
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript ->
    solverOutputDigest :=
  fun contract =>
    contract solverOutputDigest
      (fun _benchmarkProof _binaryProof _buildProof _configProof outputProof
          _artifactProof _checkerProof _archiveProof _environmentProof
          _fallbackProof _auditProof => outputProof)

theorem ay_rbmg_contract_artifact
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _benchmarkProof _binaryProof _buildProof _configProof _outputProof
          artifactProof _checkerProof _archiveProof _environmentProof
          _fallbackProof _auditProof => artifactProof)

theorem ay_rbmg_contract_checker
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _benchmarkProof _binaryProof _buildProof _configProof _outputProof
          _artifactProof checkerProof _archiveProof _environmentProof
          _fallbackProof _auditProof => checkerProof)

theorem ay_rbmg_contract_archive
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript ->
    archiveBundleManifest :=
  fun contract =>
    contract archiveBundleManifest
      (fun _benchmarkProof _binaryProof _buildProof _configProof _outputProof
          _artifactProof _checkerProof archiveProof _environmentProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_rbmg_contract_environment
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript ->
    environmentManifest :=
  fun contract =>
    contract environmentManifest
      (fun _benchmarkProof _binaryProof _buildProof _configProof _outputProof
          _artifactProof _checkerProof _archiveProof environmentProof
          _fallbackProof _auditProof => environmentProof)

theorem ay_rbmg_contract_fallback
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _benchmarkProof _binaryProof _buildProof _configProof _outputProof
          _artifactProof _checkerProof _archiveProof _environmentProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_rbmg_contract_audit
    (benchmarkFingerprint solverBinaryDigest solverBuildManifest
      solverConfigDigest solverOutputDigest modelProofArtifactDigest
      checkerTranscript archiveBundleManifest environmentManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_rbmg_bundle_contract benchmarkFingerprint solverBinaryDigest
      solverBuildManifest solverConfigDigest solverOutputDigest
      modelProofArtifactDigest checkerTranscript archiveBundleManifest
      environmentManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _benchmarkProof _binaryProof _buildProof _configProof _outputProof
          _artifactProof _checkerProof _archiveProof _environmentProof
          _fallbackProof auditProof => auditProof)

theorem ay_rbmg_sat_publication_intro
    (bundleContract coherentBundle independentValidation checkedModel
      originalBenchmarkSat : Prop) :
    bundleContract -> coherentBundle -> independentValidation ->
    checkedModel -> originalBenchmarkSat ->
    ay_rbmg_sat_publication bundleContract coherentBundle
      independentValidation checkedModel originalBenchmarkSat :=
  fun hcontract hcoherent hvalidated hchecked horiginal =>
    ay_rbmg_conj_intro bundleContract
      (ay_rbmg_conj coherentBundle
        (ay_rbmg_conj independentValidation
          (ay_rbmg_conj checkedModel originalBenchmarkSat)))
      hcontract
      (ay_rbmg_conj_intro coherentBundle
        (ay_rbmg_conj independentValidation
          (ay_rbmg_conj checkedModel originalBenchmarkSat))
        hcoherent
        (ay_rbmg_conj_intro independentValidation
          (ay_rbmg_conj checkedModel originalBenchmarkSat)
          hvalidated
          (ay_rbmg_conj_intro checkedModel originalBenchmarkSat hchecked
            horiginal)))

theorem ay_rbmg_unsat_publication_intro
    (bundleContract coherentBundle independentValidation checkedProof
      originalBenchmarkUnsat : Prop) :
    bundleContract -> coherentBundle -> independentValidation ->
    checkedProof -> originalBenchmarkUnsat ->
    ay_rbmg_unsat_publication bundleContract coherentBundle
      independentValidation checkedProof originalBenchmarkUnsat :=
  fun hcontract hcoherent hvalidated hchecked horiginal =>
    ay_rbmg_conj_intro bundleContract
      (ay_rbmg_conj coherentBundle
        (ay_rbmg_conj independentValidation
          (ay_rbmg_conj checkedProof originalBenchmarkUnsat)))
      hcontract
      (ay_rbmg_conj_intro coherentBundle
        (ay_rbmg_conj independentValidation
          (ay_rbmg_conj checkedProof originalBenchmarkUnsat))
        hcoherent
        (ay_rbmg_conj_intro independentValidation
          (ay_rbmg_conj checkedProof originalBenchmarkUnsat)
          hvalidated
          (ay_rbmg_conj_intro checkedProof originalBenchmarkUnsat hchecked
            horiginal)))

theorem ay_rbmg_sat_publication_original_claim
    (bundleContract coherentBundle independentValidation checkedModel
      originalBenchmarkSat : Prop) :
    ay_rbmg_sat_publication bundleContract coherentBundle
      independentValidation checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_rbmg_conj_right checkedModel originalBenchmarkSat
      (ay_rbmg_conj_right independentValidation
        (ay_rbmg_conj checkedModel originalBenchmarkSat)
        (ay_rbmg_conj_right coherentBundle
          (ay_rbmg_conj independentValidation
            (ay_rbmg_conj checkedModel originalBenchmarkSat))
          (ay_rbmg_conj_right bundleContract
            (ay_rbmg_conj coherentBundle
              (ay_rbmg_conj independentValidation
                (ay_rbmg_conj checkedModel originalBenchmarkSat)))
            publication)))

theorem ay_rbmg_unsat_publication_original_claim
    (bundleContract coherentBundle independentValidation checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_rbmg_unsat_publication bundleContract coherentBundle
      independentValidation checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_rbmg_conj_right checkedProof originalBenchmarkUnsat
      (ay_rbmg_conj_right independentValidation
        (ay_rbmg_conj checkedProof originalBenchmarkUnsat)
        (ay_rbmg_conj_right coherentBundle
          (ay_rbmg_conj independentValidation
            (ay_rbmg_conj checkedProof originalBenchmarkUnsat))
          (ay_rbmg_conj_right bundleContract
            (ay_rbmg_conj coherentBundle
              (ay_rbmg_conj independentValidation
                (ay_rbmg_conj checkedProof originalBenchmarkUnsat)))
            publication)))

theorem ay_rbmg_accepted_bundle_preserves_sat_soundness
    (bundleContract coherentBundle independentValidation checkedModel
      originalBenchmarkSat : Prop) :
    ay_rbmg_sat_publication bundleContract coherentBundle
      independentValidation checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_rbmg_sat_publication_original_claim bundleContract coherentBundle
    independentValidation checkedModel originalBenchmarkSat

theorem ay_rbmg_accepted_bundle_preserves_unsat_soundness
    (bundleContract coherentBundle independentValidation checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_rbmg_unsat_publication bundleContract coherentBundle
      independentValidation checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_rbmg_unsat_publication_original_claim bundleContract coherentBundle
    independentValidation checkedProof originalBenchmarkUnsat

theorem ay_rbmg_solver_output_alone_cannot_publish_sat
    (satFact unsatFact solverOutputOnly : Prop) :
    ay_rbmg_blocked_publication satFact unsatFact solverOutputOnly ->
    satFact -> False :=
  fun blocked =>
    ay_rbmg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_rbmg_conj_right solverOutputOnly
        (ay_rbmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rbmg_solver_output_alone_cannot_publish_unsat
    (satFact unsatFact solverOutputOnly : Prop) :
    ay_rbmg_blocked_publication satFact unsatFact solverOutputOnly ->
    unsatFact -> False :=
  fun blocked =>
    ay_rbmg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_rbmg_conj_right solverOutputOnly
        (ay_rbmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

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

theorem ay_rbmg_bundle_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rbmg_blocked_publication satFact unsatFact reason ->
    ay_rbmg_recompute reason fallbackPath recomputeObligation ->
    ay_rbmg_bundle_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_rbmg_conj_intro
      (ay_rbmg_blocked_publication satFact unsatFact reason)
      (ay_rbmg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_rbmg_bundle_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rbmg_bundle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_rbmg_blocked_publication_no_sat satFact unsatFact reason
      (ay_rbmg_conj_left
        (ay_rbmg_blocked_publication satFact unsatFact reason)
        (ay_rbmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rbmg_bundle_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rbmg_bundle_failure satFact unsatFact reason fallbackPath
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

theorem ay_rbmg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_rbmg_config_mismatch_forces_no_claim
    (configMismatch fallbackPath auditTrail : Prop) :
    configMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim configMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim configMismatch fallbackPath auditTrail

theorem ay_rbmg_environment_mismatch_forces_no_claim
    (environmentMismatch fallbackPath auditTrail : Prop) :
    environmentMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim environmentMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim environmentMismatch fallbackPath auditTrail

theorem ay_rbmg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_rbmg_stale_bundle_forces_no_claim
    (staleBundle fallbackPath auditTrail : Prop) :
    staleBundle -> fallbackPath -> auditTrail ->
    ay_rbmg_no_claim staleBundle fallbackPath auditTrail :=
  ay_rbmg_mismatch_forces_no_claim staleBundle fallbackPath auditTrail

theorem ay_rbmg_partial_bundle_forces_recompute
    (partialBundle fallbackPath recomputeObligation : Prop) :
    partialBundle -> fallbackPath -> recomputeObligation ->
    ay_rbmg_recompute partialBundle fallbackPath recomputeObligation :=
  ay_rbmg_recompute_intro partialBundle fallbackPath recomputeObligation

theorem ay_rbmg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_rbmg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_rbmg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_rbmg_stale_bundle_cannot_bless_sat
    (satFact unsatFact staleBundle : Prop) :
    ay_rbmg_blocked_publication satFact unsatFact staleBundle ->
    satFact -> False :=
  ay_rbmg_blocked_publication_no_sat satFact unsatFact staleBundle

theorem ay_rbmg_stale_bundle_cannot_bless_unsat
    (satFact unsatFact staleBundle : Prop) :
    ay_rbmg_blocked_publication satFact unsatFact staleBundle ->
    unsatFact -> False :=
  ay_rbmg_blocked_publication_no_unsat satFact unsatFact staleBundle

theorem ay_rbmg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rbmg_bundle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_rbmg_bundle_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_rbmg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rbmg_bundle_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_rbmg_bundle_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
