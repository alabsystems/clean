-- SAT-COMP validator incremental checker-cache guard core.
--
-- Cached checker results may accelerate validation only when the cache key and
-- all benchmark, artifact, build, checker, environment, archive, gate, and
-- audit evidence agree. A cache hit by itself cannot publish SAT/UNSAT.

def ay_iccg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_iccg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_iccg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_iccg_disj satFact (ay_iccg_disj unsatFact noClaimFact)

def ay_iccg_cache_contract
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint -> originalCnfDigest ->
      solverBinaryBuildConfigDigest -> checkerVersionDigest ->
      checkerInputArtifactDigest -> cachedResultDigest ->
      cacheKeyDerivationWitness -> cacheHitTranscript ->
      freshCheckFallbackPath -> environmentManifest -> archiveManifest ->
      validatorGate -> auditTranscript -> result) ->
    result

def ay_iccg_sat_publication
    (cacheContract exactCacheGuard independentValidation checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_iccg_conj cacheContract
    (ay_iccg_conj exactCacheGuard
      (ay_iccg_conj independentValidation
        (ay_iccg_conj checkedModel originalBenchmarkSat)))

def ay_iccg_unsat_publication
    (cacheContract exactCacheGuard independentValidation checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_iccg_conj cacheContract
    (ay_iccg_conj exactCacheGuard
      (ay_iccg_conj independentValidation
        (ay_iccg_conj checkedProof originalBenchmarkUnsat)))

def ay_iccg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_iccg_conj reason (ay_iccg_conj fallbackPath auditTrail)

def ay_iccg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_iccg_conj reason
    (ay_iccg_conj (satFact -> False) (unsatFact -> False))

def ay_iccg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_iccg_conj reason
    (ay_iccg_conj fallbackPath recomputeObligation)

def ay_iccg_cache_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_iccg_conj
    (ay_iccg_blocked_publication satFact unsatFact reason)
    (ay_iccg_recompute reason fallbackPath recomputeObligation)

theorem ay_iccg_conj_intro (left right : Prop) :
    left -> right -> ay_iccg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_iccg_conj_left (left right : Prop) :
    ay_iccg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_iccg_conj_right (left right : Prop) :
    ay_iccg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_iccg_disj_left (left right : Prop) :
    left -> ay_iccg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_iccg_disj_right (left right : Prop) :
    right -> ay_iccg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_iccg_cache_contract_intro
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    benchmarkFingerprint -> originalCnfDigest ->
    solverBinaryBuildConfigDigest -> checkerVersionDigest ->
    checkerInputArtifactDigest -> cachedResultDigest ->
    cacheKeyDerivationWitness -> cacheHitTranscript ->
    freshCheckFallbackPath -> environmentManifest -> archiveManifest ->
    validatorGate -> auditTranscript ->
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript :=
  fun benchmarkProof cnfProof buildProof checkerVersionProof artifactProof
      cachedProof keyProof hitProof fallbackProof environmentProof archiveProof
      gateProof auditProof result build =>
    build benchmarkProof cnfProof buildProof checkerVersionProof artifactProof
      cachedProof keyProof hitProof fallbackProof environmentProof archiveProof
      gateProof auditProof

theorem ay_iccg_contract_benchmark
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun benchmarkProof _cnfProof _buildProof _checkerVersionProof
          _artifactProof _cachedProof _keyProof _hitProof _fallbackProof
          _environmentProof _archiveProof _gateProof _auditProof =>
        benchmarkProof)

theorem ay_iccg_contract_original_cnf
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    originalCnfDigest :=
  fun contract =>
    contract originalCnfDigest
      (fun _benchmarkProof cnfProof _buildProof _checkerVersionProof
          _artifactProof _cachedProof _keyProof _hitProof _fallbackProof
          _environmentProof _archiveProof _gateProof _auditProof => cnfProof)

theorem ay_iccg_contract_solver_build_config
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    solverBinaryBuildConfigDigest :=
  fun contract =>
    contract solverBinaryBuildConfigDigest
      (fun _benchmarkProof _cnfProof buildProof _checkerVersionProof
          _artifactProof _cachedProof _keyProof _hitProof _fallbackProof
          _environmentProof _archiveProof _gateProof _auditProof => buildProof)

theorem ay_iccg_contract_checker_version
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    checkerVersionDigest :=
  fun contract =>
    contract checkerVersionDigest
      (fun _benchmarkProof _cnfProof _buildProof checkerVersionProof
          _artifactProof _cachedProof _keyProof _hitProof _fallbackProof
          _environmentProof _archiveProof _gateProof _auditProof =>
        checkerVersionProof)

theorem ay_iccg_contract_checker_input_artifact
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    checkerInputArtifactDigest :=
  fun contract =>
    contract checkerInputArtifactDigest
      (fun _benchmarkProof _cnfProof _buildProof _checkerVersionProof
          artifactProof _cachedProof _keyProof _hitProof _fallbackProof
          _environmentProof _archiveProof _gateProof _auditProof =>
        artifactProof)

theorem ay_iccg_contract_cached_result
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    cachedResultDigest :=
  fun contract =>
    contract cachedResultDigest
      (fun _benchmarkProof _cnfProof _buildProof _checkerVersionProof
          _artifactProof cachedProof _keyProof _hitProof _fallbackProof
          _environmentProof _archiveProof _gateProof _auditProof => cachedProof)

theorem ay_iccg_contract_cache_key
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    cacheKeyDerivationWitness :=
  fun contract =>
    contract cacheKeyDerivationWitness
      (fun _benchmarkProof _cnfProof _buildProof _checkerVersionProof
          _artifactProof _cachedProof keyProof _hitProof _fallbackProof
          _environmentProof _archiveProof _gateProof _auditProof => keyProof)

theorem ay_iccg_contract_cache_hit
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    cacheHitTranscript :=
  fun contract =>
    contract cacheHitTranscript
      (fun _benchmarkProof _cnfProof _buildProof _checkerVersionProof
          _artifactProof _cachedProof _keyProof hitProof _fallbackProof
          _environmentProof _archiveProof _gateProof _auditProof => hitProof)

theorem ay_iccg_contract_fresh_fallback
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    freshCheckFallbackPath :=
  fun contract =>
    contract freshCheckFallbackPath
      (fun _benchmarkProof _cnfProof _buildProof _checkerVersionProof
          _artifactProof _cachedProof _keyProof _hitProof fallbackProof
          _environmentProof _archiveProof _gateProof _auditProof =>
        fallbackProof)

theorem ay_iccg_contract_environment
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    environmentManifest :=
  fun contract =>
    contract environmentManifest
      (fun _benchmarkProof _cnfProof _buildProof _checkerVersionProof
          _artifactProof _cachedProof _keyProof _hitProof _fallbackProof
          environmentProof _archiveProof _gateProof _auditProof =>
        environmentProof)

theorem ay_iccg_contract_archive
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _benchmarkProof _cnfProof _buildProof _checkerVersionProof
          _artifactProof _cachedProof _keyProof _hitProof _fallbackProof
          _environmentProof archiveProof _gateProof _auditProof =>
        archiveProof)

theorem ay_iccg_contract_validator_gate
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    validatorGate :=
  fun contract =>
    contract validatorGate
      (fun _benchmarkProof _cnfProof _buildProof _checkerVersionProof
          _artifactProof _cachedProof _keyProof _hitProof _fallbackProof
          _environmentProof _archiveProof gateProof _auditProof => gateProof)

theorem ay_iccg_contract_audit
    (benchmarkFingerprint originalCnfDigest solverBinaryBuildConfigDigest
      checkerVersionDigest checkerInputArtifactDigest cachedResultDigest
      cacheKeyDerivationWitness cacheHitTranscript freshCheckFallbackPath
      environmentManifest archiveManifest validatorGate
      auditTranscript : Prop) :
    ay_iccg_cache_contract benchmarkFingerprint originalCnfDigest
      solverBinaryBuildConfigDigest checkerVersionDigest
      checkerInputArtifactDigest cachedResultDigest cacheKeyDerivationWitness
      cacheHitTranscript freshCheckFallbackPath environmentManifest
      archiveManifest validatorGate auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _benchmarkProof _cnfProof _buildProof _checkerVersionProof
          _artifactProof _cachedProof _keyProof _hitProof _fallbackProof
          _environmentProof _archiveProof _gateProof auditProof => auditProof)

theorem ay_iccg_sat_publication_intro
    (cacheContract exactCacheGuard independentValidation checkedModel
      originalBenchmarkSat : Prop) :
    cacheContract -> exactCacheGuard -> independentValidation ->
    checkedModel -> originalBenchmarkSat ->
    ay_iccg_sat_publication cacheContract exactCacheGuard
      independentValidation checkedModel originalBenchmarkSat :=
  fun hcontract hguard hvalidated hchecked horiginal =>
    ay_iccg_conj_intro cacheContract
      (ay_iccg_conj exactCacheGuard
        (ay_iccg_conj independentValidation
          (ay_iccg_conj checkedModel originalBenchmarkSat)))
      hcontract
      (ay_iccg_conj_intro exactCacheGuard
        (ay_iccg_conj independentValidation
          (ay_iccg_conj checkedModel originalBenchmarkSat))
        hguard
        (ay_iccg_conj_intro independentValidation
          (ay_iccg_conj checkedModel originalBenchmarkSat)
          hvalidated
          (ay_iccg_conj_intro checkedModel originalBenchmarkSat hchecked
            horiginal)))

theorem ay_iccg_unsat_publication_intro
    (cacheContract exactCacheGuard independentValidation checkedProof
      originalBenchmarkUnsat : Prop) :
    cacheContract -> exactCacheGuard -> independentValidation ->
    checkedProof -> originalBenchmarkUnsat ->
    ay_iccg_unsat_publication cacheContract exactCacheGuard
      independentValidation checkedProof originalBenchmarkUnsat :=
  fun hcontract hguard hvalidated hchecked horiginal =>
    ay_iccg_conj_intro cacheContract
      (ay_iccg_conj exactCacheGuard
        (ay_iccg_conj independentValidation
          (ay_iccg_conj checkedProof originalBenchmarkUnsat)))
      hcontract
      (ay_iccg_conj_intro exactCacheGuard
        (ay_iccg_conj independentValidation
          (ay_iccg_conj checkedProof originalBenchmarkUnsat))
        hguard
        (ay_iccg_conj_intro independentValidation
          (ay_iccg_conj checkedProof originalBenchmarkUnsat)
          hvalidated
          (ay_iccg_conj_intro checkedProof originalBenchmarkUnsat hchecked
            horiginal)))

theorem ay_iccg_sat_publication_original_claim
    (cacheContract exactCacheGuard independentValidation checkedModel
      originalBenchmarkSat : Prop) :
    ay_iccg_sat_publication cacheContract exactCacheGuard
      independentValidation checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_iccg_conj_right checkedModel originalBenchmarkSat
      (ay_iccg_conj_right independentValidation
        (ay_iccg_conj checkedModel originalBenchmarkSat)
        (ay_iccg_conj_right exactCacheGuard
          (ay_iccg_conj independentValidation
            (ay_iccg_conj checkedModel originalBenchmarkSat))
          (ay_iccg_conj_right cacheContract
            (ay_iccg_conj exactCacheGuard
              (ay_iccg_conj independentValidation
                (ay_iccg_conj checkedModel originalBenchmarkSat)))
            publication)))

theorem ay_iccg_unsat_publication_original_claim
    (cacheContract exactCacheGuard independentValidation checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_iccg_unsat_publication cacheContract exactCacheGuard
      independentValidation checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_iccg_conj_right checkedProof originalBenchmarkUnsat
      (ay_iccg_conj_right independentValidation
        (ay_iccg_conj checkedProof originalBenchmarkUnsat)
        (ay_iccg_conj_right exactCacheGuard
          (ay_iccg_conj independentValidation
            (ay_iccg_conj checkedProof originalBenchmarkUnsat))
          (ay_iccg_conj_right cacheContract
            (ay_iccg_conj exactCacheGuard
              (ay_iccg_conj independentValidation
                (ay_iccg_conj checkedProof originalBenchmarkUnsat)))
            publication)))

theorem ay_iccg_accepted_cache_preserves_sat_soundness
    (cacheContract exactCacheGuard independentValidation checkedModel
      originalBenchmarkSat : Prop) :
    ay_iccg_sat_publication cacheContract exactCacheGuard
      independentValidation checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_iccg_sat_publication_original_claim cacheContract exactCacheGuard
    independentValidation checkedModel originalBenchmarkSat

theorem ay_iccg_accepted_cache_preserves_unsat_soundness
    (cacheContract exactCacheGuard independentValidation checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_iccg_unsat_publication cacheContract exactCacheGuard
      independentValidation checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_iccg_unsat_publication_original_claim cacheContract exactCacheGuard
    independentValidation checkedProof originalBenchmarkUnsat

theorem ay_iccg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_iccg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_iccg_conj_intro reason (ay_iccg_conj fallbackPath auditTrail)
      hreason
      (ay_iccg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_iccg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_iccg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_iccg_conj_intro reason
      (ay_iccg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_iccg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_iccg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_iccg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_iccg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_iccg_conj_right reason
        (ay_iccg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_iccg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_iccg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_iccg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_iccg_conj_right reason
        (ay_iccg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_iccg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_iccg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_iccg_conj_intro reason
      (ay_iccg_conj fallbackPath recomputeObligation)
      hreason
      (ay_iccg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_iccg_cache_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_iccg_blocked_publication satFact unsatFact reason ->
    ay_iccg_recompute reason fallbackPath recomputeObligation ->
    ay_iccg_cache_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_iccg_conj_intro
      (ay_iccg_blocked_publication satFact unsatFact reason)
      (ay_iccg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_iccg_cache_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_iccg_cache_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_iccg_blocked_publication_no_sat satFact unsatFact reason
      (ay_iccg_conj_left
        (ay_iccg_blocked_publication satFact unsatFact reason)
        (ay_iccg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_iccg_cache_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_iccg_cache_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_iccg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_iccg_conj_left
        (ay_iccg_blocked_publication satFact unsatFact reason)
        (ay_iccg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_iccg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_iccg_no_claim reason fallbackPath auditTrail :=
  ay_iccg_no_claim_intro reason fallbackPath auditTrail

theorem ay_iccg_benchmark_mismatch_forces_no_claim
    (benchmarkMismatch fallbackPath auditTrail : Prop) :
    benchmarkMismatch -> fallbackPath -> auditTrail ->
    ay_iccg_no_claim benchmarkMismatch fallbackPath auditTrail :=
  ay_iccg_mismatch_forces_no_claim benchmarkMismatch fallbackPath auditTrail

theorem ay_iccg_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_iccg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_iccg_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_iccg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_iccg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_iccg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_iccg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_iccg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_iccg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_iccg_environment_mismatch_forces_no_claim
    (environmentMismatch fallbackPath auditTrail : Prop) :
    environmentMismatch -> fallbackPath -> auditTrail ->
    ay_iccg_no_claim environmentMismatch fallbackPath auditTrail :=
  ay_iccg_mismatch_forces_no_claim environmentMismatch fallbackPath auditTrail

theorem ay_iccg_cache_key_mismatch_forces_no_claim
    (cacheKeyMismatch fallbackPath auditTrail : Prop) :
    cacheKeyMismatch -> fallbackPath -> auditTrail ->
    ay_iccg_no_claim cacheKeyMismatch fallbackPath auditTrail :=
  ay_iccg_mismatch_forces_no_claim cacheKeyMismatch fallbackPath auditTrail

theorem ay_iccg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_iccg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_iccg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_iccg_stale_cache_forces_no_claim
    (staleCache fallbackPath auditTrail : Prop) :
    staleCache -> fallbackPath -> auditTrail ->
    ay_iccg_no_claim staleCache fallbackPath auditTrail :=
  ay_iccg_mismatch_forces_no_claim staleCache fallbackPath auditTrail

theorem ay_iccg_partial_cache_forces_recompute
    (partialCache freshFallback recomputeObligation : Prop) :
    partialCache -> freshFallback -> recomputeObligation ->
    ay_iccg_recompute partialCache freshFallback recomputeObligation :=
  ay_iccg_recompute_intro partialCache freshFallback recomputeObligation

theorem ay_iccg_fallback_activation_forces_recompute
    (fallbackActivated freshFallback recomputeObligation : Prop) :
    fallbackActivated -> freshFallback -> recomputeObligation ->
    ay_iccg_recompute fallbackActivated freshFallback recomputeObligation :=
  ay_iccg_recompute_intro fallbackActivated freshFallback recomputeObligation

theorem ay_iccg_solver_output_cache_hit_cannot_publish_sat
    (satFact unsatFact solverOutputPlusCacheHit : Prop) :
    ay_iccg_blocked_publication satFact unsatFact solverOutputPlusCacheHit ->
    satFact -> False :=
  ay_iccg_blocked_publication_no_sat satFact unsatFact
    solverOutputPlusCacheHit

theorem ay_iccg_solver_output_cache_hit_cannot_publish_unsat
    (satFact unsatFact solverOutputPlusCacheHit : Prop) :
    ay_iccg_blocked_publication satFact unsatFact solverOutputPlusCacheHit ->
    unsatFact -> False :=
  ay_iccg_blocked_publication_no_unsat satFact unsatFact
    solverOutputPlusCacheHit

theorem ay_iccg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_iccg_cache_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_iccg_cache_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_iccg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_iccg_cache_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_iccg_cache_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
