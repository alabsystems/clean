-- SAT-COMP validator resource-limit accounting guard core.
--
-- Time, memory, propagation, and conflict accounting control no-result paths.
-- They cannot publish SAT/UNSAT without independent checker-backed evidence.

def ay_rlag_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rlag_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_rlag_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_rlag_disj satFact (ay_rlag_disj unsatFact noClaimFact)

def ay_rlag_accounting_contract
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint -> configuredResourceLimits ->
      runtimeMemoryCounters -> propagationConflictCounterDigest ->
      resourceClassification -> solverOutputDigest -> checkerTranscript ->
      solverBuildEvidence -> environmentManifest -> archiveManifest ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_rlag_checked_sat_publication
    (accountingContract independentCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_rlag_conj accountingContract
    (ay_rlag_conj independentCheckerEvidence
      (ay_rlag_conj checkedModel originalBenchmarkSat))

def ay_rlag_checked_unsat_publication
    (accountingContract independentCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_rlag_conj accountingContract
    (ay_rlag_conj independentCheckerEvidence
      (ay_rlag_conj checkedProof originalBenchmarkUnsat))

def ay_rlag_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_rlag_conj reason (ay_rlag_conj fallbackPath auditTrail)

def ay_rlag_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_rlag_conj reason
    (ay_rlag_conj (satFact -> False) (unsatFact -> False))

def ay_rlag_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_rlag_conj reason
    (ay_rlag_conj fallbackPath recomputeObligation)

def ay_rlag_accounting_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_rlag_conj
    (ay_rlag_blocked_publication satFact unsatFact reason)
    (ay_rlag_recompute reason fallbackPath recomputeObligation)

theorem ay_rlag_conj_intro (left right : Prop) :
    left -> right -> ay_rlag_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_rlag_conj_left (left right : Prop) :
    ay_rlag_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_rlag_conj_right (left right : Prop) :
    ay_rlag_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_rlag_disj_left (left right : Prop) :
    left -> ay_rlag_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_rlag_disj_right (left right : Prop) :
    right -> ay_rlag_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_rlag_accounting_contract_intro
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    benchmarkFingerprint -> configuredResourceLimits ->
    runtimeMemoryCounters -> propagationConflictCounterDigest ->
    resourceClassification -> solverOutputDigest -> checkerTranscript ->
    solverBuildEvidence -> environmentManifest -> archiveManifest ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_rlag_accounting_contract benchmarkFingerprint
      configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath auditTranscript :=
  fun benchmarkProof limitProof counterProof propagationProof classificationProof
      outputProof checkerProof buildProof environmentProof archiveProof
      fallbackProof auditProof result build =>
    build benchmarkProof limitProof counterProof propagationProof
      classificationProof outputProof checkerProof buildProof environmentProof
      archiveProof fallbackProof auditProof

theorem ay_rlag_contract_benchmark
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun benchmarkProof _limitProof _counterProof _propagationProof
          _classificationProof _outputProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        benchmarkProof)

theorem ay_rlag_contract_limits
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    configuredResourceLimits :=
  fun contract =>
    contract configuredResourceLimits
      (fun _benchmarkProof limitProof _counterProof _propagationProof
          _classificationProof _outputProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        limitProof)

theorem ay_rlag_contract_runtime_counters
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    runtimeMemoryCounters :=
  fun contract =>
    contract runtimeMemoryCounters
      (fun _benchmarkProof _limitProof counterProof _propagationProof
          _classificationProof _outputProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        counterProof)

theorem ay_rlag_contract_propagation_conflict
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    propagationConflictCounterDigest :=
  fun contract =>
    contract propagationConflictCounterDigest
      (fun _benchmarkProof _limitProof _counterProof propagationProof
          _classificationProof _outputProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        propagationProof)

theorem ay_rlag_contract_classification
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    resourceClassification :=
  fun contract =>
    contract resourceClassification
      (fun _benchmarkProof _limitProof _counterProof _propagationProof
          classificationProof _outputProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        classificationProof)

theorem ay_rlag_contract_output
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverOutputDigest :=
  fun contract =>
    contract solverOutputDigest
      (fun _benchmarkProof _limitProof _counterProof _propagationProof
          _classificationProof outputProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        outputProof)

theorem ay_rlag_contract_checker
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _benchmarkProof _limitProof _counterProof _propagationProof
          _classificationProof _outputProof checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        checkerProof)

theorem ay_rlag_contract_build
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _benchmarkProof _limitProof _counterProof _propagationProof
          _classificationProof _outputProof _checkerProof buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        buildProof)

theorem ay_rlag_contract_environment
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    environmentManifest :=
  fun contract =>
    contract environmentManifest
      (fun _benchmarkProof _limitProof _counterProof _propagationProof
          _classificationProof _outputProof _checkerProof _buildProof
          environmentProof _archiveProof _fallbackProof _auditProof =>
        environmentProof)

theorem ay_rlag_contract_archive
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _benchmarkProof _limitProof _counterProof _propagationProof
          _classificationProof _outputProof _checkerProof _buildProof
          _environmentProof archiveProof _fallbackProof _auditProof =>
        archiveProof)

theorem ay_rlag_contract_fallback
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _benchmarkProof _limitProof _counterProof _propagationProof
          _classificationProof _outputProof _checkerProof _buildProof
          _environmentProof _archiveProof fallbackProof _auditProof =>
        fallbackProof)

theorem ay_rlag_contract_audit
    (benchmarkFingerprint configuredResourceLimits runtimeMemoryCounters
      propagationConflictCounterDigest resourceClassification
      solverOutputDigest checkerTranscript solverBuildEvidence
      environmentManifest archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rlag_accounting_contract benchmarkFingerprint configuredResourceLimits
      runtimeMemoryCounters propagationConflictCounterDigest
      resourceClassification solverOutputDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _benchmarkProof _limitProof _counterProof _propagationProof
          _classificationProof _outputProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof auditProof =>
        auditProof)

theorem ay_rlag_checked_sat_publication_intro
    (accountingContract independentCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) :
    accountingContract -> independentCheckerEvidence -> checkedModel ->
    originalBenchmarkSat ->
    ay_rlag_checked_sat_publication accountingContract
      independentCheckerEvidence checkedModel originalBenchmarkSat :=
  fun hcontract hchecker hchecked horiginal =>
    ay_rlag_conj_intro accountingContract
      (ay_rlag_conj independentCheckerEvidence
        (ay_rlag_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_rlag_conj_intro independentCheckerEvidence
        (ay_rlag_conj checkedModel originalBenchmarkSat)
        hchecker
        (ay_rlag_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_rlag_checked_unsat_publication_intro
    (accountingContract independentCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    accountingContract -> independentCheckerEvidence -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_rlag_checked_unsat_publication accountingContract
      independentCheckerEvidence checkedProof originalBenchmarkUnsat :=
  fun hcontract hchecker hchecked horiginal =>
    ay_rlag_conj_intro accountingContract
      (ay_rlag_conj independentCheckerEvidence
        (ay_rlag_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_rlag_conj_intro independentCheckerEvidence
        (ay_rlag_conj checkedProof originalBenchmarkUnsat)
        hchecker
        (ay_rlag_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_rlag_checked_sat_requires_checker_evidence
    (accountingContract independentCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_rlag_checked_sat_publication accountingContract
      independentCheckerEvidence checkedModel originalBenchmarkSat ->
    independentCheckerEvidence :=
  fun publication =>
    ay_rlag_conj_left independentCheckerEvidence
      (ay_rlag_conj checkedModel originalBenchmarkSat)
      (ay_rlag_conj_right accountingContract
        (ay_rlag_conj independentCheckerEvidence
          (ay_rlag_conj checkedModel originalBenchmarkSat))
        publication)

theorem ay_rlag_checked_unsat_requires_checker_evidence
    (accountingContract independentCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_rlag_checked_unsat_publication accountingContract
      independentCheckerEvidence checkedProof originalBenchmarkUnsat ->
    independentCheckerEvidence :=
  fun publication =>
    ay_rlag_conj_left independentCheckerEvidence
      (ay_rlag_conj checkedProof originalBenchmarkUnsat)
      (ay_rlag_conj_right accountingContract
        (ay_rlag_conj independentCheckerEvidence
          (ay_rlag_conj checkedProof originalBenchmarkUnsat))
        publication)

theorem ay_rlag_checked_sat_publication_original_claim
    (accountingContract independentCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_rlag_checked_sat_publication accountingContract
      independentCheckerEvidence checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_rlag_conj_right checkedModel originalBenchmarkSat
      (ay_rlag_conj_right independentCheckerEvidence
        (ay_rlag_conj checkedModel originalBenchmarkSat)
        (ay_rlag_conj_right accountingContract
          (ay_rlag_conj independentCheckerEvidence
            (ay_rlag_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_rlag_checked_unsat_publication_original_claim
    (accountingContract independentCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_rlag_checked_unsat_publication accountingContract
      independentCheckerEvidence checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_rlag_conj_right checkedProof originalBenchmarkUnsat
      (ay_rlag_conj_right independentCheckerEvidence
        (ay_rlag_conj checkedProof originalBenchmarkUnsat)
        (ay_rlag_conj_right accountingContract
          (ay_rlag_conj independentCheckerEvidence
            (ay_rlag_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_rlag_accepted_accounting_preserves_sat_soundness
    (accountingContract independentCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_rlag_checked_sat_publication accountingContract
      independentCheckerEvidence checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_rlag_checked_sat_publication_original_claim accountingContract
    independentCheckerEvidence checkedModel originalBenchmarkSat

theorem ay_rlag_accepted_accounting_preserves_unsat_soundness
    (accountingContract independentCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_rlag_checked_unsat_publication accountingContract
      independentCheckerEvidence checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_rlag_checked_unsat_publication_original_claim accountingContract
    independentCheckerEvidence checkedProof originalBenchmarkUnsat

theorem ay_rlag_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_rlag_conj_intro reason (ay_rlag_conj fallbackPath auditTrail)
      hreason
      (ay_rlag_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_rlag_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_rlag_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_rlag_conj_intro reason
      (ay_rlag_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_rlag_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_rlag_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_rlag_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_rlag_conj_left (satFact -> False) (unsatFact -> False)
      (ay_rlag_conj_right reason
        (ay_rlag_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rlag_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_rlag_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_rlag_conj_right (satFact -> False) (unsatFact -> False)
      (ay_rlag_conj_right reason
        (ay_rlag_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rlag_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_rlag_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_rlag_conj_intro reason
      (ay_rlag_conj fallbackPath recomputeObligation)
      hreason
      (ay_rlag_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_rlag_accounting_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlag_blocked_publication satFact unsatFact reason ->
    ay_rlag_recompute reason fallbackPath recomputeObligation ->
    ay_rlag_accounting_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_rlag_conj_intro
      (ay_rlag_blocked_publication satFact unsatFact reason)
      (ay_rlag_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_rlag_accounting_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlag_accounting_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_rlag_blocked_publication_no_sat satFact unsatFact reason
      (ay_rlag_conj_left
        (ay_rlag_blocked_publication satFact unsatFact reason)
        (ay_rlag_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rlag_accounting_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlag_accounting_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_rlag_blocked_publication_no_unsat satFact unsatFact reason
      (ay_rlag_conj_left
        (ay_rlag_blocked_publication satFact unsatFact reason)
        (ay_rlag_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rlag_resource_classification_no_sat
    (satFact unsatFact resourceClassification : Prop) :
    ay_rlag_blocked_publication satFact unsatFact resourceClassification ->
    satFact -> False :=
  ay_rlag_blocked_publication_no_sat satFact unsatFact resourceClassification

theorem ay_rlag_resource_classification_no_unsat
    (satFact unsatFact resourceClassification : Prop) :
    ay_rlag_blocked_publication satFact unsatFact resourceClassification ->
    unsatFact -> False :=
  ay_rlag_blocked_publication_no_unsat satFact unsatFact resourceClassification

theorem ay_rlag_timeout_classification_forces_no_claim
    (timeoutClassification fallbackPath auditTrail : Prop) :
    timeoutClassification -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim timeoutClassification fallbackPath auditTrail :=
  ay_rlag_no_claim_intro timeoutClassification fallbackPath auditTrail

theorem ay_rlag_oom_classification_forces_no_claim
    (oomClassification fallbackPath auditTrail : Prop) :
    oomClassification -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim oomClassification fallbackPath auditTrail :=
  ay_rlag_no_claim_intro oomClassification fallbackPath auditTrail

theorem ay_rlag_no_result_classification_forces_recompute
    (noResultClassification fallbackPath recomputeObligation : Prop) :
    noResultClassification -> fallbackPath -> recomputeObligation ->
    ay_rlag_recompute noResultClassification fallbackPath
      recomputeObligation :=
  ay_rlag_recompute_intro noResultClassification fallbackPath
    recomputeObligation

theorem ay_rlag_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim reason fallbackPath auditTrail :=
  ay_rlag_no_claim_intro reason fallbackPath auditTrail

theorem ay_rlag_limit_mismatch_forces_no_claim
    (limitMismatch fallbackPath auditTrail : Prop) :
    limitMismatch -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim limitMismatch fallbackPath auditTrail :=
  ay_rlag_mismatch_forces_no_claim limitMismatch fallbackPath auditTrail

theorem ay_rlag_counter_mismatch_forces_no_claim
    (counterMismatch fallbackPath auditTrail : Prop) :
    counterMismatch -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim counterMismatch fallbackPath auditTrail :=
  ay_rlag_mismatch_forces_no_claim counterMismatch fallbackPath auditTrail

theorem ay_rlag_classification_mismatch_forces_no_claim
    (classificationMismatch fallbackPath auditTrail : Prop) :
    classificationMismatch -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim classificationMismatch fallbackPath auditTrail :=
  ay_rlag_mismatch_forces_no_claim classificationMismatch fallbackPath
    auditTrail

theorem ay_rlag_output_mismatch_forces_no_claim
    (outputMismatch fallbackPath auditTrail : Prop) :
    outputMismatch -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim outputMismatch fallbackPath auditTrail :=
  ay_rlag_mismatch_forces_no_claim outputMismatch fallbackPath auditTrail

theorem ay_rlag_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_rlag_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_rlag_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim buildMismatch fallbackPath auditTrail :=
  ay_rlag_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_rlag_environment_mismatch_forces_no_claim
    (environmentMismatch fallbackPath auditTrail : Prop) :
    environmentMismatch -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim environmentMismatch fallbackPath auditTrail :=
  ay_rlag_mismatch_forces_no_claim environmentMismatch fallbackPath auditTrail

theorem ay_rlag_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_rlag_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_rlag_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_rlag_audit_mismatch_forces_recompute
    (auditMismatch fallbackPath recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> recomputeObligation ->
    ay_rlag_recompute auditMismatch fallbackPath recomputeObligation :=
  ay_rlag_recompute_intro auditMismatch fallbackPath recomputeObligation

theorem ay_rlag_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlag_accounting_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_rlag_accounting_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_rlag_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlag_accounting_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_rlag_accounting_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
