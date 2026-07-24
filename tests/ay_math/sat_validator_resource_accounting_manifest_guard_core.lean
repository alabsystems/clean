-- SAT-COMP validator resource-accounting manifest guard core.
--
-- Resource accounting supports auditability for sequential main-track runs, but
-- does not itself create SAT/UNSAT claims. Publication still requires checked
-- SAT/UNSAT evidence tied to the benchmark.

def ay_ramg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ramg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ramg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_ramg_disj satFact (ay_ramg_disj unsatFact noClaimFact)

def ay_ramg_accounting_contract
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (resourceLimitManifest -> runtimeAccountingDigest ->
      solverConfigurationDigest -> benchmarkFingerprint -> solverOutputDigest ->
      checkerTranscript -> solverBuildEvidence -> archiveManifest ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_ramg_checked_sat_publication
    (accountingContract checkedSatEvidence checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_ramg_conj accountingContract
    (ay_ramg_conj checkedSatEvidence
      (ay_ramg_conj checkedModel originalBenchmarkSat))

def ay_ramg_checked_unsat_publication
    (accountingContract checkedUnsatEvidence checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_ramg_conj accountingContract
    (ay_ramg_conj checkedUnsatEvidence
      (ay_ramg_conj checkedProof originalBenchmarkUnsat))

def ay_ramg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_ramg_conj reason (ay_ramg_conj fallbackPath auditTrail)

def ay_ramg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_ramg_conj reason
    (ay_ramg_conj (satFact -> False) (unsatFact -> False))

def ay_ramg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_ramg_conj reason
    (ay_ramg_conj fallbackPath recomputeObligation)

def ay_ramg_accounting_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_ramg_conj
    (ay_ramg_blocked_publication satFact unsatFact reason)
    (ay_ramg_recompute reason fallbackPath recomputeObligation)

theorem ay_ramg_conj_intro (left right : Prop) :
    left -> right -> ay_ramg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ramg_conj_left (left right : Prop) :
    ay_ramg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ramg_conj_right (left right : Prop) :
    ay_ramg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ramg_disj_left (left right : Prop) :
    left -> ay_ramg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ramg_disj_right (left right : Prop) :
    right -> ay_ramg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ramg_accounting_contract_intro
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    resourceLimitManifest -> runtimeAccountingDigest ->
    solverConfigurationDigest -> benchmarkFingerprint -> solverOutputDigest ->
    checkerTranscript -> solverBuildEvidence -> archiveManifest ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_ramg_accounting_contract resourceLimitManifest runtimeAccountingDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript :=
  fun resourceProof accountingProof configProof benchmarkProof outputProof
      checkerProof buildProof archiveProof fallbackProof auditProof result
      build =>
    build resourceProof accountingProof configProof benchmarkProof outputProof
      checkerProof buildProof archiveProof fallbackProof auditProof

theorem ay_ramg_contract_resource_limit
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_ramg_accounting_contract resourceLimitManifest runtimeAccountingDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    resourceLimitManifest :=
  fun contract =>
    contract resourceLimitManifest
      (fun resourceProof _accountingProof _configProof _benchmarkProof
          _outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => resourceProof)

theorem ay_ramg_contract_runtime_accounting
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_ramg_accounting_contract resourceLimitManifest runtimeAccountingDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    runtimeAccountingDigest :=
  fun contract =>
    contract runtimeAccountingDigest
      (fun _resourceProof accountingProof _configProof _benchmarkProof
          _outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => accountingProof)

theorem ay_ramg_contract_config
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_ramg_accounting_contract resourceLimitManifest runtimeAccountingDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    solverConfigurationDigest :=
  fun contract =>
    contract solverConfigurationDigest
      (fun _resourceProof _accountingProof configProof _benchmarkProof
          _outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => configProof)

theorem ay_ramg_contract_benchmark
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_ramg_accounting_contract resourceLimitManifest runtimeAccountingDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _resourceProof _accountingProof _configProof benchmarkProof
          _outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => benchmarkProof)

theorem ay_ramg_contract_output
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_ramg_accounting_contract resourceLimitManifest runtimeAccountingDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    solverOutputDigest :=
  fun contract =>
    contract solverOutputDigest
      (fun _resourceProof _accountingProof _configProof _benchmarkProof
          outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => outputProof)

theorem ay_ramg_contract_checker
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_ramg_accounting_contract resourceLimitManifest runtimeAccountingDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _resourceProof _accountingProof _configProof _benchmarkProof
          _outputProof checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_ramg_contract_build
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_ramg_accounting_contract resourceLimitManifest runtimeAccountingDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _resourceProof _accountingProof _configProof _benchmarkProof
          _outputProof _checkerProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_ramg_contract_archive
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_ramg_accounting_contract resourceLimitManifest runtimeAccountingDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _resourceProof _accountingProof _configProof _benchmarkProof
          _outputProof _checkerProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_ramg_contract_fallback
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_ramg_accounting_contract resourceLimitManifest runtimeAccountingDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _resourceProof _accountingProof _configProof _benchmarkProof
          _outputProof _checkerProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_ramg_contract_audit
    (resourceLimitManifest runtimeAccountingDigest solverConfigurationDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_ramg_accounting_contract resourceLimitManifest runtimeAccountingDigest
      solverConfigurationDigest benchmarkFingerprint solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _resourceProof _accountingProof _configProof _benchmarkProof
          _outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_ramg_checked_sat_publication_intro
    (accountingContract checkedSatEvidence checkedModel
      originalBenchmarkSat : Prop) :
    accountingContract -> checkedSatEvidence -> checkedModel ->
    originalBenchmarkSat ->
    ay_ramg_checked_sat_publication accountingContract checkedSatEvidence
      checkedModel originalBenchmarkSat :=
  fun hcontract hevidence hchecked horiginal =>
    ay_ramg_conj_intro accountingContract
      (ay_ramg_conj checkedSatEvidence
        (ay_ramg_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_ramg_conj_intro checkedSatEvidence
        (ay_ramg_conj checkedModel originalBenchmarkSat)
        hevidence
        (ay_ramg_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_ramg_checked_unsat_publication_intro
    (accountingContract checkedUnsatEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    accountingContract -> checkedUnsatEvidence -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_ramg_checked_unsat_publication accountingContract checkedUnsatEvidence
      checkedProof originalBenchmarkUnsat :=
  fun hcontract hevidence hchecked horiginal =>
    ay_ramg_conj_intro accountingContract
      (ay_ramg_conj checkedUnsatEvidence
        (ay_ramg_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_ramg_conj_intro checkedUnsatEvidence
        (ay_ramg_conj checkedProof originalBenchmarkUnsat)
        hevidence
        (ay_ramg_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_ramg_checked_sat_publication_original_claim
    (accountingContract checkedSatEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_ramg_checked_sat_publication accountingContract checkedSatEvidence
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_ramg_conj_right checkedModel originalBenchmarkSat
      (ay_ramg_conj_right checkedSatEvidence
        (ay_ramg_conj checkedModel originalBenchmarkSat)
        (ay_ramg_conj_right accountingContract
          (ay_ramg_conj checkedSatEvidence
            (ay_ramg_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_ramg_checked_unsat_publication_original_claim
    (accountingContract checkedUnsatEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_ramg_checked_unsat_publication accountingContract checkedUnsatEvidence
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_ramg_conj_right checkedProof originalBenchmarkUnsat
      (ay_ramg_conj_right checkedUnsatEvidence
        (ay_ramg_conj checkedProof originalBenchmarkUnsat)
        (ay_ramg_conj_right accountingContract
          (ay_ramg_conj checkedUnsatEvidence
            (ay_ramg_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_ramg_accounting_cannot_create_sat
    (satFact unsatFact accountingOnly : Prop) :
    ay_ramg_blocked_publication satFact unsatFact accountingOnly ->
    satFact -> False :=
  fun blocked =>
    ay_ramg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_ramg_conj_right accountingOnly
        (ay_ramg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_ramg_accounting_cannot_create_unsat
    (satFact unsatFact accountingOnly : Prop) :
    ay_ramg_blocked_publication satFact unsatFact accountingOnly ->
    unsatFact -> False :=
  fun blocked =>
    ay_ramg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_ramg_conj_right accountingOnly
        (ay_ramg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_ramg_only_checked_sat_evidence_may_publish
    (accountingContract checkedSatEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_ramg_checked_sat_publication accountingContract checkedSatEvidence
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_ramg_checked_sat_publication_original_claim accountingContract
    checkedSatEvidence checkedModel originalBenchmarkSat

theorem ay_ramg_only_checked_unsat_evidence_may_publish
    (accountingContract checkedUnsatEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_ramg_checked_unsat_publication accountingContract checkedUnsatEvidence
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_ramg_checked_unsat_publication_original_claim accountingContract
    checkedUnsatEvidence checkedProof originalBenchmarkUnsat

theorem ay_ramg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_ramg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_ramg_conj_intro reason (ay_ramg_conj fallbackPath auditTrail)
      hreason
      (ay_ramg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_ramg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ramg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_ramg_conj_intro reason
      (ay_ramg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_ramg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_ramg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_ramg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_ramg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_ramg_conj_right reason
        (ay_ramg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_ramg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_ramg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_ramg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_ramg_conj_right reason
        (ay_ramg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_ramg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_ramg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_ramg_conj_intro reason
      (ay_ramg_conj fallbackPath recomputeObligation)
      hreason
      (ay_ramg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_ramg_accounting_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ramg_blocked_publication satFact unsatFact reason ->
    ay_ramg_recompute reason fallbackPath recomputeObligation ->
    ay_ramg_accounting_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_ramg_conj_intro
      (ay_ramg_blocked_publication satFact unsatFact reason)
      (ay_ramg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_ramg_accounting_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ramg_accounting_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_ramg_blocked_publication_no_sat satFact unsatFact reason
      (ay_ramg_conj_left
        (ay_ramg_blocked_publication satFact unsatFact reason)
        (ay_ramg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ramg_accounting_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ramg_accounting_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_ramg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_ramg_conj_left
        (ay_ramg_blocked_publication satFact unsatFact reason)
        (ay_ramg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ramg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_ramg_no_claim reason fallbackPath auditTrail :=
  ay_ramg_no_claim_intro reason fallbackPath auditTrail

theorem ay_ramg_resource_mismatch_forces_no_claim
    (resourceMismatch fallbackPath auditTrail : Prop) :
    resourceMismatch -> fallbackPath -> auditTrail ->
    ay_ramg_no_claim resourceMismatch fallbackPath auditTrail :=
  ay_ramg_mismatch_forces_no_claim resourceMismatch fallbackPath auditTrail

theorem ay_ramg_config_mismatch_forces_no_claim
    (configMismatch fallbackPath auditTrail : Prop) :
    configMismatch -> fallbackPath -> auditTrail ->
    ay_ramg_no_claim configMismatch fallbackPath auditTrail :=
  ay_ramg_mismatch_forces_no_claim configMismatch fallbackPath auditTrail

theorem ay_ramg_output_mismatch_forces_no_claim
    (outputMismatch fallbackPath auditTrail : Prop) :
    outputMismatch -> fallbackPath -> auditTrail ->
    ay_ramg_no_claim outputMismatch fallbackPath auditTrail :=
  ay_ramg_mismatch_forces_no_claim outputMismatch fallbackPath auditTrail

theorem ay_ramg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_ramg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_ramg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_ramg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_ramg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_ramg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_ramg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_ramg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_ramg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_ramg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_ramg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_ramg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_ramg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ramg_accounting_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_ramg_accounting_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_ramg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ramg_accounting_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_ramg_accounting_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation
