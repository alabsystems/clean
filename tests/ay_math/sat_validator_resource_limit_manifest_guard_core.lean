-- SAT-COMP validator resource-limit manifest guard core.
--
-- Public SAT/UNSAT claims require wall/cpu/memory limit manifests,
-- scheduler/cgroup/ulimit evidence, process exit evidence, checker transcript,
-- benchmark fingerprint, solver build evidence, archive manifest, no-claim
-- fallback, and audit transcript to agree.  Resource-limit failures become
-- no-claim recompute obligations rather than public semantic answers.

def ay_rlmg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rlmg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_rlmg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_rlmg_disj satFact (ay_rlmg_disj unsatFact noClaimFact)

def ay_rlmg_resource_contract
    (wallCpuMemoryLimitManifest schedulerCgroupUlimitEvidence
      processExitEvidence checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) : Prop :=
  forall result : Prop,
    (wallCpuMemoryLimitManifest -> schedulerCgroupUlimitEvidence ->
      processExitEvidence -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> noClaimFallback ->
      auditTranscript -> result) ->
    result

def ay_rlmg_sat_publication
    (resourceContract acceptedResourceLimits checkedModel originalModel :
      Prop) : Prop :=
  ay_rlmg_conj resourceContract
    (ay_rlmg_conj acceptedResourceLimits
      (ay_rlmg_conj checkedModel originalModel))

def ay_rlmg_unsat_publication
    (resourceContract acceptedResourceLimits checkedProof
      originalEmptyClause : Prop) : Prop :=
  ay_rlmg_conj resourceContract
    (ay_rlmg_conj acceptedResourceLimits
      (ay_rlmg_conj checkedProof originalEmptyClause))

def ay_rlmg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_rlmg_conj reason (ay_rlmg_conj fallbackPath auditTrail)

def ay_rlmg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_rlmg_conj reason
    (ay_rlmg_conj (satFact -> False) (unsatFact -> False))

def ay_rlmg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_rlmg_conj reason
    (ay_rlmg_conj fallbackPath recomputeObligation)

def ay_rlmg_resource_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_rlmg_conj
    (ay_rlmg_blocked_publication satFact unsatFact reason)
    (ay_rlmg_recompute reason fallbackPath recomputeObligation)

theorem ay_rlmg_conj_intro (left right : Prop) :
    left -> right -> ay_rlmg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_rlmg_conj_left (left right : Prop) :
    ay_rlmg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_rlmg_conj_right (left right : Prop) :
    ay_rlmg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_rlmg_disj_left (left right : Prop) :
    left -> ay_rlmg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_rlmg_disj_right (left right : Prop) :
    right -> ay_rlmg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_rlmg_resource_contract_intro
    (wallCpuMemoryLimitManifest schedulerCgroupUlimitEvidence
      processExitEvidence checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    wallCpuMemoryLimitManifest -> schedulerCgroupUlimitEvidence ->
    processExitEvidence -> checkerTranscript -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> noClaimFallback ->
    auditTranscript ->
    ay_rlmg_resource_contract wallCpuMemoryLimitManifest
      schedulerCgroupUlimitEvidence processExitEvidence checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript :=
  fun limitProof schedulerProof exitProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof result build =>
    build limitProof schedulerProof exitProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof

theorem ay_rlmg_contract_limit_manifest
    (wallCpuMemoryLimitManifest schedulerCgroupUlimitEvidence
      processExitEvidence checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_rlmg_resource_contract wallCpuMemoryLimitManifest
      schedulerCgroupUlimitEvidence processExitEvidence checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    wallCpuMemoryLimitManifest :=
  fun contract =>
    contract wallCpuMemoryLimitManifest
      (fun limitProof _schedulerProof _exitProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => limitProof)

theorem ay_rlmg_contract_scheduler_cgroup_ulimit
    (wallCpuMemoryLimitManifest schedulerCgroupUlimitEvidence
      processExitEvidence checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_rlmg_resource_contract wallCpuMemoryLimitManifest
      schedulerCgroupUlimitEvidence processExitEvidence checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    schedulerCgroupUlimitEvidence :=
  fun contract =>
    contract schedulerCgroupUlimitEvidence
      (fun _limitProof schedulerProof _exitProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => schedulerProof)

theorem ay_rlmg_contract_exit
    (wallCpuMemoryLimitManifest schedulerCgroupUlimitEvidence
      processExitEvidence checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_rlmg_resource_contract wallCpuMemoryLimitManifest
      schedulerCgroupUlimitEvidence processExitEvidence checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    processExitEvidence :=
  fun contract =>
    contract processExitEvidence
      (fun _limitProof _schedulerProof exitProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => exitProof)

theorem ay_rlmg_contract_checker
    (wallCpuMemoryLimitManifest schedulerCgroupUlimitEvidence
      processExitEvidence checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_rlmg_resource_contract wallCpuMemoryLimitManifest
      schedulerCgroupUlimitEvidence processExitEvidence checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _limitProof _schedulerProof _exitProof checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_rlmg_contract_fingerprint
    (wallCpuMemoryLimitManifest schedulerCgroupUlimitEvidence
      processExitEvidence checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_rlmg_resource_contract wallCpuMemoryLimitManifest
      schedulerCgroupUlimitEvidence processExitEvidence checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _limitProof _schedulerProof _exitProof _checkerProof
          fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_rlmg_contract_build
    (wallCpuMemoryLimitManifest schedulerCgroupUlimitEvidence
      processExitEvidence checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_rlmg_resource_contract wallCpuMemoryLimitManifest
      schedulerCgroupUlimitEvidence processExitEvidence checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _limitProof _schedulerProof _exitProof _checkerProof
          _fingerprintProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_rlmg_contract_archive
    (wallCpuMemoryLimitManifest schedulerCgroupUlimitEvidence
      processExitEvidence checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_rlmg_resource_contract wallCpuMemoryLimitManifest
      schedulerCgroupUlimitEvidence processExitEvidence checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _limitProof _schedulerProof _exitProof _checkerProof
          _fingerprintProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_rlmg_contract_fallback
    (wallCpuMemoryLimitManifest schedulerCgroupUlimitEvidence
      processExitEvidence checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_rlmg_resource_contract wallCpuMemoryLimitManifest
      schedulerCgroupUlimitEvidence processExitEvidence checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _limitProof _schedulerProof _exitProof _checkerProof
          _fingerprintProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_rlmg_contract_audit
    (wallCpuMemoryLimitManifest schedulerCgroupUlimitEvidence
      processExitEvidence checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_rlmg_resource_contract wallCpuMemoryLimitManifest
      schedulerCgroupUlimitEvidence processExitEvidence checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _limitProof _schedulerProof _exitProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_rlmg_sat_publication_intro
    (resourceContract acceptedResourceLimits checkedModel originalModel :
      Prop) :
    resourceContract -> acceptedResourceLimits -> checkedModel ->
    originalModel ->
    ay_rlmg_sat_publication resourceContract acceptedResourceLimits
      checkedModel originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_rlmg_conj_intro resourceContract
      (ay_rlmg_conj acceptedResourceLimits
        (ay_rlmg_conj checkedModel originalModel))
      contractProof
      (ay_rlmg_conj_intro acceptedResourceLimits
        (ay_rlmg_conj checkedModel originalModel)
        acceptedProof
        (ay_rlmg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_rlmg_sat_publication_resource
    (resourceContract acceptedResourceLimits checkedModel originalModel :
      Prop) :
    ay_rlmg_sat_publication resourceContract acceptedResourceLimits
      checkedModel originalModel ->
    resourceContract :=
  fun publication =>
    ay_rlmg_conj_left resourceContract
      (ay_rlmg_conj acceptedResourceLimits
        (ay_rlmg_conj checkedModel originalModel))
      publication

theorem ay_rlmg_sat_publication_original_model
    (resourceContract acceptedResourceLimits checkedModel originalModel :
      Prop) :
    ay_rlmg_sat_publication resourceContract acceptedResourceLimits
      checkedModel originalModel ->
    originalModel :=
  fun publication =>
    ay_rlmg_conj_right checkedModel originalModel
      (ay_rlmg_conj_right acceptedResourceLimits
        (ay_rlmg_conj checkedModel originalModel)
        (ay_rlmg_conj_right resourceContract
          (ay_rlmg_conj acceptedResourceLimits
            (ay_rlmg_conj checkedModel originalModel))
          publication))

theorem ay_rlmg_unsat_publication_intro
    (resourceContract acceptedResourceLimits checkedProof
      originalEmptyClause : Prop) :
    resourceContract -> acceptedResourceLimits -> checkedProof ->
    originalEmptyClause ->
    ay_rlmg_unsat_publication resourceContract acceptedResourceLimits
      checkedProof originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_rlmg_conj_intro resourceContract
      (ay_rlmg_conj acceptedResourceLimits
        (ay_rlmg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_rlmg_conj_intro acceptedResourceLimits
        (ay_rlmg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_rlmg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_rlmg_unsat_publication_resource
    (resourceContract acceptedResourceLimits checkedProof
      originalEmptyClause : Prop) :
    ay_rlmg_unsat_publication resourceContract acceptedResourceLimits
      checkedProof originalEmptyClause ->
    resourceContract :=
  fun publication =>
    ay_rlmg_conj_left resourceContract
      (ay_rlmg_conj acceptedResourceLimits
        (ay_rlmg_conj checkedProof originalEmptyClause))
      publication

theorem ay_rlmg_unsat_publication_original_empty_clause
    (resourceContract acceptedResourceLimits checkedProof
      originalEmptyClause : Prop) :
    ay_rlmg_unsat_publication resourceContract acceptedResourceLimits
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_rlmg_conj_right checkedProof originalEmptyClause
      (ay_rlmg_conj_right acceptedResourceLimits
        (ay_rlmg_conj checkedProof originalEmptyClause)
        (ay_rlmg_conj_right resourceContract
          (ay_rlmg_conj acceptedResourceLimits
            (ay_rlmg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_rlmg_accepted_resource_sat_passes_publication
    (resourceContract acceptedResourceLimits checkedModel originalModel :
      Prop) :
    ay_rlmg_sat_publication resourceContract acceptedResourceLimits
      checkedModel originalModel ->
    ay_rlmg_public_result originalModel False False :=
  fun publication =>
    ay_rlmg_disj_left originalModel (ay_rlmg_disj False False)
      (ay_rlmg_sat_publication_original_model resourceContract
        acceptedResourceLimits checkedModel originalModel publication)

theorem ay_rlmg_accepted_resource_unsat_passes_publication
    (resourceContract acceptedResourceLimits checkedProof
      originalEmptyClause : Prop) :
    ay_rlmg_unsat_publication resourceContract acceptedResourceLimits
      checkedProof originalEmptyClause ->
    ay_rlmg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_rlmg_disj_right False (ay_rlmg_disj originalEmptyClause False)
      (ay_rlmg_disj_left originalEmptyClause False
        (ay_rlmg_unsat_publication_original_empty_clause resourceContract
          acceptedResourceLimits checkedProof originalEmptyClause publication))

theorem ay_rlmg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_rlmg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_rlmg_conj_intro reason (ay_rlmg_conj fallbackPath auditTrail)
      reasonProof
      (ay_rlmg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_rlmg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_rlmg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_rlmg_conj_intro reason
      (ay_rlmg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_rlmg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_rlmg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_rlmg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_rlmg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_rlmg_conj_right reason
        (ay_rlmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rlmg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_rlmg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_rlmg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_rlmg_conj_right reason
        (ay_rlmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rlmg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_rlmg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_rlmg_conj_intro reason
      (ay_rlmg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_rlmg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_rlmg_resource_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlmg_blocked_publication satFact unsatFact reason ->
    ay_rlmg_recompute reason fallbackPath recomputeObligation ->
    ay_rlmg_resource_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_rlmg_conj_intro
      (ay_rlmg_blocked_publication satFact unsatFact reason)
      (ay_rlmg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_rlmg_resource_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlmg_resource_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_rlmg_blocked_publication_no_sat satFact unsatFact reason
      (ay_rlmg_conj_left
        (ay_rlmg_blocked_publication satFact unsatFact reason)
        (ay_rlmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rlmg_resource_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlmg_resource_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_rlmg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_rlmg_conj_left
        (ay_rlmg_blocked_publication satFact unsatFact reason)
        (ay_rlmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rlmg_resource_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlmg_resource_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_rlmg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_rlmg_conj_right
      (ay_rlmg_blocked_publication satFact unsatFact reason)
      (ay_rlmg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_rlmg_missing_resource_limit_forces_no_claim
    (satFact unsatFact missingResourceLimit fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingResourceLimit -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rlmg_no_claim missingResourceLimit fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rlmg_no_claim_intro missingResourceLimit fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rlmg_stale_resource_limit_forces_recompute
    (satFact unsatFact staleResourceLimit fallbackPath recomputeObligation :
      Prop) :
    staleResourceLimit -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_rlmg_resource_failure satFact unsatFact staleResourceLimit fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_rlmg_resource_failure_intro satFact unsatFact staleResourceLimit
      fallbackPath recomputeObligation
      (ay_rlmg_blocked_publication_intro satFact unsatFact staleResourceLimit
        reasonProof noSat noUnsat)
      (ay_rlmg_recompute_intro staleResourceLimit fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_rlmg_scheduler_cgroup_drift_forces_no_claim
    (satFact unsatFact schedulerCgroupDrift fallbackPath auditTrail
      recomputeObligation : Prop) :
    schedulerCgroupDrift -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rlmg_no_claim schedulerCgroupDrift fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rlmg_no_claim_intro schedulerCgroupDrift fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rlmg_ulimit_mismatch_forces_no_claim
    (satFact unsatFact ulimitMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    ulimitMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rlmg_no_claim ulimitMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rlmg_no_claim_intro ulimitMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rlmg_exit_mismatch_forces_no_claim
    (satFact unsatFact exitMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    exitMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rlmg_no_claim exitMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rlmg_no_claim_intro exitMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rlmg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rlmg_no_claim checkerMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rlmg_no_claim_intro checkerMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rlmg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rlmg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rlmg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rlmg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rlmg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rlmg_no_claim_intro buildMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rlmg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rlmg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rlmg_no_claim_intro archiveMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rlmg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivation fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivation -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rlmg_no_claim fallbackActivation fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rlmg_no_claim_intro fallbackActivation fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rlmg_failed_resource_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlmg_resource_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_rlmg_resource_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_rlmg_failed_resource_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlmg_resource_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_rlmg_resource_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_rlmg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_rlmg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_rlmg_conj_left reason (ay_rlmg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_rlmg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_rlmg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_rlmg_conj_left reason (ay_rlmg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
