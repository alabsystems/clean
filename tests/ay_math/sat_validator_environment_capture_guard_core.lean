-- SAT-COMP validator environment-capture guard core.
--
-- Public SAT/UNSAT claims require solver command digest, environment manifest,
-- resource limits, working-directory/input path digest, checker transcript,
-- benchmark fingerprint, solver build evidence, archive manifest, no-claim
-- fallback, and audit transcript to agree.

def ay_ecag_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ecag_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ecag_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_ecag_disj satFact (ay_ecag_disj unsatFact noClaimFact)

def ay_ecag_environment_contract
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) : Prop :=
  forall result : Prop,
    (solverCommandDigest -> environmentVariableManifest ->
      resourceLimitManifest -> workingDirectoryInputPathDigest ->
      checkerTranscript -> benchmarkFingerprint -> solverBuildEvidence ->
      archiveManifest -> noClaimFallback -> auditTranscript -> result) ->
    result

def ay_ecag_sat_publication
    (environmentContract acceptedEnvironmentCapture modelEvidence
      originalModel : Prop) : Prop :=
  ay_ecag_conj environmentContract
    (ay_ecag_conj acceptedEnvironmentCapture
      (ay_ecag_conj modelEvidence originalModel))

def ay_ecag_unsat_publication
    (environmentContract acceptedEnvironmentCapture proofEvidence
      originalEmptyClause : Prop) : Prop :=
  ay_ecag_conj environmentContract
    (ay_ecag_conj acceptedEnvironmentCapture
      (ay_ecag_conj proofEvidence originalEmptyClause))

def ay_ecag_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_ecag_conj reason (ay_ecag_conj fallbackPath auditTrail)

def ay_ecag_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_ecag_conj reason
    (ay_ecag_conj (satFact -> False) (unsatFact -> False))

def ay_ecag_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_ecag_conj reason
    (ay_ecag_conj fallbackPath recomputeObligation)

def ay_ecag_environment_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_ecag_conj
    (ay_ecag_blocked_publication satFact unsatFact reason)
    (ay_ecag_recompute reason fallbackPath recomputeObligation)

theorem ay_ecag_conj_intro (left right : Prop) :
    left -> right -> ay_ecag_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ecag_conj_left (left right : Prop) :
    ay_ecag_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ecag_conj_right (left right : Prop) :
    ay_ecag_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ecag_disj_left (left right : Prop) :
    left -> ay_ecag_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ecag_disj_right (left right : Prop) :
    right -> ay_ecag_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ecag_environment_contract_intro
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    solverCommandDigest -> environmentVariableManifest ->
    resourceLimitManifest -> workingDirectoryInputPathDigest ->
    checkerTranscript -> benchmarkFingerprint -> solverBuildEvidence ->
    archiveManifest -> noClaimFallback -> auditTranscript ->
    ay_ecag_environment_contract solverCommandDigest
      environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :=
  fun commandProof envProof resourceProof pathProof checkerProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof result
      build =>
    build commandProof envProof resourceProof pathProof checkerProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof

theorem ay_ecag_environment_contract_command
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_ecag_environment_contract solverCommandDigest
      environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    solverCommandDigest :=
  fun contract =>
    contract solverCommandDigest
      (fun commandProof _envProof _resourceProof _pathProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => commandProof)

theorem ay_ecag_environment_contract_environment
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_ecag_environment_contract solverCommandDigest
      environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    environmentVariableManifest :=
  fun contract =>
    contract environmentVariableManifest
      (fun _commandProof envProof _resourceProof _pathProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => envProof)

theorem ay_ecag_environment_contract_resource
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_ecag_environment_contract solverCommandDigest
      environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    resourceLimitManifest :=
  fun contract =>
    contract resourceLimitManifest
      (fun _commandProof _envProof resourceProof _pathProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => resourceProof)

theorem ay_ecag_environment_contract_path
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_ecag_environment_contract solverCommandDigest
      environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    workingDirectoryInputPathDigest :=
  fun contract =>
    contract workingDirectoryInputPathDigest
      (fun _commandProof _envProof _resourceProof pathProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => pathProof)

theorem ay_ecag_environment_contract_checker
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_ecag_environment_contract solverCommandDigest
      environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _commandProof _envProof _resourceProof _pathProof checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_ecag_environment_contract_fingerprint
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_ecag_environment_contract solverCommandDigest
      environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _commandProof _envProof _resourceProof _pathProof _checkerProof
          fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_ecag_environment_contract_build
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_ecag_environment_contract solverCommandDigest
      environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _commandProof _envProof _resourceProof _pathProof _checkerProof
          _fingerprintProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_ecag_environment_contract_archive
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_ecag_environment_contract solverCommandDigest
      environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _commandProof _envProof _resourceProof _pathProof _checkerProof
          _fingerprintProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_ecag_environment_contract_fallback
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_ecag_environment_contract solverCommandDigest
      environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _commandProof _envProof _resourceProof _pathProof _checkerProof
          _fingerprintProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_ecag_environment_contract_audit
    (solverCommandDigest environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_ecag_environment_contract solverCommandDigest
      environmentVariableManifest resourceLimitManifest
      workingDirectoryInputPathDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _commandProof _envProof _resourceProof _pathProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_ecag_sat_publication_intro
    (environmentContract acceptedEnvironmentCapture modelEvidence
      originalModel : Prop) :
    environmentContract -> acceptedEnvironmentCapture -> modelEvidence ->
    originalModel ->
    ay_ecag_sat_publication environmentContract acceptedEnvironmentCapture
      modelEvidence originalModel :=
  fun contractProof captureProof modelProof originalProof =>
    ay_ecag_conj_intro environmentContract
      (ay_ecag_conj acceptedEnvironmentCapture
        (ay_ecag_conj modelEvidence originalModel)) contractProof
      (ay_ecag_conj_intro acceptedEnvironmentCapture
        (ay_ecag_conj modelEvidence originalModel) captureProof
        (ay_ecag_conj_intro modelEvidence originalModel modelProof
          originalProof))

theorem ay_ecag_sat_publication_capture
    (environmentContract acceptedEnvironmentCapture modelEvidence
      originalModel : Prop) :
    ay_ecag_sat_publication environmentContract acceptedEnvironmentCapture
      modelEvidence originalModel ->
    acceptedEnvironmentCapture :=
  fun publication =>
    ay_ecag_conj_left acceptedEnvironmentCapture
      (ay_ecag_conj modelEvidence originalModel)
      (ay_ecag_conj_right environmentContract
        (ay_ecag_conj acceptedEnvironmentCapture
          (ay_ecag_conj modelEvidence originalModel)) publication)

theorem ay_ecag_sat_publication_original_model
    (environmentContract acceptedEnvironmentCapture modelEvidence
      originalModel : Prop) :
    ay_ecag_sat_publication environmentContract acceptedEnvironmentCapture
      modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_ecag_conj_right modelEvidence originalModel
      (ay_ecag_conj_right acceptedEnvironmentCapture
        (ay_ecag_conj modelEvidence originalModel)
        (ay_ecag_conj_right environmentContract
          (ay_ecag_conj acceptedEnvironmentCapture
            (ay_ecag_conj modelEvidence originalModel)) publication))

theorem ay_ecag_unsat_publication_intro
    (environmentContract acceptedEnvironmentCapture proofEvidence
      originalEmptyClause : Prop) :
    environmentContract -> acceptedEnvironmentCapture -> proofEvidence ->
    originalEmptyClause ->
    ay_ecag_unsat_publication environmentContract acceptedEnvironmentCapture
      proofEvidence originalEmptyClause :=
  fun contractProof captureProof proofProof emptyProof =>
    ay_ecag_conj_intro environmentContract
      (ay_ecag_conj acceptedEnvironmentCapture
        (ay_ecag_conj proofEvidence originalEmptyClause)) contractProof
      (ay_ecag_conj_intro acceptedEnvironmentCapture
        (ay_ecag_conj proofEvidence originalEmptyClause) captureProof
        (ay_ecag_conj_intro proofEvidence originalEmptyClause proofProof
          emptyProof))

theorem ay_ecag_unsat_publication_capture
    (environmentContract acceptedEnvironmentCapture proofEvidence
      originalEmptyClause : Prop) :
    ay_ecag_unsat_publication environmentContract acceptedEnvironmentCapture
      proofEvidence originalEmptyClause ->
    acceptedEnvironmentCapture :=
  fun publication =>
    ay_ecag_conj_left acceptedEnvironmentCapture
      (ay_ecag_conj proofEvidence originalEmptyClause)
      (ay_ecag_conj_right environmentContract
        (ay_ecag_conj acceptedEnvironmentCapture
          (ay_ecag_conj proofEvidence originalEmptyClause)) publication)

theorem ay_ecag_unsat_publication_original_empty_clause
    (environmentContract acceptedEnvironmentCapture proofEvidence
      originalEmptyClause : Prop) :
    ay_ecag_unsat_publication environmentContract acceptedEnvironmentCapture
      proofEvidence originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_ecag_conj_right proofEvidence originalEmptyClause
      (ay_ecag_conj_right acceptedEnvironmentCapture
        (ay_ecag_conj proofEvidence originalEmptyClause)
        (ay_ecag_conj_right environmentContract
          (ay_ecag_conj acceptedEnvironmentCapture
            (ay_ecag_conj proofEvidence originalEmptyClause)) publication))

theorem ay_ecag_accepted_environment_sat_passes_publication
    (environmentContract acceptedEnvironmentCapture modelEvidence
      originalModel : Prop) :
    ay_ecag_sat_publication environmentContract acceptedEnvironmentCapture
      modelEvidence originalModel ->
    ay_ecag_conj acceptedEnvironmentCapture originalModel :=
  fun publication =>
    ay_ecag_conj_intro acceptedEnvironmentCapture originalModel
      (ay_ecag_sat_publication_capture environmentContract
        acceptedEnvironmentCapture modelEvidence originalModel publication)
      (ay_ecag_sat_publication_original_model environmentContract
        acceptedEnvironmentCapture modelEvidence originalModel publication)

theorem ay_ecag_accepted_environment_unsat_passes_publication
    (environmentContract acceptedEnvironmentCapture proofEvidence
      originalEmptyClause : Prop) :
    ay_ecag_unsat_publication environmentContract acceptedEnvironmentCapture
      proofEvidence originalEmptyClause ->
    ay_ecag_conj acceptedEnvironmentCapture originalEmptyClause :=
  fun publication =>
    ay_ecag_conj_intro acceptedEnvironmentCapture originalEmptyClause
      (ay_ecag_unsat_publication_capture environmentContract
        acceptedEnvironmentCapture proofEvidence originalEmptyClause
        publication)
      (ay_ecag_unsat_publication_original_empty_clause environmentContract
        acceptedEnvironmentCapture proofEvidence originalEmptyClause
        publication)

theorem ay_ecag_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_ecag_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_ecag_conj_intro reason (ay_ecag_conj fallbackPath auditTrail)
      reasonProof
      (ay_ecag_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_ecag_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_ecag_conj_intro reason
      (ay_ecag_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_ecag_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_ecag_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_ecag_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_ecag_conj_left (satFact -> False) (unsatFact -> False)
      (ay_ecag_conj_right reason
        (ay_ecag_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_ecag_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_ecag_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_ecag_conj_right (satFact -> False) (unsatFact -> False)
      (ay_ecag_conj_right reason
        (ay_ecag_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_ecag_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_ecag_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_ecag_conj_intro reason
      (ay_ecag_conj fallbackPath recomputeObligation) reasonProof
      (ay_ecag_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_ecag_environment_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_ecag_conj_intro
      (ay_ecag_blocked_publication satFact unsatFact reason)
      (ay_ecag_recompute reason fallbackPath recomputeObligation)
      (ay_ecag_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_ecag_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_ecag_environment_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecag_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_ecag_blocked_publication_no_sat satFact unsatFact reason
      (ay_ecag_conj_left
        (ay_ecag_blocked_publication satFact unsatFact reason)
        (ay_ecag_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ecag_environment_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecag_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_ecag_blocked_publication_no_unsat satFact unsatFact reason
      (ay_ecag_conj_left
        (ay_ecag_blocked_publication satFact unsatFact reason)
        (ay_ecag_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ecag_environment_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecag_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_ecag_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_ecag_conj_right
      (ay_ecag_blocked_publication satFact unsatFact reason)
      (ay_ecag_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_ecag_environment_drift_forces_no_claim
    (satFact unsatFact environmentDrift fallbackPath auditTrail
      recomputeObligation : Prop) :
    environmentDrift -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_no_claim environmentDrift fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ecag_no_claim_intro environmentDrift fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ecag_missing_resource_limit_forces_no_claim
    (satFact unsatFact missingResourceLimit fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingResourceLimit -> fallbackPath -> auditTrail ->
    recomputeObligation -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_no_claim missingResourceLimit fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ecag_no_claim_intro missingResourceLimit fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ecag_path_input_mismatch_forces_no_claim
    (satFact unsatFact pathInputMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    pathInputMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_no_claim pathInputMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ecag_no_claim_intro pathInputMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ecag_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_no_claim checkerMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ecag_no_claim_intro checkerMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_ecag_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ecag_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ecag_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ecag_no_claim_intro buildMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_ecag_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ecag_no_claim_intro archiveMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_ecag_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivated fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_no_claim fallbackActivated fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ecag_no_claim_intro fallbackActivated fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ecag_failed_environment_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecag_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_ecag_environment_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_ecag_failed_environment_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecag_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_ecag_environment_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_ecag_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_ecag_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_ecag_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_ecag_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
