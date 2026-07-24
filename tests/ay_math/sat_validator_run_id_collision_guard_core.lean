-- SAT-COMP validator run-id collision guard core.
--
-- Public SAT/UNSAT claims require unique run-id evidence, work-directory
-- identity, artifact namespace separation, checker transcript, benchmark
-- fingerprint, solver build evidence, archive manifest, no-claim fallback, and
-- audit transcript to agree.  Run-id or namespace collisions become no-claim
-- recompute obligations rather than public semantic answers.

def ay_ricg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ricg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ricg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_ricg_disj satFact (ay_ricg_disj unsatFact noClaimFact)

def ay_ricg_unique_run_contract
    (uniqueRunIdManifest workDirectoryDigest artifactNamespaceLedger
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (uniqueRunIdManifest -> workDirectoryDigest ->
      artifactNamespaceLedger -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> noClaimFallback ->
      auditTranscript -> result) ->
    result

def ay_ricg_sat_publication
    (runContract acceptedUniqueRun checkedModel originalModel : Prop) : Prop :=
  ay_ricg_conj runContract
    (ay_ricg_conj acceptedUniqueRun
      (ay_ricg_conj checkedModel originalModel))

def ay_ricg_unsat_publication
    (runContract acceptedUniqueRun checkedProof originalEmptyClause : Prop) :
    Prop :=
  ay_ricg_conj runContract
    (ay_ricg_conj acceptedUniqueRun
      (ay_ricg_conj checkedProof originalEmptyClause))

def ay_ricg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_ricg_conj reason (ay_ricg_conj fallbackPath auditTrail)

def ay_ricg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_ricg_conj reason
    (ay_ricg_conj (satFact -> False) (unsatFact -> False))

def ay_ricg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_ricg_conj reason
    (ay_ricg_conj fallbackPath recomputeObligation)

def ay_ricg_run_id_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_ricg_conj
    (ay_ricg_blocked_publication satFact unsatFact reason)
    (ay_ricg_recompute reason fallbackPath recomputeObligation)

theorem ay_ricg_conj_intro (left right : Prop) :
    left -> right -> ay_ricg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ricg_conj_left (left right : Prop) :
    ay_ricg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ricg_conj_right (left right : Prop) :
    ay_ricg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ricg_disj_left (left right : Prop) :
    left -> ay_ricg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ricg_disj_right (left right : Prop) :
    right -> ay_ricg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ricg_unique_run_contract_intro
    (uniqueRunIdManifest workDirectoryDigest artifactNamespaceLedger
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    uniqueRunIdManifest -> workDirectoryDigest -> artifactNamespaceLedger ->
    checkerTranscript -> benchmarkFingerprint -> solverBuildEvidence ->
    archiveManifest -> noClaimFallback -> auditTranscript ->
    ay_ricg_unique_run_contract uniqueRunIdManifest workDirectoryDigest
      artifactNamespaceLedger checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :=
  fun runProof workdirProof namespaceProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof result build =>
    build runProof workdirProof namespaceProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof

theorem ay_ricg_contract_run_id
    (uniqueRunIdManifest workDirectoryDigest artifactNamespaceLedger
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_ricg_unique_run_contract uniqueRunIdManifest workDirectoryDigest
      artifactNamespaceLedger checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    uniqueRunIdManifest :=
  fun contract =>
    contract uniqueRunIdManifest
      (fun runProof _workdirProof _namespaceProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => runProof)

theorem ay_ricg_contract_workdir
    (uniqueRunIdManifest workDirectoryDigest artifactNamespaceLedger
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_ricg_unique_run_contract uniqueRunIdManifest workDirectoryDigest
      artifactNamespaceLedger checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    workDirectoryDigest :=
  fun contract =>
    contract workDirectoryDigest
      (fun _runProof workdirProof _namespaceProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => workdirProof)

theorem ay_ricg_contract_namespace
    (uniqueRunIdManifest workDirectoryDigest artifactNamespaceLedger
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_ricg_unique_run_contract uniqueRunIdManifest workDirectoryDigest
      artifactNamespaceLedger checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    artifactNamespaceLedger :=
  fun contract =>
    contract artifactNamespaceLedger
      (fun _runProof _workdirProof namespaceProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => namespaceProof)

theorem ay_ricg_contract_checker
    (uniqueRunIdManifest workDirectoryDigest artifactNamespaceLedger
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_ricg_unique_run_contract uniqueRunIdManifest workDirectoryDigest
      artifactNamespaceLedger checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _runProof _workdirProof _namespaceProof checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_ricg_contract_fingerprint
    (uniqueRunIdManifest workDirectoryDigest artifactNamespaceLedger
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_ricg_unique_run_contract uniqueRunIdManifest workDirectoryDigest
      artifactNamespaceLedger checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _runProof _workdirProof _namespaceProof _checkerProof
          fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_ricg_contract_build
    (uniqueRunIdManifest workDirectoryDigest artifactNamespaceLedger
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_ricg_unique_run_contract uniqueRunIdManifest workDirectoryDigest
      artifactNamespaceLedger checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _runProof _workdirProof _namespaceProof _checkerProof
          _fingerprintProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_ricg_contract_archive
    (uniqueRunIdManifest workDirectoryDigest artifactNamespaceLedger
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_ricg_unique_run_contract uniqueRunIdManifest workDirectoryDigest
      artifactNamespaceLedger checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _runProof _workdirProof _namespaceProof _checkerProof
          _fingerprintProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_ricg_contract_fallback
    (uniqueRunIdManifest workDirectoryDigest artifactNamespaceLedger
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_ricg_unique_run_contract uniqueRunIdManifest workDirectoryDigest
      artifactNamespaceLedger checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _runProof _workdirProof _namespaceProof _checkerProof
          _fingerprintProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_ricg_contract_audit
    (uniqueRunIdManifest workDirectoryDigest artifactNamespaceLedger
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_ricg_unique_run_contract uniqueRunIdManifest workDirectoryDigest
      artifactNamespaceLedger checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _runProof _workdirProof _namespaceProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_ricg_sat_publication_intro
    (runContract acceptedUniqueRun checkedModel originalModel : Prop) :
    runContract -> acceptedUniqueRun -> checkedModel -> originalModel ->
    ay_ricg_sat_publication runContract acceptedUniqueRun checkedModel
      originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_ricg_conj_intro runContract
      (ay_ricg_conj acceptedUniqueRun
        (ay_ricg_conj checkedModel originalModel))
      contractProof
      (ay_ricg_conj_intro acceptedUniqueRun
        (ay_ricg_conj checkedModel originalModel)
        acceptedProof
        (ay_ricg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_ricg_sat_publication_run_contract
    (runContract acceptedUniqueRun checkedModel originalModel : Prop) :
    ay_ricg_sat_publication runContract acceptedUniqueRun checkedModel
      originalModel ->
    runContract :=
  fun publication =>
    ay_ricg_conj_left runContract
      (ay_ricg_conj acceptedUniqueRun
        (ay_ricg_conj checkedModel originalModel))
      publication

theorem ay_ricg_sat_publication_original_model
    (runContract acceptedUniqueRun checkedModel originalModel : Prop) :
    ay_ricg_sat_publication runContract acceptedUniqueRun checkedModel
      originalModel ->
    originalModel :=
  fun publication =>
    ay_ricg_conj_right checkedModel originalModel
      (ay_ricg_conj_right acceptedUniqueRun
        (ay_ricg_conj checkedModel originalModel)
        (ay_ricg_conj_right runContract
          (ay_ricg_conj acceptedUniqueRun
            (ay_ricg_conj checkedModel originalModel))
          publication))

theorem ay_ricg_unsat_publication_intro
    (runContract acceptedUniqueRun checkedProof originalEmptyClause : Prop) :
    runContract -> acceptedUniqueRun -> checkedProof -> originalEmptyClause ->
    ay_ricg_unsat_publication runContract acceptedUniqueRun checkedProof
      originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_ricg_conj_intro runContract
      (ay_ricg_conj acceptedUniqueRun
        (ay_ricg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_ricg_conj_intro acceptedUniqueRun
        (ay_ricg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_ricg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_ricg_unsat_publication_run_contract
    (runContract acceptedUniqueRun checkedProof originalEmptyClause : Prop) :
    ay_ricg_unsat_publication runContract acceptedUniqueRun checkedProof
      originalEmptyClause ->
    runContract :=
  fun publication =>
    ay_ricg_conj_left runContract
      (ay_ricg_conj acceptedUniqueRun
        (ay_ricg_conj checkedProof originalEmptyClause))
      publication

theorem ay_ricg_unsat_publication_original_empty_clause
    (runContract acceptedUniqueRun checkedProof originalEmptyClause : Prop) :
    ay_ricg_unsat_publication runContract acceptedUniqueRun checkedProof
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_ricg_conj_right checkedProof originalEmptyClause
      (ay_ricg_conj_right acceptedUniqueRun
        (ay_ricg_conj checkedProof originalEmptyClause)
        (ay_ricg_conj_right runContract
          (ay_ricg_conj acceptedUniqueRun
            (ay_ricg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_ricg_accepted_unique_run_sat_passes_publication
    (runContract acceptedUniqueRun checkedModel originalModel : Prop) :
    ay_ricg_sat_publication runContract acceptedUniqueRun checkedModel
      originalModel ->
    ay_ricg_public_result originalModel False False :=
  fun publication =>
    ay_ricg_disj_left originalModel (ay_ricg_disj False False)
      (ay_ricg_sat_publication_original_model runContract acceptedUniqueRun
        checkedModel originalModel publication)

theorem ay_ricg_accepted_unique_run_unsat_passes_publication
    (runContract acceptedUniqueRun checkedProof originalEmptyClause : Prop) :
    ay_ricg_unsat_publication runContract acceptedUniqueRun checkedProof
      originalEmptyClause ->
    ay_ricg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_ricg_disj_right False (ay_ricg_disj originalEmptyClause False)
      (ay_ricg_disj_left originalEmptyClause False
        (ay_ricg_unsat_publication_original_empty_clause runContract
          acceptedUniqueRun checkedProof originalEmptyClause publication))

theorem ay_ricg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_ricg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_ricg_conj_intro reason (ay_ricg_conj fallbackPath auditTrail)
      reasonProof
      (ay_ricg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_ricg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ricg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_ricg_conj_intro reason
      (ay_ricg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_ricg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_ricg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_ricg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_ricg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_ricg_conj_right reason
        (ay_ricg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_ricg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_ricg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_ricg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_ricg_conj_right reason
        (ay_ricg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_ricg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_ricg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_ricg_conj_intro reason
      (ay_ricg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_ricg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_ricg_run_id_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ricg_blocked_publication satFact unsatFact reason ->
    ay_ricg_recompute reason fallbackPath recomputeObligation ->
    ay_ricg_run_id_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_ricg_conj_intro
      (ay_ricg_blocked_publication satFact unsatFact reason)
      (ay_ricg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_ricg_run_id_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ricg_run_id_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_ricg_blocked_publication_no_sat satFact unsatFact reason
      (ay_ricg_conj_left
        (ay_ricg_blocked_publication satFact unsatFact reason)
        (ay_ricg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ricg_run_id_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ricg_run_id_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_ricg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_ricg_conj_left
        (ay_ricg_blocked_publication satFact unsatFact reason)
        (ay_ricg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ricg_run_id_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ricg_run_id_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_ricg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_ricg_conj_right
      (ay_ricg_blocked_publication satFact unsatFact reason)
      (ay_ricg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_ricg_duplicate_run_id_forces_no_claim
    (satFact unsatFact duplicateRunId fallbackPath auditTrail
      recomputeObligation : Prop) :
    duplicateRunId -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_ricg_no_claim duplicateRunId fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_ricg_no_claim_intro duplicateRunId fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ricg_workdir_collision_forces_recompute
    (satFact unsatFact workdirCollision fallbackPath recomputeObligation :
      Prop) :
    workdirCollision -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_ricg_run_id_failure satFact unsatFact workdirCollision fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_ricg_run_id_failure_intro satFact unsatFact workdirCollision
      fallbackPath recomputeObligation
      (ay_ricg_blocked_publication_intro satFact unsatFact workdirCollision
        reasonProof noSat noUnsat)
      (ay_ricg_recompute_intro workdirCollision fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_ricg_artifact_namespace_collision_forces_no_claim
    (satFact unsatFact artifactNamespaceCollision fallbackPath auditTrail
      recomputeObligation : Prop) :
    artifactNamespaceCollision -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_ricg_no_claim artifactNamespaceCollision fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_ricg_no_claim_intro artifactNamespaceCollision fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ricg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_ricg_no_claim checkerMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_ricg_no_claim_intro checkerMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ricg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_ricg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_ricg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ricg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_ricg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_ricg_no_claim_intro buildMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ricg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_ricg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_ricg_no_claim_intro archiveMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ricg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivation fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivation -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_ricg_no_claim fallbackActivation fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_ricg_no_claim_intro fallbackActivation fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_ricg_failed_run_id_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ricg_run_id_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_ricg_run_id_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_ricg_failed_run_id_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ricg_run_id_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_ricg_run_id_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_ricg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_ricg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_ricg_conj_left reason (ay_ricg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_ricg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_ricg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_ricg_conj_left reason (ay_ricg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
