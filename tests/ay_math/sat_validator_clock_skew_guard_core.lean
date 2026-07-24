-- SAT-COMP validator clock-skew/run-timestamp guard core.
--
-- Public SAT/UNSAT claims require timestamp evidence, monotonic clock evidence,
-- wall/cpu consistency, resource-limit evidence, checker transcript, benchmark
-- fingerprint, solver build evidence, archive manifest, fallback, and audit
-- transcript to agree.

def ay_cskg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cskg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cskg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_cskg_disj satFact (ay_cskg_disj unsatFact noClaimFact)

def ay_cskg_clock_contract
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) : Prop :=
  forall result : Prop,
    (runTimestampManifest -> monotonicClockLedger ->
      wallCpuTimeConsistencyWitness -> resourceLimitManifest ->
      checkerTranscript -> benchmarkFingerprint -> solverBuildEvidence ->
      archiveManifest -> fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_cskg_sat_publication
    (clockContract acceptedClockEvidence checkedModel originalModel : Prop) :
    Prop :=
  ay_cskg_conj clockContract
    (ay_cskg_conj acceptedClockEvidence
      (ay_cskg_conj checkedModel originalModel))

def ay_cskg_unsat_publication
    (clockContract acceptedClockEvidence checkedProof originalEmptyClause :
      Prop) : Prop :=
  ay_cskg_conj clockContract
    (ay_cskg_conj acceptedClockEvidence
      (ay_cskg_conj checkedProof originalEmptyClause))

def ay_cskg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_cskg_conj reason (ay_cskg_conj fallbackPath auditTrail)

def ay_cskg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_cskg_conj reason
    (ay_cskg_conj (satFact -> False) (unsatFact -> False))

def ay_cskg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_cskg_conj reason
    (ay_cskg_conj fallbackPath recomputeObligation)

def ay_cskg_clock_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_cskg_conj
    (ay_cskg_blocked_publication satFact unsatFact reason)
    (ay_cskg_recompute reason fallbackPath recomputeObligation)

theorem ay_cskg_conj_intro (left right : Prop) :
    left -> right -> ay_cskg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_cskg_conj_left (left right : Prop) :
    ay_cskg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_cskg_conj_right (left right : Prop) :
    ay_cskg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_cskg_disj_left (left right : Prop) :
    left -> ay_cskg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_cskg_disj_right (left right : Prop) :
    right -> ay_cskg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_cskg_clock_contract_intro
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    runTimestampManifest -> monotonicClockLedger ->
    wallCpuTimeConsistencyWitness -> resourceLimitManifest ->
    checkerTranscript -> benchmarkFingerprint -> solverBuildEvidence ->
    archiveManifest -> fallbackNoClaimPath -> auditTranscript ->
    ay_cskg_clock_contract runTimestampManifest monotonicClockLedger
      wallCpuTimeConsistencyWitness resourceLimitManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript :=
  fun timestampProof monotonicProof wallCpuProof resourceProof checkerProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof result
      build =>
    build timestampProof monotonicProof wallCpuProof resourceProof
      checkerProof fingerprintProof buildProof archiveProof fallbackProof
      auditProof

theorem ay_cskg_contract_timestamp
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_cskg_clock_contract runTimestampManifest monotonicClockLedger
      wallCpuTimeConsistencyWitness resourceLimitManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    runTimestampManifest :=
  fun contract =>
    contract runTimestampManifest
      (fun timestampProof _monotonicProof _wallCpuProof _resourceProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => timestampProof)

theorem ay_cskg_contract_monotonic
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_cskg_clock_contract runTimestampManifest monotonicClockLedger
      wallCpuTimeConsistencyWitness resourceLimitManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    monotonicClockLedger :=
  fun contract =>
    contract monotonicClockLedger
      (fun _timestampProof monotonicProof _wallCpuProof _resourceProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => monotonicProof)

theorem ay_cskg_contract_wall_cpu
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_cskg_clock_contract runTimestampManifest monotonicClockLedger
      wallCpuTimeConsistencyWitness resourceLimitManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    wallCpuTimeConsistencyWitness :=
  fun contract =>
    contract wallCpuTimeConsistencyWitness
      (fun _timestampProof _monotonicProof wallCpuProof _resourceProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => wallCpuProof)

theorem ay_cskg_contract_resource
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_cskg_clock_contract runTimestampManifest monotonicClockLedger
      wallCpuTimeConsistencyWitness resourceLimitManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    resourceLimitManifest :=
  fun contract =>
    contract resourceLimitManifest
      (fun _timestampProof _monotonicProof _wallCpuProof resourceProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => resourceProof)

theorem ay_cskg_contract_checker
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_cskg_clock_contract runTimestampManifest monotonicClockLedger
      wallCpuTimeConsistencyWitness resourceLimitManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _timestampProof _monotonicProof _wallCpuProof _resourceProof
          checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => checkerProof)

theorem ay_cskg_contract_fingerprint
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_cskg_clock_contract runTimestampManifest monotonicClockLedger
      wallCpuTimeConsistencyWitness resourceLimitManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _timestampProof _monotonicProof _wallCpuProof _resourceProof
          _checkerProof fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => fingerprintProof)

theorem ay_cskg_contract_build
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_cskg_clock_contract runTimestampManifest monotonicClockLedger
      wallCpuTimeConsistencyWitness resourceLimitManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _timestampProof _monotonicProof _wallCpuProof _resourceProof
          _checkerProof _fingerprintProof buildProof _archiveProof
          _fallbackProof _auditProof => buildProof)

theorem ay_cskg_contract_archive
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_cskg_clock_contract runTimestampManifest monotonicClockLedger
      wallCpuTimeConsistencyWitness resourceLimitManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _timestampProof _monotonicProof _wallCpuProof _resourceProof
          _checkerProof _fingerprintProof _buildProof archiveProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_cskg_contract_fallback
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_cskg_clock_contract runTimestampManifest monotonicClockLedger
      wallCpuTimeConsistencyWitness resourceLimitManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _timestampProof _monotonicProof _wallCpuProof _resourceProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_cskg_contract_audit
    (runTimestampManifest monotonicClockLedger wallCpuTimeConsistencyWitness
      resourceLimitManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_cskg_clock_contract runTimestampManifest monotonicClockLedger
      wallCpuTimeConsistencyWitness resourceLimitManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _timestampProof _monotonicProof _wallCpuProof _resourceProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof auditProof => auditProof)

theorem ay_cskg_sat_publication_intro
    (clockContract acceptedClockEvidence checkedModel originalModel : Prop) :
    clockContract -> acceptedClockEvidence -> checkedModel -> originalModel ->
    ay_cskg_sat_publication clockContract acceptedClockEvidence checkedModel
      originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_cskg_conj_intro clockContract
      (ay_cskg_conj acceptedClockEvidence
        (ay_cskg_conj checkedModel originalModel))
      contractProof
      (ay_cskg_conj_intro acceptedClockEvidence
        (ay_cskg_conj checkedModel originalModel)
        acceptedProof
        (ay_cskg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_cskg_unsat_publication_intro
    (clockContract acceptedClockEvidence checkedProof originalEmptyClause :
      Prop) :
    clockContract -> acceptedClockEvidence -> checkedProof ->
    originalEmptyClause ->
    ay_cskg_unsat_publication clockContract acceptedClockEvidence checkedProof
      originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_cskg_conj_intro clockContract
      (ay_cskg_conj acceptedClockEvidence
        (ay_cskg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_cskg_conj_intro acceptedClockEvidence
        (ay_cskg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_cskg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_cskg_sat_publication_original_model
    (clockContract acceptedClockEvidence checkedModel originalModel : Prop) :
    ay_cskg_sat_publication clockContract acceptedClockEvidence checkedModel
      originalModel ->
    originalModel :=
  fun publication =>
    ay_cskg_conj_right checkedModel originalModel
      (ay_cskg_conj_right acceptedClockEvidence
        (ay_cskg_conj checkedModel originalModel)
        (ay_cskg_conj_right clockContract
          (ay_cskg_conj acceptedClockEvidence
            (ay_cskg_conj checkedModel originalModel))
          publication))

theorem ay_cskg_unsat_publication_original_empty_clause
    (clockContract acceptedClockEvidence checkedProof originalEmptyClause :
      Prop) :
    ay_cskg_unsat_publication clockContract acceptedClockEvidence checkedProof
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_cskg_conj_right checkedProof originalEmptyClause
      (ay_cskg_conj_right acceptedClockEvidence
        (ay_cskg_conj checkedProof originalEmptyClause)
        (ay_cskg_conj_right clockContract
          (ay_cskg_conj acceptedClockEvidence
            (ay_cskg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_cskg_accepted_clock_supports_sat_publication
    (clockContract acceptedClockEvidence checkedModel originalModel : Prop) :
    ay_cskg_sat_publication clockContract acceptedClockEvidence checkedModel
      originalModel ->
    ay_cskg_public_result originalModel False False :=
  fun publication =>
    ay_cskg_disj_left originalModel (ay_cskg_disj False False)
      (ay_cskg_sat_publication_original_model clockContract
        acceptedClockEvidence checkedModel originalModel publication)

theorem ay_cskg_accepted_clock_supports_unsat_publication
    (clockContract acceptedClockEvidence checkedProof originalEmptyClause :
      Prop) :
    ay_cskg_unsat_publication clockContract acceptedClockEvidence checkedProof
      originalEmptyClause ->
    ay_cskg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_cskg_disj_right False (ay_cskg_disj originalEmptyClause False)
      (ay_cskg_disj_left originalEmptyClause False
        (ay_cskg_unsat_publication_original_empty_clause clockContract
          acceptedClockEvidence checkedProof originalEmptyClause publication))

theorem ay_cskg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_cskg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_cskg_conj_intro reason (ay_cskg_conj fallbackPath auditTrail)
      reasonProof
      (ay_cskg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_cskg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_cskg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_cskg_conj_intro reason
      (ay_cskg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_cskg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_cskg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_cskg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_cskg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_cskg_conj_right reason
        (ay_cskg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_cskg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_cskg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_cskg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_cskg_conj_right reason
        (ay_cskg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_cskg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_cskg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_cskg_conj_intro reason
      (ay_cskg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_cskg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_cskg_clock_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cskg_blocked_publication satFact unsatFact reason ->
    ay_cskg_recompute reason fallbackPath recomputeObligation ->
    ay_cskg_clock_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_cskg_conj_intro
      (ay_cskg_blocked_publication satFact unsatFact reason)
      (ay_cskg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_cskg_clock_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cskg_clock_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_cskg_blocked_publication_no_sat satFact unsatFact reason
      (ay_cskg_conj_left
        (ay_cskg_blocked_publication satFact unsatFact reason)
        (ay_cskg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_cskg_clock_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cskg_clock_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_cskg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_cskg_conj_left
        (ay_cskg_blocked_publication satFact unsatFact reason)
        (ay_cskg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_cskg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cskg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_cskg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_cskg_timestamp_mismatch_forces_no_claim
    (satFact unsatFact timestampMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    timestampMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cskg_no_claim timestampMismatch fallbackPath auditTrail :=
  ay_cskg_mismatch_forces_no_claim satFact unsatFact timestampMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cskg_monotonic_mismatch_forces_no_claim
    (satFact unsatFact monotonicMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    monotonicMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cskg_no_claim monotonicMismatch fallbackPath auditTrail :=
  ay_cskg_mismatch_forces_no_claim satFact unsatFact monotonicMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cskg_wall_cpu_mismatch_forces_no_claim
    (satFact unsatFact wallCpuMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    wallCpuMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cskg_no_claim wallCpuMismatch fallbackPath auditTrail :=
  ay_cskg_mismatch_forces_no_claim satFact unsatFact wallCpuMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cskg_resource_mismatch_forces_no_claim
    (satFact unsatFact resourceMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    resourceMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cskg_no_claim resourceMismatch fallbackPath auditTrail :=
  ay_cskg_mismatch_forces_no_claim satFact unsatFact resourceMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cskg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cskg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_cskg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cskg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cskg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_cskg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cskg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cskg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_cskg_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cskg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cskg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_cskg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cskg_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cskg_no_claim auditMismatch fallbackPath auditTrail :=
  ay_cskg_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cskg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_cskg_clock_failure satFact unsatFact fallbackActivation fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_cskg_clock_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_cskg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_cskg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_cskg_failed_clock_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cskg_clock_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_cskg_clock_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_cskg_failed_clock_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cskg_clock_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_cskg_clock_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_cskg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_cskg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_cskg_conj_left reason (ay_cskg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_cskg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_cskg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_cskg_conj_left reason (ay_cskg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
