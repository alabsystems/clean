-- SAT-COMP validator clock/provenance guard core.
--
-- Public SAT/UNSAT claims require monotonic clock evidence, resource ledgers,
-- command/checker provenance, input identity, archive evidence, fallback, and
-- audit transcript to agree.  Clock or provenance failures become no-claim
-- recompute obligations rather than public semantic answers.

def ay_cpkg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cpkg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cpkg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_cpkg_disj satFact (ay_cpkg_disj unsatFact noClaimFact)

def ay_cpkg_clock_provenance_contract
    (monotonicClockTranscript cpuWallResourceLedger solverCommandDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (monotonicClockTranscript -> cpuWallResourceLedger ->
      solverCommandDigest -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> noClaimFallback ->
      auditTranscript -> result) ->
    result

def ay_cpkg_sat_publication
    (provenanceContract acceptedClockProvenance checkedModel
      originalModel : Prop) : Prop :=
  ay_cpkg_conj provenanceContract
    (ay_cpkg_conj acceptedClockProvenance
      (ay_cpkg_conj checkedModel originalModel))

def ay_cpkg_unsat_publication
    (provenanceContract acceptedClockProvenance checkedProof
      originalEmptyClause : Prop) : Prop :=
  ay_cpkg_conj provenanceContract
    (ay_cpkg_conj acceptedClockProvenance
      (ay_cpkg_conj checkedProof originalEmptyClause))

def ay_cpkg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_cpkg_conj reason (ay_cpkg_conj fallbackPath auditTrail)

def ay_cpkg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_cpkg_conj reason
    (ay_cpkg_conj (satFact -> False) (unsatFact -> False))

def ay_cpkg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_cpkg_conj reason
    (ay_cpkg_conj fallbackPath recomputeObligation)

def ay_cpkg_provenance_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_cpkg_conj
    (ay_cpkg_blocked_publication satFact unsatFact reason)
    (ay_cpkg_recompute reason fallbackPath recomputeObligation)

theorem ay_cpkg_conj_intro (left right : Prop) :
    left -> right -> ay_cpkg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_cpkg_conj_left (left right : Prop) :
    ay_cpkg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_cpkg_conj_right (left right : Prop) :
    ay_cpkg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_cpkg_disj_left (left right : Prop) :
    left -> ay_cpkg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_cpkg_disj_right (left right : Prop) :
    right -> ay_cpkg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_cpkg_clock_provenance_contract_intro
    (monotonicClockTranscript cpuWallResourceLedger solverCommandDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    monotonicClockTranscript -> cpuWallResourceLedger ->
    solverCommandDigest -> checkerTranscript -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> noClaimFallback ->
    auditTranscript ->
    ay_cpkg_clock_provenance_contract monotonicClockTranscript
      cpuWallResourceLedger solverCommandDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript :=
  fun clockProof ledgerProof commandProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof result build =>
    build clockProof ledgerProof commandProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof

theorem ay_cpkg_contract_clock
    (monotonicClockTranscript cpuWallResourceLedger solverCommandDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_cpkg_clock_provenance_contract monotonicClockTranscript
      cpuWallResourceLedger solverCommandDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    monotonicClockTranscript :=
  fun contract =>
    contract monotonicClockTranscript
      (fun clockProof _ledgerProof _commandProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => clockProof)

theorem ay_cpkg_contract_resource_ledger
    (monotonicClockTranscript cpuWallResourceLedger solverCommandDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_cpkg_clock_provenance_contract monotonicClockTranscript
      cpuWallResourceLedger solverCommandDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    cpuWallResourceLedger :=
  fun contract =>
    contract cpuWallResourceLedger
      (fun _clockProof ledgerProof _commandProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => ledgerProof)

theorem ay_cpkg_contract_command
    (monotonicClockTranscript cpuWallResourceLedger solverCommandDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_cpkg_clock_provenance_contract monotonicClockTranscript
      cpuWallResourceLedger solverCommandDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    solverCommandDigest :=
  fun contract =>
    contract solverCommandDigest
      (fun _clockProof _ledgerProof commandProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => commandProof)

theorem ay_cpkg_contract_checker
    (monotonicClockTranscript cpuWallResourceLedger solverCommandDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_cpkg_clock_provenance_contract monotonicClockTranscript
      cpuWallResourceLedger solverCommandDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _clockProof _ledgerProof _commandProof checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_cpkg_contract_fingerprint
    (monotonicClockTranscript cpuWallResourceLedger solverCommandDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_cpkg_clock_provenance_contract monotonicClockTranscript
      cpuWallResourceLedger solverCommandDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _clockProof _ledgerProof _commandProof _checkerProof
          fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_cpkg_contract_build
    (monotonicClockTranscript cpuWallResourceLedger solverCommandDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_cpkg_clock_provenance_contract monotonicClockTranscript
      cpuWallResourceLedger solverCommandDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _clockProof _ledgerProof _commandProof _checkerProof
          _fingerprintProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_cpkg_contract_archive
    (monotonicClockTranscript cpuWallResourceLedger solverCommandDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_cpkg_clock_provenance_contract monotonicClockTranscript
      cpuWallResourceLedger solverCommandDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _clockProof _ledgerProof _commandProof _checkerProof
          _fingerprintProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_cpkg_contract_fallback
    (monotonicClockTranscript cpuWallResourceLedger solverCommandDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_cpkg_clock_provenance_contract monotonicClockTranscript
      cpuWallResourceLedger solverCommandDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _clockProof _ledgerProof _commandProof _checkerProof
          _fingerprintProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_cpkg_contract_audit
    (monotonicClockTranscript cpuWallResourceLedger solverCommandDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_cpkg_clock_provenance_contract monotonicClockTranscript
      cpuWallResourceLedger solverCommandDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _clockProof _ledgerProof _commandProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_cpkg_sat_publication_intro
    (provenanceContract acceptedClockProvenance checkedModel
      originalModel : Prop) :
    provenanceContract -> acceptedClockProvenance -> checkedModel ->
    originalModel ->
    ay_cpkg_sat_publication provenanceContract acceptedClockProvenance
      checkedModel originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_cpkg_conj_intro provenanceContract
      (ay_cpkg_conj acceptedClockProvenance
        (ay_cpkg_conj checkedModel originalModel))
      contractProof
      (ay_cpkg_conj_intro acceptedClockProvenance
        (ay_cpkg_conj checkedModel originalModel)
        acceptedProof
        (ay_cpkg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_cpkg_sat_publication_provenance
    (provenanceContract acceptedClockProvenance checkedModel
      originalModel : Prop) :
    ay_cpkg_sat_publication provenanceContract acceptedClockProvenance
      checkedModel originalModel ->
    provenanceContract :=
  fun publication =>
    ay_cpkg_conj_left provenanceContract
      (ay_cpkg_conj acceptedClockProvenance
        (ay_cpkg_conj checkedModel originalModel))
      publication

theorem ay_cpkg_sat_publication_original_model
    (provenanceContract acceptedClockProvenance checkedModel
      originalModel : Prop) :
    ay_cpkg_sat_publication provenanceContract acceptedClockProvenance
      checkedModel originalModel ->
    originalModel :=
  fun publication =>
    ay_cpkg_conj_right checkedModel originalModel
      (ay_cpkg_conj_right acceptedClockProvenance
        (ay_cpkg_conj checkedModel originalModel)
        (ay_cpkg_conj_right provenanceContract
          (ay_cpkg_conj acceptedClockProvenance
            (ay_cpkg_conj checkedModel originalModel))
          publication))

theorem ay_cpkg_unsat_publication_intro
    (provenanceContract acceptedClockProvenance checkedProof
      originalEmptyClause : Prop) :
    provenanceContract -> acceptedClockProvenance -> checkedProof ->
    originalEmptyClause ->
    ay_cpkg_unsat_publication provenanceContract acceptedClockProvenance
      checkedProof originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_cpkg_conj_intro provenanceContract
      (ay_cpkg_conj acceptedClockProvenance
        (ay_cpkg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_cpkg_conj_intro acceptedClockProvenance
        (ay_cpkg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_cpkg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_cpkg_unsat_publication_provenance
    (provenanceContract acceptedClockProvenance checkedProof
      originalEmptyClause : Prop) :
    ay_cpkg_unsat_publication provenanceContract acceptedClockProvenance
      checkedProof originalEmptyClause ->
    provenanceContract :=
  fun publication =>
    ay_cpkg_conj_left provenanceContract
      (ay_cpkg_conj acceptedClockProvenance
        (ay_cpkg_conj checkedProof originalEmptyClause))
      publication

theorem ay_cpkg_unsat_publication_original_empty_clause
    (provenanceContract acceptedClockProvenance checkedProof
      originalEmptyClause : Prop) :
    ay_cpkg_unsat_publication provenanceContract acceptedClockProvenance
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_cpkg_conj_right checkedProof originalEmptyClause
      (ay_cpkg_conj_right acceptedClockProvenance
        (ay_cpkg_conj checkedProof originalEmptyClause)
        (ay_cpkg_conj_right provenanceContract
          (ay_cpkg_conj acceptedClockProvenance
            (ay_cpkg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_cpkg_accepted_provenance_sat_passes_publication
    (provenanceContract acceptedClockProvenance checkedModel
      originalModel : Prop) :
    ay_cpkg_sat_publication provenanceContract acceptedClockProvenance
      checkedModel originalModel ->
    ay_cpkg_public_result originalModel False False :=
  fun publication =>
    ay_cpkg_disj_left originalModel (ay_cpkg_disj False False)
      (ay_cpkg_sat_publication_original_model provenanceContract
        acceptedClockProvenance checkedModel originalModel publication)

theorem ay_cpkg_accepted_provenance_unsat_passes_publication
    (provenanceContract acceptedClockProvenance checkedProof
      originalEmptyClause : Prop) :
    ay_cpkg_unsat_publication provenanceContract acceptedClockProvenance
      checkedProof originalEmptyClause ->
    ay_cpkg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_cpkg_disj_right False (ay_cpkg_disj originalEmptyClause False)
      (ay_cpkg_disj_left originalEmptyClause False
        (ay_cpkg_unsat_publication_original_empty_clause provenanceContract
          acceptedClockProvenance checkedProof originalEmptyClause
          publication))

theorem ay_cpkg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_cpkg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_cpkg_conj_intro reason (ay_cpkg_conj fallbackPath auditTrail)
      reasonProof
      (ay_cpkg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_cpkg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_cpkg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_cpkg_conj_intro reason
      (ay_cpkg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_cpkg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_cpkg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_cpkg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_cpkg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_cpkg_conj_right reason
        (ay_cpkg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_cpkg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_cpkg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_cpkg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_cpkg_conj_right reason
        (ay_cpkg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_cpkg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_cpkg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_cpkg_conj_intro reason
      (ay_cpkg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_cpkg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_cpkg_provenance_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cpkg_blocked_publication satFact unsatFact reason ->
    ay_cpkg_recompute reason fallbackPath recomputeObligation ->
    ay_cpkg_provenance_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_cpkg_conj_intro
      (ay_cpkg_blocked_publication satFact unsatFact reason)
      (ay_cpkg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_cpkg_provenance_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cpkg_provenance_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_cpkg_blocked_publication_no_sat satFact unsatFact reason
      (ay_cpkg_conj_left
        (ay_cpkg_blocked_publication satFact unsatFact reason)
        (ay_cpkg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_cpkg_provenance_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cpkg_provenance_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_cpkg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_cpkg_conj_left
        (ay_cpkg_blocked_publication satFact unsatFact reason)
        (ay_cpkg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_cpkg_provenance_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cpkg_provenance_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_cpkg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_cpkg_conj_right
      (ay_cpkg_blocked_publication satFact unsatFact reason)
      (ay_cpkg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_cpkg_missing_clock_forces_no_claim
    (satFact unsatFact missingOrNonmonotoneClock fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingOrNonmonotoneClock -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cpkg_no_claim missingOrNonmonotoneClock fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_cpkg_no_claim_intro missingOrNonmonotoneClock fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_cpkg_nonmonotone_clock_forces_recompute
    (satFact unsatFact nonmonotoneClock fallbackPath recomputeObligation :
      Prop) :
    nonmonotoneClock -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_cpkg_provenance_failure satFact unsatFact nonmonotoneClock
      fallbackPath recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_cpkg_provenance_failure_intro satFact unsatFact nonmonotoneClock
      fallbackPath recomputeObligation
      (ay_cpkg_blocked_publication_intro satFact unsatFact nonmonotoneClock
        reasonProof noSat noUnsat)
      (ay_cpkg_recompute_intro nonmonotoneClock fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_cpkg_resource_ledger_drift_forces_no_claim
    (satFact unsatFact resourceLedgerDrift fallbackPath auditTrail
      recomputeObligation : Prop) :
    resourceLedgerDrift -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cpkg_no_claim resourceLedgerDrift fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_cpkg_no_claim_intro resourceLedgerDrift fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_cpkg_command_mismatch_forces_no_claim
    (satFact unsatFact commandMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    commandMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cpkg_no_claim commandMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_cpkg_no_claim_intro commandMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_cpkg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cpkg_no_claim checkerMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_cpkg_no_claim_intro checkerMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_cpkg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cpkg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_cpkg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_cpkg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cpkg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_cpkg_no_claim_intro buildMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_cpkg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cpkg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_cpkg_no_claim_intro archiveMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_cpkg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivation fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivation -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cpkg_no_claim fallbackActivation fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_cpkg_no_claim_intro fallbackActivation fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_cpkg_failed_provenance_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cpkg_provenance_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_cpkg_provenance_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_cpkg_failed_provenance_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cpkg_provenance_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_cpkg_provenance_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_cpkg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_cpkg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_cpkg_conj_left reason (ay_cpkg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_cpkg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_cpkg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_cpkg_conj_left reason (ay_cpkg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
