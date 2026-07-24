-- SAT-COMP validator environment-variable manifest guard core.
--
-- Public SAT/UNSAT claims require environment manifest evidence, whitelisted
-- variables, locale/timezone evidence, thread/process counts, command manifest,
-- checker transcript, benchmark fingerprint, build evidence, archive evidence,
-- fallback, and audit transcript to agree.

def ay_evgg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_evgg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_evgg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_evgg_disj satFact (ay_evgg_disj unsatFact noClaimFact)

def ay_evgg_environment_contract
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (environmentManifestDigest -> whitelistedVariableLedger ->
      localeTimezoneWitness -> threadCountProcessCountWitness ->
      solverCommandManifest -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_evgg_sat_publication
    (environmentContract acceptedEnvironment checkedModel originalModel :
      Prop) : Prop :=
  ay_evgg_conj environmentContract
    (ay_evgg_conj acceptedEnvironment
      (ay_evgg_conj checkedModel originalModel))

def ay_evgg_unsat_publication
    (environmentContract acceptedEnvironment checkedProof
      originalEmptyClause : Prop) : Prop :=
  ay_evgg_conj environmentContract
    (ay_evgg_conj acceptedEnvironment
      (ay_evgg_conj checkedProof originalEmptyClause))

def ay_evgg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_evgg_conj reason (ay_evgg_conj fallbackPath auditTrail)

def ay_evgg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_evgg_conj reason
    (ay_evgg_conj (satFact -> False) (unsatFact -> False))

def ay_evgg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_evgg_conj reason
    (ay_evgg_conj fallbackPath recomputeObligation)

def ay_evgg_environment_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_evgg_conj
    (ay_evgg_blocked_publication satFact unsatFact reason)
    (ay_evgg_recompute reason fallbackPath recomputeObligation)

theorem ay_evgg_conj_intro (left right : Prop) :
    left -> right -> ay_evgg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_evgg_conj_left (left right : Prop) :
    ay_evgg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_evgg_conj_right (left right : Prop) :
    ay_evgg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_evgg_disj_left (left right : Prop) :
    left -> ay_evgg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_evgg_disj_right (left right : Prop) :
    right -> ay_evgg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_evgg_environment_contract_intro
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    environmentManifestDigest -> whitelistedVariableLedger ->
    localeTimezoneWitness -> threadCountProcessCountWitness ->
    solverCommandManifest -> checkerTranscript -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript :=
  fun environmentProof whitelistProof localeProof countProof commandProof
      checkerProof fingerprintProof buildProof archiveProof fallbackProof
      auditProof result build =>
    build environmentProof whitelistProof localeProof countProof commandProof
      checkerProof fingerprintProof buildProof archiveProof fallbackProof
      auditProof

theorem ay_evgg_contract_environment
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    environmentManifestDigest :=
  fun contract =>
    contract environmentManifestDigest
      (fun environmentProof _whitelistProof _localeProof _countProof
          _commandProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => environmentProof)

theorem ay_evgg_contract_whitelist
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    whitelistedVariableLedger :=
  fun contract =>
    contract whitelistedVariableLedger
      (fun _environmentProof whitelistProof _localeProof _countProof
          _commandProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => whitelistProof)

theorem ay_evgg_contract_locale
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    localeTimezoneWitness :=
  fun contract =>
    contract localeTimezoneWitness
      (fun _environmentProof _whitelistProof localeProof _countProof
          _commandProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => localeProof)

theorem ay_evgg_contract_thread_process
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    threadCountProcessCountWitness :=
  fun contract =>
    contract threadCountProcessCountWitness
      (fun _environmentProof _whitelistProof _localeProof countProof
          _commandProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => countProof)

theorem ay_evgg_contract_command
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverCommandManifest :=
  fun contract =>
    contract solverCommandManifest
      (fun _environmentProof _whitelistProof _localeProof _countProof
          commandProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => commandProof)

theorem ay_evgg_contract_checker
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _environmentProof _whitelistProof _localeProof _countProof
          _commandProof checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => checkerProof)

theorem ay_evgg_contract_fingerprint
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _environmentProof _whitelistProof _localeProof _countProof
          _commandProof _checkerProof fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => fingerprintProof)

theorem ay_evgg_contract_build
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _environmentProof _whitelistProof _localeProof _countProof
          _commandProof _checkerProof _fingerprintProof buildProof
          _archiveProof _fallbackProof _auditProof => buildProof)

theorem ay_evgg_contract_archive
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _environmentProof _whitelistProof _localeProof _countProof
          _commandProof _checkerProof _fingerprintProof _buildProof
          archiveProof _fallbackProof _auditProof => archiveProof)

theorem ay_evgg_contract_fallback
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _environmentProof _whitelistProof _localeProof _countProof
          _commandProof _checkerProof _fingerprintProof _buildProof
          _archiveProof fallbackProof _auditProof => fallbackProof)

theorem ay_evgg_contract_audit
    (environmentManifestDigest whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_evgg_environment_contract environmentManifestDigest
      whitelistedVariableLedger localeTimezoneWitness
      threadCountProcessCountWitness solverCommandManifest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _environmentProof _whitelistProof _localeProof _countProof
          _commandProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof auditProof => auditProof)

theorem ay_evgg_sat_publication_intro
    (environmentContract acceptedEnvironment checkedModel originalModel :
      Prop) :
    environmentContract -> acceptedEnvironment -> checkedModel ->
    originalModel ->
    ay_evgg_sat_publication environmentContract acceptedEnvironment
      checkedModel originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_evgg_conj_intro environmentContract
      (ay_evgg_conj acceptedEnvironment
        (ay_evgg_conj checkedModel originalModel))
      contractProof
      (ay_evgg_conj_intro acceptedEnvironment
        (ay_evgg_conj checkedModel originalModel)
        acceptedProof
        (ay_evgg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_evgg_unsat_publication_intro
    (environmentContract acceptedEnvironment checkedProof
      originalEmptyClause : Prop) :
    environmentContract -> acceptedEnvironment -> checkedProof ->
    originalEmptyClause ->
    ay_evgg_unsat_publication environmentContract acceptedEnvironment
      checkedProof originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_evgg_conj_intro environmentContract
      (ay_evgg_conj acceptedEnvironment
        (ay_evgg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_evgg_conj_intro acceptedEnvironment
        (ay_evgg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_evgg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_evgg_sat_publication_original_model
    (environmentContract acceptedEnvironment checkedModel originalModel :
      Prop) :
    ay_evgg_sat_publication environmentContract acceptedEnvironment
      checkedModel originalModel ->
    originalModel :=
  fun publication =>
    ay_evgg_conj_right checkedModel originalModel
      (ay_evgg_conj_right acceptedEnvironment
        (ay_evgg_conj checkedModel originalModel)
        (ay_evgg_conj_right environmentContract
          (ay_evgg_conj acceptedEnvironment
            (ay_evgg_conj checkedModel originalModel))
          publication))

theorem ay_evgg_unsat_publication_original_empty_clause
    (environmentContract acceptedEnvironment checkedProof
      originalEmptyClause : Prop) :
    ay_evgg_unsat_publication environmentContract acceptedEnvironment
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_evgg_conj_right checkedProof originalEmptyClause
      (ay_evgg_conj_right acceptedEnvironment
        (ay_evgg_conj checkedProof originalEmptyClause)
        (ay_evgg_conj_right environmentContract
          (ay_evgg_conj acceptedEnvironment
            (ay_evgg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_evgg_accepted_environment_preserves_sat_publication
    (environmentContract acceptedEnvironment checkedModel originalModel :
      Prop) :
    ay_evgg_sat_publication environmentContract acceptedEnvironment
      checkedModel originalModel ->
    ay_evgg_public_result originalModel False False :=
  fun publication =>
    ay_evgg_disj_left originalModel (ay_evgg_disj False False)
      (ay_evgg_sat_publication_original_model environmentContract
        acceptedEnvironment checkedModel originalModel publication)

theorem ay_evgg_accepted_environment_preserves_unsat_publication
    (environmentContract acceptedEnvironment checkedProof
      originalEmptyClause : Prop) :
    ay_evgg_unsat_publication environmentContract acceptedEnvironment
      checkedProof originalEmptyClause ->
    ay_evgg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_evgg_disj_right False (ay_evgg_disj originalEmptyClause False)
      (ay_evgg_disj_left originalEmptyClause False
        (ay_evgg_unsat_publication_original_empty_clause environmentContract
          acceptedEnvironment checkedProof originalEmptyClause publication))

theorem ay_evgg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_evgg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_evgg_conj_intro reason (ay_evgg_conj fallbackPath auditTrail)
      reasonProof
      (ay_evgg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_evgg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_evgg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_evgg_conj_intro reason
      (ay_evgg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_evgg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_evgg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_evgg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_evgg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_evgg_conj_right reason
        (ay_evgg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_evgg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_evgg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_evgg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_evgg_conj_right reason
        (ay_evgg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_evgg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_evgg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_evgg_conj_intro reason
      (ay_evgg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_evgg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_evgg_environment_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_evgg_blocked_publication satFact unsatFact reason ->
    ay_evgg_recompute reason fallbackPath recomputeObligation ->
    ay_evgg_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_evgg_conj_intro
      (ay_evgg_blocked_publication satFact unsatFact reason)
      (ay_evgg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_evgg_environment_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_evgg_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_evgg_blocked_publication_no_sat satFact unsatFact reason
      (ay_evgg_conj_left
        (ay_evgg_blocked_publication satFact unsatFact reason)
        (ay_evgg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_evgg_environment_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_evgg_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_evgg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_evgg_conj_left
        (ay_evgg_blocked_publication satFact unsatFact reason)
        (ay_evgg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_evgg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_evgg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_evgg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_evgg_environment_mismatch_forces_no_claim
    (satFact unsatFact environmentMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    environmentMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_evgg_no_claim environmentMismatch fallbackPath auditTrail :=
  ay_evgg_mismatch_forces_no_claim satFact unsatFact environmentMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_evgg_whitelist_mismatch_forces_no_claim
    (satFact unsatFact whitelistMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    whitelistMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_evgg_no_claim whitelistMismatch fallbackPath auditTrail :=
  ay_evgg_mismatch_forces_no_claim satFact unsatFact whitelistMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_evgg_locale_mismatch_forces_no_claim
    (satFact unsatFact localeMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    localeMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_evgg_no_claim localeMismatch fallbackPath auditTrail :=
  ay_evgg_mismatch_forces_no_claim satFact unsatFact localeMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_evgg_thread_mismatch_forces_no_claim
    (satFact unsatFact threadMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    threadMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_evgg_no_claim threadMismatch fallbackPath auditTrail :=
  ay_evgg_mismatch_forces_no_claim satFact unsatFact threadMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_evgg_command_mismatch_forces_no_claim
    (satFact unsatFact commandMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    commandMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_evgg_no_claim commandMismatch fallbackPath auditTrail :=
  ay_evgg_mismatch_forces_no_claim satFact unsatFact commandMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_evgg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_evgg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_evgg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_evgg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_evgg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_evgg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_evgg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_evgg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_evgg_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_evgg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_evgg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_evgg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_evgg_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_evgg_no_claim auditMismatch fallbackPath auditTrail :=
  ay_evgg_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_evgg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_evgg_environment_failure satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_evgg_environment_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_evgg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_evgg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_evgg_failed_environment_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_evgg_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_evgg_environment_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_evgg_failed_environment_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_evgg_environment_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_evgg_environment_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_evgg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_evgg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_evgg_conj_left reason (ay_evgg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_evgg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_evgg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_evgg_conj_left reason (ay_evgg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
