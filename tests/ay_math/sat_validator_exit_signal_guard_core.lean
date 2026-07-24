-- SAT-COMP validator exit-signal/termination guard core.
--
-- Public SAT/UNSAT claims require process exit-code evidence, signal/timeout
-- ledger, result artifact digest, checker transcript, benchmark fingerprint,
-- solver build evidence, archive manifest, no-claim fallback, and audit
-- transcript to agree.  Abnormal termination failures become no-claim
-- recompute obligations rather than public semantic answers.

def ay_esgg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_esgg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_esgg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_esgg_disj satFact (ay_esgg_disj unsatFact noClaimFact)

def ay_esgg_clean_termination_contract
    (processExitCodeManifest signalTimeoutLedger resultArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (processExitCodeManifest -> signalTimeoutLedger ->
      resultArtifactDigest -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> noClaimFallback ->
      auditTranscript -> result) ->
    result

def ay_esgg_sat_publication
    (terminationContract acceptedcleanTermination checkedModel
      originalModel : Prop) : Prop :=
  ay_esgg_conj terminationContract
    (ay_esgg_conj acceptedcleanTermination
      (ay_esgg_conj checkedModel originalModel))

def ay_esgg_unsat_publication
    (terminationContract acceptedcleanTermination checkedProof
      originalEmptyClause : Prop) : Prop :=
  ay_esgg_conj terminationContract
    (ay_esgg_conj acceptedcleanTermination
      (ay_esgg_conj checkedProof originalEmptyClause))

def ay_esgg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_esgg_conj reason (ay_esgg_conj fallbackPath auditTrail)

def ay_esgg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_esgg_conj reason
    (ay_esgg_conj (satFact -> False) (unsatFact -> False))

def ay_esgg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_esgg_conj reason
    (ay_esgg_conj fallbackPath recomputeObligation)

def ay_esgg_termination_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_esgg_conj
    (ay_esgg_blocked_publication satFact unsatFact reason)
    (ay_esgg_recompute reason fallbackPath recomputeObligation)

theorem ay_esgg_conj_intro (left right : Prop) :
    left -> right -> ay_esgg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_esgg_conj_left (left right : Prop) :
    ay_esgg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_esgg_conj_right (left right : Prop) :
    ay_esgg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_esgg_disj_left (left right : Prop) :
    left -> ay_esgg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_esgg_disj_right (left right : Prop) :
    right -> ay_esgg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_esgg_clean_termination_contract_intro
    (processExitCodeManifest signalTimeoutLedger resultArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    processExitCodeManifest -> signalTimeoutLedger -> resultArtifactDigest ->
    checkerTranscript -> benchmarkFingerprint -> solverBuildEvidence ->
    archiveManifest -> noClaimFallback -> auditTranscript ->
    ay_esgg_clean_termination_contract processExitCodeManifest
      signalTimeoutLedger resultArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript :=
  fun exitProof signalProof artifactProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof result build =>
    build exitProof signalProof artifactProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof

theorem ay_esgg_contract_exit_code
    (processExitCodeManifest signalTimeoutLedger resultArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_esgg_clean_termination_contract processExitCodeManifest
      signalTimeoutLedger resultArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    processExitCodeManifest :=
  fun contract =>
    contract processExitCodeManifest
      (fun exitProof _signalProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => exitProof)

theorem ay_esgg_contract_signal_ledger
    (processExitCodeManifest signalTimeoutLedger resultArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_esgg_clean_termination_contract processExitCodeManifest
      signalTimeoutLedger resultArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    signalTimeoutLedger :=
  fun contract =>
    contract signalTimeoutLedger
      (fun _exitProof signalProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => signalProof)

theorem ay_esgg_contract_artifact
    (processExitCodeManifest signalTimeoutLedger resultArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_esgg_clean_termination_contract processExitCodeManifest
      signalTimeoutLedger resultArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    resultArtifactDigest :=
  fun contract =>
    contract resultArtifactDigest
      (fun _exitProof _signalProof artifactProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => artifactProof)

theorem ay_esgg_contract_checker
    (processExitCodeManifest signalTimeoutLedger resultArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_esgg_clean_termination_contract processExitCodeManifest
      signalTimeoutLedger resultArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _exitProof _signalProof _artifactProof checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_esgg_contract_fingerprint
    (processExitCodeManifest signalTimeoutLedger resultArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_esgg_clean_termination_contract processExitCodeManifest
      signalTimeoutLedger resultArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _exitProof _signalProof _artifactProof _checkerProof
          fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_esgg_contract_build
    (processExitCodeManifest signalTimeoutLedger resultArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_esgg_clean_termination_contract processExitCodeManifest
      signalTimeoutLedger resultArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _exitProof _signalProof _artifactProof _checkerProof
          _fingerprintProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_esgg_contract_archive
    (processExitCodeManifest signalTimeoutLedger resultArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_esgg_clean_termination_contract processExitCodeManifest
      signalTimeoutLedger resultArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _exitProof _signalProof _artifactProof _checkerProof
          _fingerprintProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_esgg_contract_fallback
    (processExitCodeManifest signalTimeoutLedger resultArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_esgg_clean_termination_contract processExitCodeManifest
      signalTimeoutLedger resultArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _exitProof _signalProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_esgg_contract_audit
    (processExitCodeManifest signalTimeoutLedger resultArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_esgg_clean_termination_contract processExitCodeManifest
      signalTimeoutLedger resultArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _exitProof _signalProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_esgg_sat_publication_intro
    (terminationContract acceptedcleanTermination checkedModel
      originalModel : Prop) :
    terminationContract -> acceptedcleanTermination -> checkedModel ->
    originalModel ->
    ay_esgg_sat_publication terminationContract acceptedcleanTermination
      checkedModel originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_esgg_conj_intro terminationContract
      (ay_esgg_conj acceptedcleanTermination
        (ay_esgg_conj checkedModel originalModel))
      contractProof
      (ay_esgg_conj_intro acceptedcleanTermination
        (ay_esgg_conj checkedModel originalModel)
        acceptedProof
        (ay_esgg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_esgg_sat_publication_termination
    (terminationContract acceptedcleanTermination checkedModel
      originalModel : Prop) :
    ay_esgg_sat_publication terminationContract acceptedcleanTermination
      checkedModel originalModel ->
    terminationContract :=
  fun publication =>
    ay_esgg_conj_left terminationContract
      (ay_esgg_conj acceptedcleanTermination
        (ay_esgg_conj checkedModel originalModel))
      publication

theorem ay_esgg_sat_publication_original_model
    (terminationContract acceptedcleanTermination checkedModel
      originalModel : Prop) :
    ay_esgg_sat_publication terminationContract acceptedcleanTermination
      checkedModel originalModel ->
    originalModel :=
  fun publication =>
    ay_esgg_conj_right checkedModel originalModel
      (ay_esgg_conj_right acceptedcleanTermination
        (ay_esgg_conj checkedModel originalModel)
        (ay_esgg_conj_right terminationContract
          (ay_esgg_conj acceptedcleanTermination
            (ay_esgg_conj checkedModel originalModel))
          publication))

theorem ay_esgg_unsat_publication_intro
    (terminationContract acceptedcleanTermination checkedProof
      originalEmptyClause : Prop) :
    terminationContract -> acceptedcleanTermination -> checkedProof ->
    originalEmptyClause ->
    ay_esgg_unsat_publication terminationContract acceptedcleanTermination
      checkedProof originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_esgg_conj_intro terminationContract
      (ay_esgg_conj acceptedcleanTermination
        (ay_esgg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_esgg_conj_intro acceptedcleanTermination
        (ay_esgg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_esgg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_esgg_unsat_publication_termination
    (terminationContract acceptedcleanTermination checkedProof
      originalEmptyClause : Prop) :
    ay_esgg_unsat_publication terminationContract acceptedcleanTermination
      checkedProof originalEmptyClause ->
    terminationContract :=
  fun publication =>
    ay_esgg_conj_left terminationContract
      (ay_esgg_conj acceptedcleanTermination
        (ay_esgg_conj checkedProof originalEmptyClause))
      publication

theorem ay_esgg_unsat_publication_original_empty_clause
    (terminationContract acceptedcleanTermination checkedProof
      originalEmptyClause : Prop) :
    ay_esgg_unsat_publication terminationContract acceptedcleanTermination
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_esgg_conj_right checkedProof originalEmptyClause
      (ay_esgg_conj_right acceptedcleanTermination
        (ay_esgg_conj checkedProof originalEmptyClause)
        (ay_esgg_conj_right terminationContract
          (ay_esgg_conj acceptedcleanTermination
            (ay_esgg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_esgg_accepted_clean_sat_passes_publication
    (terminationContract acceptedcleanTermination checkedModel
      originalModel : Prop) :
    ay_esgg_sat_publication terminationContract acceptedcleanTermination
      checkedModel originalModel ->
    ay_esgg_public_result originalModel False False :=
  fun publication =>
    ay_esgg_disj_left originalModel (ay_esgg_disj False False)
      (ay_esgg_sat_publication_original_model terminationContract
        acceptedcleanTermination checkedModel originalModel publication)

theorem ay_esgg_accepted_clean_unsat_passes_publication
    (terminationContract acceptedcleanTermination checkedProof
      originalEmptyClause : Prop) :
    ay_esgg_unsat_publication terminationContract acceptedcleanTermination
      checkedProof originalEmptyClause ->
    ay_esgg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_esgg_disj_right False (ay_esgg_disj originalEmptyClause False)
      (ay_esgg_disj_left originalEmptyClause False
        (ay_esgg_unsat_publication_original_empty_clause terminationContract
          acceptedcleanTermination checkedProof originalEmptyClause
          publication))

theorem ay_esgg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_esgg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_esgg_conj_intro reason (ay_esgg_conj fallbackPath auditTrail)
      reasonProof
      (ay_esgg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_esgg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_esgg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_esgg_conj_intro reason
      (ay_esgg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_esgg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_esgg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_esgg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_esgg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_esgg_conj_right reason
        (ay_esgg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_esgg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_esgg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_esgg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_esgg_conj_right reason
        (ay_esgg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_esgg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_esgg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_esgg_conj_intro reason
      (ay_esgg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_esgg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_esgg_termination_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_esgg_blocked_publication satFact unsatFact reason ->
    ay_esgg_recompute reason fallbackPath recomputeObligation ->
    ay_esgg_termination_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_esgg_conj_intro
      (ay_esgg_blocked_publication satFact unsatFact reason)
      (ay_esgg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_esgg_termination_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_esgg_termination_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_esgg_blocked_publication_no_sat satFact unsatFact reason
      (ay_esgg_conj_left
        (ay_esgg_blocked_publication satFact unsatFact reason)
        (ay_esgg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_esgg_termination_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_esgg_termination_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_esgg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_esgg_conj_left
        (ay_esgg_blocked_publication satFact unsatFact reason)
        (ay_esgg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_esgg_termination_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_esgg_termination_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_esgg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_esgg_conj_right
      (ay_esgg_blocked_publication satFact unsatFact reason)
      (ay_esgg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_esgg_killed_by_signal_forces_no_claim
    (satFact unsatFact killedBySignal fallbackPath auditTrail
      recomputeObligation : Prop) :
    killedBySignal -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_esgg_no_claim killedBySignal fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_esgg_no_claim_intro killedBySignal fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_esgg_timeout_race_forces_recompute
    (satFact unsatFact timeoutRace fallbackPath recomputeObligation : Prop) :
    timeoutRace -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_esgg_termination_failure satFact unsatFact timeoutRace fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_esgg_termination_failure_intro satFact unsatFact timeoutRace
      fallbackPath recomputeObligation
      (ay_esgg_blocked_publication_intro satFact unsatFact timeoutRace
        reasonProof noSat noUnsat)
      (ay_esgg_recompute_intro timeoutRace fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_esgg_nonzero_exit_with_result_forces_no_claim
    (satFact unsatFact nonzeroExitWithResult fallbackPath auditTrail
      recomputeObligation : Prop) :
    nonzeroExitWithResult -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_esgg_no_claim nonzeroExitWithResult fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_esgg_no_claim_intro nonzeroExitWithResult fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_esgg_missing_exit_evidence_forces_no_claim
    (satFact unsatFact missingExitEvidence fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingExitEvidence -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_esgg_no_claim missingExitEvidence fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_esgg_no_claim_intro missingExitEvidence fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_esgg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_esgg_no_claim checkerMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_esgg_no_claim_intro checkerMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_esgg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_esgg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_esgg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_esgg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_esgg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_esgg_no_claim_intro buildMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_esgg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_esgg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_esgg_no_claim_intro archiveMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_esgg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivation fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivation -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_esgg_no_claim fallbackActivation fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_esgg_no_claim_intro fallbackActivation fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_esgg_failed_termination_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_esgg_termination_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_esgg_termination_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_esgg_failed_termination_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_esgg_termination_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_esgg_termination_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_esgg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_esgg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_esgg_conj_left reason (ay_esgg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_esgg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_esgg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_esgg_conj_left reason (ay_esgg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
