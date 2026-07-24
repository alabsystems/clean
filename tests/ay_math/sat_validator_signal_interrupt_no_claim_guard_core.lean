-- SAT-COMP validator signal/interrupt no-claim guard core.
--
-- Public SAT/UNSAT claims are allowed only when solver artifacts, signal
-- status, shutdown transcript, checker replay, benchmark identity,
-- archive/build evidence, and no-claim fallback agree.

def ay_sigg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_sigg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_sigg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_sigg_disj satFact (ay_sigg_disj unsatFact noClaimFact)

def ay_sigg_signal_contract
    (solverResultArtifact signalStatus shutdownTranscript
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    Prop :=
  forall result : Prop,
    (solverResultArtifact -> signalStatus -> shutdownTranscript ->
      certificateModelArtifact -> checkerTranscript -> benchmarkFingerprint ->
      archiveManifest -> solverBuildEvidence -> noClaimFallbackPath ->
      result) ->
    result

def ay_sigg_sat_publication
    (signalContract modelEvidence originalModel : Prop) : Prop :=
  ay_sigg_conj signalContract
    (ay_sigg_conj modelEvidence originalModel)

def ay_sigg_unsat_publication
    (signalContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_sigg_conj signalContract
    (ay_sigg_conj proofEvidence originalEmptyClause)

def ay_sigg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_sigg_conj reason (ay_sigg_conj fallbackPath auditTrail)

def ay_sigg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_sigg_conj reason
    (ay_sigg_conj (satFact -> False) (unsatFact -> False))

def ay_sigg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_sigg_conj reason
    (ay_sigg_conj fallbackPath recomputeObligation)

def ay_sigg_signal_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_sigg_conj
    (ay_sigg_blocked_publication satFact unsatFact reason)
    (ay_sigg_recompute reason fallbackPath recomputeObligation)

theorem ay_sigg_conj_intro (left right : Prop) :
    left -> right -> ay_sigg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_sigg_conj_left (left right : Prop) :
    ay_sigg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_sigg_conj_right (left right : Prop) :
    ay_sigg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_sigg_disj_left (left right : Prop) :
    left -> ay_sigg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_sigg_disj_right (left right : Prop) :
    right -> ay_sigg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_sigg_signal_contract_intro
    (solverResultArtifact signalStatus shutdownTranscript
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    solverResultArtifact -> signalStatus -> shutdownTranscript ->
    certificateModelArtifact -> checkerTranscript -> benchmarkFingerprint ->
    archiveManifest -> solverBuildEvidence -> noClaimFallbackPath ->
    ay_sigg_signal_contract solverResultArtifact signalStatus
      shutdownTranscript certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath :=
  fun artifactProof signalProof shutdownProof certificateProof checkerProof
      fingerprintProof archiveProof buildProof fallbackProof result build =>
    build artifactProof signalProof shutdownProof certificateProof checkerProof
      fingerprintProof archiveProof buildProof fallbackProof

theorem ay_sigg_signal_contract_artifact
    (solverResultArtifact signalStatus shutdownTranscript
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_sigg_signal_contract solverResultArtifact signalStatus
      shutdownTranscript certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    solverResultArtifact :=
  fun contract =>
    contract solverResultArtifact
      (fun artifactProof _signalProof _shutdownProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => artifactProof)

theorem ay_sigg_signal_contract_signal_status
    (solverResultArtifact signalStatus shutdownTranscript
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_sigg_signal_contract solverResultArtifact signalStatus
      shutdownTranscript certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    signalStatus :=
  fun contract =>
    contract signalStatus
      (fun _artifactProof signalProof _shutdownProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => signalProof)

theorem ay_sigg_signal_contract_shutdown
    (solverResultArtifact signalStatus shutdownTranscript
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_sigg_signal_contract solverResultArtifact signalStatus
      shutdownTranscript certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    shutdownTranscript :=
  fun contract =>
    contract shutdownTranscript
      (fun _artifactProof _signalProof shutdownProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => shutdownProof)

theorem ay_sigg_signal_contract_certificate
    (solverResultArtifact signalStatus shutdownTranscript
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_sigg_signal_contract solverResultArtifact signalStatus
      shutdownTranscript certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    certificateModelArtifact :=
  fun contract =>
    contract certificateModelArtifact
      (fun _artifactProof _signalProof _shutdownProof certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => certificateProof)

theorem ay_sigg_signal_contract_checker
    (solverResultArtifact signalStatus shutdownTranscript
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_sigg_signal_contract solverResultArtifact signalStatus
      shutdownTranscript certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _artifactProof _signalProof _shutdownProof _certificateProof
          checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => checkerProof)

theorem ay_sigg_signal_contract_fingerprint
    (solverResultArtifact signalStatus shutdownTranscript
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_sigg_signal_contract solverResultArtifact signalStatus
      shutdownTranscript certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _artifactProof _signalProof _shutdownProof _certificateProof
          _checkerProof fingerprintProof _archiveProof _buildProof
          _fallbackProof => fingerprintProof)

theorem ay_sigg_signal_contract_archive
    (solverResultArtifact signalStatus shutdownTranscript
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_sigg_signal_contract solverResultArtifact signalStatus
      shutdownTranscript certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _artifactProof _signalProof _shutdownProof _certificateProof
          _checkerProof _fingerprintProof archiveProof _buildProof
          _fallbackProof => archiveProof)

theorem ay_sigg_signal_contract_build
    (solverResultArtifact signalStatus shutdownTranscript
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_sigg_signal_contract solverResultArtifact signalStatus
      shutdownTranscript certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _artifactProof _signalProof _shutdownProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof buildProof
          _fallbackProof => buildProof)

theorem ay_sigg_signal_contract_fallback
    (solverResultArtifact signalStatus shutdownTranscript
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_sigg_signal_contract solverResultArtifact signalStatus
      shutdownTranscript certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _artifactProof _signalProof _shutdownProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          fallbackProof => fallbackProof)

theorem ay_sigg_sat_publication_intro
    (signalContract modelEvidence originalModel : Prop) :
    signalContract -> modelEvidence -> originalModel ->
    ay_sigg_sat_publication signalContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_sigg_conj_intro signalContract
      (ay_sigg_conj modelEvidence originalModel) contractProof
      (ay_sigg_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_sigg_sat_publication_original_model
    (signalContract modelEvidence originalModel : Prop) :
    ay_sigg_sat_publication signalContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_sigg_conj_right modelEvidence originalModel
      (ay_sigg_conj_right signalContract
        (ay_sigg_conj modelEvidence originalModel) publication)

theorem ay_sigg_unsat_publication_intro
    (signalContract proofEvidence originalEmptyClause : Prop) :
    signalContract -> proofEvidence -> originalEmptyClause ->
    ay_sigg_unsat_publication signalContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_sigg_conj_intro signalContract
      (ay_sigg_conj proofEvidence originalEmptyClause) contractProof
      (ay_sigg_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_sigg_unsat_publication_original_empty_clause
    (signalContract proofEvidence originalEmptyClause : Prop) :
    ay_sigg_unsat_publication signalContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_sigg_conj_right proofEvidence originalEmptyClause
      (ay_sigg_conj_right signalContract
        (ay_sigg_conj proofEvidence originalEmptyClause) publication)

theorem ay_sigg_accepted_signal_contract_sat_sound
    (signalContract modelEvidence originalModel : Prop) :
    ay_sigg_sat_publication signalContract modelEvidence originalModel ->
    originalModel :=
  ay_sigg_sat_publication_original_model signalContract modelEvidence
    originalModel

theorem ay_sigg_accepted_signal_contract_unsat_sound
    (signalContract proofEvidence originalEmptyClause : Prop) :
    ay_sigg_unsat_publication signalContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_sigg_unsat_publication_original_empty_clause signalContract proofEvidence
    originalEmptyClause

theorem ay_sigg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_sigg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_sigg_conj_intro reason (ay_sigg_conj fallbackPath auditTrail)
      reasonProof
      (ay_sigg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_sigg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_sigg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_sigg_conj_intro reason
      (ay_sigg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_sigg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_sigg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_sigg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_sigg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_sigg_conj_right reason
        (ay_sigg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_sigg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_sigg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_sigg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_sigg_conj_right reason
        (ay_sigg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_sigg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_sigg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_sigg_conj_intro reason
      (ay_sigg_conj fallbackPath recomputeObligation) reasonProof
      (ay_sigg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_sigg_signal_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_sigg_signal_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_sigg_conj_intro
      (ay_sigg_blocked_publication satFact unsatFact reason)
      (ay_sigg_recompute reason fallbackPath recomputeObligation)
      (ay_sigg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_sigg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_sigg_signal_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sigg_signal_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_sigg_blocked_publication_no_sat satFact unsatFact reason
      (ay_sigg_conj_left
        (ay_sigg_blocked_publication satFact unsatFact reason)
        (ay_sigg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_sigg_signal_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sigg_signal_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_sigg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_sigg_conj_left
        (ay_sigg_blocked_publication satFact unsatFact reason)
        (ay_sigg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_sigg_signal_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sigg_signal_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_sigg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_sigg_conj_right
      (ay_sigg_blocked_publication satFact unsatFact reason)
      (ay_sigg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_sigg_interrupt_forces_no_claim
    (satFact unsatFact interruptReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    interruptReason -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_sigg_no_claim interruptReason fallbackPath auditTrail :=
  fun interruptProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_sigg_no_claim_intro interruptReason fallbackPath auditTrail
      interruptProof fallbackProof auditProof

theorem ay_sigg_abort_forces_no_claim
    (satFact unsatFact abortReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    abortReason -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_sigg_no_claim abortReason fallbackPath auditTrail :=
  fun abortProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_sigg_no_claim_intro abortReason fallbackPath auditTrail abortProof
      fallbackProof auditProof

theorem ay_sigg_incomplete_shutdown_forces_no_claim
    (satFact unsatFact incompleteShutdown fallbackPath auditTrail
      recomputeObligation : Prop) :
    incompleteShutdown -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_sigg_no_claim incompleteShutdown fallbackPath auditTrail :=
  fun incompleteProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_sigg_no_claim_intro incompleteShutdown fallbackPath auditTrail
      incompleteProof fallbackProof auditProof

theorem ay_sigg_failed_signal_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sigg_signal_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_sigg_signal_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_sigg_failed_signal_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sigg_signal_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_sigg_signal_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_sigg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_sigg_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_sigg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_sigg_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
