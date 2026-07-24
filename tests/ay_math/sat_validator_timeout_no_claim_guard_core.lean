-- SAT-COMP validator timeout no-claim guard core.
--
-- Public SAT/UNSAT claims are allowed only when solver artifacts, timeout
-- status, resource limits, checker replay, benchmark identity, archive/build
-- evidence, and no-claim fallback agree.

def ay_vtog_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vtog_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vtog_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vtog_disj satFact (ay_vtog_disj unsatFact noClaimFact)

def ay_vtog_timeout_contract
    (solverResultArtifact timeoutStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    Prop :=
  forall result : Prop,
    (solverResultArtifact -> timeoutStatus -> resourceLimitManifest ->
      certificateModelArtifact -> checkerTranscript -> benchmarkFingerprint ->
      archiveManifest -> solverBuildEvidence -> noClaimFallbackPath ->
      result) ->
    result

def ay_vtog_sat_publication
    (timeoutContract modelEvidence originalModel : Prop) : Prop :=
  ay_vtog_conj timeoutContract
    (ay_vtog_conj modelEvidence originalModel)

def ay_vtog_unsat_publication
    (timeoutContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vtog_conj timeoutContract
    (ay_vtog_conj proofEvidence originalEmptyClause)

def ay_vtog_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vtog_conj reason (ay_vtog_conj fallbackPath auditTrail)

def ay_vtog_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vtog_conj reason
    (ay_vtog_conj (satFact -> False) (unsatFact -> False))

def ay_vtog_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vtog_conj reason
    (ay_vtog_conj fallbackPath recomputeObligation)

def ay_vtog_timeout_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vtog_conj
    (ay_vtog_blocked_publication satFact unsatFact reason)
    (ay_vtog_recompute reason fallbackPath recomputeObligation)

theorem ay_vtog_conj_intro (left right : Prop) :
    left -> right -> ay_vtog_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vtog_conj_left (left right : Prop) :
    ay_vtog_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vtog_conj_right (left right : Prop) :
    ay_vtog_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vtog_disj_left (left right : Prop) :
    left -> ay_vtog_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vtog_disj_right (left right : Prop) :
    right -> ay_vtog_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vtog_timeout_contract_intro
    (solverResultArtifact timeoutStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    solverResultArtifact -> timeoutStatus -> resourceLimitManifest ->
    certificateModelArtifact -> checkerTranscript -> benchmarkFingerprint ->
    archiveManifest -> solverBuildEvidence -> noClaimFallbackPath ->
    ay_vtog_timeout_contract solverResultArtifact timeoutStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath :=
  fun artifactProof timeoutProof resourceProof certificateProof checkerProof
      fingerprintProof archiveProof buildProof fallbackProof result build =>
    build artifactProof timeoutProof resourceProof certificateProof
      checkerProof fingerprintProof archiveProof buildProof fallbackProof

theorem ay_vtog_timeout_contract_artifact
    (solverResultArtifact timeoutStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_vtog_timeout_contract solverResultArtifact timeoutStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    solverResultArtifact :=
  fun contract =>
    contract solverResultArtifact
      (fun artifactProof _timeoutProof _resourceProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => artifactProof)

theorem ay_vtog_timeout_contract_timeout_status
    (solverResultArtifact timeoutStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_vtog_timeout_contract solverResultArtifact timeoutStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    timeoutStatus :=
  fun contract =>
    contract timeoutStatus
      (fun _artifactProof timeoutProof _resourceProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => timeoutProof)

theorem ay_vtog_timeout_contract_resource_manifest
    (solverResultArtifact timeoutStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_vtog_timeout_contract solverResultArtifact timeoutStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    resourceLimitManifest :=
  fun contract =>
    contract resourceLimitManifest
      (fun _artifactProof _timeoutProof resourceProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => resourceProof)

theorem ay_vtog_timeout_contract_certificate
    (solverResultArtifact timeoutStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_vtog_timeout_contract solverResultArtifact timeoutStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    certificateModelArtifact :=
  fun contract =>
    contract certificateModelArtifact
      (fun _artifactProof _timeoutProof _resourceProof certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => certificateProof)

theorem ay_vtog_timeout_contract_checker
    (solverResultArtifact timeoutStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_vtog_timeout_contract solverResultArtifact timeoutStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _artifactProof _timeoutProof _resourceProof _certificateProof
          checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => checkerProof)

theorem ay_vtog_timeout_contract_fingerprint
    (solverResultArtifact timeoutStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_vtog_timeout_contract solverResultArtifact timeoutStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _artifactProof _timeoutProof _resourceProof _certificateProof
          _checkerProof fingerprintProof _archiveProof _buildProof
          _fallbackProof => fingerprintProof)

theorem ay_vtog_timeout_contract_archive
    (solverResultArtifact timeoutStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_vtog_timeout_contract solverResultArtifact timeoutStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _artifactProof _timeoutProof _resourceProof _certificateProof
          _checkerProof _fingerprintProof archiveProof _buildProof
          _fallbackProof => archiveProof)

theorem ay_vtog_timeout_contract_build
    (solverResultArtifact timeoutStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_vtog_timeout_contract solverResultArtifact timeoutStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _artifactProof _timeoutProof _resourceProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof buildProof
          _fallbackProof => buildProof)

theorem ay_vtog_timeout_contract_fallback
    (solverResultArtifact timeoutStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_vtog_timeout_contract solverResultArtifact timeoutStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _artifactProof _timeoutProof _resourceProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          fallbackProof => fallbackProof)

theorem ay_vtog_sat_publication_intro
    (timeoutContract modelEvidence originalModel : Prop) :
    timeoutContract -> modelEvidence -> originalModel ->
    ay_vtog_sat_publication timeoutContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vtog_conj_intro timeoutContract
      (ay_vtog_conj modelEvidence originalModel) contractProof
      (ay_vtog_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vtog_sat_publication_original_model
    (timeoutContract modelEvidence originalModel : Prop) :
    ay_vtog_sat_publication timeoutContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vtog_conj_right modelEvidence originalModel
      (ay_vtog_conj_right timeoutContract
        (ay_vtog_conj modelEvidence originalModel) publication)

theorem ay_vtog_unsat_publication_intro
    (timeoutContract proofEvidence originalEmptyClause : Prop) :
    timeoutContract -> proofEvidence -> originalEmptyClause ->
    ay_vtog_unsat_publication timeoutContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vtog_conj_intro timeoutContract
      (ay_vtog_conj proofEvidence originalEmptyClause) contractProof
      (ay_vtog_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vtog_unsat_publication_original_empty_clause
    (timeoutContract proofEvidence originalEmptyClause : Prop) :
    ay_vtog_unsat_publication timeoutContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vtog_conj_right proofEvidence originalEmptyClause
      (ay_vtog_conj_right timeoutContract
        (ay_vtog_conj proofEvidence originalEmptyClause) publication)

theorem ay_vtog_accepted_timeout_contract_sat_sound
    (timeoutContract modelEvidence originalModel : Prop) :
    ay_vtog_sat_publication timeoutContract modelEvidence originalModel ->
    originalModel :=
  ay_vtog_sat_publication_original_model timeoutContract modelEvidence
    originalModel

theorem ay_vtog_accepted_timeout_contract_unsat_sound
    (timeoutContract proofEvidence originalEmptyClause : Prop) :
    ay_vtog_unsat_publication timeoutContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_vtog_unsat_publication_original_empty_clause timeoutContract
    proofEvidence originalEmptyClause

theorem ay_vtog_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vtog_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vtog_conj_intro reason (ay_vtog_conj fallbackPath auditTrail)
      reasonProof
      (ay_vtog_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_vtog_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vtog_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_vtog_conj_intro reason
      (ay_vtog_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_vtog_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_vtog_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vtog_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vtog_conj_left (satFact -> False) (unsatFact -> False)
      (ay_vtog_conj_right reason
        (ay_vtog_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vtog_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vtog_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vtog_conj_right (satFact -> False) (unsatFact -> False)
      (ay_vtog_conj_right reason
        (ay_vtog_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vtog_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vtog_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vtog_conj_intro reason
      (ay_vtog_conj fallbackPath recomputeObligation) reasonProof
      (ay_vtog_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_vtog_timeout_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtog_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_vtog_conj_intro
      (ay_vtog_blocked_publication satFact unsatFact reason)
      (ay_vtog_recompute reason fallbackPath recomputeObligation)
      (ay_vtog_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_vtog_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vtog_timeout_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vtog_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vtog_blocked_publication_no_sat satFact unsatFact reason
      (ay_vtog_conj_left
        (ay_vtog_blocked_publication satFact unsatFact reason)
        (ay_vtog_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vtog_timeout_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vtog_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vtog_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vtog_conj_left
        (ay_vtog_blocked_publication satFact unsatFact reason)
        (ay_vtog_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vtog_timeout_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vtog_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vtog_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vtog_conj_right
      (ay_vtog_blocked_publication satFact unsatFact reason)
      (ay_vtog_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vtog_timeout_forces_no_claim
    (satFact unsatFact timeoutReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    timeoutReason -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtog_no_claim timeoutReason fallbackPath auditTrail :=
  fun timeoutProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_vtog_no_claim_intro timeoutReason fallbackPath auditTrail timeoutProof
      fallbackProof auditProof

theorem ay_vtog_resource_exhaustion_forces_no_claim
    (satFact unsatFact resourceExhaustion fallbackPath auditTrail
      recomputeObligation : Prop) :
    resourceExhaustion -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtog_no_claim resourceExhaustion fallbackPath auditTrail :=
  fun resourceProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_vtog_no_claim_intro resourceExhaustion fallbackPath auditTrail
      resourceProof fallbackProof auditProof

theorem ay_vtog_incomplete_status_forces_no_claim
    (satFact unsatFact incompleteStatus fallbackPath auditTrail
      recomputeObligation : Prop) :
    incompleteStatus -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vtog_no_claim incompleteStatus fallbackPath auditTrail :=
  fun incompleteProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_vtog_no_claim_intro incompleteStatus fallbackPath auditTrail
      incompleteProof fallbackProof auditProof

theorem ay_vtog_failed_timeout_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vtog_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vtog_timeout_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vtog_failed_timeout_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vtog_timeout_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vtog_timeout_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vtog_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_vtog_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_vtog_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_vtog_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
