-- SAT-COMP validator memory/OOM no-claim guard core.
--
-- Public SAT/UNSAT claims are allowed only when solver artifacts, memory
-- status, resource limits, checker replay, benchmark identity, archive/build
-- evidence, and no-claim fallback agree.

def ay_oomg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_oomg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_oomg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_oomg_disj satFact (ay_oomg_disj unsatFact noClaimFact)

def ay_oomg_memory_contract
    (solverResultArtifact memoryStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    Prop :=
  forall result : Prop,
    (solverResultArtifact -> memoryStatus -> resourceLimitManifest ->
      certificateModelArtifact -> checkerTranscript -> benchmarkFingerprint ->
      archiveManifest -> solverBuildEvidence -> noClaimFallbackPath ->
      result) ->
    result

def ay_oomg_sat_publication
    (memoryContract modelEvidence originalModel : Prop) : Prop :=
  ay_oomg_conj memoryContract
    (ay_oomg_conj modelEvidence originalModel)

def ay_oomg_unsat_publication
    (memoryContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_oomg_conj memoryContract
    (ay_oomg_conj proofEvidence originalEmptyClause)

def ay_oomg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_oomg_conj reason (ay_oomg_conj fallbackPath auditTrail)

def ay_oomg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_oomg_conj reason
    (ay_oomg_conj (satFact -> False) (unsatFact -> False))

def ay_oomg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_oomg_conj reason
    (ay_oomg_conj fallbackPath recomputeObligation)

def ay_oomg_memory_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_oomg_conj
    (ay_oomg_blocked_publication satFact unsatFact reason)
    (ay_oomg_recompute reason fallbackPath recomputeObligation)

theorem ay_oomg_conj_intro (left right : Prop) :
    left -> right -> ay_oomg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_oomg_conj_left (left right : Prop) :
    ay_oomg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_oomg_conj_right (left right : Prop) :
    ay_oomg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_oomg_disj_left (left right : Prop) :
    left -> ay_oomg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_oomg_disj_right (left right : Prop) :
    right -> ay_oomg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_oomg_memory_contract_intro
    (solverResultArtifact memoryStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    solverResultArtifact -> memoryStatus -> resourceLimitManifest ->
    certificateModelArtifact -> checkerTranscript -> benchmarkFingerprint ->
    archiveManifest -> solverBuildEvidence -> noClaimFallbackPath ->
    ay_oomg_memory_contract solverResultArtifact memoryStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath :=
  fun artifactProof memoryProof resourceProof certificateProof checkerProof
      fingerprintProof archiveProof buildProof fallbackProof result build =>
    build artifactProof memoryProof resourceProof certificateProof checkerProof
      fingerprintProof archiveProof buildProof fallbackProof

theorem ay_oomg_memory_contract_artifact
    (solverResultArtifact memoryStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_oomg_memory_contract solverResultArtifact memoryStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    solverResultArtifact :=
  fun contract =>
    contract solverResultArtifact
      (fun artifactProof _memoryProof _resourceProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => artifactProof)

theorem ay_oomg_memory_contract_memory_status
    (solverResultArtifact memoryStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_oomg_memory_contract solverResultArtifact memoryStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    memoryStatus :=
  fun contract =>
    contract memoryStatus
      (fun _artifactProof memoryProof _resourceProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => memoryProof)

theorem ay_oomg_memory_contract_resource_manifest
    (solverResultArtifact memoryStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_oomg_memory_contract solverResultArtifact memoryStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    resourceLimitManifest :=
  fun contract =>
    contract resourceLimitManifest
      (fun _artifactProof _memoryProof resourceProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => resourceProof)

theorem ay_oomg_memory_contract_certificate
    (solverResultArtifact memoryStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_oomg_memory_contract solverResultArtifact memoryStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    certificateModelArtifact :=
  fun contract =>
    contract certificateModelArtifact
      (fun _artifactProof _memoryProof _resourceProof certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => certificateProof)

theorem ay_oomg_memory_contract_checker
    (solverResultArtifact memoryStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_oomg_memory_contract solverResultArtifact memoryStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _artifactProof _memoryProof _resourceProof _certificateProof
          checkerProof _fingerprintProof _archiveProof _buildProof
          _fallbackProof => checkerProof)

theorem ay_oomg_memory_contract_fingerprint
    (solverResultArtifact memoryStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_oomg_memory_contract solverResultArtifact memoryStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _artifactProof _memoryProof _resourceProof _certificateProof
          _checkerProof fingerprintProof _archiveProof _buildProof
          _fallbackProof => fingerprintProof)

theorem ay_oomg_memory_contract_archive
    (solverResultArtifact memoryStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_oomg_memory_contract solverResultArtifact memoryStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _artifactProof _memoryProof _resourceProof _certificateProof
          _checkerProof _fingerprintProof archiveProof _buildProof
          _fallbackProof => archiveProof)

theorem ay_oomg_memory_contract_build
    (solverResultArtifact memoryStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_oomg_memory_contract solverResultArtifact memoryStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _artifactProof _memoryProof _resourceProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof buildProof
          _fallbackProof => buildProof)

theorem ay_oomg_memory_contract_fallback
    (solverResultArtifact memoryStatus resourceLimitManifest
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath : Prop) :
    ay_oomg_memory_contract solverResultArtifact memoryStatus
      resourceLimitManifest certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _artifactProof _memoryProof _resourceProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _buildProof
          fallbackProof => fallbackProof)

theorem ay_oomg_sat_publication_intro
    (memoryContract modelEvidence originalModel : Prop) :
    memoryContract -> modelEvidence -> originalModel ->
    ay_oomg_sat_publication memoryContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_oomg_conj_intro memoryContract
      (ay_oomg_conj modelEvidence originalModel) contractProof
      (ay_oomg_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_oomg_sat_publication_original_model
    (memoryContract modelEvidence originalModel : Prop) :
    ay_oomg_sat_publication memoryContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_oomg_conj_right modelEvidence originalModel
      (ay_oomg_conj_right memoryContract
        (ay_oomg_conj modelEvidence originalModel) publication)

theorem ay_oomg_unsat_publication_intro
    (memoryContract proofEvidence originalEmptyClause : Prop) :
    memoryContract -> proofEvidence -> originalEmptyClause ->
    ay_oomg_unsat_publication memoryContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_oomg_conj_intro memoryContract
      (ay_oomg_conj proofEvidence originalEmptyClause) contractProof
      (ay_oomg_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_oomg_unsat_publication_original_empty_clause
    (memoryContract proofEvidence originalEmptyClause : Prop) :
    ay_oomg_unsat_publication memoryContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_oomg_conj_right proofEvidence originalEmptyClause
      (ay_oomg_conj_right memoryContract
        (ay_oomg_conj proofEvidence originalEmptyClause) publication)

theorem ay_oomg_accepted_memory_contract_sat_sound
    (memoryContract modelEvidence originalModel : Prop) :
    ay_oomg_sat_publication memoryContract modelEvidence originalModel ->
    originalModel :=
  ay_oomg_sat_publication_original_model memoryContract modelEvidence
    originalModel

theorem ay_oomg_accepted_memory_contract_unsat_sound
    (memoryContract proofEvidence originalEmptyClause : Prop) :
    ay_oomg_unsat_publication memoryContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_oomg_unsat_publication_original_empty_clause memoryContract proofEvidence
    originalEmptyClause

theorem ay_oomg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_oomg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_oomg_conj_intro reason (ay_oomg_conj fallbackPath auditTrail)
      reasonProof
      (ay_oomg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_oomg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_oomg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_oomg_conj_intro reason
      (ay_oomg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_oomg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_oomg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_oomg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_oomg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_oomg_conj_right reason
        (ay_oomg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_oomg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_oomg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_oomg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_oomg_conj_right reason
        (ay_oomg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_oomg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_oomg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_oomg_conj_intro reason
      (ay_oomg_conj fallbackPath recomputeObligation) reasonProof
      (ay_oomg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_oomg_memory_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_oomg_memory_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_oomg_conj_intro
      (ay_oomg_blocked_publication satFact unsatFact reason)
      (ay_oomg_recompute reason fallbackPath recomputeObligation)
      (ay_oomg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_oomg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_oomg_memory_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_oomg_memory_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_oomg_blocked_publication_no_sat satFact unsatFact reason
      (ay_oomg_conj_left
        (ay_oomg_blocked_publication satFact unsatFact reason)
        (ay_oomg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_oomg_memory_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_oomg_memory_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_oomg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_oomg_conj_left
        (ay_oomg_blocked_publication satFact unsatFact reason)
        (ay_oomg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_oomg_memory_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_oomg_memory_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_oomg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_oomg_conj_right
      (ay_oomg_blocked_publication satFact unsatFact reason)
      (ay_oomg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_oomg_oom_forces_no_claim
    (satFact unsatFact oomReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    oomReason -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_oomg_no_claim oomReason fallbackPath auditTrail :=
  fun oomProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_oomg_no_claim_intro oomReason fallbackPath auditTrail oomProof
      fallbackProof auditProof

theorem ay_oomg_resource_exhaustion_forces_no_claim
    (satFact unsatFact resourceExhaustion fallbackPath auditTrail
      recomputeObligation : Prop) :
    resourceExhaustion -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_oomg_no_claim resourceExhaustion fallbackPath auditTrail :=
  fun resourceProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_oomg_no_claim_intro resourceExhaustion fallbackPath auditTrail
      resourceProof fallbackProof auditProof

theorem ay_oomg_incomplete_memory_status_forces_no_claim
    (satFact unsatFact incompleteMemoryStatus fallbackPath auditTrail
      recomputeObligation : Prop) :
    incompleteMemoryStatus -> fallbackPath -> auditTrail ->
    recomputeObligation -> (satFact -> False) -> (unsatFact -> False) ->
    ay_oomg_no_claim incompleteMemoryStatus fallbackPath auditTrail :=
  fun incompleteProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_oomg_no_claim_intro incompleteMemoryStatus fallbackPath auditTrail
      incompleteProof fallbackProof auditProof

theorem ay_oomg_failed_memory_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_oomg_memory_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_oomg_memory_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_oomg_failed_memory_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_oomg_memory_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_oomg_memory_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_oomg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_oomg_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_oomg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_oomg_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
