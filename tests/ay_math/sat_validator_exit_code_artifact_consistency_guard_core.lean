-- SAT-COMP validator exit-code/artifact consistency guard core.
--
-- Public SAT/UNSAT claims are allowed only when process exit code, result
-- artifact, certificate/model artifact, checker transcript, benchmark
-- fingerprint, archive manifest, solver build evidence, and no-claim fallback
-- agree.

def ay_ecag_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ecag_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ecag_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_ecag_disj satFact (ay_ecag_disj unsatFact noClaimFact)

def ay_ecag_exit_artifact_contract
    (processExitCode resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) : Prop :=
  forall result : Prop,
    (processExitCode -> resultArtifact -> certificateModelArtifact ->
      checkerTranscript -> benchmarkFingerprint -> archiveManifest ->
      solverBuildEvidence -> noClaimFallbackPath -> result) ->
    result

def ay_ecag_sat_publication
    (exitArtifactContract modelEvidence originalModel : Prop) : Prop :=
  ay_ecag_conj exitArtifactContract
    (ay_ecag_conj modelEvidence originalModel)

def ay_ecag_unsat_publication
    (exitArtifactContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_ecag_conj exitArtifactContract
    (ay_ecag_conj proofEvidence originalEmptyClause)

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

def ay_ecag_consistency_failure
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

theorem ay_ecag_exit_artifact_contract_intro
    (processExitCode resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    processExitCode -> resultArtifact -> certificateModelArtifact ->
    checkerTranscript -> benchmarkFingerprint -> archiveManifest ->
    solverBuildEvidence -> noClaimFallbackPath ->
    ay_ecag_exit_artifact_contract processExitCode resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath :=
  fun exitProof artifactProof certificateProof checkerProof fingerprintProof
      archiveProof buildProof fallbackProof result build =>
    build exitProof artifactProof certificateProof checkerProof
      fingerprintProof archiveProof buildProof fallbackProof

theorem ay_ecag_exit_artifact_contract_exit_code
    (processExitCode resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ecag_exit_artifact_contract processExitCode resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    processExitCode :=
  fun contract =>
    contract processExitCode
      (fun exitProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        exitProof)

theorem ay_ecag_exit_artifact_contract_result_artifact
    (processExitCode resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ecag_exit_artifact_contract processExitCode resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    resultArtifact :=
  fun contract =>
    contract resultArtifact
      (fun _exitProof artifactProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        artifactProof)

theorem ay_ecag_exit_artifact_contract_certificate
    (processExitCode resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ecag_exit_artifact_contract processExitCode resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    certificateModelArtifact :=
  fun contract =>
    contract certificateModelArtifact
      (fun _exitProof _artifactProof certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        certificateProof)

theorem ay_ecag_exit_artifact_contract_checker
    (processExitCode resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ecag_exit_artifact_contract processExitCode resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _exitProof _artifactProof _certificateProof checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        checkerProof)

theorem ay_ecag_exit_artifact_contract_fingerprint
    (processExitCode resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ecag_exit_artifact_contract processExitCode resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _exitProof _artifactProof _certificateProof _checkerProof
          fingerprintProof _archiveProof _buildProof _fallbackProof =>
        fingerprintProof)

theorem ay_ecag_exit_artifact_contract_archive
    (processExitCode resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ecag_exit_artifact_contract processExitCode resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _exitProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof archiveProof _buildProof _fallbackProof =>
        archiveProof)

theorem ay_ecag_exit_artifact_contract_build
    (processExitCode resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ecag_exit_artifact_contract processExitCode resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _exitProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof buildProof _fallbackProof =>
        buildProof)

theorem ay_ecag_exit_artifact_contract_fallback
    (processExitCode resultArtifact certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ecag_exit_artifact_contract processExitCode resultArtifact
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _exitProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof fallbackProof =>
        fallbackProof)

theorem ay_ecag_sat_publication_intro
    (exitArtifactContract modelEvidence originalModel : Prop) :
    exitArtifactContract -> modelEvidence -> originalModel ->
    ay_ecag_sat_publication exitArtifactContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_ecag_conj_intro exitArtifactContract
      (ay_ecag_conj modelEvidence originalModel) contractProof
      (ay_ecag_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_ecag_sat_publication_original_model
    (exitArtifactContract modelEvidence originalModel : Prop) :
    ay_ecag_sat_publication exitArtifactContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_ecag_conj_right modelEvidence originalModel
      (ay_ecag_conj_right exitArtifactContract
        (ay_ecag_conj modelEvidence originalModel) publication)

theorem ay_ecag_unsat_publication_intro
    (exitArtifactContract proofEvidence originalEmptyClause : Prop) :
    exitArtifactContract -> proofEvidence -> originalEmptyClause ->
    ay_ecag_unsat_publication exitArtifactContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_ecag_conj_intro exitArtifactContract
      (ay_ecag_conj proofEvidence originalEmptyClause) contractProof
      (ay_ecag_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_ecag_unsat_publication_original_empty_clause
    (exitArtifactContract proofEvidence originalEmptyClause : Prop) :
    ay_ecag_unsat_publication exitArtifactContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_ecag_conj_right proofEvidence originalEmptyClause
      (ay_ecag_conj_right exitArtifactContract
        (ay_ecag_conj proofEvidence originalEmptyClause) publication)

theorem ay_ecag_accepted_exit_artifact_sat_sound
    (exitArtifactContract modelEvidence originalModel : Prop) :
    ay_ecag_sat_publication exitArtifactContract modelEvidence originalModel ->
    originalModel :=
  ay_ecag_sat_publication_original_model exitArtifactContract modelEvidence
    originalModel

theorem ay_ecag_accepted_exit_artifact_unsat_sound
    (exitArtifactContract proofEvidence originalEmptyClause : Prop) :
    ay_ecag_unsat_publication exitArtifactContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_ecag_unsat_publication_original_empty_clause exitArtifactContract
    proofEvidence originalEmptyClause

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

theorem ay_ecag_consistency_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_consistency_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_ecag_conj_intro
      (ay_ecag_blocked_publication satFact unsatFact reason)
      (ay_ecag_recompute reason fallbackPath recomputeObligation)
      (ay_ecag_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_ecag_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_ecag_consistency_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecag_consistency_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_ecag_blocked_publication_no_sat satFact unsatFact reason
      (ay_ecag_conj_left
        (ay_ecag_blocked_publication satFact unsatFact reason)
        (ay_ecag_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ecag_consistency_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecag_consistency_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_ecag_blocked_publication_no_unsat satFact unsatFact reason
      (ay_ecag_conj_left
        (ay_ecag_blocked_publication satFact unsatFact reason)
        (ay_ecag_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ecag_consistency_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecag_consistency_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_ecag_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_ecag_conj_right
      (ay_ecag_blocked_publication satFact unsatFact reason)
      (ay_ecag_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_ecag_exit_artifact_mismatch_forces_no_claim
    (satFact unsatFact exitArtifactMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    exitArtifactMismatch -> fallbackPath -> auditTrail ->
    recomputeObligation -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_no_claim exitArtifactMismatch fallbackPath auditTrail :=
  fun mismatchProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ecag_no_claim_intro exitArtifactMismatch fallbackPath auditTrail
      mismatchProof fallbackProof auditProof

theorem ay_ecag_missing_certificate_forces_no_claim
    (satFact unsatFact missingCertificate fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingCertificate -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_no_claim missingCertificate fallbackPath auditTrail :=
  fun missingProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ecag_no_claim_intro missingCertificate fallbackPath auditTrail
      missingProof fallbackProof auditProof

theorem ay_ecag_checker_disagreement_forces_no_claim
    (satFact unsatFact checkerDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerDisagreement -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ecag_no_claim checkerDisagreement fallbackPath auditTrail :=
  fun disagreementProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ecag_no_claim_intro checkerDisagreement fallbackPath auditTrail
      disagreementProof fallbackProof auditProof

theorem ay_ecag_failed_consistency_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecag_consistency_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_ecag_consistency_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_ecag_failed_consistency_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecag_consistency_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_ecag_consistency_failure_blocks_unsat satFact unsatFact reason
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
