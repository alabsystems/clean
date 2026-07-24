-- SAT-COMP validator artifact-permissions no-claim guard core.
--
-- Unreadable or mispermissioned result artifacts publish no semantic SAT/UNSAT
-- claim unless readable-artifact evidence and all validation artifacts agree.

def ay_vapg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vapg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vapg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vapg_disj satFact (ay_vapg_disj unsatFact noClaimFact)

def ay_vapg_readable_artifact_contract
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      readablePermissionEvidence : Prop) : Prop :=
  forall result : Prop,
    (completeResultArtifact -> certificateModel -> checkerTranscript ->
      benchmarkFingerprint -> buildConfig -> archiveManifest ->
      submissionManifest -> readablePermissionEvidence -> result) ->
    result

def ay_vapg_sat_publication
    (readableContract modelEvidence originalModel : Prop) : Prop :=
  ay_vapg_conj readableContract
    (ay_vapg_conj modelEvidence originalModel)

def ay_vapg_unsat_publication
    (readableContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vapg_conj readableContract
    (ay_vapg_conj proofEvidence originalEmptyClause)

def ay_vapg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vapg_conj reason (ay_vapg_conj fallbackPath auditTrail)

def ay_vapg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vapg_conj reason
    (ay_vapg_conj (satFact -> False) (unsatFact -> False))

def ay_vapg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vapg_conj reason
    (ay_vapg_conj fallbackPath recomputeObligation)

def ay_vapg_permission_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vapg_conj
    (ay_vapg_blocked_publication satFact unsatFact reason)
    (ay_vapg_recompute reason fallbackPath recomputeObligation)

theorem ay_vapg_conj_intro (left right : Prop) :
    left -> right -> ay_vapg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vapg_conj_left (left right : Prop) :
    ay_vapg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vapg_conj_right (left right : Prop) :
    ay_vapg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vapg_disj_left (left right : Prop) :
    left -> ay_vapg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vapg_disj_right (left right : Prop) :
    right -> ay_vapg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vapg_readable_artifact_contract_intro
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      readablePermissionEvidence : Prop) :
    completeResultArtifact -> certificateModel -> checkerTranscript ->
    benchmarkFingerprint -> buildConfig -> archiveManifest ->
    submissionManifest -> readablePermissionEvidence ->
    ay_vapg_readable_artifact_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest readablePermissionEvidence :=
  fun resultProof certificateProof checkerProof fingerprintProof buildProof
      archiveProof submissionProof readableProof result build =>
    build resultProof certificateProof checkerProof fingerprintProof buildProof
      archiveProof submissionProof readableProof

theorem ay_vapg_readable_artifact_contract_result_artifact
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      readablePermissionEvidence : Prop) :
    ay_vapg_readable_artifact_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest readablePermissionEvidence ->
    completeResultArtifact :=
  fun contract =>
    contract completeResultArtifact
      (fun resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof _readableProof =>
        resultProof)

theorem ay_vapg_readable_artifact_contract_certificate_model
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      readablePermissionEvidence : Prop) :
    ay_vapg_readable_artifact_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest readablePermissionEvidence ->
    certificateModel :=
  fun contract =>
    contract certificateModel
      (fun _resultProof certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof _readableProof =>
        certificateProof)

theorem ay_vapg_readable_artifact_contract_checker
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      readablePermissionEvidence : Prop) :
    ay_vapg_readable_artifact_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest readablePermissionEvidence ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _resultProof _certificateProof checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof _readableProof =>
        checkerProof)

theorem ay_vapg_readable_artifact_contract_fingerprint
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      readablePermissionEvidence : Prop) :
    ay_vapg_readable_artifact_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest readablePermissionEvidence ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _resultProof _certificateProof _checkerProof fingerprintProof
          _buildProof _archiveProof _submissionProof _readableProof =>
        fingerprintProof)

theorem ay_vapg_readable_artifact_contract_build
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      readablePermissionEvidence : Prop) :
    ay_vapg_readable_artifact_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest readablePermissionEvidence ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          buildProof _archiveProof _submissionProof _readableProof =>
        buildProof)

theorem ay_vapg_readable_artifact_contract_archive
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      readablePermissionEvidence : Prop) :
    ay_vapg_readable_artifact_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest readablePermissionEvidence ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof archiveProof _submissionProof _readableProof =>
        archiveProof)

theorem ay_vapg_readable_artifact_contract_submission
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      readablePermissionEvidence : Prop) :
    ay_vapg_readable_artifact_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest readablePermissionEvidence ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof submissionProof _readableProof =>
        submissionProof)

theorem ay_vapg_readable_artifact_contract_readable_permission
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      readablePermissionEvidence : Prop) :
    ay_vapg_readable_artifact_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest readablePermissionEvidence ->
    readablePermissionEvidence :=
  fun contract =>
    contract readablePermissionEvidence
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof readableProof =>
        readableProof)

theorem ay_vapg_sat_publication_intro
    (readableContract modelEvidence originalModel : Prop) :
    readableContract -> modelEvidence -> originalModel ->
    ay_vapg_sat_publication readableContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vapg_conj_intro readableContract
      (ay_vapg_conj modelEvidence originalModel) contractProof
      (ay_vapg_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vapg_sat_publication_original_model
    (readableContract modelEvidence originalModel : Prop) :
    ay_vapg_sat_publication readableContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vapg_conj_right modelEvidence originalModel
      (ay_vapg_conj_right readableContract
        (ay_vapg_conj modelEvidence originalModel) publication)

theorem ay_vapg_unsat_publication_intro
    (readableContract proofEvidence originalEmptyClause : Prop) :
    readableContract -> proofEvidence -> originalEmptyClause ->
    ay_vapg_unsat_publication readableContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vapg_conj_intro readableContract
      (ay_vapg_conj proofEvidence originalEmptyClause) contractProof
      (ay_vapg_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vapg_unsat_publication_original_empty_clause
    (readableContract proofEvidence originalEmptyClause : Prop) :
    ay_vapg_unsat_publication readableContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vapg_conj_right proofEvidence originalEmptyClause
      (ay_vapg_conj_right readableContract
        (ay_vapg_conj proofEvidence originalEmptyClause) publication)

theorem ay_vapg_accepted_readable_artifact_sat_sound
    (readableContract modelEvidence originalModel : Prop) :
    ay_vapg_sat_publication readableContract modelEvidence originalModel ->
    originalModel :=
  ay_vapg_sat_publication_original_model readableContract modelEvidence
    originalModel

theorem ay_vapg_accepted_readable_artifact_unsat_sound
    (readableContract proofEvidence originalEmptyClause : Prop) :
    ay_vapg_unsat_publication readableContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_vapg_unsat_publication_original_empty_clause readableContract
    proofEvidence originalEmptyClause

theorem ay_vapg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vapg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vapg_conj_intro reason (ay_vapg_conj fallbackPath auditTrail)
      reasonProof
      (ay_vapg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_vapg_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vapg_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vapg_conj_left reason (ay_vapg_conj fallbackPath auditTrail)
      noClaim

theorem ay_vapg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vapg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_vapg_conj_intro reason
      (ay_vapg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_vapg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_vapg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vapg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vapg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_vapg_conj_right reason
        (ay_vapg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vapg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vapg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vapg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_vapg_conj_right reason
        (ay_vapg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vapg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vapg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vapg_conj_intro reason
      (ay_vapg_conj fallbackPath recomputeObligation) reasonProof
      (ay_vapg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_vapg_permission_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vapg_permission_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_vapg_conj_intro
      (ay_vapg_blocked_publication satFact unsatFact reason)
      (ay_vapg_recompute reason fallbackPath recomputeObligation)
      (ay_vapg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_vapg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vapg_permission_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vapg_permission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vapg_blocked_publication_no_sat satFact unsatFact reason
      (ay_vapg_conj_left
        (ay_vapg_blocked_publication satFact unsatFact reason)
        (ay_vapg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vapg_permission_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vapg_permission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vapg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vapg_conj_left
        (ay_vapg_blocked_publication satFact unsatFact reason)
        (ay_vapg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vapg_permission_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vapg_permission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vapg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vapg_conj_right
      (ay_vapg_blocked_publication satFact unsatFact reason)
      (ay_vapg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vapg_permission_read_failure_forces_no_claim
    (satFact unsatFact permissionReadFailure fallbackPath auditTrail
      recomputeObligation : Prop) :
    permissionReadFailure -> fallbackPath -> auditTrail ->
    recomputeObligation -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vapg_no_claim permissionReadFailure fallbackPath auditTrail :=
  fun failureProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_vapg_no_claim_intro permissionReadFailure fallbackPath auditTrail
      failureProof fallbackProof auditProof

theorem ay_vapg_incomplete_artifact_forces_no_claim
    (satFact unsatFact incompleteArtifact fallbackPath auditTrail
      recomputeObligation : Prop) :
    incompleteArtifact -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vapg_no_claim incompleteArtifact fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vapg_no_claim_intro incompleteArtifact fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vapg_missing_checker_forces_no_claim
    (satFact unsatFact missingChecker fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingChecker -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vapg_no_claim missingChecker fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vapg_no_claim_intro missingChecker fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vapg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vapg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vapg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vapg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vapg_no_claim buildMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vapg_no_claim_intro buildMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vapg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vapg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vapg_no_claim_intro archiveMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vapg_submission_mismatch_forces_no_claim
    (satFact unsatFact submissionMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    submissionMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vapg_no_claim submissionMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vapg_no_claim_intro submissionMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vapg_failed_permission_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vapg_permission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vapg_permission_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vapg_failed_permission_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vapg_permission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vapg_permission_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation
