-- SAT-COMP validator signal/crash no-claim guard core.
--
-- Signal, crash, or abnormal-exit outcomes publish no semantic SAT/UNSAT
-- claim unless complete artifacts and crash-free exit evidence agree.

def ay_vscg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vscg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vscg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vscg_disj satFact (ay_vscg_disj unsatFact noClaimFact)

def ay_vscg_crash_free_contract
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      crashFreeExit : Prop) : Prop :=
  forall result : Prop,
    (completeResultArtifact -> certificateModel -> checkerTranscript ->
      benchmarkFingerprint -> buildConfig -> archiveManifest ->
      submissionManifest -> crashFreeExit -> result) ->
    result

def ay_vscg_sat_publication
    (crashFreeContract modelEvidence originalModel : Prop) : Prop :=
  ay_vscg_conj crashFreeContract
    (ay_vscg_conj modelEvidence originalModel)

def ay_vscg_unsat_publication
    (crashFreeContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vscg_conj crashFreeContract
    (ay_vscg_conj proofEvidence originalEmptyClause)

def ay_vscg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vscg_conj reason (ay_vscg_conj fallbackPath auditTrail)

def ay_vscg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vscg_conj reason
    (ay_vscg_conj (satFact -> False) (unsatFact -> False))

def ay_vscg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vscg_conj reason
    (ay_vscg_conj fallbackPath recomputeObligation)

def ay_vscg_crash_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vscg_conj
    (ay_vscg_blocked_publication satFact unsatFact reason)
    (ay_vscg_recompute reason fallbackPath recomputeObligation)

theorem ay_vscg_conj_intro (left right : Prop) :
    left -> right -> ay_vscg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vscg_conj_left (left right : Prop) :
    ay_vscg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vscg_conj_right (left right : Prop) :
    ay_vscg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vscg_disj_left (left right : Prop) :
    left -> ay_vscg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vscg_disj_right (left right : Prop) :
    right -> ay_vscg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vscg_crash_free_contract_intro
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      crashFreeExit : Prop) :
    completeResultArtifact -> certificateModel -> checkerTranscript ->
    benchmarkFingerprint -> buildConfig -> archiveManifest ->
    submissionManifest -> crashFreeExit ->
    ay_vscg_crash_free_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest crashFreeExit :=
  fun resultProof certificateProof checkerProof fingerprintProof buildProof
      archiveProof submissionProof exitProof result build =>
    build resultProof certificateProof checkerProof fingerprintProof buildProof
      archiveProof submissionProof exitProof

theorem ay_vscg_crash_free_contract_result_artifact
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      crashFreeExit : Prop) :
    ay_vscg_crash_free_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest crashFreeExit ->
    completeResultArtifact :=
  fun contract =>
    contract completeResultArtifact
      (fun resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof _exitProof =>
        resultProof)

theorem ay_vscg_crash_free_contract_certificate_model
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      crashFreeExit : Prop) :
    ay_vscg_crash_free_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest crashFreeExit ->
    certificateModel :=
  fun contract =>
    contract certificateModel
      (fun _resultProof certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof _exitProof =>
        certificateProof)

theorem ay_vscg_crash_free_contract_checker
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      crashFreeExit : Prop) :
    ay_vscg_crash_free_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest crashFreeExit ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _resultProof _certificateProof checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof _exitProof =>
        checkerProof)

theorem ay_vscg_crash_free_contract_fingerprint
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      crashFreeExit : Prop) :
    ay_vscg_crash_free_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest crashFreeExit ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _resultProof _certificateProof _checkerProof fingerprintProof
          _buildProof _archiveProof _submissionProof _exitProof =>
        fingerprintProof)

theorem ay_vscg_crash_free_contract_build
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      crashFreeExit : Prop) :
    ay_vscg_crash_free_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest crashFreeExit ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          buildProof _archiveProof _submissionProof _exitProof => buildProof)

theorem ay_vscg_crash_free_contract_archive
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      crashFreeExit : Prop) :
    ay_vscg_crash_free_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest crashFreeExit ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof archiveProof _submissionProof _exitProof =>
        archiveProof)

theorem ay_vscg_crash_free_contract_submission
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      crashFreeExit : Prop) :
    ay_vscg_crash_free_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest crashFreeExit ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof submissionProof _exitProof =>
        submissionProof)

theorem ay_vscg_crash_free_contract_exit
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      crashFreeExit : Prop) :
    ay_vscg_crash_free_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest crashFreeExit ->
    crashFreeExit :=
  fun contract =>
    contract crashFreeExit
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof exitProof => exitProof)

theorem ay_vscg_sat_publication_intro
    (crashFreeContract modelEvidence originalModel : Prop) :
    crashFreeContract -> modelEvidence -> originalModel ->
    ay_vscg_sat_publication crashFreeContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vscg_conj_intro crashFreeContract
      (ay_vscg_conj modelEvidence originalModel) contractProof
      (ay_vscg_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vscg_sat_publication_original_model
    (crashFreeContract modelEvidence originalModel : Prop) :
    ay_vscg_sat_publication crashFreeContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vscg_conj_right modelEvidence originalModel
      (ay_vscg_conj_right crashFreeContract
        (ay_vscg_conj modelEvidence originalModel) publication)

theorem ay_vscg_unsat_publication_intro
    (crashFreeContract proofEvidence originalEmptyClause : Prop) :
    crashFreeContract -> proofEvidence -> originalEmptyClause ->
    ay_vscg_unsat_publication crashFreeContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vscg_conj_intro crashFreeContract
      (ay_vscg_conj proofEvidence originalEmptyClause) contractProof
      (ay_vscg_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vscg_unsat_publication_original_empty_clause
    (crashFreeContract proofEvidence originalEmptyClause : Prop) :
    ay_vscg_unsat_publication crashFreeContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vscg_conj_right proofEvidence originalEmptyClause
      (ay_vscg_conj_right crashFreeContract
        (ay_vscg_conj proofEvidence originalEmptyClause) publication)

theorem ay_vscg_accepted_crash_free_sat_sound
    (crashFreeContract modelEvidence originalModel : Prop) :
    ay_vscg_sat_publication crashFreeContract modelEvidence originalModel ->
    originalModel :=
  ay_vscg_sat_publication_original_model crashFreeContract modelEvidence
    originalModel

theorem ay_vscg_accepted_crash_free_unsat_sound
    (crashFreeContract proofEvidence originalEmptyClause : Prop) :
    ay_vscg_unsat_publication crashFreeContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_vscg_unsat_publication_original_empty_clause crashFreeContract
    proofEvidence originalEmptyClause

theorem ay_vscg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vscg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vscg_conj_intro reason (ay_vscg_conj fallbackPath auditTrail)
      reasonProof
      (ay_vscg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_vscg_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vscg_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vscg_conj_left reason (ay_vscg_conj fallbackPath auditTrail)
      noClaim

theorem ay_vscg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vscg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_vscg_conj_intro reason
      (ay_vscg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_vscg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_vscg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vscg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vscg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_vscg_conj_right reason
        (ay_vscg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vscg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vscg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vscg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_vscg_conj_right reason
        (ay_vscg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vscg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vscg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vscg_conj_intro reason
      (ay_vscg_conj fallbackPath recomputeObligation) reasonProof
      (ay_vscg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_vscg_crash_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vscg_crash_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_vscg_conj_intro
      (ay_vscg_blocked_publication satFact unsatFact reason)
      (ay_vscg_recompute reason fallbackPath recomputeObligation)
      (ay_vscg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_vscg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vscg_crash_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vscg_crash_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vscg_blocked_publication_no_sat satFact unsatFact reason
      (ay_vscg_conj_left
        (ay_vscg_blocked_publication satFact unsatFact reason)
        (ay_vscg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vscg_crash_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vscg_crash_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vscg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vscg_conj_left
        (ay_vscg_blocked_publication satFact unsatFact reason)
        (ay_vscg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vscg_crash_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vscg_crash_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vscg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vscg_conj_right
      (ay_vscg_blocked_publication satFact unsatFact reason)
      (ay_vscg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vscg_signal_crash_forces_no_claim
    (satFact unsatFact signalCrash fallbackPath auditTrail
      recomputeObligation : Prop) :
    signalCrash -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vscg_no_claim signalCrash fallbackPath auditTrail :=
  fun crashProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vscg_no_claim_intro signalCrash fallbackPath auditTrail crashProof
      fallbackProof auditProof

theorem ay_vscg_incomplete_artifact_forces_no_claim
    (satFact unsatFact incompleteArtifact fallbackPath auditTrail
      recomputeObligation : Prop) :
    incompleteArtifact -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vscg_no_claim incompleteArtifact fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vscg_no_claim_intro incompleteArtifact fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vscg_missing_checker_forces_no_claim
    (satFact unsatFact missingChecker fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingChecker -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vscg_no_claim missingChecker fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vscg_no_claim_intro missingChecker fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vscg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vscg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vscg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vscg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vscg_no_claim buildMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vscg_no_claim_intro buildMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vscg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vscg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vscg_no_claim_intro archiveMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vscg_submission_mismatch_forces_no_claim
    (satFact unsatFact submissionMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    submissionMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vscg_no_claim submissionMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vscg_no_claim_intro submissionMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vscg_failed_crash_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vscg_crash_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vscg_crash_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vscg_failed_crash_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vscg_crash_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vscg_crash_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
