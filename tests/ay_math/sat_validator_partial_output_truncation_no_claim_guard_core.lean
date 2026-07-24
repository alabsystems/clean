-- SAT-COMP validator partial-output truncation no-claim guard core.
--
-- Partial or truncated stdout/stderr and result artifacts publish no semantic
-- SAT/UNSAT claim unless complete-output evidence and all validation artifacts
-- agree.

def ay_vpot_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vpot_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vpot_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vpot_disj satFact (ay_vpot_disj unsatFact noClaimFact)

def ay_vpot_complete_output_contract
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      truncationFreeEvidence : Prop) : Prop :=
  forall result : Prop,
    (completeResultArtifact -> certificateModel -> checkerTranscript ->
      benchmarkFingerprint -> buildConfig -> archiveManifest ->
      submissionManifest -> truncationFreeEvidence -> result) ->
    result

def ay_vpot_sat_publication
    (completeOutputContract modelEvidence originalModel : Prop) : Prop :=
  ay_vpot_conj completeOutputContract
    (ay_vpot_conj modelEvidence originalModel)

def ay_vpot_unsat_publication
    (completeOutputContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vpot_conj completeOutputContract
    (ay_vpot_conj proofEvidence originalEmptyClause)

def ay_vpot_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vpot_conj reason (ay_vpot_conj fallbackPath auditTrail)

def ay_vpot_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vpot_conj reason
    (ay_vpot_conj (satFact -> False) (unsatFact -> False))

def ay_vpot_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vpot_conj reason
    (ay_vpot_conj fallbackPath recomputeObligation)

def ay_vpot_truncation_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vpot_conj
    (ay_vpot_blocked_publication satFact unsatFact reason)
    (ay_vpot_recompute reason fallbackPath recomputeObligation)

theorem ay_vpot_conj_intro (left right : Prop) :
    left -> right -> ay_vpot_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vpot_conj_left (left right : Prop) :
    ay_vpot_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vpot_conj_right (left right : Prop) :
    ay_vpot_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vpot_disj_left (left right : Prop) :
    left -> ay_vpot_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vpot_disj_right (left right : Prop) :
    right -> ay_vpot_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vpot_complete_output_contract_intro
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      truncationFreeEvidence : Prop) :
    completeResultArtifact -> certificateModel -> checkerTranscript ->
    benchmarkFingerprint -> buildConfig -> archiveManifest ->
    submissionManifest -> truncationFreeEvidence ->
    ay_vpot_complete_output_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest truncationFreeEvidence :=
  fun resultProof certificateProof checkerProof fingerprintProof buildProof
      archiveProof submissionProof truncationProof result build =>
    build resultProof certificateProof checkerProof fingerprintProof buildProof
      archiveProof submissionProof truncationProof

theorem ay_vpot_complete_output_contract_result_artifact
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      truncationFreeEvidence : Prop) :
    ay_vpot_complete_output_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest truncationFreeEvidence ->
    completeResultArtifact :=
  fun contract =>
    contract completeResultArtifact
      (fun resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof _truncationProof =>
        resultProof)

theorem ay_vpot_complete_output_contract_certificate_model
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      truncationFreeEvidence : Prop) :
    ay_vpot_complete_output_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest truncationFreeEvidence ->
    certificateModel :=
  fun contract =>
    contract certificateModel
      (fun _resultProof certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof _truncationProof =>
        certificateProof)

theorem ay_vpot_complete_output_contract_checker
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      truncationFreeEvidence : Prop) :
    ay_vpot_complete_output_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest truncationFreeEvidence ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _resultProof _certificateProof checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof _truncationProof =>
        checkerProof)

theorem ay_vpot_complete_output_contract_fingerprint
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      truncationFreeEvidence : Prop) :
    ay_vpot_complete_output_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest truncationFreeEvidence ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _resultProof _certificateProof _checkerProof fingerprintProof
          _buildProof _archiveProof _submissionProof _truncationProof =>
        fingerprintProof)

theorem ay_vpot_complete_output_contract_build
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      truncationFreeEvidence : Prop) :
    ay_vpot_complete_output_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest truncationFreeEvidence ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          buildProof _archiveProof _submissionProof _truncationProof =>
        buildProof)

theorem ay_vpot_complete_output_contract_archive
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      truncationFreeEvidence : Prop) :
    ay_vpot_complete_output_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest truncationFreeEvidence ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof archiveProof _submissionProof _truncationProof =>
        archiveProof)

theorem ay_vpot_complete_output_contract_submission
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      truncationFreeEvidence : Prop) :
    ay_vpot_complete_output_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest truncationFreeEvidence ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof submissionProof _truncationProof =>
        submissionProof)

theorem ay_vpot_complete_output_contract_truncation_free
    (completeResultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      truncationFreeEvidence : Prop) :
    ay_vpot_complete_output_contract completeResultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest truncationFreeEvidence ->
    truncationFreeEvidence :=
  fun contract =>
    contract truncationFreeEvidence
      (fun _resultProof _certificateProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _submissionProof truncationProof =>
        truncationProof)

theorem ay_vpot_sat_publication_intro
    (completeOutputContract modelEvidence originalModel : Prop) :
    completeOutputContract -> modelEvidence -> originalModel ->
    ay_vpot_sat_publication completeOutputContract modelEvidence
      originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vpot_conj_intro completeOutputContract
      (ay_vpot_conj modelEvidence originalModel) contractProof
      (ay_vpot_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vpot_sat_publication_original_model
    (completeOutputContract modelEvidence originalModel : Prop) :
    ay_vpot_sat_publication completeOutputContract modelEvidence
      originalModel ->
    originalModel :=
  fun publication =>
    ay_vpot_conj_right modelEvidence originalModel
      (ay_vpot_conj_right completeOutputContract
        (ay_vpot_conj modelEvidence originalModel) publication)

theorem ay_vpot_unsat_publication_intro
    (completeOutputContract proofEvidence originalEmptyClause : Prop) :
    completeOutputContract -> proofEvidence -> originalEmptyClause ->
    ay_vpot_unsat_publication completeOutputContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vpot_conj_intro completeOutputContract
      (ay_vpot_conj proofEvidence originalEmptyClause) contractProof
      (ay_vpot_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vpot_unsat_publication_original_empty_clause
    (completeOutputContract proofEvidence originalEmptyClause : Prop) :
    ay_vpot_unsat_publication completeOutputContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vpot_conj_right proofEvidence originalEmptyClause
      (ay_vpot_conj_right completeOutputContract
        (ay_vpot_conj proofEvidence originalEmptyClause) publication)

theorem ay_vpot_accepted_complete_output_sat_sound
    (completeOutputContract modelEvidence originalModel : Prop) :
    ay_vpot_sat_publication completeOutputContract modelEvidence
      originalModel ->
    originalModel :=
  ay_vpot_sat_publication_original_model completeOutputContract modelEvidence
    originalModel

theorem ay_vpot_accepted_complete_output_unsat_sound
    (completeOutputContract proofEvidence originalEmptyClause : Prop) :
    ay_vpot_unsat_publication completeOutputContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_vpot_unsat_publication_original_empty_clause completeOutputContract
    proofEvidence originalEmptyClause

theorem ay_vpot_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vpot_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vpot_conj_intro reason (ay_vpot_conj fallbackPath auditTrail)
      reasonProof
      (ay_vpot_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_vpot_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vpot_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vpot_conj_left reason (ay_vpot_conj fallbackPath auditTrail)
      noClaim

theorem ay_vpot_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vpot_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_vpot_conj_intro reason
      (ay_vpot_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_vpot_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_vpot_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vpot_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vpot_conj_left (satFact -> False) (unsatFact -> False)
      (ay_vpot_conj_right reason
        (ay_vpot_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vpot_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vpot_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vpot_conj_right (satFact -> False) (unsatFact -> False)
      (ay_vpot_conj_right reason
        (ay_vpot_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vpot_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vpot_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vpot_conj_intro reason
      (ay_vpot_conj fallbackPath recomputeObligation) reasonProof
      (ay_vpot_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_vpot_truncation_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vpot_truncation_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_vpot_conj_intro
      (ay_vpot_blocked_publication satFact unsatFact reason)
      (ay_vpot_recompute reason fallbackPath recomputeObligation)
      (ay_vpot_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_vpot_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vpot_truncation_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vpot_truncation_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vpot_blocked_publication_no_sat satFact unsatFact reason
      (ay_vpot_conj_left
        (ay_vpot_blocked_publication satFact unsatFact reason)
        (ay_vpot_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vpot_truncation_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vpot_truncation_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vpot_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vpot_conj_left
        (ay_vpot_blocked_publication satFact unsatFact reason)
        (ay_vpot_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vpot_truncation_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vpot_truncation_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vpot_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vpot_conj_right
      (ay_vpot_blocked_publication satFact unsatFact reason)
      (ay_vpot_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vpot_truncation_forces_no_claim
    (satFact unsatFact truncation fallbackPath auditTrail
      recomputeObligation : Prop) :
    truncation -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vpot_no_claim truncation fallbackPath auditTrail :=
  fun truncationProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_vpot_no_claim_intro truncation fallbackPath auditTrail
      truncationProof fallbackProof auditProof

theorem ay_vpot_incomplete_artifact_forces_no_claim
    (satFact unsatFact incompleteArtifact fallbackPath auditTrail
      recomputeObligation : Prop) :
    incompleteArtifact -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vpot_no_claim incompleteArtifact fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vpot_no_claim_intro incompleteArtifact fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vpot_missing_checker_forces_no_claim
    (satFact unsatFact missingChecker fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingChecker -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vpot_no_claim missingChecker fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vpot_no_claim_intro missingChecker fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vpot_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vpot_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vpot_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vpot_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vpot_no_claim buildMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vpot_no_claim_intro buildMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vpot_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vpot_no_claim archiveMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vpot_no_claim_intro archiveMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vpot_submission_mismatch_forces_no_claim
    (satFact unsatFact submissionMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    submissionMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vpot_no_claim submissionMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vpot_no_claim_intro submissionMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vpot_failed_truncation_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vpot_truncation_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vpot_truncation_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vpot_failed_truncation_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vpot_truncation_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vpot_truncation_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation
