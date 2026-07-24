-- SAT-COMP validator result-code table guard core.
--
-- Public reports are produced only from checked SAT/UNSAT/no-claim outcomes
-- whose exit code, signal ledger, stdout status token, checker transcript,
-- model/proof artifact digest, benchmark fingerprint, track/category manifest,
-- solver build evidence, archive manifest, fallback, and audit transcript
-- agree.

def ay_rctg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rctg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_rctg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_rctg_disj satFact (ay_rctg_disj unsatFact noClaimFact)

def ay_rctg_result_code_contract
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (solverExitCode -> signalLedger -> stdoutStatusToken ->
      checkerTranscript -> modelProofArtifactDigest -> benchmarkFingerprint ->
      trackCategoryManifest -> solverBuildEvidence -> archiveManifest ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_rctg_checked_outcome
    (checkedSat checkedUnsat checkedNoClaim : Prop) : Prop :=
  ay_rctg_public_result checkedSat checkedUnsat checkedNoClaim

def ay_rctg_sat_publication
    (codeContract checkedSat originalModel : Prop) : Prop :=
  ay_rctg_conj codeContract (ay_rctg_conj checkedSat originalModel)

def ay_rctg_unsat_publication
    (codeContract checkedUnsat originalEmptyClause : Prop) : Prop :=
  ay_rctg_conj codeContract
    (ay_rctg_conj checkedUnsat originalEmptyClause)

def ay_rctg_no_claim_publication
    (codeContract checkedNoClaim auditTrail : Prop) : Prop :=
  ay_rctg_conj codeContract (ay_rctg_conj checkedNoClaim auditTrail)

def ay_rctg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_rctg_conj reason (ay_rctg_conj fallbackPath auditTrail)

def ay_rctg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_rctg_conj reason
    (ay_rctg_conj (satFact -> False) (unsatFact -> False))

def ay_rctg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_rctg_conj reason
    (ay_rctg_conj fallbackPath recomputeObligation)

def ay_rctg_result_code_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_rctg_conj
    (ay_rctg_blocked_publication satFact unsatFact reason)
    (ay_rctg_recompute reason fallbackPath recomputeObligation)

theorem ay_rctg_conj_intro (left right : Prop) :
    left -> right -> ay_rctg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_rctg_conj_left (left right : Prop) :
    ay_rctg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_rctg_conj_right (left right : Prop) :
    ay_rctg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_rctg_disj_left (left right : Prop) :
    left -> ay_rctg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_rctg_disj_right (left right : Prop) :
    right -> ay_rctg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_rctg_result_code_contract_intro
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    solverExitCode -> signalLedger -> stdoutStatusToken ->
    checkerTranscript -> modelProofArtifactDigest -> benchmarkFingerprint ->
    trackCategoryManifest -> solverBuildEvidence -> archiveManifest ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript :=
  fun exitProof signalProof statusProof checkerProof artifactProof
      fingerprintProof trackProof buildProof archiveProof fallbackProof
      auditProof result build =>
    build exitProof signalProof statusProof checkerProof artifactProof
      fingerprintProof trackProof buildProof archiveProof fallbackProof
      auditProof

theorem ay_rctg_contract_exit
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverExitCode :=
  fun contract =>
    contract solverExitCode
      (fun exitProof _signalProof _statusProof _checkerProof _artifactProof
          _fingerprintProof _trackProof _buildProof _archiveProof
          _fallbackProof _auditProof => exitProof)

theorem ay_rctg_contract_signal
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    signalLedger :=
  fun contract =>
    contract signalLedger
      (fun _exitProof signalProof _statusProof _checkerProof _artifactProof
          _fingerprintProof _trackProof _buildProof _archiveProof
          _fallbackProof _auditProof => signalProof)

theorem ay_rctg_contract_status
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    stdoutStatusToken :=
  fun contract =>
    contract stdoutStatusToken
      (fun _exitProof _signalProof statusProof _checkerProof _artifactProof
          _fingerprintProof _trackProof _buildProof _archiveProof
          _fallbackProof _auditProof => statusProof)

theorem ay_rctg_contract_checker
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _exitProof _signalProof _statusProof checkerProof _artifactProof
          _fingerprintProof _trackProof _buildProof _archiveProof
          _fallbackProof _auditProof => checkerProof)

theorem ay_rctg_contract_artifact
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _exitProof _signalProof _statusProof _checkerProof artifactProof
          _fingerprintProof _trackProof _buildProof _archiveProof
          _fallbackProof _auditProof => artifactProof)

theorem ay_rctg_contract_fingerprint
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _exitProof _signalProof _statusProof _checkerProof _artifactProof
          fingerprintProof _trackProof _buildProof _archiveProof
          _fallbackProof _auditProof => fingerprintProof)

theorem ay_rctg_contract_track
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    trackCategoryManifest :=
  fun contract =>
    contract trackCategoryManifest
      (fun _exitProof _signalProof _statusProof _checkerProof _artifactProof
          _fingerprintProof trackProof _buildProof _archiveProof
          _fallbackProof _auditProof => trackProof)

theorem ay_rctg_contract_build
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _exitProof _signalProof _statusProof _checkerProof _artifactProof
          _fingerprintProof _trackProof buildProof _archiveProof
          _fallbackProof _auditProof => buildProof)

theorem ay_rctg_contract_archive
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _exitProof _signalProof _statusProof _checkerProof _artifactProof
          _fingerprintProof _trackProof _buildProof archiveProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_rctg_contract_fallback
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _exitProof _signalProof _statusProof _checkerProof _artifactProof
          _fingerprintProof _trackProof _buildProof _archiveProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_rctg_contract_audit
    (solverExitCode signalLedger stdoutStatusToken checkerTranscript
      modelProofArtifactDigest benchmarkFingerprint trackCategoryManifest
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_rctg_result_code_contract solverExitCode signalLedger
      stdoutStatusToken checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint trackCategoryManifest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _exitProof _signalProof _statusProof _checkerProof _artifactProof
          _fingerprintProof _trackProof _buildProof _archiveProof
          _fallbackProof auditProof => auditProof)

theorem ay_rctg_checked_sat_maps_to_public_report
    (codeContract checkedSat originalModel : Prop) :
    codeContract -> checkedSat -> originalModel ->
    ay_rctg_sat_publication codeContract checkedSat originalModel :=
  fun contractProof satProof modelProof =>
    ay_rctg_conj_intro codeContract
      (ay_rctg_conj checkedSat originalModel) contractProof
      (ay_rctg_conj_intro checkedSat originalModel satProof modelProof)

theorem ay_rctg_checked_unsat_maps_to_public_report
    (codeContract checkedUnsat originalEmptyClause : Prop) :
    codeContract -> checkedUnsat -> originalEmptyClause ->
    ay_rctg_unsat_publication codeContract checkedUnsat
      originalEmptyClause :=
  fun contractProof unsatProof emptyProof =>
    ay_rctg_conj_intro codeContract
      (ay_rctg_conj checkedUnsat originalEmptyClause) contractProof
      (ay_rctg_conj_intro checkedUnsat originalEmptyClause unsatProof
        emptyProof)

theorem ay_rctg_checked_no_claim_maps_to_public_report
    (codeContract checkedNoClaim auditTrail : Prop) :
    codeContract -> checkedNoClaim -> auditTrail ->
    ay_rctg_no_claim_publication codeContract checkedNoClaim auditTrail :=
  fun contractProof noClaimProof auditProof =>
    ay_rctg_conj_intro codeContract
      (ay_rctg_conj checkedNoClaim auditTrail) contractProof
      (ay_rctg_conj_intro checkedNoClaim auditTrail noClaimProof auditProof)

theorem ay_rctg_sat_publication_original_model
    (codeContract checkedSat originalModel : Prop) :
    ay_rctg_sat_publication codeContract checkedSat originalModel ->
    originalModel :=
  fun publication =>
    ay_rctg_conj_right checkedSat originalModel
      (ay_rctg_conj_right codeContract
        (ay_rctg_conj checkedSat originalModel) publication)

theorem ay_rctg_unsat_publication_original_empty_clause
    (codeContract checkedUnsat originalEmptyClause : Prop) :
    ay_rctg_unsat_publication codeContract checkedUnsat
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_rctg_conj_right checkedUnsat originalEmptyClause
      (ay_rctg_conj_right codeContract
        (ay_rctg_conj checkedUnsat originalEmptyClause) publication)

theorem ay_rctg_accepted_sat_code_is_checked_public_sat
    (codeContract checkedSat originalModel : Prop) :
    ay_rctg_sat_publication codeContract checkedSat originalModel ->
    ay_rctg_public_result originalModel False False :=
  fun publication =>
    ay_rctg_disj_left originalModel (ay_rctg_disj False False)
      (ay_rctg_sat_publication_original_model codeContract checkedSat
        originalModel publication)

theorem ay_rctg_accepted_unsat_code_is_checked_public_unsat
    (codeContract checkedUnsat originalEmptyClause : Prop) :
    ay_rctg_unsat_publication codeContract checkedUnsat
      originalEmptyClause ->
    ay_rctg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_rctg_disj_right False (ay_rctg_disj originalEmptyClause False)
      (ay_rctg_disj_left originalEmptyClause False
        (ay_rctg_unsat_publication_original_empty_clause codeContract
          checkedUnsat originalEmptyClause publication))

theorem ay_rctg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_rctg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_rctg_conj_intro reason (ay_rctg_conj fallbackPath auditTrail)
      reasonProof
      (ay_rctg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_rctg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_rctg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_rctg_conj_intro reason
      (ay_rctg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_rctg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_rctg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_rctg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_rctg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_rctg_conj_right reason
        (ay_rctg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rctg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_rctg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_rctg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_rctg_conj_right reason
        (ay_rctg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rctg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_rctg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_rctg_conj_intro reason
      (ay_rctg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_rctg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_rctg_result_code_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rctg_blocked_publication satFact unsatFact reason ->
    ay_rctg_recompute reason fallbackPath recomputeObligation ->
    ay_rctg_result_code_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_rctg_conj_intro
      (ay_rctg_blocked_publication satFact unsatFact reason)
      (ay_rctg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_rctg_result_code_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rctg_result_code_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_rctg_blocked_publication_no_sat satFact unsatFact reason
      (ay_rctg_conj_left
        (ay_rctg_blocked_publication satFact unsatFact reason)
        (ay_rctg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rctg_result_code_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rctg_result_code_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_rctg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_rctg_conj_left
        (ay_rctg_blocked_publication satFact unsatFact reason)
        (ay_rctg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rctg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rctg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rctg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rctg_exit_mismatch_forces_no_claim
    (satFact unsatFact exitMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    exitMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rctg_no_claim exitMismatch fallbackPath auditTrail :=
  ay_rctg_mismatch_forces_no_claim satFact unsatFact exitMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_rctg_signal_mismatch_forces_no_claim
    (satFact unsatFact signalMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    signalMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rctg_no_claim signalMismatch fallbackPath auditTrail :=
  ay_rctg_mismatch_forces_no_claim satFact unsatFact signalMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_rctg_status_mismatch_forces_no_claim
    (satFact unsatFact statusMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    statusMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rctg_no_claim statusMismatch fallbackPath auditTrail :=
  ay_rctg_mismatch_forces_no_claim satFact unsatFact statusMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_rctg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rctg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_rctg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_rctg_artifact_mismatch_forces_no_claim
    (satFact unsatFact artifactMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rctg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_rctg_mismatch_forces_no_claim satFact unsatFact artifactMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_rctg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rctg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_rctg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_rctg_track_mismatch_forces_no_claim
    (satFact unsatFact trackMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    trackMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rctg_no_claim trackMismatch fallbackPath auditTrail :=
  ay_rctg_mismatch_forces_no_claim satFact unsatFact trackMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_rctg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rctg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_rctg_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_rctg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rctg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_rctg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_rctg_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rctg_no_claim auditMismatch fallbackPath auditTrail :=
  ay_rctg_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_rctg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_rctg_result_code_failure satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_rctg_result_code_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_rctg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_rctg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_rctg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rctg_result_code_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_rctg_result_code_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_rctg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rctg_result_code_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_rctg_result_code_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_rctg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_rctg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_rctg_conj_left reason (ay_rctg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_rctg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_rctg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_rctg_conj_left reason (ay_rctg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
