-- SAT-COMP validator stdout status-token guard core.
--
-- Public reports are produced only from checker-backed SAT/UNSAT/no-claim
-- status whose stdout digest, unique status-token parse, stderr diagnostics,
-- checker transcript, model/proof artifact digest, benchmark fingerprint,
-- solver build evidence, archive manifest, fallback, and audit transcript
-- agree.

def ay_sstg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_sstg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_sstg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_sstg_disj satFact (ay_sstg_disj unsatFact noClaimFact)

def ay_sstg_stdout_token_contract
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) : Prop :=
  forall result : Prop,
    (stdoutDigest -> uniqueStatusTokenParse -> stderrDiagnosticLedger ->
      checkerTranscript -> modelProofArtifactDigest -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_sstg_checked_status
    (checkedSat checkedUnsat checkedNoClaim : Prop) : Prop :=
  ay_sstg_public_result checkedSat checkedUnsat checkedNoClaim

def ay_sstg_sat_publication
    (tokenContract checkedSat originalModel : Prop) : Prop :=
  ay_sstg_conj tokenContract (ay_sstg_conj checkedSat originalModel)

def ay_sstg_unsat_publication
    (tokenContract checkedUnsat originalEmptyClause : Prop) : Prop :=
  ay_sstg_conj tokenContract
    (ay_sstg_conj checkedUnsat originalEmptyClause)

def ay_sstg_no_claim_publication
    (tokenContract checkedNoClaim auditTrail : Prop) : Prop :=
  ay_sstg_conj tokenContract (ay_sstg_conj checkedNoClaim auditTrail)

def ay_sstg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_sstg_conj reason (ay_sstg_conj fallbackPath auditTrail)

def ay_sstg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_sstg_conj reason
    (ay_sstg_conj (satFact -> False) (unsatFact -> False))

def ay_sstg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_sstg_conj reason
    (ay_sstg_conj fallbackPath recomputeObligation)

def ay_sstg_token_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_sstg_conj
    (ay_sstg_blocked_publication satFact unsatFact reason)
    (ay_sstg_recompute reason fallbackPath recomputeObligation)

theorem ay_sstg_conj_intro (left right : Prop) :
    left -> right -> ay_sstg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_sstg_conj_left (left right : Prop) :
    ay_sstg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_sstg_conj_right (left right : Prop) :
    ay_sstg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_sstg_disj_left (left right : Prop) :
    left -> ay_sstg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_sstg_disj_right (left right : Prop) :
    right -> ay_sstg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_sstg_stdout_token_contract_intro
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    stdoutDigest -> uniqueStatusTokenParse -> stderrDiagnosticLedger ->
    checkerTranscript -> modelProofArtifactDigest -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_sstg_stdout_token_contract stdoutDigest uniqueStatusTokenParse
      stderrDiagnosticLedger checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript :=
  fun stdoutProof tokenProof stderrProof checkerProof artifactProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof result
      build =>
    build stdoutProof tokenProof stderrProof checkerProof artifactProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof

theorem ay_sstg_contract_stdout
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_sstg_stdout_token_contract stdoutDigest uniqueStatusTokenParse
      stderrDiagnosticLedger checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    stdoutDigest :=
  fun contract =>
    contract stdoutDigest
      (fun stdoutProof _tokenProof _stderrProof _checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => stdoutProof)

theorem ay_sstg_contract_unique_token
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_sstg_stdout_token_contract stdoutDigest uniqueStatusTokenParse
      stderrDiagnosticLedger checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    uniqueStatusTokenParse :=
  fun contract =>
    contract uniqueStatusTokenParse
      (fun _stdoutProof tokenProof _stderrProof _checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => tokenProof)

theorem ay_sstg_contract_stderr
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_sstg_stdout_token_contract stdoutDigest uniqueStatusTokenParse
      stderrDiagnosticLedger checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    stderrDiagnosticLedger :=
  fun contract =>
    contract stderrDiagnosticLedger
      (fun _stdoutProof _tokenProof stderrProof _checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => stderrProof)

theorem ay_sstg_contract_checker
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_sstg_stdout_token_contract stdoutDigest uniqueStatusTokenParse
      stderrDiagnosticLedger checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _stdoutProof _tokenProof _stderrProof checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_sstg_contract_artifact
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_sstg_stdout_token_contract stdoutDigest uniqueStatusTokenParse
      stderrDiagnosticLedger checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _stdoutProof _tokenProof _stderrProof _checkerProof artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => artifactProof)

theorem ay_sstg_contract_fingerprint
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_sstg_stdout_token_contract stdoutDigest uniqueStatusTokenParse
      stderrDiagnosticLedger checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _stdoutProof _tokenProof _stderrProof _checkerProof _artifactProof
          fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_sstg_contract_build
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_sstg_stdout_token_contract stdoutDigest uniqueStatusTokenParse
      stderrDiagnosticLedger checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _stdoutProof _tokenProof _stderrProof _checkerProof _artifactProof
          _fingerprintProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_sstg_contract_archive
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_sstg_stdout_token_contract stdoutDigest uniqueStatusTokenParse
      stderrDiagnosticLedger checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _stdoutProof _tokenProof _stderrProof _checkerProof _artifactProof
          _fingerprintProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_sstg_contract_fallback
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_sstg_stdout_token_contract stdoutDigest uniqueStatusTokenParse
      stderrDiagnosticLedger checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _stdoutProof _tokenProof _stderrProof _checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_sstg_contract_audit
    (stdoutDigest uniqueStatusTokenParse stderrDiagnosticLedger
      checkerTranscript modelProofArtifactDigest benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :
      Prop) :
    ay_sstg_stdout_token_contract stdoutDigest uniqueStatusTokenParse
      stderrDiagnosticLedger checkerTranscript modelProofArtifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _stdoutProof _tokenProof _stderrProof _checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_sstg_checked_sat_maps_to_public_report
    (tokenContract checkedSat originalModel : Prop) :
    tokenContract -> checkedSat -> originalModel ->
    ay_sstg_sat_publication tokenContract checkedSat originalModel :=
  fun contractProof satProof modelProof =>
    ay_sstg_conj_intro tokenContract
      (ay_sstg_conj checkedSat originalModel) contractProof
      (ay_sstg_conj_intro checkedSat originalModel satProof modelProof)

theorem ay_sstg_checked_unsat_maps_to_public_report
    (tokenContract checkedUnsat originalEmptyClause : Prop) :
    tokenContract -> checkedUnsat -> originalEmptyClause ->
    ay_sstg_unsat_publication tokenContract checkedUnsat
      originalEmptyClause :=
  fun contractProof unsatProof emptyProof =>
    ay_sstg_conj_intro tokenContract
      (ay_sstg_conj checkedUnsat originalEmptyClause) contractProof
      (ay_sstg_conj_intro checkedUnsat originalEmptyClause unsatProof
        emptyProof)

theorem ay_sstg_checked_no_claim_maps_to_public_report
    (tokenContract checkedNoClaim auditTrail : Prop) :
    tokenContract -> checkedNoClaim -> auditTrail ->
    ay_sstg_no_claim_publication tokenContract checkedNoClaim auditTrail :=
  fun contractProof noClaimProof auditProof =>
    ay_sstg_conj_intro tokenContract
      (ay_sstg_conj checkedNoClaim auditTrail) contractProof
      (ay_sstg_conj_intro checkedNoClaim auditTrail noClaimProof auditProof)

theorem ay_sstg_sat_publication_original_model
    (tokenContract checkedSat originalModel : Prop) :
    ay_sstg_sat_publication tokenContract checkedSat originalModel ->
    originalModel :=
  fun publication =>
    ay_sstg_conj_right checkedSat originalModel
      (ay_sstg_conj_right tokenContract
        (ay_sstg_conj checkedSat originalModel) publication)

theorem ay_sstg_unsat_publication_original_empty_clause
    (tokenContract checkedUnsat originalEmptyClause : Prop) :
    ay_sstg_unsat_publication tokenContract checkedUnsat
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_sstg_conj_right checkedUnsat originalEmptyClause
      (ay_sstg_conj_right tokenContract
        (ay_sstg_conj checkedUnsat originalEmptyClause) publication)

theorem ay_sstg_accepted_sat_token_is_checker_backed_public_sat
    (tokenContract checkedSat originalModel : Prop) :
    ay_sstg_sat_publication tokenContract checkedSat originalModel ->
    ay_sstg_public_result originalModel False False :=
  fun publication =>
    ay_sstg_disj_left originalModel (ay_sstg_disj False False)
      (ay_sstg_sat_publication_original_model tokenContract checkedSat
        originalModel publication)

theorem ay_sstg_accepted_unsat_token_is_checker_backed_public_unsat
    (tokenContract checkedUnsat originalEmptyClause : Prop) :
    ay_sstg_unsat_publication tokenContract checkedUnsat
      originalEmptyClause ->
    ay_sstg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_sstg_disj_right False (ay_sstg_disj originalEmptyClause False)
      (ay_sstg_disj_left originalEmptyClause False
        (ay_sstg_unsat_publication_original_empty_clause tokenContract
          checkedUnsat originalEmptyClause publication))

theorem ay_sstg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_sstg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_sstg_conj_intro reason (ay_sstg_conj fallbackPath auditTrail)
      reasonProof
      (ay_sstg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_sstg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_sstg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_sstg_conj_intro reason
      (ay_sstg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_sstg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_sstg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_sstg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_sstg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_sstg_conj_right reason
        (ay_sstg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_sstg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_sstg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_sstg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_sstg_conj_right reason
        (ay_sstg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_sstg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_sstg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_sstg_conj_intro reason
      (ay_sstg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_sstg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_sstg_token_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sstg_blocked_publication satFact unsatFact reason ->
    ay_sstg_recompute reason fallbackPath recomputeObligation ->
    ay_sstg_token_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_sstg_conj_intro
      (ay_sstg_blocked_publication satFact unsatFact reason)
      (ay_sstg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_sstg_token_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sstg_token_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_sstg_blocked_publication_no_sat satFact unsatFact reason
      (ay_sstg_conj_left
        (ay_sstg_blocked_publication satFact unsatFact reason)
        (ay_sstg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_sstg_token_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sstg_token_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_sstg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_sstg_conj_left
        (ay_sstg_blocked_publication satFact unsatFact reason)
        (ay_sstg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_sstg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sstg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_sstg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_sstg_stdout_mismatch_forces_no_claim
    (satFact unsatFact stdoutMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    stdoutMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sstg_no_claim stdoutMismatch fallbackPath auditTrail :=
  ay_sstg_mismatch_forces_no_claim satFact unsatFact stdoutMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_sstg_duplicate_token_forces_no_claim
    (satFact unsatFact duplicateToken fallbackPath auditTrail
      recomputeObligation : Prop) :
    duplicateToken -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sstg_no_claim duplicateToken fallbackPath auditTrail :=
  ay_sstg_mismatch_forces_no_claim satFact unsatFact duplicateToken
    fallbackPath auditTrail recomputeObligation

theorem ay_sstg_stderr_mismatch_forces_no_claim
    (satFact unsatFact stderrMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    stderrMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sstg_no_claim stderrMismatch fallbackPath auditTrail :=
  ay_sstg_mismatch_forces_no_claim satFact unsatFact stderrMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_sstg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sstg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_sstg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_sstg_artifact_mismatch_forces_no_claim
    (satFact unsatFact artifactMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sstg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_sstg_mismatch_forces_no_claim satFact unsatFact artifactMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_sstg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sstg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_sstg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_sstg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sstg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_sstg_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_sstg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sstg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_sstg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_sstg_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_sstg_no_claim auditMismatch fallbackPath auditTrail :=
  ay_sstg_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_sstg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_sstg_token_failure satFact unsatFact fallbackActivation fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_sstg_token_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_sstg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_sstg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_sstg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sstg_token_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_sstg_token_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_sstg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_sstg_token_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_sstg_token_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_sstg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_sstg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_sstg_conj_left reason (ay_sstg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_sstg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_sstg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_sstg_conj_left reason (ay_sstg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
