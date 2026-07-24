-- SAT-COMP validator checker-version matrix guard core.
--
-- Public SAT/UNSAT claims require solver build evidence, checker binary digest,
-- checker version matrix, proof/model format manifest, command-line manifest,
-- transcript digest, benchmark fingerprint, archive manifest, fallback
-- no-claim path, and audit transcript to agree.

def ay_cvmg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cvmg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cvmg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_cvmg_disj satFact (ay_cvmg_disj unsatFact noClaimFact)

def ay_cvmg_checker_version_contract
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (solverBuildEvidence -> checkerBinaryDigest -> checkerVersionMatrix ->
      proofModelFormatManifest -> commandLineManifest -> transcriptDigest ->
      benchmarkFingerprint -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_cvmg_sat_publication
    (versionContract formatCompatible checkedModel originalModel : Prop) :
    Prop :=
  ay_cvmg_conj versionContract
    (ay_cvmg_conj formatCompatible
      (ay_cvmg_conj checkedModel originalModel))

def ay_cvmg_unsat_publication
    (versionContract formatCompatible checkedProof originalEmptyClause :
      Prop) : Prop :=
  ay_cvmg_conj versionContract
    (ay_cvmg_conj formatCompatible
      (ay_cvmg_conj checkedProof originalEmptyClause))

def ay_cvmg_semantics_preserved
    (originalBenchmarkFormula replayBenchmarkFormula : Prop) : Prop :=
  originalBenchmarkFormula -> replayBenchmarkFormula

def ay_cvmg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_cvmg_conj reason (ay_cvmg_conj fallbackPath auditTrail)

def ay_cvmg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_cvmg_conj reason
    (ay_cvmg_conj (satFact -> False) (unsatFact -> False))

def ay_cvmg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_cvmg_conj reason
    (ay_cvmg_conj fallbackPath recomputeObligation)

def ay_cvmg_checker_version_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_cvmg_conj
    (ay_cvmg_blocked_publication satFact unsatFact reason)
    (ay_cvmg_recompute reason fallbackPath recomputeObligation)

theorem ay_cvmg_conj_intro (left right : Prop) :
    left -> right -> ay_cvmg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_cvmg_conj_left (left right : Prop) :
    ay_cvmg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_cvmg_conj_right (left right : Prop) :
    ay_cvmg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_cvmg_disj_left (left right : Prop) :
    left -> ay_cvmg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_cvmg_disj_right (left right : Prop) :
    right -> ay_cvmg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_cvmg_checker_version_contract_intro
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    solverBuildEvidence -> checkerBinaryDigest -> checkerVersionMatrix ->
    proofModelFormatManifest -> commandLineManifest -> transcriptDigest ->
    benchmarkFingerprint -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_cvmg_checker_version_contract solverBuildEvidence checkerBinaryDigest
      checkerVersionMatrix proofModelFormatManifest commandLineManifest
      transcriptDigest benchmarkFingerprint archiveManifest
      fallbackNoClaimPath auditTranscript :=
  fun solverProof checkerProof versionProof formatProof commandProof
      transcriptProof fingerprintProof archiveProof fallbackProof auditProof
      result build =>
    build solverProof checkerProof versionProof formatProof commandProof
      transcriptProof fingerprintProof archiveProof fallbackProof auditProof

theorem ay_cvmg_contract_solver
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_cvmg_checker_version_contract solverBuildEvidence checkerBinaryDigest
      checkerVersionMatrix proofModelFormatManifest commandLineManifest
      transcriptDigest benchmarkFingerprint archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun solverProof _checkerProof _versionProof _formatProof _commandProof
          _transcriptProof _fingerprintProof _archiveProof _fallbackProof
          _auditProof => solverProof)

theorem ay_cvmg_contract_checker
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_cvmg_checker_version_contract solverBuildEvidence checkerBinaryDigest
      checkerVersionMatrix proofModelFormatManifest commandLineManifest
      transcriptDigest benchmarkFingerprint archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerBinaryDigest :=
  fun contract =>
    contract checkerBinaryDigest
      (fun _solverProof checkerProof _versionProof _formatProof _commandProof
          _transcriptProof _fingerprintProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_cvmg_contract_version
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_cvmg_checker_version_contract solverBuildEvidence checkerBinaryDigest
      checkerVersionMatrix proofModelFormatManifest commandLineManifest
      transcriptDigest benchmarkFingerprint archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerVersionMatrix :=
  fun contract =>
    contract checkerVersionMatrix
      (fun _solverProof _checkerProof versionProof _formatProof _commandProof
          _transcriptProof _fingerprintProof _archiveProof _fallbackProof
          _auditProof => versionProof)

theorem ay_cvmg_contract_format
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_cvmg_checker_version_contract solverBuildEvidence checkerBinaryDigest
      checkerVersionMatrix proofModelFormatManifest commandLineManifest
      transcriptDigest benchmarkFingerprint archiveManifest
      fallbackNoClaimPath auditTranscript ->
    proofModelFormatManifest :=
  fun contract =>
    contract proofModelFormatManifest
      (fun _solverProof _checkerProof _versionProof formatProof _commandProof
          _transcriptProof _fingerprintProof _archiveProof _fallbackProof
          _auditProof => formatProof)

theorem ay_cvmg_contract_command
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_cvmg_checker_version_contract solverBuildEvidence checkerBinaryDigest
      checkerVersionMatrix proofModelFormatManifest commandLineManifest
      transcriptDigest benchmarkFingerprint archiveManifest
      fallbackNoClaimPath auditTranscript ->
    commandLineManifest :=
  fun contract =>
    contract commandLineManifest
      (fun _solverProof _checkerProof _versionProof _formatProof commandProof
          _transcriptProof _fingerprintProof _archiveProof _fallbackProof
          _auditProof => commandProof)

theorem ay_cvmg_contract_transcript
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_cvmg_checker_version_contract solverBuildEvidence checkerBinaryDigest
      checkerVersionMatrix proofModelFormatManifest commandLineManifest
      transcriptDigest benchmarkFingerprint archiveManifest
      fallbackNoClaimPath auditTranscript ->
    transcriptDigest :=
  fun contract =>
    contract transcriptDigest
      (fun _solverProof _checkerProof _versionProof _formatProof _commandProof
          transcriptProof _fingerprintProof _archiveProof _fallbackProof
          _auditProof => transcriptProof)

theorem ay_cvmg_contract_fingerprint
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_cvmg_checker_version_contract solverBuildEvidence checkerBinaryDigest
      checkerVersionMatrix proofModelFormatManifest commandLineManifest
      transcriptDigest benchmarkFingerprint archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _solverProof _checkerProof _versionProof _formatProof _commandProof
          _transcriptProof fingerprintProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_cvmg_contract_archive
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_cvmg_checker_version_contract solverBuildEvidence checkerBinaryDigest
      checkerVersionMatrix proofModelFormatManifest commandLineManifest
      transcriptDigest benchmarkFingerprint archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _solverProof _checkerProof _versionProof _formatProof _commandProof
          _transcriptProof _fingerprintProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_cvmg_contract_fallback
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_cvmg_checker_version_contract solverBuildEvidence checkerBinaryDigest
      checkerVersionMatrix proofModelFormatManifest commandLineManifest
      transcriptDigest benchmarkFingerprint archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _solverProof _checkerProof _versionProof _formatProof _commandProof
          _transcriptProof _fingerprintProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_cvmg_contract_audit
    (solverBuildEvidence checkerBinaryDigest checkerVersionMatrix
      proofModelFormatManifest commandLineManifest transcriptDigest
      benchmarkFingerprint archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_cvmg_checker_version_contract solverBuildEvidence checkerBinaryDigest
      checkerVersionMatrix proofModelFormatManifest commandLineManifest
      transcriptDigest benchmarkFingerprint archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _solverProof _checkerProof _versionProof _formatProof _commandProof
          _transcriptProof _fingerprintProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_cvmg_sat_publication_intro
    (versionContract formatCompatible checkedModel originalModel : Prop) :
    versionContract -> formatCompatible -> checkedModel -> originalModel ->
    ay_cvmg_sat_publication versionContract formatCompatible checkedModel
      originalModel :=
  fun contractProof compatibleProof modelProof originalProof =>
    ay_cvmg_conj_intro versionContract
      (ay_cvmg_conj formatCompatible
        (ay_cvmg_conj checkedModel originalModel))
      contractProof
      (ay_cvmg_conj_intro formatCompatible
        (ay_cvmg_conj checkedModel originalModel)
        compatibleProof
        (ay_cvmg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_cvmg_unsat_publication_intro
    (versionContract formatCompatible checkedProof originalEmptyClause :
      Prop) :
    versionContract -> formatCompatible -> checkedProof ->
    originalEmptyClause ->
    ay_cvmg_unsat_publication versionContract formatCompatible checkedProof
      originalEmptyClause :=
  fun contractProof compatibleProof proofProof originalProof =>
    ay_cvmg_conj_intro versionContract
      (ay_cvmg_conj formatCompatible
        (ay_cvmg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_cvmg_conj_intro formatCompatible
        (ay_cvmg_conj checkedProof originalEmptyClause)
        compatibleProof
        (ay_cvmg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_cvmg_sat_publication_original_model
    (versionContract formatCompatible checkedModel originalModel : Prop) :
    ay_cvmg_sat_publication versionContract formatCompatible checkedModel
      originalModel ->
    originalModel :=
  fun publication =>
    ay_cvmg_conj_right checkedModel originalModel
      (ay_cvmg_conj_right formatCompatible
        (ay_cvmg_conj checkedModel originalModel)
        (ay_cvmg_conj_right versionContract
          (ay_cvmg_conj formatCompatible
            (ay_cvmg_conj checkedModel originalModel))
          publication))

theorem ay_cvmg_unsat_publication_original_empty_clause
    (versionContract formatCompatible checkedProof originalEmptyClause :
      Prop) :
    ay_cvmg_unsat_publication versionContract formatCompatible checkedProof
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_cvmg_conj_right checkedProof originalEmptyClause
      (ay_cvmg_conj_right formatCompatible
        (ay_cvmg_conj checkedProof originalEmptyClause)
        (ay_cvmg_conj_right versionContract
          (ay_cvmg_conj formatCompatible
            (ay_cvmg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_cvmg_accepted_checker_version_sat_validates
    (versionContract formatCompatible checkedModel originalModel : Prop) :
    ay_cvmg_sat_publication versionContract formatCompatible checkedModel
      originalModel ->
    ay_cvmg_public_result originalModel False False :=
  fun publication =>
    ay_cvmg_disj_left originalModel (ay_cvmg_disj False False)
      (ay_cvmg_sat_publication_original_model versionContract
        formatCompatible checkedModel originalModel publication)

theorem ay_cvmg_accepted_checker_version_unsat_validates
    (versionContract formatCompatible checkedProof originalEmptyClause :
      Prop) :
    ay_cvmg_unsat_publication versionContract formatCompatible checkedProof
      originalEmptyClause ->
    ay_cvmg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_cvmg_disj_right False (ay_cvmg_disj originalEmptyClause False)
      (ay_cvmg_disj_left originalEmptyClause False
        (ay_cvmg_unsat_publication_original_empty_clause versionContract
          formatCompatible checkedProof originalEmptyClause publication))

theorem ay_cvmg_does_not_change_original_benchmark_semantics
    (originalBenchmarkFormula replayBenchmarkFormula : Prop) :
    ay_cvmg_semantics_preserved originalBenchmarkFormula
      replayBenchmarkFormula ->
    originalBenchmarkFormula -> replayBenchmarkFormula :=
  fun preserved => preserved

theorem ay_cvmg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_cvmg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_cvmg_conj_intro reason (ay_cvmg_conj fallbackPath auditTrail)
      reasonProof
      (ay_cvmg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_cvmg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_cvmg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_cvmg_conj_intro reason
      (ay_cvmg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_cvmg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_cvmg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_cvmg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_cvmg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_cvmg_conj_right reason
        (ay_cvmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_cvmg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_cvmg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_cvmg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_cvmg_conj_right reason
        (ay_cvmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_cvmg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_cvmg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_cvmg_conj_intro reason
      (ay_cvmg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_cvmg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_cvmg_checker_version_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cvmg_blocked_publication satFact unsatFact reason ->
    ay_cvmg_recompute reason fallbackPath recomputeObligation ->
    ay_cvmg_checker_version_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_cvmg_conj_intro
      (ay_cvmg_blocked_publication satFact unsatFact reason)
      (ay_cvmg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_cvmg_checker_version_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cvmg_checker_version_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_cvmg_blocked_publication_no_sat satFact unsatFact reason
      (ay_cvmg_conj_left
        (ay_cvmg_blocked_publication satFact unsatFact reason)
        (ay_cvmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_cvmg_checker_version_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cvmg_checker_version_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_cvmg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_cvmg_conj_left
        (ay_cvmg_blocked_publication satFact unsatFact reason)
        (ay_cvmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_cvmg_checker_version_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cvmg_checker_version_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_cvmg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_cvmg_conj_right
      (ay_cvmg_blocked_publication satFact unsatFact reason)
      (ay_cvmg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_cvmg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cvmg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_cvmg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_cvmg_solver_mismatch_forces_no_claim
    (satFact unsatFact solverMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    solverMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cvmg_no_claim solverMismatch fallbackPath auditTrail :=
  ay_cvmg_mismatch_forces_no_claim satFact unsatFact solverMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cvmg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cvmg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_cvmg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cvmg_version_mismatch_forces_no_claim
    (satFact unsatFact versionMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    versionMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cvmg_no_claim versionMismatch fallbackPath auditTrail :=
  ay_cvmg_mismatch_forces_no_claim satFact unsatFact versionMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cvmg_format_mismatch_forces_no_claim
    (satFact unsatFact formatMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    formatMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cvmg_no_claim formatMismatch fallbackPath auditTrail :=
  ay_cvmg_mismatch_forces_no_claim satFact unsatFact formatMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cvmg_command_mismatch_forces_no_claim
    (satFact unsatFact commandMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    commandMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cvmg_no_claim commandMismatch fallbackPath auditTrail :=
  ay_cvmg_mismatch_forces_no_claim satFact unsatFact commandMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cvmg_transcript_mismatch_forces_no_claim
    (satFact unsatFact transcriptMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    transcriptMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cvmg_no_claim transcriptMismatch fallbackPath auditTrail :=
  ay_cvmg_mismatch_forces_no_claim satFact unsatFact transcriptMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cvmg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cvmg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_cvmg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cvmg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cvmg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_cvmg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cvmg_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cvmg_no_claim auditMismatch fallbackPath auditTrail :=
  ay_cvmg_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cvmg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_cvmg_checker_version_failure satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_cvmg_checker_version_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_cvmg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_cvmg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_cvmg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cvmg_checker_version_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_cvmg_checker_version_failure_blocks_sat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_cvmg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cvmg_checker_version_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_cvmg_checker_version_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_cvmg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_cvmg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_cvmg_conj_left reason (ay_cvmg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_cvmg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_cvmg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_cvmg_conj_left reason (ay_cvmg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
