-- SAT-COMP validator result-line consistency guard core.
--
-- Public SAT/UNSAT claims require the solver exit code, stdout/stderr result
-- line, artifact digest, checker transcript, benchmark fingerprint, build
-- evidence, archive manifest, fallback path, and audit transcript to agree.

def ay_rlcg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rlcg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_rlcg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_rlcg_disj satFact (ay_rlcg_disj unsatFact noClaimFact)

def ay_rlcg_line_contract
    (solverExitCodeManifest resultLineDigest modelProofArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (solverExitCodeManifest -> resultLineDigest ->
      modelProofArtifactDigest -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_rlcg_sat_publication
    (lineContract lineExitArtifactCheckerAgree checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_rlcg_conj lineContract
    (ay_rlcg_conj lineExitArtifactCheckerAgree
      (ay_rlcg_conj checkedModel originalBenchmarkSat))

def ay_rlcg_unsat_publication
    (lineContract lineExitArtifactCheckerAgree checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_rlcg_conj lineContract
    (ay_rlcg_conj lineExitArtifactCheckerAgree
      (ay_rlcg_conj checkedProof originalBenchmarkUnsat))

def ay_rlcg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_rlcg_conj reason (ay_rlcg_conj fallbackPath auditTrail)

def ay_rlcg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_rlcg_conj reason
    (ay_rlcg_conj (satFact -> False) (unsatFact -> False))

def ay_rlcg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_rlcg_conj reason
    (ay_rlcg_conj fallbackPath recomputeObligation)

def ay_rlcg_line_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_rlcg_conj
    (ay_rlcg_blocked_publication satFact unsatFact reason)
    (ay_rlcg_recompute reason fallbackPath recomputeObligation)

theorem ay_rlcg_conj_intro (left right : Prop) :
    left -> right -> ay_rlcg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_rlcg_conj_left (left right : Prop) :
    ay_rlcg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_rlcg_conj_right (left right : Prop) :
    ay_rlcg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_rlcg_disj_left (left right : Prop) :
    left -> ay_rlcg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_rlcg_disj_right (left right : Prop) :
    right -> ay_rlcg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_rlcg_line_contract_intro
    (solverExitCodeManifest resultLineDigest modelProofArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    solverExitCodeManifest -> resultLineDigest ->
    modelProofArtifactDigest -> checkerTranscript -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_rlcg_line_contract solverExitCodeManifest resultLineDigest
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript :=
  fun exitProof lineProof artifactProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof result build =>
    build exitProof lineProof artifactProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof

theorem ay_rlcg_contract_exit_code
    (solverExitCodeManifest resultLineDigest modelProofArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlcg_line_contract solverExitCodeManifest resultLineDigest
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    solverExitCodeManifest :=
  fun contract =>
    contract solverExitCodeManifest
      (fun exitProof _lineProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => exitProof)

theorem ay_rlcg_contract_result_line
    (solverExitCodeManifest resultLineDigest modelProofArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlcg_line_contract solverExitCodeManifest resultLineDigest
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    resultLineDigest :=
  fun contract =>
    contract resultLineDigest
      (fun _exitProof lineProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => lineProof)

theorem ay_rlcg_contract_artifact
    (solverExitCodeManifest resultLineDigest modelProofArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlcg_line_contract solverExitCodeManifest resultLineDigest
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _exitProof _lineProof artifactProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => artifactProof)

theorem ay_rlcg_contract_checker
    (solverExitCodeManifest resultLineDigest modelProofArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlcg_line_contract solverExitCodeManifest resultLineDigest
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _exitProof _lineProof _artifactProof checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_rlcg_contract_fingerprint
    (solverExitCodeManifest resultLineDigest modelProofArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlcg_line_contract solverExitCodeManifest resultLineDigest
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _exitProof _lineProof _artifactProof _checkerProof
          fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_rlcg_contract_build
    (solverExitCodeManifest resultLineDigest modelProofArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlcg_line_contract solverExitCodeManifest resultLineDigest
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _exitProof _lineProof _artifactProof _checkerProof
          _fingerprintProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_rlcg_contract_archive
    (solverExitCodeManifest resultLineDigest modelProofArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlcg_line_contract solverExitCodeManifest resultLineDigest
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _exitProof _lineProof _artifactProof _checkerProof
          _fingerprintProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_rlcg_contract_fallback
    (solverExitCodeManifest resultLineDigest modelProofArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlcg_line_contract solverExitCodeManifest resultLineDigest
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _exitProof _lineProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_rlcg_contract_audit
    (solverExitCodeManifest resultLineDigest modelProofArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlcg_line_contract solverExitCodeManifest resultLineDigest
      modelProofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _exitProof _lineProof _artifactProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_rlcg_sat_publication_intro
    (lineContract lineExitArtifactCheckerAgree checkedModel
      originalBenchmarkSat : Prop) :
    lineContract -> lineExitArtifactCheckerAgree -> checkedModel ->
    originalBenchmarkSat ->
    ay_rlcg_sat_publication lineContract lineExitArtifactCheckerAgree
      checkedModel originalBenchmarkSat :=
  fun hcontract hagree hchecked horiginal =>
    ay_rlcg_conj_intro lineContract
      (ay_rlcg_conj lineExitArtifactCheckerAgree
        (ay_rlcg_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_rlcg_conj_intro lineExitArtifactCheckerAgree
        (ay_rlcg_conj checkedModel originalBenchmarkSat)
        hagree
        (ay_rlcg_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_rlcg_unsat_publication_intro
    (lineContract lineExitArtifactCheckerAgree checkedProof
      originalBenchmarkUnsat : Prop) :
    lineContract -> lineExitArtifactCheckerAgree -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_rlcg_unsat_publication lineContract lineExitArtifactCheckerAgree
      checkedProof originalBenchmarkUnsat :=
  fun hcontract hagree hchecked horiginal =>
    ay_rlcg_conj_intro lineContract
      (ay_rlcg_conj lineExitArtifactCheckerAgree
        (ay_rlcg_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_rlcg_conj_intro lineExitArtifactCheckerAgree
        (ay_rlcg_conj checkedProof originalBenchmarkUnsat)
        hagree
        (ay_rlcg_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_rlcg_sat_publication_original_claim
    (lineContract lineExitArtifactCheckerAgree checkedModel
      originalBenchmarkSat : Prop) :
    ay_rlcg_sat_publication lineContract lineExitArtifactCheckerAgree
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_rlcg_conj_right checkedModel originalBenchmarkSat
      (ay_rlcg_conj_right lineExitArtifactCheckerAgree
        (ay_rlcg_conj checkedModel originalBenchmarkSat)
        (ay_rlcg_conj_right lineContract
          (ay_rlcg_conj lineExitArtifactCheckerAgree
            (ay_rlcg_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_rlcg_unsat_publication_original_claim
    (lineContract lineExitArtifactCheckerAgree checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_rlcg_unsat_publication lineContract lineExitArtifactCheckerAgree
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_rlcg_conj_right checkedProof originalBenchmarkUnsat
      (ay_rlcg_conj_right lineExitArtifactCheckerAgree
        (ay_rlcg_conj checkedProof originalBenchmarkUnsat)
        (ay_rlcg_conj_right lineContract
          (ay_rlcg_conj lineExitArtifactCheckerAgree
            (ay_rlcg_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_rlcg_accepted_line_preserves_sat_soundness
    (lineContract lineExitArtifactCheckerAgree checkedModel
      originalBenchmarkSat : Prop) :
    ay_rlcg_sat_publication lineContract lineExitArtifactCheckerAgree
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_rlcg_sat_publication_original_claim lineContract
    lineExitArtifactCheckerAgree checkedModel originalBenchmarkSat

theorem ay_rlcg_accepted_line_preserves_unsat_soundness
    (lineContract lineExitArtifactCheckerAgree checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_rlcg_unsat_publication lineContract lineExitArtifactCheckerAgree
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_rlcg_unsat_publication_original_claim lineContract
    lineExitArtifactCheckerAgree checkedProof originalBenchmarkUnsat

theorem ay_rlcg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_rlcg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_rlcg_conj_intro reason (ay_rlcg_conj fallbackPath auditTrail)
      hreason
      (ay_rlcg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_rlcg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_rlcg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_rlcg_conj_intro reason
      (ay_rlcg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_rlcg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_rlcg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_rlcg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_rlcg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_rlcg_conj_right reason
        (ay_rlcg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rlcg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_rlcg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_rlcg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_rlcg_conj_right reason
        (ay_rlcg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rlcg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_rlcg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_rlcg_conj_intro reason
      (ay_rlcg_conj fallbackPath recomputeObligation)
      hreason
      (ay_rlcg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_rlcg_line_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlcg_blocked_publication satFact unsatFact reason ->
    ay_rlcg_recompute reason fallbackPath recomputeObligation ->
    ay_rlcg_line_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_rlcg_conj_intro
      (ay_rlcg_blocked_publication satFact unsatFact reason)
      (ay_rlcg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_rlcg_line_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlcg_line_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_rlcg_blocked_publication_no_sat satFact unsatFact reason
      (ay_rlcg_conj_left
        (ay_rlcg_blocked_publication satFact unsatFact reason)
        (ay_rlcg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rlcg_line_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlcg_line_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_rlcg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_rlcg_conj_left
        (ay_rlcg_blocked_publication satFact unsatFact reason)
        (ay_rlcg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rlcg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_rlcg_no_claim reason fallbackPath auditTrail :=
  ay_rlcg_no_claim_intro reason fallbackPath auditTrail

theorem ay_rlcg_exit_status_mismatch_forces_no_claim
    (exitStatusMismatch fallbackPath auditTrail : Prop) :
    exitStatusMismatch -> fallbackPath -> auditTrail ->
    ay_rlcg_no_claim exitStatusMismatch fallbackPath auditTrail :=
  ay_rlcg_mismatch_forces_no_claim exitStatusMismatch fallbackPath auditTrail

theorem ay_rlcg_result_line_mismatch_forces_no_claim
    (resultLineMismatch fallbackPath auditTrail : Prop) :
    resultLineMismatch -> fallbackPath -> auditTrail ->
    ay_rlcg_no_claim resultLineMismatch fallbackPath auditTrail :=
  ay_rlcg_mismatch_forces_no_claim resultLineMismatch fallbackPath auditTrail

theorem ay_rlcg_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_rlcg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_rlcg_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_rlcg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_rlcg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_rlcg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_rlcg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch fallbackPath auditTrail : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    ay_rlcg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_rlcg_mismatch_forces_no_claim fingerprintMismatch fallbackPath auditTrail

theorem ay_rlcg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_rlcg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_rlcg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_rlcg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_rlcg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_rlcg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_rlcg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_rlcg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_rlcg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_rlcg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlcg_line_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_rlcg_line_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_rlcg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlcg_line_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_rlcg_line_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
