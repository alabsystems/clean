-- SAT-COMP validator witness-kind match guard core.
--
-- Public SAT claims require checked model-kind evidence, while public UNSAT
-- claims require checked proof-kind evidence. Cross-kind or stale artifacts
-- force no-claim/recompute rather than publication.

def ay_wkmg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_wkmg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_wkmg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_wkmg_disj satFact (ay_wkmg_disj unsatFact noClaimFact)

def ay_wkmg_kind_contract
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (publicResultKind -> solverExitResultDigest -> modelArtifactDigest ->
      proofArtifactDigest -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_wkmg_sat_publication
    (kindContract satKindMatches checkedModelKind originalBenchmarkSat : Prop) :
    Prop :=
  ay_wkmg_conj kindContract
    (ay_wkmg_conj satKindMatches
      (ay_wkmg_conj checkedModelKind originalBenchmarkSat))

def ay_wkmg_unsat_publication
    (kindContract unsatKindMatches checkedProofKind
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_wkmg_conj kindContract
    (ay_wkmg_conj unsatKindMatches
      (ay_wkmg_conj checkedProofKind originalBenchmarkUnsat))

def ay_wkmg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_wkmg_conj reason (ay_wkmg_conj fallbackPath auditTrail)

def ay_wkmg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_wkmg_conj reason
    (ay_wkmg_conj (satFact -> False) (unsatFact -> False))

def ay_wkmg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_wkmg_conj reason
    (ay_wkmg_conj fallbackPath recomputeObligation)

def ay_wkmg_kind_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_wkmg_conj
    (ay_wkmg_blocked_publication satFact unsatFact reason)
    (ay_wkmg_recompute reason fallbackPath recomputeObligation)

theorem ay_wkmg_conj_intro (left right : Prop) :
    left -> right -> ay_wkmg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_wkmg_conj_left (left right : Prop) :
    ay_wkmg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_wkmg_conj_right (left right : Prop) :
    ay_wkmg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_wkmg_disj_left (left right : Prop) :
    left -> ay_wkmg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_wkmg_disj_right (left right : Prop) :
    right -> ay_wkmg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_wkmg_kind_contract_intro
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    publicResultKind -> solverExitResultDigest -> modelArtifactDigest ->
    proofArtifactDigest -> checkerTranscript -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_wkmg_kind_contract publicResultKind solverExitResultDigest
      modelArtifactDigest proofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript :=
  fun kindProof resultProof modelProof proofProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof result build =>
    build kindProof resultProof modelProof proofProof checkerProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof

theorem ay_wkmg_contract_public_kind
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_wkmg_kind_contract publicResultKind solverExitResultDigest
      modelArtifactDigest proofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    publicResultKind :=
  fun contract =>
    contract publicResultKind
      (fun kindProof _resultProof _modelProof _proofProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => kindProof)

theorem ay_wkmg_contract_solver_result
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_wkmg_kind_contract publicResultKind solverExitResultDigest
      modelArtifactDigest proofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverExitResultDigest :=
  fun contract =>
    contract solverExitResultDigest
      (fun _kindProof resultProof _modelProof _proofProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => resultProof)

theorem ay_wkmg_contract_model_artifact
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_wkmg_kind_contract publicResultKind solverExitResultDigest
      modelArtifactDigest proofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    modelArtifactDigest :=
  fun contract =>
    contract modelArtifactDigest
      (fun _kindProof _resultProof modelProof _proofProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => modelProof)

theorem ay_wkmg_contract_proof_artifact
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_wkmg_kind_contract publicResultKind solverExitResultDigest
      modelArtifactDigest proofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    proofArtifactDigest :=
  fun contract =>
    contract proofArtifactDigest
      (fun _kindProof _resultProof _modelProof proofProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => proofProof)

theorem ay_wkmg_contract_checker
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_wkmg_kind_contract publicResultKind solverExitResultDigest
      modelArtifactDigest proofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _kindProof _resultProof _modelProof _proofProof checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_wkmg_contract_fingerprint
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_wkmg_kind_contract publicResultKind solverExitResultDigest
      modelArtifactDigest proofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _kindProof _resultProof _modelProof _proofProof _checkerProof
          fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_wkmg_contract_build
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_wkmg_kind_contract publicResultKind solverExitResultDigest
      modelArtifactDigest proofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _kindProof _resultProof _modelProof _proofProof _checkerProof
          _fingerprintProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_wkmg_contract_archive
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_wkmg_kind_contract publicResultKind solverExitResultDigest
      modelArtifactDigest proofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _kindProof _resultProof _modelProof _proofProof _checkerProof
          _fingerprintProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_wkmg_contract_fallback
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_wkmg_kind_contract publicResultKind solverExitResultDigest
      modelArtifactDigest proofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _kindProof _resultProof _modelProof _proofProof _checkerProof
          _fingerprintProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_wkmg_contract_audit
    (publicResultKind solverExitResultDigest modelArtifactDigest
      proofArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_wkmg_kind_contract publicResultKind solverExitResultDigest
      modelArtifactDigest proofArtifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _kindProof _resultProof _modelProof _proofProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_wkmg_sat_publication_intro
    (kindContract satKindMatches checkedModelKind originalBenchmarkSat : Prop) :
    kindContract -> satKindMatches -> checkedModelKind ->
    originalBenchmarkSat ->
    ay_wkmg_sat_publication kindContract satKindMatches checkedModelKind
      originalBenchmarkSat :=
  fun hcontract hkind hchecked horiginal =>
    ay_wkmg_conj_intro kindContract
      (ay_wkmg_conj satKindMatches
        (ay_wkmg_conj checkedModelKind originalBenchmarkSat))
      hcontract
      (ay_wkmg_conj_intro satKindMatches
        (ay_wkmg_conj checkedModelKind originalBenchmarkSat)
        hkind
        (ay_wkmg_conj_intro checkedModelKind originalBenchmarkSat hchecked
          horiginal))

theorem ay_wkmg_unsat_publication_intro
    (kindContract unsatKindMatches checkedProofKind
      originalBenchmarkUnsat : Prop) :
    kindContract -> unsatKindMatches -> checkedProofKind ->
    originalBenchmarkUnsat ->
    ay_wkmg_unsat_publication kindContract unsatKindMatches checkedProofKind
      originalBenchmarkUnsat :=
  fun hcontract hkind hchecked horiginal =>
    ay_wkmg_conj_intro kindContract
      (ay_wkmg_conj unsatKindMatches
        (ay_wkmg_conj checkedProofKind originalBenchmarkUnsat))
      hcontract
      (ay_wkmg_conj_intro unsatKindMatches
        (ay_wkmg_conj checkedProofKind originalBenchmarkUnsat)
        hkind
        (ay_wkmg_conj_intro checkedProofKind originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_wkmg_sat_requires_checked_model_kind
    (kindContract satKindMatches checkedModelKind originalBenchmarkSat : Prop) :
    ay_wkmg_sat_publication kindContract satKindMatches checkedModelKind
      originalBenchmarkSat ->
    checkedModelKind :=
  fun publication =>
    ay_wkmg_conj_left checkedModelKind originalBenchmarkSat
      (ay_wkmg_conj_right satKindMatches
        (ay_wkmg_conj checkedModelKind originalBenchmarkSat)
        (ay_wkmg_conj_right kindContract
          (ay_wkmg_conj satKindMatches
            (ay_wkmg_conj checkedModelKind originalBenchmarkSat))
          publication))

theorem ay_wkmg_unsat_requires_checked_proof_kind
    (kindContract unsatKindMatches checkedProofKind
      originalBenchmarkUnsat : Prop) :
    ay_wkmg_unsat_publication kindContract unsatKindMatches checkedProofKind
      originalBenchmarkUnsat ->
    checkedProofKind :=
  fun publication =>
    ay_wkmg_conj_left checkedProofKind originalBenchmarkUnsat
      (ay_wkmg_conj_right unsatKindMatches
        (ay_wkmg_conj checkedProofKind originalBenchmarkUnsat)
        (ay_wkmg_conj_right kindContract
          (ay_wkmg_conj unsatKindMatches
            (ay_wkmg_conj checkedProofKind originalBenchmarkUnsat))
          publication))

theorem ay_wkmg_sat_publication_original_claim
    (kindContract satKindMatches checkedModelKind originalBenchmarkSat : Prop) :
    ay_wkmg_sat_publication kindContract satKindMatches checkedModelKind
      originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_wkmg_conj_right checkedModelKind originalBenchmarkSat
      (ay_wkmg_conj_right satKindMatches
        (ay_wkmg_conj checkedModelKind originalBenchmarkSat)
        (ay_wkmg_conj_right kindContract
          (ay_wkmg_conj satKindMatches
            (ay_wkmg_conj checkedModelKind originalBenchmarkSat))
          publication))

theorem ay_wkmg_unsat_publication_original_claim
    (kindContract unsatKindMatches checkedProofKind
      originalBenchmarkUnsat : Prop) :
    ay_wkmg_unsat_publication kindContract unsatKindMatches checkedProofKind
      originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_wkmg_conj_right checkedProofKind originalBenchmarkUnsat
      (ay_wkmg_conj_right unsatKindMatches
        (ay_wkmg_conj checkedProofKind originalBenchmarkUnsat)
        (ay_wkmg_conj_right kindContract
          (ay_wkmg_conj unsatKindMatches
            (ay_wkmg_conj checkedProofKind originalBenchmarkUnsat))
          publication))

theorem ay_wkmg_accepted_sat_preserves_soundness
    (kindContract satKindMatches checkedModelKind originalBenchmarkSat : Prop) :
    ay_wkmg_sat_publication kindContract satKindMatches checkedModelKind
      originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_wkmg_sat_publication_original_claim kindContract satKindMatches
    checkedModelKind originalBenchmarkSat

theorem ay_wkmg_accepted_unsat_preserves_soundness
    (kindContract unsatKindMatches checkedProofKind
      originalBenchmarkUnsat : Prop) :
    ay_wkmg_unsat_publication kindContract unsatKindMatches checkedProofKind
      originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_wkmg_unsat_publication_original_claim kindContract unsatKindMatches
    checkedProofKind originalBenchmarkUnsat

theorem ay_wkmg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_wkmg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_wkmg_conj_intro reason (ay_wkmg_conj fallbackPath auditTrail)
      hreason
      (ay_wkmg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_wkmg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_wkmg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_wkmg_conj_intro reason
      (ay_wkmg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_wkmg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_wkmg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_wkmg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_wkmg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_wkmg_conj_right reason
        (ay_wkmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_wkmg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_wkmg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_wkmg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_wkmg_conj_right reason
        (ay_wkmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_wkmg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_wkmg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_wkmg_conj_intro reason
      (ay_wkmg_conj fallbackPath recomputeObligation)
      hreason
      (ay_wkmg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_wkmg_kind_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_wkmg_blocked_publication satFact unsatFact reason ->
    ay_wkmg_recompute reason fallbackPath recomputeObligation ->
    ay_wkmg_kind_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_wkmg_conj_intro
      (ay_wkmg_blocked_publication satFact unsatFact reason)
      (ay_wkmg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_wkmg_kind_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_wkmg_kind_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_wkmg_blocked_publication_no_sat satFact unsatFact reason
      (ay_wkmg_conj_left
        (ay_wkmg_blocked_publication satFact unsatFact reason)
        (ay_wkmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_wkmg_kind_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_wkmg_kind_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_wkmg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_wkmg_conj_left
        (ay_wkmg_blocked_publication satFact unsatFact reason)
        (ay_wkmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_wkmg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_wkmg_no_claim reason fallbackPath auditTrail :=
  ay_wkmg_no_claim_intro reason fallbackPath auditTrail

theorem ay_wkmg_result_mismatch_forces_no_claim
    (resultMismatch fallbackPath auditTrail : Prop) :
    resultMismatch -> fallbackPath -> auditTrail ->
    ay_wkmg_no_claim resultMismatch fallbackPath auditTrail :=
  ay_wkmg_mismatch_forces_no_claim resultMismatch fallbackPath auditTrail

theorem ay_wkmg_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_wkmg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_wkmg_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_wkmg_kind_mismatch_forces_no_claim
    (kindMismatch fallbackPath auditTrail : Prop) :
    kindMismatch -> fallbackPath -> auditTrail ->
    ay_wkmg_no_claim kindMismatch fallbackPath auditTrail :=
  ay_wkmg_mismatch_forces_no_claim kindMismatch fallbackPath auditTrail

theorem ay_wkmg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_wkmg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_wkmg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_wkmg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_wkmg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_wkmg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_wkmg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_wkmg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_wkmg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_wkmg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_wkmg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_wkmg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_wkmg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_wkmg_kind_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_wkmg_kind_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_wkmg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_wkmg_kind_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_wkmg_kind_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
