-- SAT-COMP validator artifact archive-manifest guard core.
--
-- Public SAT/UNSAT claims may be published from archived artifacts only when
-- benchmark, solver output, model/proof artifact, archive, serialization,
-- checker, build, fallback, and audit evidence agree.

def ay_aamg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_aamg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_aamg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_aamg_disj satFact (ay_aamg_disj unsatFact noClaimFact)

def ay_aamg_archive_contract
    (benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      archiveManifest compressionSerializationManifest checkerTranscript
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint -> solverOutputDigest -> modelProofArtifactDigest ->
      archiveManifest -> compressionSerializationManifest ->
      checkerTranscript -> solverBuildEvidence -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_aamg_sat_publication
    (archiveContract archiveEvidencePreserves checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_aamg_conj archiveContract
    (ay_aamg_conj archiveEvidencePreserves
      (ay_aamg_conj checkedModel originalBenchmarkSat))

def ay_aamg_unsat_publication
    (archiveContract archiveEvidencePreserves checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_aamg_conj archiveContract
    (ay_aamg_conj archiveEvidencePreserves
      (ay_aamg_conj checkedProof originalBenchmarkUnsat))

def ay_aamg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_aamg_conj reason (ay_aamg_conj fallbackPath auditTrail)

def ay_aamg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_aamg_conj reason
    (ay_aamg_conj (satFact -> False) (unsatFact -> False))

def ay_aamg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_aamg_conj reason
    (ay_aamg_conj fallbackPath recomputeObligation)

def ay_aamg_archive_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_aamg_conj
    (ay_aamg_blocked_publication satFact unsatFact reason)
    (ay_aamg_recompute reason fallbackPath recomputeObligation)

theorem ay_aamg_conj_intro (left right : Prop) :
    left -> right -> ay_aamg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_aamg_conj_left (left right : Prop) :
    ay_aamg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_aamg_conj_right (left right : Prop) :
    ay_aamg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_aamg_disj_left (left right : Prop) :
    left -> ay_aamg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_aamg_disj_right (left right : Prop) :
    right -> ay_aamg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_aamg_archive_contract_intro
    (benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      archiveManifest compressionSerializationManifest checkerTranscript
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    benchmarkFingerprint -> solverOutputDigest -> modelProofArtifactDigest ->
    archiveManifest -> compressionSerializationManifest ->
    checkerTranscript -> solverBuildEvidence -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_aamg_archive_contract benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest archiveManifest compressionSerializationManifest
      checkerTranscript solverBuildEvidence fallbackNoClaimPath
      auditTranscript :=
  fun fingerprintProof outputProof artifactProof archiveProof
      serializationProof checkerProof buildProof fallbackProof auditProof
      result build =>
    build fingerprintProof outputProof artifactProof archiveProof
      serializationProof checkerProof buildProof fallbackProof auditProof

theorem ay_aamg_contract_fingerprint
    (benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      archiveManifest compressionSerializationManifest checkerTranscript
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_aamg_archive_contract benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest archiveManifest compressionSerializationManifest
      checkerTranscript solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun fingerprintProof _outputProof _artifactProof _archiveProof
          _serializationProof _checkerProof _buildProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_aamg_contract_solver_output
    (benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      archiveManifest compressionSerializationManifest checkerTranscript
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_aamg_archive_contract benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest archiveManifest compressionSerializationManifest
      checkerTranscript solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    solverOutputDigest :=
  fun contract =>
    contract solverOutputDigest
      (fun _fingerprintProof outputProof _artifactProof _archiveProof
          _serializationProof _checkerProof _buildProof _fallbackProof
          _auditProof => outputProof)

theorem ay_aamg_contract_artifact
    (benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      archiveManifest compressionSerializationManifest checkerTranscript
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_aamg_archive_contract benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest archiveManifest compressionSerializationManifest
      checkerTranscript solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _fingerprintProof _outputProof artifactProof _archiveProof
          _serializationProof _checkerProof _buildProof _fallbackProof
          _auditProof => artifactProof)

theorem ay_aamg_contract_archive
    (benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      archiveManifest compressionSerializationManifest checkerTranscript
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_aamg_archive_contract benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest archiveManifest compressionSerializationManifest
      checkerTranscript solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _fingerprintProof _outputProof _artifactProof archiveProof
          _serializationProof _checkerProof _buildProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_aamg_contract_serialization
    (benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      archiveManifest compressionSerializationManifest checkerTranscript
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_aamg_archive_contract benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest archiveManifest compressionSerializationManifest
      checkerTranscript solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    compressionSerializationManifest :=
  fun contract =>
    contract compressionSerializationManifest
      (fun _fingerprintProof _outputProof _artifactProof _archiveProof
          serializationProof _checkerProof _buildProof _fallbackProof
          _auditProof => serializationProof)

theorem ay_aamg_contract_checker
    (benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      archiveManifest compressionSerializationManifest checkerTranscript
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_aamg_archive_contract benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest archiveManifest compressionSerializationManifest
      checkerTranscript solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _fingerprintProof _outputProof _artifactProof _archiveProof
          _serializationProof checkerProof _buildProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_aamg_contract_build
    (benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      archiveManifest compressionSerializationManifest checkerTranscript
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_aamg_archive_contract benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest archiveManifest compressionSerializationManifest
      checkerTranscript solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _fingerprintProof _outputProof _artifactProof _archiveProof
          _serializationProof _checkerProof buildProof _fallbackProof
          _auditProof => buildProof)

theorem ay_aamg_contract_fallback
    (benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      archiveManifest compressionSerializationManifest checkerTranscript
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_aamg_archive_contract benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest archiveManifest compressionSerializationManifest
      checkerTranscript solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _fingerprintProof _outputProof _artifactProof _archiveProof
          _serializationProof _checkerProof _buildProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_aamg_contract_audit
    (benchmarkFingerprint solverOutputDigest modelProofArtifactDigest
      archiveManifest compressionSerializationManifest checkerTranscript
      solverBuildEvidence fallbackNoClaimPath auditTranscript : Prop) :
    ay_aamg_archive_contract benchmarkFingerprint solverOutputDigest
      modelProofArtifactDigest archiveManifest compressionSerializationManifest
      checkerTranscript solverBuildEvidence fallbackNoClaimPath
      auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _fingerprintProof _outputProof _artifactProof _archiveProof
          _serializationProof _checkerProof _buildProof _fallbackProof
          auditProof => auditProof)

theorem ay_aamg_sat_publication_intro
    (archiveContract archiveEvidencePreserves checkedModel
      originalBenchmarkSat : Prop) :
    archiveContract -> archiveEvidencePreserves -> checkedModel ->
    originalBenchmarkSat ->
    ay_aamg_sat_publication archiveContract archiveEvidencePreserves
      checkedModel originalBenchmarkSat :=
  fun hcontract hpreserves hchecked horiginal =>
    ay_aamg_conj_intro archiveContract
      (ay_aamg_conj archiveEvidencePreserves
        (ay_aamg_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_aamg_conj_intro archiveEvidencePreserves
        (ay_aamg_conj checkedModel originalBenchmarkSat)
        hpreserves
        (ay_aamg_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_aamg_unsat_publication_intro
    (archiveContract archiveEvidencePreserves checkedProof
      originalBenchmarkUnsat : Prop) :
    archiveContract -> archiveEvidencePreserves -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_aamg_unsat_publication archiveContract archiveEvidencePreserves
      checkedProof originalBenchmarkUnsat :=
  fun hcontract hpreserves hchecked horiginal =>
    ay_aamg_conj_intro archiveContract
      (ay_aamg_conj archiveEvidencePreserves
        (ay_aamg_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_aamg_conj_intro archiveEvidencePreserves
        (ay_aamg_conj checkedProof originalBenchmarkUnsat)
        hpreserves
        (ay_aamg_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_aamg_sat_publication_original_claim
    (archiveContract archiveEvidencePreserves checkedModel
      originalBenchmarkSat : Prop) :
    ay_aamg_sat_publication archiveContract archiveEvidencePreserves
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_aamg_conj_right checkedModel originalBenchmarkSat
      (ay_aamg_conj_right archiveEvidencePreserves
        (ay_aamg_conj checkedModel originalBenchmarkSat)
        (ay_aamg_conj_right archiveContract
          (ay_aamg_conj archiveEvidencePreserves
            (ay_aamg_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_aamg_unsat_publication_original_claim
    (archiveContract archiveEvidencePreserves checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_aamg_unsat_publication archiveContract archiveEvidencePreserves
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_aamg_conj_right checkedProof originalBenchmarkUnsat
      (ay_aamg_conj_right archiveEvidencePreserves
        (ay_aamg_conj checkedProof originalBenchmarkUnsat)
        (ay_aamg_conj_right archiveContract
          (ay_aamg_conj archiveEvidencePreserves
            (ay_aamg_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_aamg_accepted_archive_preserves_sat_soundness
    (archiveContract archiveEvidencePreserves checkedModel
      originalBenchmarkSat : Prop) :
    ay_aamg_sat_publication archiveContract archiveEvidencePreserves
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_aamg_sat_publication_original_claim archiveContract
    archiveEvidencePreserves checkedModel originalBenchmarkSat

theorem ay_aamg_accepted_archive_preserves_unsat_soundness
    (archiveContract archiveEvidencePreserves checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_aamg_unsat_publication archiveContract archiveEvidencePreserves
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_aamg_unsat_publication_original_claim archiveContract
    archiveEvidencePreserves checkedProof originalBenchmarkUnsat

theorem ay_aamg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_aamg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_aamg_conj_intro reason (ay_aamg_conj fallbackPath auditTrail)
      hreason
      (ay_aamg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_aamg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_aamg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_aamg_conj_intro reason
      (ay_aamg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_aamg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_aamg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_aamg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_aamg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_aamg_conj_right reason
        (ay_aamg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_aamg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_aamg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_aamg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_aamg_conj_right reason
        (ay_aamg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_aamg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_aamg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_aamg_conj_intro reason
      (ay_aamg_conj fallbackPath recomputeObligation)
      hreason
      (ay_aamg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_aamg_archive_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_aamg_blocked_publication satFact unsatFact reason ->
    ay_aamg_recompute reason fallbackPath recomputeObligation ->
    ay_aamg_archive_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_aamg_conj_intro
      (ay_aamg_blocked_publication satFact unsatFact reason)
      (ay_aamg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_aamg_archive_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_aamg_archive_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_aamg_blocked_publication_no_sat satFact unsatFact reason
      (ay_aamg_conj_left
        (ay_aamg_blocked_publication satFact unsatFact reason)
        (ay_aamg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_aamg_archive_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_aamg_archive_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_aamg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_aamg_conj_left
        (ay_aamg_blocked_publication satFact unsatFact reason)
        (ay_aamg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_aamg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_aamg_no_claim reason fallbackPath auditTrail :=
  ay_aamg_no_claim_intro reason fallbackPath auditTrail

theorem ay_aamg_output_mismatch_forces_no_claim
    (outputMismatch fallbackPath auditTrail : Prop) :
    outputMismatch -> fallbackPath -> auditTrail ->
    ay_aamg_no_claim outputMismatch fallbackPath auditTrail :=
  ay_aamg_mismatch_forces_no_claim outputMismatch fallbackPath auditTrail

theorem ay_aamg_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_aamg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_aamg_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_aamg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_aamg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_aamg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_aamg_serialization_mismatch_forces_no_claim
    (serializationMismatch fallbackPath auditTrail : Prop) :
    serializationMismatch -> fallbackPath -> auditTrail ->
    ay_aamg_no_claim serializationMismatch fallbackPath auditTrail :=
  ay_aamg_mismatch_forces_no_claim serializationMismatch fallbackPath
    auditTrail

theorem ay_aamg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_aamg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_aamg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_aamg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_aamg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_aamg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_aamg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch fallbackPath auditTrail : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    ay_aamg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_aamg_mismatch_forces_no_claim fingerprintMismatch fallbackPath auditTrail

theorem ay_aamg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_aamg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_aamg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_aamg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_aamg_archive_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_aamg_archive_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_aamg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_aamg_archive_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_aamg_archive_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
