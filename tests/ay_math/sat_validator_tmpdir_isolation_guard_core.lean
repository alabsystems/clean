-- SAT-COMP validator temporary-directory isolation guard core.
--
-- Public SAT/UNSAT claims require tmpdir evidence, per-run isolation,
-- no-cross-run artifacts, artifact digest, checker transcript, benchmark
-- fingerprint, solver build evidence, archive manifest, fallback, and audit
-- transcript to agree.

def ay_tdig_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_tdig_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_tdig_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_tdig_disj satFact (ay_tdig_disj unsatFact noClaimFact)

def ay_tdig_tmpdir_contract
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (tmpdirManifest -> perRunIsolationWitness -> noCrossRunArtifactWitness ->
      artifactDigest -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_tdig_sat_publication
    (tmpdirContract intendedRun checkedModel originalModel : Prop) : Prop :=
  ay_tdig_conj tmpdirContract
    (ay_tdig_conj intendedRun
      (ay_tdig_conj checkedModel originalModel))

def ay_tdig_unsat_publication
    (tmpdirContract intendedRun checkedProof originalEmptyClause : Prop) :
    Prop :=
  ay_tdig_conj tmpdirContract
    (ay_tdig_conj intendedRun
      (ay_tdig_conj checkedProof originalEmptyClause))

def ay_tdig_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_tdig_conj reason (ay_tdig_conj fallbackPath auditTrail)

def ay_tdig_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_tdig_conj reason
    (ay_tdig_conj (satFact -> False) (unsatFact -> False))

def ay_tdig_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_tdig_conj reason
    (ay_tdig_conj fallbackPath recomputeObligation)

def ay_tdig_tmpdir_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_tdig_conj
    (ay_tdig_blocked_publication satFact unsatFact reason)
    (ay_tdig_recompute reason fallbackPath recomputeObligation)

theorem ay_tdig_conj_intro (left right : Prop) :
    left -> right -> ay_tdig_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_tdig_conj_left (left right : Prop) :
    ay_tdig_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_tdig_conj_right (left right : Prop) :
    ay_tdig_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_tdig_disj_left (left right : Prop) :
    left -> ay_tdig_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_tdig_disj_right (left right : Prop) :
    right -> ay_tdig_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_tdig_tmpdir_contract_intro
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    tmpdirManifest -> perRunIsolationWitness -> noCrossRunArtifactWitness ->
    artifactDigest -> checkerTranscript -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_tdig_tmpdir_contract tmpdirManifest perRunIsolationWitness
      noCrossRunArtifactWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript :=
  fun tmpdirProof isolationProof crossRunProof artifactProof checkerProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof result
      build =>
    build tmpdirProof isolationProof crossRunProof artifactProof checkerProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof

theorem ay_tdig_contract_tmpdir
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tdig_tmpdir_contract tmpdirManifest perRunIsolationWitness
      noCrossRunArtifactWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    tmpdirManifest :=
  fun contract =>
    contract tmpdirManifest
      (fun tmpdirProof _isolationProof _crossRunProof _artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => tmpdirProof)

theorem ay_tdig_contract_isolation
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tdig_tmpdir_contract tmpdirManifest perRunIsolationWitness
      noCrossRunArtifactWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    perRunIsolationWitness :=
  fun contract =>
    contract perRunIsolationWitness
      (fun _tmpdirProof isolationProof _crossRunProof _artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => isolationProof)

theorem ay_tdig_contract_no_cross_run
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tdig_tmpdir_contract tmpdirManifest perRunIsolationWitness
      noCrossRunArtifactWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    noCrossRunArtifactWitness :=
  fun contract =>
    contract noCrossRunArtifactWitness
      (fun _tmpdirProof _isolationProof crossRunProof _artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => crossRunProof)

theorem ay_tdig_contract_artifact
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tdig_tmpdir_contract tmpdirManifest perRunIsolationWitness
      noCrossRunArtifactWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    artifactDigest :=
  fun contract =>
    contract artifactDigest
      (fun _tmpdirProof _isolationProof _crossRunProof artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => artifactProof)

theorem ay_tdig_contract_checker
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tdig_tmpdir_contract tmpdirManifest perRunIsolationWitness
      noCrossRunArtifactWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _tmpdirProof _isolationProof _crossRunProof _artifactProof
          checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => checkerProof)

theorem ay_tdig_contract_fingerprint
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tdig_tmpdir_contract tmpdirManifest perRunIsolationWitness
      noCrossRunArtifactWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _tmpdirProof _isolationProof _crossRunProof _artifactProof
          _checkerProof fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => fingerprintProof)

theorem ay_tdig_contract_build
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tdig_tmpdir_contract tmpdirManifest perRunIsolationWitness
      noCrossRunArtifactWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _tmpdirProof _isolationProof _crossRunProof _artifactProof
          _checkerProof _fingerprintProof buildProof _archiveProof
          _fallbackProof _auditProof => buildProof)

theorem ay_tdig_contract_archive
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tdig_tmpdir_contract tmpdirManifest perRunIsolationWitness
      noCrossRunArtifactWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _tmpdirProof _isolationProof _crossRunProof _artifactProof
          _checkerProof _fingerprintProof _buildProof archiveProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_tdig_contract_fallback
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tdig_tmpdir_contract tmpdirManifest perRunIsolationWitness
      noCrossRunArtifactWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _tmpdirProof _isolationProof _crossRunProof _artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_tdig_contract_audit
    (tmpdirManifest perRunIsolationWitness noCrossRunArtifactWitness
      artifactDigest checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tdig_tmpdir_contract tmpdirManifest perRunIsolationWitness
      noCrossRunArtifactWitness artifactDigest checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _tmpdirProof _isolationProof _crossRunProof _artifactProof
          _checkerProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof auditProof => auditProof)

theorem ay_tdig_sat_publication_intro
    (tmpdirContract intendedRun checkedModel originalModel : Prop) :
    tmpdirContract -> intendedRun -> checkedModel -> originalModel ->
    ay_tdig_sat_publication tmpdirContract intendedRun checkedModel
      originalModel :=
  fun contractProof runProof modelProof originalProof =>
    ay_tdig_conj_intro tmpdirContract
      (ay_tdig_conj intendedRun
        (ay_tdig_conj checkedModel originalModel))
      contractProof
      (ay_tdig_conj_intro intendedRun
        (ay_tdig_conj checkedModel originalModel)
        runProof
        (ay_tdig_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_tdig_unsat_publication_intro
    (tmpdirContract intendedRun checkedProof originalEmptyClause : Prop) :
    tmpdirContract -> intendedRun -> checkedProof -> originalEmptyClause ->
    ay_tdig_unsat_publication tmpdirContract intendedRun checkedProof
      originalEmptyClause :=
  fun contractProof runProof proofProof originalProof =>
    ay_tdig_conj_intro tmpdirContract
      (ay_tdig_conj intendedRun
        (ay_tdig_conj checkedProof originalEmptyClause))
      contractProof
      (ay_tdig_conj_intro intendedRun
        (ay_tdig_conj checkedProof originalEmptyClause)
        runProof
        (ay_tdig_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_tdig_sat_publication_original_model
    (tmpdirContract intendedRun checkedModel originalModel : Prop) :
    ay_tdig_sat_publication tmpdirContract intendedRun checkedModel
      originalModel ->
    originalModel :=
  fun publication =>
    ay_tdig_conj_right checkedModel originalModel
      (ay_tdig_conj_right intendedRun
        (ay_tdig_conj checkedModel originalModel)
        (ay_tdig_conj_right tmpdirContract
          (ay_tdig_conj intendedRun
            (ay_tdig_conj checkedModel originalModel))
          publication))

theorem ay_tdig_unsat_publication_original_empty_clause
    (tmpdirContract intendedRun checkedProof originalEmptyClause : Prop) :
    ay_tdig_unsat_publication tmpdirContract intendedRun checkedProof
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_tdig_conj_right checkedProof originalEmptyClause
      (ay_tdig_conj_right intendedRun
        (ay_tdig_conj checkedProof originalEmptyClause)
        (ay_tdig_conj_right tmpdirContract
          (ay_tdig_conj intendedRun
            (ay_tdig_conj checkedProof originalEmptyClause))
          publication))

theorem ay_tdig_accepted_tmpdir_ties_sat_to_intended_run
    (tmpdirContract intendedRun checkedModel originalModel : Prop) :
    ay_tdig_sat_publication tmpdirContract intendedRun checkedModel
      originalModel ->
    ay_tdig_public_result originalModel False False :=
  fun publication =>
    ay_tdig_disj_left originalModel (ay_tdig_disj False False)
      (ay_tdig_sat_publication_original_model tmpdirContract intendedRun
        checkedModel originalModel publication)

theorem ay_tdig_accepted_tmpdir_ties_unsat_to_intended_run
    (tmpdirContract intendedRun checkedProof originalEmptyClause : Prop) :
    ay_tdig_unsat_publication tmpdirContract intendedRun checkedProof
      originalEmptyClause ->
    ay_tdig_public_result False originalEmptyClause False :=
  fun publication =>
    ay_tdig_disj_right False (ay_tdig_disj originalEmptyClause False)
      (ay_tdig_disj_left originalEmptyClause False
        (ay_tdig_unsat_publication_original_empty_clause tmpdirContract
          intendedRun checkedProof originalEmptyClause publication))

theorem ay_tdig_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_tdig_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_tdig_conj_intro reason (ay_tdig_conj fallbackPath auditTrail)
      reasonProof
      (ay_tdig_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_tdig_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_tdig_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_tdig_conj_intro reason
      (ay_tdig_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_tdig_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_tdig_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_tdig_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_tdig_conj_left (satFact -> False) (unsatFact -> False)
      (ay_tdig_conj_right reason
        (ay_tdig_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_tdig_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_tdig_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_tdig_conj_right (satFact -> False) (unsatFact -> False)
      (ay_tdig_conj_right reason
        (ay_tdig_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_tdig_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_tdig_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_tdig_conj_intro reason
      (ay_tdig_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_tdig_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_tdig_tmpdir_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_tdig_blocked_publication satFact unsatFact reason ->
    ay_tdig_recompute reason fallbackPath recomputeObligation ->
    ay_tdig_tmpdir_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_tdig_conj_intro
      (ay_tdig_blocked_publication satFact unsatFact reason)
      (ay_tdig_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_tdig_tmpdir_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_tdig_tmpdir_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_tdig_blocked_publication_no_sat satFact unsatFact reason
      (ay_tdig_conj_left
        (ay_tdig_blocked_publication satFact unsatFact reason)
        (ay_tdig_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_tdig_tmpdir_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_tdig_tmpdir_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_tdig_blocked_publication_no_unsat satFact unsatFact reason
      (ay_tdig_conj_left
        (ay_tdig_blocked_publication satFact unsatFact reason)
        (ay_tdig_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_tdig_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_tdig_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_tdig_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_tdig_tmpdir_mismatch_forces_no_claim
    (satFact unsatFact tmpdirMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    tmpdirMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_tdig_no_claim tmpdirMismatch fallbackPath auditTrail :=
  ay_tdig_mismatch_forces_no_claim satFact unsatFact tmpdirMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_tdig_isolation_mismatch_forces_no_claim
    (satFact unsatFact isolationMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    isolationMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_tdig_no_claim isolationMismatch fallbackPath auditTrail :=
  ay_tdig_mismatch_forces_no_claim satFact unsatFact isolationMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_tdig_cross_run_mismatch_forces_no_claim
    (satFact unsatFact crossRunMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    crossRunMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_tdig_no_claim crossRunMismatch fallbackPath auditTrail :=
  ay_tdig_mismatch_forces_no_claim satFact unsatFact crossRunMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_tdig_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    digestMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_tdig_no_claim digestMismatch fallbackPath auditTrail :=
  ay_tdig_mismatch_forces_no_claim satFact unsatFact digestMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_tdig_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_tdig_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_tdig_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_tdig_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_tdig_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_tdig_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_tdig_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_tdig_no_claim buildMismatch fallbackPath auditTrail :=
  ay_tdig_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_tdig_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_tdig_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_tdig_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_tdig_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_tdig_no_claim auditMismatch fallbackPath auditTrail :=
  ay_tdig_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_tdig_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_tdig_tmpdir_failure satFact unsatFact fallbackActivation fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_tdig_tmpdir_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_tdig_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_tdig_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_tdig_failed_tmpdir_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_tdig_tmpdir_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_tdig_tmpdir_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_tdig_failed_tmpdir_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_tdig_tmpdir_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_tdig_tmpdir_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_tdig_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_tdig_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_tdig_conj_left reason (ay_tdig_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_tdig_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_tdig_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_tdig_conj_left reason (ay_tdig_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
