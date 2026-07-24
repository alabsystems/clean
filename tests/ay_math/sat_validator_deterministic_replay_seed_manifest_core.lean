-- SAT-COMP validator deterministic replay seed manifest core.
--
-- Deterministic sequential-main replay may publish SAT/UNSAT only when the
-- seed manifest, build/config digest, benchmark fingerprint, result artifact
-- digest, certificate/model digest, checker transcript, stdout/stderr digests,
-- archive manifest, submission manifest, and fallback/no-claim path agree.

def ay_vdrs_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vdrs_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vdrs_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vdrs_disj satFact (ay_vdrs_disj unsatFact noClaimFact)

def ay_vdrs_replay_contract
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) : Prop :=
  forall result : Prop,
    (runSeedManifest -> buildConfigDigest -> benchmarkFingerprint ->
      resultArtifactDigest -> certificateModelDigest -> checkerTranscript ->
      stdoutStderrDigests -> archiveManifest -> submissionManifest ->
      fallbackNoClaimPath -> result) ->
    result

def ay_vdrs_sat_publication
    (replayContract modelEvidence originalModel : Prop) : Prop :=
  ay_vdrs_conj replayContract
    (ay_vdrs_conj modelEvidence originalModel)

def ay_vdrs_unsat_publication
    (replayContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vdrs_conj replayContract
    (ay_vdrs_conj proofEvidence originalEmptyClause)

def ay_vdrs_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vdrs_conj reason (ay_vdrs_conj fallbackPath auditTrail)

def ay_vdrs_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vdrs_conj reason
    (ay_vdrs_conj (satFact -> False) (unsatFact -> False))

def ay_vdrs_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vdrs_conj reason
    (ay_vdrs_conj fallbackPath recomputeObligation)

def ay_vdrs_replay_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vdrs_conj
    (ay_vdrs_blocked_publication satFact unsatFact reason)
    (ay_vdrs_recompute reason fallbackPath recomputeObligation)

theorem ay_vdrs_conj_intro (left right : Prop) :
    left -> right -> ay_vdrs_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vdrs_conj_left (left right : Prop) :
    ay_vdrs_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vdrs_conj_right (left right : Prop) :
    ay_vdrs_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vdrs_disj_left (left right : Prop) :
    left -> ay_vdrs_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vdrs_disj_right (left right : Prop) :
    right -> ay_vdrs_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vdrs_replay_contract_intro
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) :
    runSeedManifest -> buildConfigDigest -> benchmarkFingerprint ->
    resultArtifactDigest -> certificateModelDigest -> checkerTranscript ->
    stdoutStderrDigests -> archiveManifest -> submissionManifest ->
    fallbackNoClaimPath ->
    ay_vdrs_replay_contract runSeedManifest buildConfigDigest
      benchmarkFingerprint resultArtifactDigest certificateModelDigest
      checkerTranscript stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath :=
  fun seedProof buildProof fingerprintProof resultProof certificateProof
      checkerProof logProof archiveProof submissionProof fallbackProof
      result build =>
    build seedProof buildProof fingerprintProof resultProof certificateProof
      checkerProof logProof archiveProof submissionProof fallbackProof

theorem ay_vdrs_replay_contract_seed
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) :
    ay_vdrs_replay_contract runSeedManifest buildConfigDigest
      benchmarkFingerprint resultArtifactDigest certificateModelDigest
      checkerTranscript stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath ->
    runSeedManifest :=
  fun contract =>
    contract runSeedManifest
      (fun seedProof _buildProof _fingerprintProof _resultProof
          _certificateProof _checkerProof _logProof _archiveProof
          _submissionProof _fallbackProof => seedProof)

theorem ay_vdrs_replay_contract_build
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) :
    ay_vdrs_replay_contract runSeedManifest buildConfigDigest
      benchmarkFingerprint resultArtifactDigest certificateModelDigest
      checkerTranscript stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath ->
    buildConfigDigest :=
  fun contract =>
    contract buildConfigDigest
      (fun _seedProof buildProof _fingerprintProof _resultProof
          _certificateProof _checkerProof _logProof _archiveProof
          _submissionProof _fallbackProof => buildProof)

theorem ay_vdrs_replay_contract_fingerprint
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) :
    ay_vdrs_replay_contract runSeedManifest buildConfigDigest
      benchmarkFingerprint resultArtifactDigest certificateModelDigest
      checkerTranscript stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _seedProof _buildProof fingerprintProof _resultProof
          _certificateProof _checkerProof _logProof _archiveProof
          _submissionProof _fallbackProof => fingerprintProof)

theorem ay_vdrs_replay_contract_result_artifact
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) :
    ay_vdrs_replay_contract runSeedManifest buildConfigDigest
      benchmarkFingerprint resultArtifactDigest certificateModelDigest
      checkerTranscript stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath ->
    resultArtifactDigest :=
  fun contract =>
    contract resultArtifactDigest
      (fun _seedProof _buildProof _fingerprintProof resultProof
          _certificateProof _checkerProof _logProof _archiveProof
          _submissionProof _fallbackProof => resultProof)

theorem ay_vdrs_replay_contract_certificate_model
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) :
    ay_vdrs_replay_contract runSeedManifest buildConfigDigest
      benchmarkFingerprint resultArtifactDigest certificateModelDigest
      checkerTranscript stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath ->
    certificateModelDigest :=
  fun contract =>
    contract certificateModelDigest
      (fun _seedProof _buildProof _fingerprintProof _resultProof
          certificateProof _checkerProof _logProof _archiveProof
          _submissionProof _fallbackProof => certificateProof)

theorem ay_vdrs_replay_contract_checker
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) :
    ay_vdrs_replay_contract runSeedManifest buildConfigDigest
      benchmarkFingerprint resultArtifactDigest certificateModelDigest
      checkerTranscript stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _seedProof _buildProof _fingerprintProof _resultProof
          _certificateProof checkerProof _logProof _archiveProof
          _submissionProof _fallbackProof => checkerProof)

theorem ay_vdrs_replay_contract_logs
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) :
    ay_vdrs_replay_contract runSeedManifest buildConfigDigest
      benchmarkFingerprint resultArtifactDigest certificateModelDigest
      checkerTranscript stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath ->
    stdoutStderrDigests :=
  fun contract =>
    contract stdoutStderrDigests
      (fun _seedProof _buildProof _fingerprintProof _resultProof
          _certificateProof _checkerProof logProof _archiveProof
          _submissionProof _fallbackProof => logProof)

theorem ay_vdrs_replay_contract_archive
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) :
    ay_vdrs_replay_contract runSeedManifest buildConfigDigest
      benchmarkFingerprint resultArtifactDigest certificateModelDigest
      checkerTranscript stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _seedProof _buildProof _fingerprintProof _resultProof
          _certificateProof _checkerProof _logProof archiveProof
          _submissionProof _fallbackProof => archiveProof)

theorem ay_vdrs_replay_contract_submission
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) :
    ay_vdrs_replay_contract runSeedManifest buildConfigDigest
      benchmarkFingerprint resultArtifactDigest certificateModelDigest
      checkerTranscript stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun _seedProof _buildProof _fingerprintProof _resultProof
          _certificateProof _checkerProof _logProof _archiveProof
          submissionProof _fallbackProof => submissionProof)

theorem ay_vdrs_replay_contract_fallback
    (runSeedManifest buildConfigDigest benchmarkFingerprint
      resultArtifactDigest certificateModelDigest checkerTranscript
      stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath : Prop) :
    ay_vdrs_replay_contract runSeedManifest buildConfigDigest
      benchmarkFingerprint resultArtifactDigest certificateModelDigest
      checkerTranscript stdoutStderrDigests archiveManifest submissionManifest
      fallbackNoClaimPath ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _seedProof _buildProof _fingerprintProof _resultProof
          _certificateProof _checkerProof _logProof _archiveProof
          _submissionProof fallbackProof => fallbackProof)

theorem ay_vdrs_sat_publication_intro
    (replayContract modelEvidence originalModel : Prop) :
    replayContract -> modelEvidence -> originalModel ->
    ay_vdrs_sat_publication replayContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vdrs_conj_intro replayContract
      (ay_vdrs_conj modelEvidence originalModel) contractProof
      (ay_vdrs_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vdrs_sat_publication_original_model
    (replayContract modelEvidence originalModel : Prop) :
    ay_vdrs_sat_publication replayContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vdrs_conj_right modelEvidence originalModel
      (ay_vdrs_conj_right replayContract
        (ay_vdrs_conj modelEvidence originalModel) publication)

theorem ay_vdrs_unsat_publication_intro
    (replayContract proofEvidence originalEmptyClause : Prop) :
    replayContract -> proofEvidence -> originalEmptyClause ->
    ay_vdrs_unsat_publication replayContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vdrs_conj_intro replayContract
      (ay_vdrs_conj proofEvidence originalEmptyClause) contractProof
      (ay_vdrs_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vdrs_unsat_publication_original_empty_clause
    (replayContract proofEvidence originalEmptyClause : Prop) :
    ay_vdrs_unsat_publication replayContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vdrs_conj_right proofEvidence originalEmptyClause
      (ay_vdrs_conj_right replayContract
        (ay_vdrs_conj proofEvidence originalEmptyClause) publication)

theorem ay_vdrs_accepted_replay_sat_sound
    (replayContract modelEvidence originalModel : Prop) :
    ay_vdrs_sat_publication replayContract modelEvidence originalModel ->
    originalModel :=
  ay_vdrs_sat_publication_original_model replayContract modelEvidence
    originalModel

theorem ay_vdrs_accepted_replay_unsat_sound
    (replayContract proofEvidence originalEmptyClause : Prop) :
    ay_vdrs_unsat_publication replayContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_vdrs_unsat_publication_original_empty_clause replayContract proofEvidence
    originalEmptyClause

theorem ay_vdrs_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vdrs_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vdrs_conj_intro reason (ay_vdrs_conj fallbackPath auditTrail)
      reasonProof
      (ay_vdrs_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_vdrs_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vdrs_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vdrs_conj_left reason (ay_vdrs_conj fallbackPath auditTrail)
      noClaim

theorem ay_vdrs_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vdrs_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_vdrs_conj_intro reason
      (ay_vdrs_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_vdrs_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_vdrs_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vdrs_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vdrs_conj_left (satFact -> False) (unsatFact -> False)
      (ay_vdrs_conj_right reason
        (ay_vdrs_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vdrs_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vdrs_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vdrs_conj_right (satFact -> False) (unsatFact -> False)
      (ay_vdrs_conj_right reason
        (ay_vdrs_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vdrs_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vdrs_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vdrs_conj_intro reason
      (ay_vdrs_conj fallbackPath recomputeObligation) reasonProof
      (ay_vdrs_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_vdrs_replay_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vdrs_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_vdrs_conj_intro
      (ay_vdrs_blocked_publication satFact unsatFact reason)
      (ay_vdrs_recompute reason fallbackPath recomputeObligation)
      (ay_vdrs_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_vdrs_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vdrs_replay_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vdrs_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vdrs_blocked_publication_no_sat satFact unsatFact reason
      (ay_vdrs_conj_left
        (ay_vdrs_blocked_publication satFact unsatFact reason)
        (ay_vdrs_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vdrs_replay_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vdrs_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vdrs_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vdrs_conj_left
        (ay_vdrs_blocked_publication satFact unsatFact reason)
        (ay_vdrs_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vdrs_replay_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vdrs_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vdrs_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vdrs_conj_right
      (ay_vdrs_blocked_publication satFact unsatFact reason)
      (ay_vdrs_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vdrs_seed_mismatch_forces_no_claim
    (satFact unsatFact seedMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    seedMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vdrs_no_claim seedMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vdrs_no_claim_intro seedMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vdrs_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vdrs_no_claim buildMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vdrs_no_claim_intro buildMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vdrs_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vdrs_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vdrs_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vdrs_result_mismatch_forces_no_claim
    (satFact unsatFact resultMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    resultMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vdrs_no_claim resultMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vdrs_no_claim_intro resultMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vdrs_certificate_mismatch_forces_no_claim
    (satFact unsatFact certificateMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    certificateMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vdrs_no_claim certificateMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vdrs_no_claim_intro certificateMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vdrs_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vdrs_no_claim checkerMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vdrs_no_claim_intro checkerMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vdrs_log_mismatch_forces_no_claim
    (satFact unsatFact logMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    logMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vdrs_no_claim logMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vdrs_no_claim_intro logMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vdrs_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vdrs_no_claim archiveMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vdrs_no_claim_intro archiveMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vdrs_submission_mismatch_forces_no_claim
    (satFact unsatFact submissionMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    submissionMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vdrs_no_claim submissionMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vdrs_no_claim_intro submissionMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vdrs_failed_replay_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vdrs_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vdrs_replay_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vdrs_failed_replay_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vdrs_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vdrs_replay_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
