-- SAT-COMP validator solver-version manifest no-claim guard core.
--
-- Sequential-main publication is allowed only when solver version manifest,
-- build config digest, artifacts, checker transcript, benchmark fingerprint,
-- archive/submission manifests, and fallback/no-claim path agree.

def ay_vsvg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vsvg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vsvg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vsvg_disj satFact (ay_vsvg_disj unsatFact noClaimFact)

def ay_vsvg_version_contract
    (solverVersionManifest buildConfigDigest resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint archiveManifest
      submissionManifest fallbackNoClaimPath : Prop) : Prop :=
  forall result : Prop,
    (solverVersionManifest -> buildConfigDigest -> resultArtifact ->
      certificateModel -> checkerTranscript -> benchmarkFingerprint ->
      archiveManifest -> submissionManifest -> fallbackNoClaimPath ->
      result) ->
    result

def ay_vsvg_sat_publication
    (versionContract modelEvidence originalModel : Prop) : Prop :=
  ay_vsvg_conj versionContract
    (ay_vsvg_conj modelEvidence originalModel)

def ay_vsvg_unsat_publication
    (versionContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vsvg_conj versionContract
    (ay_vsvg_conj proofEvidence originalEmptyClause)

def ay_vsvg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vsvg_conj reason (ay_vsvg_conj fallbackPath auditTrail)

def ay_vsvg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vsvg_conj reason
    (ay_vsvg_conj (satFact -> False) (unsatFact -> False))

def ay_vsvg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vsvg_conj reason
    (ay_vsvg_conj fallbackPath recomputeObligation)

def ay_vsvg_manifest_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vsvg_conj
    (ay_vsvg_blocked_publication satFact unsatFact reason)
    (ay_vsvg_recompute reason fallbackPath recomputeObligation)

theorem ay_vsvg_conj_intro (left right : Prop) :
    left -> right -> ay_vsvg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vsvg_conj_left (left right : Prop) :
    ay_vsvg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vsvg_conj_right (left right : Prop) :
    ay_vsvg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vsvg_disj_left (left right : Prop) :
    left -> ay_vsvg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vsvg_disj_right (left right : Prop) :
    right -> ay_vsvg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vsvg_version_contract_intro
    (solverVersionManifest buildConfigDigest resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint archiveManifest
      submissionManifest fallbackNoClaimPath : Prop) :
    solverVersionManifest -> buildConfigDigest -> resultArtifact ->
    certificateModel -> checkerTranscript -> benchmarkFingerprint ->
    archiveManifest -> submissionManifest -> fallbackNoClaimPath ->
    ay_vsvg_version_contract solverVersionManifest buildConfigDigest
      resultArtifact certificateModel checkerTranscript benchmarkFingerprint
      archiveManifest submissionManifest fallbackNoClaimPath :=
  fun versionProof buildProof artifactProof certificateProof checkerProof
      fingerprintProof archiveProof submissionProof fallbackProof result
      build =>
    build versionProof buildProof artifactProof certificateProof checkerProof
      fingerprintProof archiveProof submissionProof fallbackProof

theorem ay_vsvg_version_contract_version
    (solverVersionManifest buildConfigDigest resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint archiveManifest
      submissionManifest fallbackNoClaimPath : Prop) :
    ay_vsvg_version_contract solverVersionManifest buildConfigDigest
      resultArtifact certificateModel checkerTranscript benchmarkFingerprint
      archiveManifest submissionManifest fallbackNoClaimPath ->
    solverVersionManifest :=
  fun contract =>
    contract solverVersionManifest
      (fun versionProof _buildProof _artifactProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _submissionProof
          _fallbackProof => versionProof)

theorem ay_vsvg_version_contract_build
    (solverVersionManifest buildConfigDigest resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint archiveManifest
      submissionManifest fallbackNoClaimPath : Prop) :
    ay_vsvg_version_contract solverVersionManifest buildConfigDigest
      resultArtifact certificateModel checkerTranscript benchmarkFingerprint
      archiveManifest submissionManifest fallbackNoClaimPath ->
    buildConfigDigest :=
  fun contract =>
    contract buildConfigDigest
      (fun _versionProof buildProof _artifactProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _submissionProof
          _fallbackProof => buildProof)

theorem ay_vsvg_version_contract_artifact
    (solverVersionManifest buildConfigDigest resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint archiveManifest
      submissionManifest fallbackNoClaimPath : Prop) :
    ay_vsvg_version_contract solverVersionManifest buildConfigDigest
      resultArtifact certificateModel checkerTranscript benchmarkFingerprint
      archiveManifest submissionManifest fallbackNoClaimPath ->
    resultArtifact :=
  fun contract =>
    contract resultArtifact
      (fun _versionProof _buildProof artifactProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _submissionProof
          _fallbackProof => artifactProof)

theorem ay_vsvg_version_contract_certificate_model
    (solverVersionManifest buildConfigDigest resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint archiveManifest
      submissionManifest fallbackNoClaimPath : Prop) :
    ay_vsvg_version_contract solverVersionManifest buildConfigDigest
      resultArtifact certificateModel checkerTranscript benchmarkFingerprint
      archiveManifest submissionManifest fallbackNoClaimPath ->
    certificateModel :=
  fun contract =>
    contract certificateModel
      (fun _versionProof _buildProof _artifactProof certificateProof
          _checkerProof _fingerprintProof _archiveProof _submissionProof
          _fallbackProof => certificateProof)

theorem ay_vsvg_version_contract_checker
    (solverVersionManifest buildConfigDigest resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint archiveManifest
      submissionManifest fallbackNoClaimPath : Prop) :
    ay_vsvg_version_contract solverVersionManifest buildConfigDigest
      resultArtifact certificateModel checkerTranscript benchmarkFingerprint
      archiveManifest submissionManifest fallbackNoClaimPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _versionProof _buildProof _artifactProof _certificateProof
          checkerProof _fingerprintProof _archiveProof _submissionProof
          _fallbackProof => checkerProof)

theorem ay_vsvg_version_contract_fingerprint
    (solverVersionManifest buildConfigDigest resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint archiveManifest
      submissionManifest fallbackNoClaimPath : Prop) :
    ay_vsvg_version_contract solverVersionManifest buildConfigDigest
      resultArtifact certificateModel checkerTranscript benchmarkFingerprint
      archiveManifest submissionManifest fallbackNoClaimPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _versionProof _buildProof _artifactProof _certificateProof
          _checkerProof fingerprintProof _archiveProof _submissionProof
          _fallbackProof => fingerprintProof)

theorem ay_vsvg_version_contract_archive
    (solverVersionManifest buildConfigDigest resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint archiveManifest
      submissionManifest fallbackNoClaimPath : Prop) :
    ay_vsvg_version_contract solverVersionManifest buildConfigDigest
      resultArtifact certificateModel checkerTranscript benchmarkFingerprint
      archiveManifest submissionManifest fallbackNoClaimPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _versionProof _buildProof _artifactProof _certificateProof
          _checkerProof _fingerprintProof archiveProof _submissionProof
          _fallbackProof => archiveProof)

theorem ay_vsvg_version_contract_submission
    (solverVersionManifest buildConfigDigest resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint archiveManifest
      submissionManifest fallbackNoClaimPath : Prop) :
    ay_vsvg_version_contract solverVersionManifest buildConfigDigest
      resultArtifact certificateModel checkerTranscript benchmarkFingerprint
      archiveManifest submissionManifest fallbackNoClaimPath ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun _versionProof _buildProof _artifactProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof submissionProof
          _fallbackProof => submissionProof)

theorem ay_vsvg_version_contract_fallback
    (solverVersionManifest buildConfigDigest resultArtifact
      certificateModel checkerTranscript benchmarkFingerprint archiveManifest
      submissionManifest fallbackNoClaimPath : Prop) :
    ay_vsvg_version_contract solverVersionManifest buildConfigDigest
      resultArtifact certificateModel checkerTranscript benchmarkFingerprint
      archiveManifest submissionManifest fallbackNoClaimPath ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _versionProof _buildProof _artifactProof _certificateProof
          _checkerProof _fingerprintProof _archiveProof _submissionProof
          fallbackProof => fallbackProof)

theorem ay_vsvg_sat_publication_intro
    (versionContract modelEvidence originalModel : Prop) :
    versionContract -> modelEvidence -> originalModel ->
    ay_vsvg_sat_publication versionContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vsvg_conj_intro versionContract
      (ay_vsvg_conj modelEvidence originalModel) contractProof
      (ay_vsvg_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vsvg_sat_publication_original_model
    (versionContract modelEvidence originalModel : Prop) :
    ay_vsvg_sat_publication versionContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vsvg_conj_right modelEvidence originalModel
      (ay_vsvg_conj_right versionContract
        (ay_vsvg_conj modelEvidence originalModel) publication)

theorem ay_vsvg_unsat_publication_intro
    (versionContract proofEvidence originalEmptyClause : Prop) :
    versionContract -> proofEvidence -> originalEmptyClause ->
    ay_vsvg_unsat_publication versionContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vsvg_conj_intro versionContract
      (ay_vsvg_conj proofEvidence originalEmptyClause) contractProof
      (ay_vsvg_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vsvg_unsat_publication_original_empty_clause
    (versionContract proofEvidence originalEmptyClause : Prop) :
    ay_vsvg_unsat_publication versionContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vsvg_conj_right proofEvidence originalEmptyClause
      (ay_vsvg_conj_right versionContract
        (ay_vsvg_conj proofEvidence originalEmptyClause) publication)

theorem ay_vsvg_accepted_version_sat_sound
    (versionContract modelEvidence originalModel : Prop) :
    ay_vsvg_sat_publication versionContract modelEvidence originalModel ->
    originalModel :=
  ay_vsvg_sat_publication_original_model versionContract modelEvidence
    originalModel

theorem ay_vsvg_accepted_version_unsat_sound
    (versionContract proofEvidence originalEmptyClause : Prop) :
    ay_vsvg_unsat_publication versionContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_vsvg_unsat_publication_original_empty_clause versionContract
    proofEvidence originalEmptyClause

theorem ay_vsvg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vsvg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vsvg_conj_intro reason (ay_vsvg_conj fallbackPath auditTrail)
      reasonProof
      (ay_vsvg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_vsvg_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vsvg_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vsvg_conj_left reason (ay_vsvg_conj fallbackPath auditTrail)
      noClaim

theorem ay_vsvg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vsvg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_vsvg_conj_intro reason
      (ay_vsvg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_vsvg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_vsvg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vsvg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vsvg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_vsvg_conj_right reason
        (ay_vsvg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vsvg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vsvg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vsvg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_vsvg_conj_right reason
        (ay_vsvg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vsvg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vsvg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vsvg_conj_intro reason
      (ay_vsvg_conj fallbackPath recomputeObligation) reasonProof
      (ay_vsvg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_vsvg_manifest_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsvg_manifest_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_vsvg_conj_intro
      (ay_vsvg_blocked_publication satFact unsatFact reason)
      (ay_vsvg_recompute reason fallbackPath recomputeObligation)
      (ay_vsvg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_vsvg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vsvg_manifest_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsvg_manifest_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vsvg_blocked_publication_no_sat satFact unsatFact reason
      (ay_vsvg_conj_left
        (ay_vsvg_blocked_publication satFact unsatFact reason)
        (ay_vsvg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsvg_manifest_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsvg_manifest_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vsvg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vsvg_conj_left
        (ay_vsvg_blocked_publication satFact unsatFact reason)
        (ay_vsvg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vsvg_manifest_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsvg_manifest_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vsvg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vsvg_conj_right
      (ay_vsvg_blocked_publication satFact unsatFact reason)
      (ay_vsvg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vsvg_version_mismatch_forces_no_claim
    (satFact unsatFact versionMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    versionMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsvg_no_claim versionMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vsvg_no_claim_intro versionMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vsvg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsvg_no_claim buildMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vsvg_no_claim_intro buildMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vsvg_schema_mismatch_forces_no_claim
    (satFact unsatFact schemaMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    schemaMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vsvg_no_claim schemaMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vsvg_no_claim_intro schemaMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vsvg_failed_manifest_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsvg_manifest_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vsvg_manifest_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vsvg_failed_manifest_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vsvg_manifest_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vsvg_manifest_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vsvg_no_claim_cannot_create_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_vsvg_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_vsvg_no_claim_cannot_create_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_vsvg_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
