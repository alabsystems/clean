-- SAT-COMP validator result-JSON schema no-claim guard core.
--
-- Malformed result JSON or schema-version failures publish no semantic
-- SAT/UNSAT claim unless schema evidence and all validation artifacts agree.

def ay_vjsg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vjsg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vjsg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vjsg_disj satFact (ay_vjsg_disj unsatFact noClaimFact)

def ay_vjsg_schema_contract
    (resultJsonSchema resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      schemaVersionEvidence : Prop) : Prop :=
  forall result : Prop,
    (resultJsonSchema -> resultArtifact -> certificateModel ->
      checkerTranscript -> benchmarkFingerprint -> buildConfig ->
      archiveManifest -> submissionManifest -> schemaVersionEvidence ->
      result) ->
    result

def ay_vjsg_sat_publication
    (schemaContract modelEvidence originalModel : Prop) : Prop :=
  ay_vjsg_conj schemaContract
    (ay_vjsg_conj modelEvidence originalModel)

def ay_vjsg_unsat_publication
    (schemaContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vjsg_conj schemaContract
    (ay_vjsg_conj proofEvidence originalEmptyClause)

def ay_vjsg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_vjsg_conj reason (ay_vjsg_conj fallbackPath auditTrail)

def ay_vjsg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vjsg_conj reason
    (ay_vjsg_conj (satFact -> False) (unsatFact -> False))

def ay_vjsg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_vjsg_conj reason
    (ay_vjsg_conj fallbackPath recomputeObligation)

def ay_vjsg_schema_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_vjsg_conj
    (ay_vjsg_blocked_publication satFact unsatFact reason)
    (ay_vjsg_recompute reason fallbackPath recomputeObligation)

theorem ay_vjsg_conj_intro (left right : Prop) :
    left -> right -> ay_vjsg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vjsg_conj_left (left right : Prop) :
    ay_vjsg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vjsg_conj_right (left right : Prop) :
    ay_vjsg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vjsg_disj_left (left right : Prop) :
    left -> ay_vjsg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vjsg_disj_right (left right : Prop) :
    right -> ay_vjsg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vjsg_schema_contract_intro
    (resultJsonSchema resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      schemaVersionEvidence : Prop) :
    resultJsonSchema -> resultArtifact -> certificateModel ->
    checkerTranscript -> benchmarkFingerprint -> buildConfig ->
    archiveManifest -> submissionManifest -> schemaVersionEvidence ->
    ay_vjsg_schema_contract resultJsonSchema resultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest schemaVersionEvidence :=
  fun schemaProof artifactProof certificateProof checkerProof
      fingerprintProof buildProof archiveProof submissionProof versionProof
      result build =>
    build schemaProof artifactProof certificateProof checkerProof
      fingerprintProof buildProof archiveProof submissionProof versionProof

theorem ay_vjsg_schema_contract_schema
    (resultJsonSchema resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      schemaVersionEvidence : Prop) :
    ay_vjsg_schema_contract resultJsonSchema resultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest schemaVersionEvidence ->
    resultJsonSchema :=
  fun contract =>
    contract resultJsonSchema
      (fun schemaProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _submissionProof
          _versionProof => schemaProof)

theorem ay_vjsg_schema_contract_artifact
    (resultJsonSchema resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      schemaVersionEvidence : Prop) :
    ay_vjsg_schema_contract resultJsonSchema resultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest schemaVersionEvidence ->
    resultArtifact :=
  fun contract =>
    contract resultArtifact
      (fun _schemaProof artifactProof _certificateProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _submissionProof
          _versionProof => artifactProof)

theorem ay_vjsg_schema_contract_certificate_model
    (resultJsonSchema resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      schemaVersionEvidence : Prop) :
    ay_vjsg_schema_contract resultJsonSchema resultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest schemaVersionEvidence ->
    certificateModel :=
  fun contract =>
    contract certificateModel
      (fun _schemaProof _artifactProof certificateProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _submissionProof
          _versionProof => certificateProof)

theorem ay_vjsg_schema_contract_checker
    (resultJsonSchema resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      schemaVersionEvidence : Prop) :
    ay_vjsg_schema_contract resultJsonSchema resultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest schemaVersionEvidence ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _schemaProof _artifactProof _certificateProof checkerProof
          _fingerprintProof _buildProof _archiveProof _submissionProof
          _versionProof => checkerProof)

theorem ay_vjsg_schema_contract_fingerprint
    (resultJsonSchema resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      schemaVersionEvidence : Prop) :
    ay_vjsg_schema_contract resultJsonSchema resultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest schemaVersionEvidence ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _schemaProof _artifactProof _certificateProof _checkerProof
          fingerprintProof _buildProof _archiveProof _submissionProof
          _versionProof => fingerprintProof)

theorem ay_vjsg_schema_contract_build
    (resultJsonSchema resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      schemaVersionEvidence : Prop) :
    ay_vjsg_schema_contract resultJsonSchema resultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest schemaVersionEvidence ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _schemaProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof buildProof _archiveProof _submissionProof
          _versionProof => buildProof)

theorem ay_vjsg_schema_contract_archive
    (resultJsonSchema resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      schemaVersionEvidence : Prop) :
    ay_vjsg_schema_contract resultJsonSchema resultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest schemaVersionEvidence ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _schemaProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof _buildProof archiveProof _submissionProof
          _versionProof => archiveProof)

theorem ay_vjsg_schema_contract_submission
    (resultJsonSchema resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      schemaVersionEvidence : Prop) :
    ay_vjsg_schema_contract resultJsonSchema resultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest schemaVersionEvidence ->
    submissionManifest :=
  fun contract =>
    contract submissionManifest
      (fun _schemaProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof _buildProof _archiveProof submissionProof
          _versionProof => submissionProof)

theorem ay_vjsg_schema_contract_schema_version
    (resultJsonSchema resultArtifact certificateModel checkerTranscript
      benchmarkFingerprint buildConfig archiveManifest submissionManifest
      schemaVersionEvidence : Prop) :
    ay_vjsg_schema_contract resultJsonSchema resultArtifact certificateModel
      checkerTranscript benchmarkFingerprint buildConfig archiveManifest
      submissionManifest schemaVersionEvidence ->
    schemaVersionEvidence :=
  fun contract =>
    contract schemaVersionEvidence
      (fun _schemaProof _artifactProof _certificateProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _submissionProof
          versionProof => versionProof)

theorem ay_vjsg_sat_publication_intro
    (schemaContract modelEvidence originalModel : Prop) :
    schemaContract -> modelEvidence -> originalModel ->
    ay_vjsg_sat_publication schemaContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vjsg_conj_intro schemaContract
      (ay_vjsg_conj modelEvidence originalModel) contractProof
      (ay_vjsg_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vjsg_sat_publication_original_model
    (schemaContract modelEvidence originalModel : Prop) :
    ay_vjsg_sat_publication schemaContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vjsg_conj_right modelEvidence originalModel
      (ay_vjsg_conj_right schemaContract
        (ay_vjsg_conj modelEvidence originalModel) publication)

theorem ay_vjsg_unsat_publication_intro
    (schemaContract proofEvidence originalEmptyClause : Prop) :
    schemaContract -> proofEvidence -> originalEmptyClause ->
    ay_vjsg_unsat_publication schemaContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vjsg_conj_intro schemaContract
      (ay_vjsg_conj proofEvidence originalEmptyClause) contractProof
      (ay_vjsg_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vjsg_unsat_publication_original_empty_clause
    (schemaContract proofEvidence originalEmptyClause : Prop) :
    ay_vjsg_unsat_publication schemaContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vjsg_conj_right proofEvidence originalEmptyClause
      (ay_vjsg_conj_right schemaContract
        (ay_vjsg_conj proofEvidence originalEmptyClause) publication)

theorem ay_vjsg_accepted_schema_sat_sound
    (schemaContract modelEvidence originalModel : Prop) :
    ay_vjsg_sat_publication schemaContract modelEvidence originalModel ->
    originalModel :=
  ay_vjsg_sat_publication_original_model schemaContract modelEvidence
    originalModel

theorem ay_vjsg_accepted_schema_unsat_sound
    (schemaContract proofEvidence originalEmptyClause : Prop) :
    ay_vjsg_unsat_publication schemaContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_vjsg_unsat_publication_original_empty_clause schemaContract
    proofEvidence originalEmptyClause

theorem ay_vjsg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_vjsg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vjsg_conj_intro reason (ay_vjsg_conj fallbackPath auditTrail)
      reasonProof
      (ay_vjsg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_vjsg_no_claim_reason
    (reason fallbackPath auditTrail : Prop) :
    ay_vjsg_no_claim reason fallbackPath auditTrail -> reason :=
  fun noClaim =>
    ay_vjsg_conj_left reason (ay_vjsg_conj fallbackPath auditTrail)
      noClaim

theorem ay_vjsg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vjsg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_vjsg_conj_intro reason
      (ay_vjsg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_vjsg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_vjsg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vjsg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vjsg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_vjsg_conj_right reason
        (ay_vjsg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vjsg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vjsg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vjsg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_vjsg_conj_right reason
        (ay_vjsg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_vjsg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_vjsg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vjsg_conj_intro reason
      (ay_vjsg_conj fallbackPath recomputeObligation) reasonProof
      (ay_vjsg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_vjsg_schema_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_vjsg_conj_intro
      (ay_vjsg_blocked_publication satFact unsatFact reason)
      (ay_vjsg_recompute reason fallbackPath recomputeObligation)
      (ay_vjsg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_vjsg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vjsg_schema_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vjsg_blocked_publication_no_sat satFact unsatFact reason
      (ay_vjsg_conj_left
        (ay_vjsg_blocked_publication satFact unsatFact reason)
        (ay_vjsg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vjsg_schema_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vjsg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vjsg_conj_left
        (ay_vjsg_blocked_publication satFact unsatFact reason)
        (ay_vjsg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_vjsg_schema_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_vjsg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_vjsg_conj_right
      (ay_vjsg_blocked_publication satFact unsatFact reason)
      (ay_vjsg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_vjsg_schema_mismatch_forces_no_claim
    (satFact unsatFact schemaMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    schemaMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vjsg_no_claim schemaMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vjsg_no_claim_intro schemaMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vjsg_malformed_json_forces_no_claim
    (satFact unsatFact malformedJson fallbackPath auditTrail
      recomputeObligation : Prop) :
    malformedJson -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vjsg_no_claim malformedJson fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vjsg_no_claim_intro malformedJson fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vjsg_artifact_mismatch_forces_no_claim
    (satFact unsatFact artifactMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vjsg_no_claim artifactMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vjsg_no_claim_intro artifactMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vjsg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vjsg_no_claim checkerMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vjsg_no_claim_intro checkerMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vjsg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vjsg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vjsg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vjsg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vjsg_no_claim buildMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vjsg_no_claim_intro buildMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vjsg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vjsg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vjsg_no_claim_intro archiveMismatch fallbackPath auditTrail mismatch
      fallbackProof auditProof

theorem ay_vjsg_submission_mismatch_forces_no_claim
    (satFact unsatFact submissionMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    submissionMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_vjsg_no_claim submissionMismatch fallbackPath auditTrail :=
  fun mismatch fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_vjsg_no_claim_intro submissionMismatch fallbackPath auditTrail
      mismatch fallbackProof auditProof

theorem ay_vjsg_failed_schema_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_vjsg_schema_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_vjsg_failed_schema_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_vjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_vjsg_schema_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
