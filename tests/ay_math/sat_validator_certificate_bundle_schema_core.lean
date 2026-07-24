-- SAT-COMP validator certificate-bundle schema core.
--
-- Sequential-main public certificate bundles may certify SAT/UNSAT only when
-- schema agreement and cross-field agreement connect result token,
-- model/proof artifact digests, checker transcript, formula fingerprint,
-- build config, output-line evidence, and fallback diagnostics.

def ay_vcbs_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vcbs_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vcbs_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vcbs_disj satFact (ay_vcbs_disj unsatFact noClaimFact)

def ay_vcbs_schema_contract
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) : Prop :=
  forall result : Prop,
    (schemaAgreement -> crossFieldAgreement -> resultToken ->
      artifactDigests -> checkerTranscript -> formulaFingerprint ->
      buildConfig -> outputLineEvidence -> fallbackDiagnostics -> result) ->
    result

def ay_vcbs_sat_publication
    (schemaContract modelEvidence originalModel : Prop) : Prop :=
  ay_vcbs_conj schemaContract
    (ay_vcbs_conj modelEvidence originalModel)

def ay_vcbs_unsat_publication
    (schemaContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vcbs_conj schemaContract
    (ay_vcbs_conj proofEvidence originalEmptyClause)

def ay_vcbs_no_claim
    (reason fallbackDiagnostics auditTrail : Prop) : Prop :=
  ay_vcbs_conj reason (ay_vcbs_conj fallbackDiagnostics auditTrail)

def ay_vcbs_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vcbs_conj reason
    (ay_vcbs_conj (satFact -> False) (unsatFact -> False))

def ay_vcbs_recompute
    (reason fallbackDiagnostics recomputeObligation : Prop) : Prop :=
  ay_vcbs_conj reason
    (ay_vcbs_conj fallbackDiagnostics recomputeObligation)

def ay_vcbs_schema_failure
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) : Prop :=
  ay_vcbs_conj
    (ay_vcbs_blocked_publication satFact unsatFact reason)
    (ay_vcbs_recompute reason fallbackDiagnostics recomputeObligation)

theorem ay_vcbs_conj_intro (left right : Prop) :
    left -> right -> ay_vcbs_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcbs_conj_left (left right : Prop) :
    ay_vcbs_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcbs_conj_right (left right : Prop) :
    ay_vcbs_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcbs_disj_left (left right : Prop) :
    left -> ay_vcbs_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vcbs_disj_right (left right : Prop) :
    right -> ay_vcbs_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcbs_schema_contract_intro
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    schemaAgreement -> crossFieldAgreement -> resultToken ->
    artifactDigests -> checkerTranscript -> formulaFingerprint ->
    buildConfig -> outputLineEvidence -> fallbackDiagnostics ->
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics :=
  fun schemaProof crossProof tokenProof digestProof transcriptProof
      fingerprintProof buildProof outputProof fallbackProof result build =>
    build schemaProof crossProof tokenProof digestProof transcriptProof
      fingerprintProof buildProof outputProof fallbackProof

theorem ay_vcbs_schema_contract_schema_agreement
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics ->
    schemaAgreement :=
  fun contract =>
    contract schemaAgreement
      (fun schemaProof _crossProof _tokenProof _digestProof
          _transcriptProof _fingerprintProof _buildProof _outputProof
          _fallbackProof => schemaProof)

theorem ay_vcbs_schema_contract_cross_field_agreement
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics ->
    crossFieldAgreement :=
  fun contract =>
    contract crossFieldAgreement
      (fun _schemaProof crossProof _tokenProof _digestProof
          _transcriptProof _fingerprintProof _buildProof _outputProof
          _fallbackProof => crossProof)

theorem ay_vcbs_schema_contract_result_token
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics ->
    resultToken :=
  fun contract =>
    contract resultToken
      (fun _schemaProof _crossProof tokenProof _digestProof
          _transcriptProof _fingerprintProof _buildProof _outputProof
          _fallbackProof => tokenProof)

theorem ay_vcbs_schema_contract_artifact_digests
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics ->
    artifactDigests :=
  fun contract =>
    contract artifactDigests
      (fun _schemaProof _crossProof _tokenProof digestProof
          _transcriptProof _fingerprintProof _buildProof _outputProof
          _fallbackProof => digestProof)

theorem ay_vcbs_schema_contract_checker_transcript
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _schemaProof _crossProof _tokenProof _digestProof
          transcriptProof _fingerprintProof _buildProof _outputProof
          _fallbackProof => transcriptProof)

theorem ay_vcbs_schema_contract_formula_fingerprint
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics ->
    formulaFingerprint :=
  fun contract =>
    contract formulaFingerprint
      (fun _schemaProof _crossProof _tokenProof _digestProof
          _transcriptProof fingerprintProof _buildProof _outputProof
          _fallbackProof => fingerprintProof)

theorem ay_vcbs_schema_contract_build_config
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _schemaProof _crossProof _tokenProof _digestProof
          _transcriptProof _fingerprintProof buildProof _outputProof
          _fallbackProof => buildProof)

theorem ay_vcbs_schema_contract_output_line_evidence
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics ->
    outputLineEvidence :=
  fun contract =>
    contract outputLineEvidence
      (fun _schemaProof _crossProof _tokenProof _digestProof
          _transcriptProof _fingerprintProof _buildProof outputProof
          _fallbackProof => outputProof)

theorem ay_vcbs_schema_contract_fallback_diagnostics
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics ->
    fallbackDiagnostics :=
  fun contract =>
    contract fallbackDiagnostics
      (fun _schemaProof _crossProof _tokenProof _digestProof
          _transcriptProof _fingerprintProof _buildProof _outputProof
          fallbackProof => fallbackProof)

theorem ay_vcbs_sat_publication_intro
    (schemaContract modelEvidence originalModel : Prop) :
    schemaContract -> modelEvidence -> originalModel ->
    ay_vcbs_sat_publication schemaContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vcbs_conj_intro schemaContract
      (ay_vcbs_conj modelEvidence originalModel)
      contractProof
      (ay_vcbs_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vcbs_sat_publication_original_model
    (schemaContract modelEvidence originalModel : Prop) :
    ay_vcbs_sat_publication schemaContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vcbs_conj_right schemaContract
      (ay_vcbs_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vcbs_unsat_publication_intro
    (schemaContract proofEvidence originalEmptyClause : Prop) :
    schemaContract -> proofEvidence -> originalEmptyClause ->
    ay_vcbs_unsat_publication schemaContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vcbs_conj_intro schemaContract
      (ay_vcbs_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vcbs_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vcbs_unsat_publication_original_empty_clause
    (schemaContract proofEvidence originalEmptyClause : Prop) :
    ay_vcbs_unsat_publication schemaContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vcbs_conj_right schemaContract
      (ay_vcbs_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vcbs_accepted_schema_sat_sound
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics modelEvidence originalModel : Prop) :
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vcbs_accepted_schema_unsat_sound
    (schemaAgreement crossFieldAgreement resultToken artifactDigests
      checkerTranscript formulaFingerprint buildConfig outputLineEvidence
      fallbackDiagnostics proofEvidence originalEmptyClause : Prop) :
    ay_vcbs_schema_contract schemaAgreement crossFieldAgreement resultToken
      artifactDigests checkerTranscript formulaFingerprint buildConfig
      outputLineEvidence fallbackDiagnostics ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vcbs_no_claim_intro
    (reason fallbackDiagnostics auditTrail : Prop) :
    reason -> fallbackDiagnostics -> auditTrail ->
    ay_vcbs_no_claim reason fallbackDiagnostics auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vcbs_conj_intro reason
      (ay_vcbs_conj fallbackDiagnostics auditTrail)
      reasonProof
      (ay_vcbs_conj_intro fallbackDiagnostics auditTrail
        fallbackProof auditProof)

theorem ay_vcbs_no_claim_reason
    (reason fallbackDiagnostics auditTrail : Prop) :
    ay_vcbs_no_claim reason fallbackDiagnostics auditTrail -> reason :=
  fun noClaim =>
    ay_vcbs_conj_left reason
      (ay_vcbs_conj fallbackDiagnostics auditTrail)
      noClaim

theorem ay_vcbs_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vcbs_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vcbs_conj_intro reason
      (ay_vcbs_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vcbs_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vcbs_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vcbs_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vcbs_conj_right reason
      (ay_vcbs_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vcbs_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vcbs_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vcbs_conj_right reason
      (ay_vcbs_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vcbs_recompute_intro
    (reason fallbackDiagnostics recomputeObligation : Prop) :
    reason -> fallbackDiagnostics -> recomputeObligation ->
    ay_vcbs_recompute reason fallbackDiagnostics recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vcbs_conj_intro reason
      (ay_vcbs_conj fallbackDiagnostics recomputeObligation)
      reasonProof
      (ay_vcbs_conj_intro fallbackDiagnostics recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vcbs_schema_failure_intro
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcbs_schema_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vcbs_conj_intro
      (ay_vcbs_blocked_publication satFact unsatFact reason)
      (ay_vcbs_recompute reason fallbackDiagnostics recomputeObligation)
      (ay_vcbs_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vcbs_recompute_intro reason fallbackDiagnostics recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vcbs_schema_failure_blocks_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcbs_schema_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vcbs_blocked_publication_no_sat satFact unsatFact reason
      (ay_vcbs_conj_left
        (ay_vcbs_blocked_publication satFact unsatFact reason)
        (ay_vcbs_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vcbs_schema_failure_blocks_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcbs_schema_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vcbs_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vcbs_conj_left
        (ay_vcbs_blocked_publication satFact unsatFact reason)
        (ay_vcbs_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vcbs_schema_failure_recompute
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcbs_schema_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    ay_vcbs_recompute reason fallbackDiagnostics recomputeObligation :=
  fun failure =>
    ay_vcbs_conj_right
      (ay_vcbs_blocked_publication satFact unsatFact reason)
      (ay_vcbs_recompute reason fallbackDiagnostics recomputeObligation)
      failure

theorem ay_vcbs_schema_mismatch_forces_no_claim
    (satFact unsatFact schemaMismatch fallbackDiagnostics
      recomputeObligation : Prop) :
    schemaMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcbs_schema_failure satFact unsatFact schemaMismatch
      fallbackDiagnostics recomputeObligation :=
  ay_vcbs_schema_failure_intro satFact unsatFact schemaMismatch
    fallbackDiagnostics recomputeObligation

theorem ay_vcbs_missing_digest_forces_no_claim
    (satFact unsatFact missingDigest fallbackDiagnostics
      recomputeObligation : Prop) :
    missingDigest -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcbs_schema_failure satFact unsatFact missingDigest
      fallbackDiagnostics recomputeObligation :=
  ay_vcbs_schema_failure_intro satFact unsatFact missingDigest
    fallbackDiagnostics recomputeObligation

theorem ay_vcbs_result_token_conflict_forces_no_claim
    (satFact unsatFact resultTokenConflict fallbackDiagnostics
      recomputeObligation : Prop) :
    resultTokenConflict -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcbs_schema_failure satFact unsatFact resultTokenConflict
      fallbackDiagnostics recomputeObligation :=
  ay_vcbs_schema_failure_intro satFact unsatFact resultTokenConflict
    fallbackDiagnostics recomputeObligation

theorem ay_vcbs_stale_fingerprint_forces_no_claim
    (satFact unsatFact staleFingerprint fallbackDiagnostics
      recomputeObligation : Prop) :
    staleFingerprint -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcbs_schema_failure satFact unsatFact staleFingerprint
      fallbackDiagnostics recomputeObligation :=
  ay_vcbs_schema_failure_intro satFact unsatFact staleFingerprint
    fallbackDiagnostics recomputeObligation

theorem ay_vcbs_checker_rejection_forces_no_claim
    (satFact unsatFact checkerRejection fallbackDiagnostics
      recomputeObligation : Prop) :
    checkerRejection -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcbs_schema_failure satFact unsatFact checkerRejection
      fallbackDiagnostics recomputeObligation :=
  ay_vcbs_schema_failure_intro satFact unsatFact checkerRejection
    fallbackDiagnostics recomputeObligation

theorem ay_vcbs_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackDiagnostics
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcbs_schema_failure satFact unsatFact missingTranscript
      fallbackDiagnostics recomputeObligation :=
  ay_vcbs_schema_failure_intro satFact unsatFact missingTranscript
    fallbackDiagnostics recomputeObligation

theorem ay_vcbs_failed_schema_cannot_bless_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcbs_schema_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  ay_vcbs_schema_failure_blocks_sat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation

theorem ay_vcbs_failed_schema_cannot_bless_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcbs_schema_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  ay_vcbs_schema_failure_blocks_unsat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation
