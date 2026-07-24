-- SAT-COMP validator result JSON/schema guard core.
--
-- Public SAT/UNSAT claims require schema version evidence, parsed result
-- fields, status/certificate digest agreement, checker transcript, benchmark
-- fingerprint, build evidence, archive evidence, fallback, and audit transcript
-- to agree.  JSON/schema failures become no-claim recompute obligations.

def ay_rjsg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rjsg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_rjsg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_rjsg_disj satFact (ay_rjsg_disj unsatFact noClaimFact)

def ay_rjsg_schema_contract
    (schemaVersionManifest parsedResultFields statusCertificateDigestAgreement
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (schemaVersionManifest -> parsedResultFields ->
      statusCertificateDigestAgreement -> checkerTranscript ->
      benchmarkFingerprint -> solverBuildEvidence -> archiveManifest ->
      noClaimFallback -> auditTranscript -> result) ->
    result

def ay_rjsg_sat_publication
    (schemaContract acceptedSchemaEvidence checkedModel originalModel :
      Prop) : Prop :=
  ay_rjsg_conj schemaContract
    (ay_rjsg_conj acceptedSchemaEvidence
      (ay_rjsg_conj checkedModel originalModel))

def ay_rjsg_unsat_publication
    (schemaContract acceptedSchemaEvidence checkedProof originalEmptyClause :
      Prop) : Prop :=
  ay_rjsg_conj schemaContract
    (ay_rjsg_conj acceptedSchemaEvidence
      (ay_rjsg_conj checkedProof originalEmptyClause))

def ay_rjsg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_rjsg_conj reason (ay_rjsg_conj fallbackPath auditTrail)

def ay_rjsg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_rjsg_conj reason
    (ay_rjsg_conj (satFact -> False) (unsatFact -> False))

def ay_rjsg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_rjsg_conj reason
    (ay_rjsg_conj fallbackPath recomputeObligation)

def ay_rjsg_schema_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_rjsg_conj
    (ay_rjsg_blocked_publication satFact unsatFact reason)
    (ay_rjsg_recompute reason fallbackPath recomputeObligation)

theorem ay_rjsg_conj_intro (left right : Prop) :
    left -> right -> ay_rjsg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_rjsg_conj_left (left right : Prop) :
    ay_rjsg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_rjsg_conj_right (left right : Prop) :
    ay_rjsg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_rjsg_disj_left (left right : Prop) :
    left -> ay_rjsg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_rjsg_disj_right (left right : Prop) :
    right -> ay_rjsg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_rjsg_schema_contract_intro
    (schemaVersionManifest parsedResultFields statusCertificateDigestAgreement
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    schemaVersionManifest -> parsedResultFields ->
    statusCertificateDigestAgreement -> checkerTranscript ->
    benchmarkFingerprint -> solverBuildEvidence -> archiveManifest ->
    noClaimFallback -> auditTranscript ->
    ay_rjsg_schema_contract schemaVersionManifest parsedResultFields
      statusCertificateDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :=
  fun schemaProof fieldsProof digestProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof result build =>
    build schemaProof fieldsProof digestProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof

theorem ay_rjsg_contract_schema
    (schemaVersionManifest parsedResultFields statusCertificateDigestAgreement
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_rjsg_schema_contract schemaVersionManifest parsedResultFields
      statusCertificateDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    schemaVersionManifest :=
  fun contract =>
    contract schemaVersionManifest
      (fun schemaProof _fieldsProof _digestProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => schemaProof)

theorem ay_rjsg_contract_fields
    (schemaVersionManifest parsedResultFields statusCertificateDigestAgreement
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_rjsg_schema_contract schemaVersionManifest parsedResultFields
      statusCertificateDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    parsedResultFields :=
  fun contract =>
    contract parsedResultFields
      (fun _schemaProof fieldsProof _digestProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fieldsProof)

theorem ay_rjsg_contract_digest_agreement
    (schemaVersionManifest parsedResultFields statusCertificateDigestAgreement
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_rjsg_schema_contract schemaVersionManifest parsedResultFields
      statusCertificateDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    statusCertificateDigestAgreement :=
  fun contract =>
    contract statusCertificateDigestAgreement
      (fun _schemaProof _fieldsProof digestProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => digestProof)

theorem ay_rjsg_contract_checker
    (schemaVersionManifest parsedResultFields statusCertificateDigestAgreement
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_rjsg_schema_contract schemaVersionManifest parsedResultFields
      statusCertificateDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _schemaProof _fieldsProof _digestProof checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_rjsg_contract_fingerprint
    (schemaVersionManifest parsedResultFields statusCertificateDigestAgreement
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_rjsg_schema_contract schemaVersionManifest parsedResultFields
      statusCertificateDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _schemaProof _fieldsProof _digestProof _checkerProof
          fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_rjsg_contract_build
    (schemaVersionManifest parsedResultFields statusCertificateDigestAgreement
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_rjsg_schema_contract schemaVersionManifest parsedResultFields
      statusCertificateDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _schemaProof _fieldsProof _digestProof _checkerProof
          _fingerprintProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_rjsg_contract_archive
    (schemaVersionManifest parsedResultFields statusCertificateDigestAgreement
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_rjsg_schema_contract schemaVersionManifest parsedResultFields
      statusCertificateDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _schemaProof _fieldsProof _digestProof _checkerProof
          _fingerprintProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_rjsg_contract_fallback
    (schemaVersionManifest parsedResultFields statusCertificateDigestAgreement
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_rjsg_schema_contract schemaVersionManifest parsedResultFields
      statusCertificateDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _schemaProof _fieldsProof _digestProof _checkerProof
          _fingerprintProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_rjsg_contract_audit
    (schemaVersionManifest parsedResultFields statusCertificateDigestAgreement
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest noClaimFallback auditTranscript : Prop) :
    ay_rjsg_schema_contract schemaVersionManifest parsedResultFields
      statusCertificateDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _schemaProof _fieldsProof _digestProof _checkerProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_rjsg_sat_publication_intro
    (schemaContract acceptedSchemaEvidence checkedModel originalModel :
      Prop) :
    schemaContract -> acceptedSchemaEvidence -> checkedModel ->
    originalModel ->
    ay_rjsg_sat_publication schemaContract acceptedSchemaEvidence
      checkedModel originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_rjsg_conj_intro schemaContract
      (ay_rjsg_conj acceptedSchemaEvidence
        (ay_rjsg_conj checkedModel originalModel))
      contractProof
      (ay_rjsg_conj_intro acceptedSchemaEvidence
        (ay_rjsg_conj checkedModel originalModel)
        acceptedProof
        (ay_rjsg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_rjsg_sat_publication_schema
    (schemaContract acceptedSchemaEvidence checkedModel originalModel :
      Prop) :
    ay_rjsg_sat_publication schemaContract acceptedSchemaEvidence
      checkedModel originalModel ->
    schemaContract :=
  fun publication =>
    ay_rjsg_conj_left schemaContract
      (ay_rjsg_conj acceptedSchemaEvidence
        (ay_rjsg_conj checkedModel originalModel))
      publication

theorem ay_rjsg_sat_publication_original_model
    (schemaContract acceptedSchemaEvidence checkedModel originalModel :
      Prop) :
    ay_rjsg_sat_publication schemaContract acceptedSchemaEvidence
      checkedModel originalModel ->
    originalModel :=
  fun publication =>
    ay_rjsg_conj_right checkedModel originalModel
      (ay_rjsg_conj_right acceptedSchemaEvidence
        (ay_rjsg_conj checkedModel originalModel)
        (ay_rjsg_conj_right schemaContract
          (ay_rjsg_conj acceptedSchemaEvidence
            (ay_rjsg_conj checkedModel originalModel))
          publication))

theorem ay_rjsg_unsat_publication_intro
    (schemaContract acceptedSchemaEvidence checkedProof originalEmptyClause :
      Prop) :
    schemaContract -> acceptedSchemaEvidence -> checkedProof ->
    originalEmptyClause ->
    ay_rjsg_unsat_publication schemaContract acceptedSchemaEvidence
      checkedProof originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_rjsg_conj_intro schemaContract
      (ay_rjsg_conj acceptedSchemaEvidence
        (ay_rjsg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_rjsg_conj_intro acceptedSchemaEvidence
        (ay_rjsg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_rjsg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_rjsg_unsat_publication_schema
    (schemaContract acceptedSchemaEvidence checkedProof originalEmptyClause :
      Prop) :
    ay_rjsg_unsat_publication schemaContract acceptedSchemaEvidence
      checkedProof originalEmptyClause ->
    schemaContract :=
  fun publication =>
    ay_rjsg_conj_left schemaContract
      (ay_rjsg_conj acceptedSchemaEvidence
        (ay_rjsg_conj checkedProof originalEmptyClause))
      publication

theorem ay_rjsg_unsat_publication_original_empty_clause
    (schemaContract acceptedSchemaEvidence checkedProof originalEmptyClause :
      Prop) :
    ay_rjsg_unsat_publication schemaContract acceptedSchemaEvidence
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_rjsg_conj_right checkedProof originalEmptyClause
      (ay_rjsg_conj_right acceptedSchemaEvidence
        (ay_rjsg_conj checkedProof originalEmptyClause)
        (ay_rjsg_conj_right schemaContract
          (ay_rjsg_conj acceptedSchemaEvidence
            (ay_rjsg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_rjsg_accepted_schema_sat_passes_publication
    (schemaContract acceptedSchemaEvidence checkedModel originalModel :
      Prop) :
    ay_rjsg_sat_publication schemaContract acceptedSchemaEvidence
      checkedModel originalModel ->
    ay_rjsg_public_result originalModel False False :=
  fun publication =>
    ay_rjsg_disj_left originalModel (ay_rjsg_disj False False)
      (ay_rjsg_sat_publication_original_model schemaContract
        acceptedSchemaEvidence checkedModel originalModel publication)

theorem ay_rjsg_accepted_schema_unsat_passes_publication
    (schemaContract acceptedSchemaEvidence checkedProof originalEmptyClause :
      Prop) :
    ay_rjsg_unsat_publication schemaContract acceptedSchemaEvidence
      checkedProof originalEmptyClause ->
    ay_rjsg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_rjsg_disj_right False (ay_rjsg_disj originalEmptyClause False)
      (ay_rjsg_disj_left originalEmptyClause False
        (ay_rjsg_unsat_publication_original_empty_clause schemaContract
          acceptedSchemaEvidence checkedProof originalEmptyClause
          publication))

theorem ay_rjsg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_rjsg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_rjsg_conj_intro reason (ay_rjsg_conj fallbackPath auditTrail)
      reasonProof
      (ay_rjsg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_rjsg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_rjsg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_rjsg_conj_intro reason
      (ay_rjsg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_rjsg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_rjsg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_rjsg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_rjsg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_rjsg_conj_right reason
        (ay_rjsg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rjsg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_rjsg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_rjsg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_rjsg_conj_right reason
        (ay_rjsg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rjsg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_rjsg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_rjsg_conj_intro reason
      (ay_rjsg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_rjsg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_rjsg_schema_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rjsg_blocked_publication satFact unsatFact reason ->
    ay_rjsg_recompute reason fallbackPath recomputeObligation ->
    ay_rjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_rjsg_conj_intro
      (ay_rjsg_blocked_publication satFact unsatFact reason)
      (ay_rjsg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_rjsg_schema_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_rjsg_blocked_publication_no_sat satFact unsatFact reason
      (ay_rjsg_conj_left
        (ay_rjsg_blocked_publication satFact unsatFact reason)
        (ay_rjsg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rjsg_schema_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_rjsg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_rjsg_conj_left
        (ay_rjsg_blocked_publication satFact unsatFact reason)
        (ay_rjsg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rjsg_schema_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_rjsg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_rjsg_conj_right
      (ay_rjsg_blocked_publication satFact unsatFact reason)
      (ay_rjsg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_rjsg_malformed_json_forces_no_claim
    (satFact unsatFact malformedJson fallbackPath auditTrail
      recomputeObligation : Prop) :
    malformedJson -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rjsg_no_claim malformedJson fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rjsg_no_claim_intro malformedJson fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rjsg_unknown_schema_forces_recompute
    (satFact unsatFact unknownSchema fallbackPath recomputeObligation :
      Prop) :
    unknownSchema -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_rjsg_schema_failure satFact unsatFact unknownSchema fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_rjsg_schema_failure_intro satFact unsatFact unknownSchema
      fallbackPath recomputeObligation
      (ay_rjsg_blocked_publication_intro satFact unsatFact unknownSchema
        reasonProof noSat noUnsat)
      (ay_rjsg_recompute_intro unknownSchema fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_rjsg_missing_status_field_forces_no_claim
    (satFact unsatFact missingStatusField fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingStatusField -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rjsg_no_claim missingStatusField fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rjsg_no_claim_intro missingStatusField fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rjsg_missing_certificate_field_forces_no_claim
    (satFact unsatFact missingCertificateField fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingCertificateField -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rjsg_no_claim missingCertificateField fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rjsg_no_claim_intro missingCertificateField fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rjsg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rjsg_no_claim checkerMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rjsg_no_claim_intro checkerMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rjsg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rjsg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rjsg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rjsg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rjsg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rjsg_no_claim_intro buildMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rjsg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rjsg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rjsg_no_claim_intro archiveMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rjsg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivation fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivation -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_rjsg_no_claim fallbackActivation fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_rjsg_no_claim_intro fallbackActivation fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_rjsg_failed_schema_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_rjsg_schema_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_rjsg_failed_schema_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rjsg_schema_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_rjsg_schema_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_rjsg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_rjsg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_rjsg_conj_left reason (ay_rjsg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_rjsg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_rjsg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_rjsg_conj_left reason (ay_rjsg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
