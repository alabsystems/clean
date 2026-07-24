-- SAT-COMP validator resource-limit classification guard core.
--
-- Timeout, memout, and other resource-limit classifications are no-claim
-- outcomes unless separate checker-backed SAT/UNSAT evidence is available.

def ay_rlim_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rlim_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_rlim_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_rlim_disj satFact (ay_rlim_disj unsatFact noClaimFact)

def ay_rlim_classification_contract
    (resourceLimitManifest exitClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (resourceLimitManifest -> exitClassificationDigest -> transcriptDigest ->
      partialArtifactQuarantineLedger -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_rlim_checked_sat_publication
    (classificationContract separateCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_rlim_conj classificationContract
    (ay_rlim_conj separateCheckerEvidence
      (ay_rlim_conj checkedModel originalBenchmarkSat))

def ay_rlim_checked_unsat_publication
    (classificationContract separateCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_rlim_conj classificationContract
    (ay_rlim_conj separateCheckerEvidence
      (ay_rlim_conj checkedProof originalBenchmarkUnsat))

def ay_rlim_no_claim
    (classificationReason fallbackPath auditTrail : Prop) : Prop :=
  ay_rlim_conj classificationReason
    (ay_rlim_conj fallbackPath auditTrail)

def ay_rlim_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_rlim_conj reason
    (ay_rlim_conj (satFact -> False) (unsatFact -> False))

def ay_rlim_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_rlim_conj reason
    (ay_rlim_conj fallbackPath recomputeObligation)

def ay_rlim_classification_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_rlim_conj
    (ay_rlim_blocked_publication satFact unsatFact reason)
    (ay_rlim_recompute reason fallbackPath recomputeObligation)

theorem ay_rlim_conj_intro (left right : Prop) :
    left -> right -> ay_rlim_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_rlim_conj_left (left right : Prop) :
    ay_rlim_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_rlim_conj_right (left right : Prop) :
    ay_rlim_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_rlim_disj_left (left right : Prop) :
    left -> ay_rlim_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_rlim_disj_right (left right : Prop) :
    right -> ay_rlim_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_rlim_classification_contract_intro
    (resourceLimitManifest exitClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    resourceLimitManifest -> exitClassificationDigest -> transcriptDigest ->
    partialArtifactQuarantineLedger -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_rlim_classification_contract resourceLimitManifest
      exitClassificationDigest transcriptDigest partialArtifactQuarantineLedger
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript :=
  fun resourceProof classificationProof transcriptProof quarantineProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof result
      build =>
    build resourceProof classificationProof transcriptProof quarantineProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof

theorem ay_rlim_contract_resource_limit
    (resourceLimitManifest exitClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlim_classification_contract resourceLimitManifest
      exitClassificationDigest transcriptDigest partialArtifactQuarantineLedger
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    resourceLimitManifest :=
  fun contract =>
    contract resourceLimitManifest
      (fun resourceProof _classificationProof _transcriptProof
          _quarantineProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => resourceProof)

theorem ay_rlim_contract_exit_classification
    (resourceLimitManifest exitClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlim_classification_contract resourceLimitManifest
      exitClassificationDigest transcriptDigest partialArtifactQuarantineLedger
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    exitClassificationDigest :=
  fun contract =>
    contract exitClassificationDigest
      (fun _resourceProof classificationProof _transcriptProof
          _quarantineProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => classificationProof)

theorem ay_rlim_contract_transcript
    (resourceLimitManifest exitClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlim_classification_contract resourceLimitManifest
      exitClassificationDigest transcriptDigest partialArtifactQuarantineLedger
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    transcriptDigest :=
  fun contract =>
    contract transcriptDigest
      (fun _resourceProof _classificationProof transcriptProof
          _quarantineProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => transcriptProof)

theorem ay_rlim_contract_quarantine
    (resourceLimitManifest exitClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlim_classification_contract resourceLimitManifest
      exitClassificationDigest transcriptDigest partialArtifactQuarantineLedger
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    partialArtifactQuarantineLedger :=
  fun contract =>
    contract partialArtifactQuarantineLedger
      (fun _resourceProof _classificationProof _transcriptProof
          quarantineProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => quarantineProof)

theorem ay_rlim_contract_fingerprint
    (resourceLimitManifest exitClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlim_classification_contract resourceLimitManifest
      exitClassificationDigest transcriptDigest partialArtifactQuarantineLedger
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _resourceProof _classificationProof _transcriptProof
          _quarantineProof fingerprintProof _buildProof _archiveProof
          _fallbackProof _auditProof => fingerprintProof)

theorem ay_rlim_contract_build
    (resourceLimitManifest exitClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlim_classification_contract resourceLimitManifest
      exitClassificationDigest transcriptDigest partialArtifactQuarantineLedger
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _resourceProof _classificationProof _transcriptProof
          _quarantineProof _fingerprintProof buildProof _archiveProof
          _fallbackProof _auditProof => buildProof)

theorem ay_rlim_contract_archive
    (resourceLimitManifest exitClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlim_classification_contract resourceLimitManifest
      exitClassificationDigest transcriptDigest partialArtifactQuarantineLedger
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _resourceProof _classificationProof _transcriptProof
          _quarantineProof _fingerprintProof _buildProof archiveProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_rlim_contract_fallback
    (resourceLimitManifest exitClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlim_classification_contract resourceLimitManifest
      exitClassificationDigest transcriptDigest partialArtifactQuarantineLedger
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _resourceProof _classificationProof _transcriptProof
          _quarantineProof _fingerprintProof _buildProof _archiveProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_rlim_contract_audit
    (resourceLimitManifest exitClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_rlim_classification_contract resourceLimitManifest
      exitClassificationDigest transcriptDigest partialArtifactQuarantineLedger
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _resourceProof _classificationProof _transcriptProof
          _quarantineProof _fingerprintProof _buildProof _archiveProof
          _fallbackProof auditProof => auditProof)

theorem ay_rlim_checked_sat_publication_intro
    (classificationContract separateCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) :
    classificationContract -> separateCheckerEvidence -> checkedModel ->
    originalBenchmarkSat ->
    ay_rlim_checked_sat_publication classificationContract
      separateCheckerEvidence checkedModel originalBenchmarkSat :=
  fun hcontract hchecker hchecked horiginal =>
    ay_rlim_conj_intro classificationContract
      (ay_rlim_conj separateCheckerEvidence
        (ay_rlim_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_rlim_conj_intro separateCheckerEvidence
        (ay_rlim_conj checkedModel originalBenchmarkSat)
        hchecker
        (ay_rlim_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_rlim_checked_unsat_publication_intro
    (classificationContract separateCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    classificationContract -> separateCheckerEvidence -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_rlim_checked_unsat_publication classificationContract
      separateCheckerEvidence checkedProof originalBenchmarkUnsat :=
  fun hcontract hchecker hchecked horiginal =>
    ay_rlim_conj_intro classificationContract
      (ay_rlim_conj separateCheckerEvidence
        (ay_rlim_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_rlim_conj_intro separateCheckerEvidence
        (ay_rlim_conj checkedProof originalBenchmarkUnsat)
        hchecker
        (ay_rlim_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_rlim_checked_sat_publication_original_claim
    (classificationContract separateCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_rlim_checked_sat_publication classificationContract
      separateCheckerEvidence checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_rlim_conj_right checkedModel originalBenchmarkSat
      (ay_rlim_conj_right separateCheckerEvidence
        (ay_rlim_conj checkedModel originalBenchmarkSat)
        (ay_rlim_conj_right classificationContract
          (ay_rlim_conj separateCheckerEvidence
            (ay_rlim_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_rlim_checked_unsat_publication_original_claim
    (classificationContract separateCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_rlim_checked_unsat_publication classificationContract
      separateCheckerEvidence checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_rlim_conj_right checkedProof originalBenchmarkUnsat
      (ay_rlim_conj_right separateCheckerEvidence
        (ay_rlim_conj checkedProof originalBenchmarkUnsat)
        (ay_rlim_conj_right classificationContract
          (ay_rlim_conj separateCheckerEvidence
            (ay_rlim_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_rlim_only_checked_sat_evidence_may_publish
    (classificationContract separateCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_rlim_checked_sat_publication classificationContract
      separateCheckerEvidence checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_rlim_checked_sat_publication_original_claim classificationContract
    separateCheckerEvidence checkedModel originalBenchmarkSat

theorem ay_rlim_only_checked_unsat_evidence_may_publish
    (classificationContract separateCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_rlim_checked_unsat_publication classificationContract
      separateCheckerEvidence checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_rlim_checked_unsat_publication_original_claim classificationContract
    separateCheckerEvidence checkedProof originalBenchmarkUnsat

theorem ay_rlim_no_claim_intro
    (classificationReason fallbackPath auditTrail : Prop) :
    classificationReason -> fallbackPath -> auditTrail ->
    ay_rlim_no_claim classificationReason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_rlim_conj_intro classificationReason
      (ay_rlim_conj fallbackPath auditTrail)
      hreason
      (ay_rlim_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_rlim_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_rlim_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_rlim_conj_intro reason
      (ay_rlim_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_rlim_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_rlim_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_rlim_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_rlim_conj_left (satFact -> False) (unsatFact -> False)
      (ay_rlim_conj_right reason
        (ay_rlim_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rlim_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_rlim_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_rlim_conj_right (satFact -> False) (unsatFact -> False)
      (ay_rlim_conj_right reason
        (ay_rlim_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_rlim_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_rlim_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_rlim_conj_intro reason
      (ay_rlim_conj fallbackPath recomputeObligation)
      hreason
      (ay_rlim_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_rlim_classification_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlim_blocked_publication satFact unsatFact reason ->
    ay_rlim_recompute reason fallbackPath recomputeObligation ->
    ay_rlim_classification_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_rlim_conj_intro
      (ay_rlim_blocked_publication satFact unsatFact reason)
      (ay_rlim_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_rlim_classification_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlim_classification_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_rlim_blocked_publication_no_sat satFact unsatFact reason
      (ay_rlim_conj_left
        (ay_rlim_blocked_publication satFact unsatFact reason)
        (ay_rlim_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rlim_classification_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlim_classification_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_rlim_blocked_publication_no_unsat satFact unsatFact reason
      (ay_rlim_conj_left
        (ay_rlim_blocked_publication satFact unsatFact reason)
        (ay_rlim_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_rlim_resource_limit_classification_no_sat
    (satFact unsatFact resourceLimitClassification : Prop) :
    ay_rlim_blocked_publication satFact unsatFact
      resourceLimitClassification ->
    satFact -> False :=
  ay_rlim_blocked_publication_no_sat satFact unsatFact
    resourceLimitClassification

theorem ay_rlim_resource_limit_classification_no_unsat
    (satFact unsatFact resourceLimitClassification : Prop) :
    ay_rlim_blocked_publication satFact unsatFact
      resourceLimitClassification ->
    unsatFact -> False :=
  ay_rlim_blocked_publication_no_unsat satFact unsatFact
    resourceLimitClassification

theorem ay_rlim_timeout_classification_forces_no_claim
    (timeoutClassification fallbackPath auditTrail : Prop) :
    timeoutClassification -> fallbackPath -> auditTrail ->
    ay_rlim_no_claim timeoutClassification fallbackPath auditTrail :=
  ay_rlim_no_claim_intro timeoutClassification fallbackPath auditTrail

theorem ay_rlim_memout_classification_forces_no_claim
    (memoutClassification fallbackPath auditTrail : Prop) :
    memoutClassification -> fallbackPath -> auditTrail ->
    ay_rlim_no_claim memoutClassification fallbackPath auditTrail :=
  ay_rlim_no_claim_intro memoutClassification fallbackPath auditTrail

theorem ay_rlim_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_rlim_no_claim reason fallbackPath auditTrail :=
  ay_rlim_no_claim_intro reason fallbackPath auditTrail

theorem ay_rlim_classification_mismatch_forces_no_claim
    (classificationMismatch fallbackPath auditTrail : Prop) :
    classificationMismatch -> fallbackPath -> auditTrail ->
    ay_rlim_no_claim classificationMismatch fallbackPath auditTrail :=
  ay_rlim_mismatch_forces_no_claim classificationMismatch fallbackPath
    auditTrail

theorem ay_rlim_transcript_mismatch_forces_no_claim
    (transcriptMismatch fallbackPath auditTrail : Prop) :
    transcriptMismatch -> fallbackPath -> auditTrail ->
    ay_rlim_no_claim transcriptMismatch fallbackPath auditTrail :=
  ay_rlim_mismatch_forces_no_claim transcriptMismatch fallbackPath auditTrail

theorem ay_rlim_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_rlim_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_rlim_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_rlim_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_rlim_no_claim buildMismatch fallbackPath auditTrail :=
  ay_rlim_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_rlim_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_rlim_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_rlim_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_rlim_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_rlim_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_rlim_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_rlim_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlim_classification_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_rlim_classification_failure_blocks_sat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_rlim_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_rlim_classification_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_rlim_classification_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation
