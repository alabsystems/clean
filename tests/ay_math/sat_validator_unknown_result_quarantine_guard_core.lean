-- SAT-COMP validator UNKNOWN/no-result quarantine guard core.
--
-- UNKNOWN and no-result classifications quarantine partial artifacts and make
-- no public SAT/UNSAT claim unless separate checker-backed evidence exists.

def ay_urqg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_urqg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_urqg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_urqg_disj satFact (ay_urqg_disj unsatFact noClaimFact)

def ay_urqg_quarantine_contract
    (unknownResultClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (unknownResultClassificationDigest -> transcriptDigest ->
      partialArtifactQuarantineLedger -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_urqg_checked_sat_publication
    (quarantineContract separateCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_urqg_conj quarantineContract
    (ay_urqg_conj separateCheckerEvidence
      (ay_urqg_conj checkedModel originalBenchmarkSat))

def ay_urqg_checked_unsat_publication
    (quarantineContract separateCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_urqg_conj quarantineContract
    (ay_urqg_conj separateCheckerEvidence
      (ay_urqg_conj checkedProof originalBenchmarkUnsat))

def ay_urqg_no_claim
    (classificationReason fallbackPath auditTrail : Prop) : Prop :=
  ay_urqg_conj classificationReason
    (ay_urqg_conj fallbackPath auditTrail)

def ay_urqg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_urqg_conj reason
    (ay_urqg_conj (satFact -> False) (unsatFact -> False))

def ay_urqg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_urqg_conj reason
    (ay_urqg_conj fallbackPath recomputeObligation)

def ay_urqg_quarantine_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_urqg_conj
    (ay_urqg_blocked_publication satFact unsatFact reason)
    (ay_urqg_recompute reason fallbackPath recomputeObligation)

theorem ay_urqg_conj_intro (left right : Prop) :
    left -> right -> ay_urqg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_urqg_conj_left (left right : Prop) :
    ay_urqg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_urqg_conj_right (left right : Prop) :
    ay_urqg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_urqg_disj_left (left right : Prop) :
    left -> ay_urqg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_urqg_disj_right (left right : Prop) :
    right -> ay_urqg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_urqg_quarantine_contract_intro
    (unknownResultClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    unknownResultClassificationDigest -> transcriptDigest ->
    partialArtifactQuarantineLedger -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_urqg_quarantine_contract unknownResultClassificationDigest
      transcriptDigest partialArtifactQuarantineLedger benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript :=
  fun classificationProof transcriptProof quarantineProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof result build =>
    build classificationProof transcriptProof quarantineProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof

theorem ay_urqg_contract_unknown_classification
    (unknownResultClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_urqg_quarantine_contract unknownResultClassificationDigest
      transcriptDigest partialArtifactQuarantineLedger benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    unknownResultClassificationDigest :=
  fun contract =>
    contract unknownResultClassificationDigest
      (fun classificationProof _transcriptProof _quarantineProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => classificationProof)

theorem ay_urqg_contract_transcript
    (unknownResultClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_urqg_quarantine_contract unknownResultClassificationDigest
      transcriptDigest partialArtifactQuarantineLedger benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    transcriptDigest :=
  fun contract =>
    contract transcriptDigest
      (fun _classificationProof transcriptProof _quarantineProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => transcriptProof)

theorem ay_urqg_contract_quarantine
    (unknownResultClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_urqg_quarantine_contract unknownResultClassificationDigest
      transcriptDigest partialArtifactQuarantineLedger benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    partialArtifactQuarantineLedger :=
  fun contract =>
    contract partialArtifactQuarantineLedger
      (fun _classificationProof _transcriptProof quarantineProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => quarantineProof)

theorem ay_urqg_contract_fingerprint
    (unknownResultClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_urqg_quarantine_contract unknownResultClassificationDigest
      transcriptDigest partialArtifactQuarantineLedger benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _classificationProof _transcriptProof _quarantineProof
          fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_urqg_contract_build
    (unknownResultClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_urqg_quarantine_contract unknownResultClassificationDigest
      transcriptDigest partialArtifactQuarantineLedger benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _classificationProof _transcriptProof _quarantineProof
          _fingerprintProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_urqg_contract_archive
    (unknownResultClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_urqg_quarantine_contract unknownResultClassificationDigest
      transcriptDigest partialArtifactQuarantineLedger benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _classificationProof _transcriptProof _quarantineProof
          _fingerprintProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_urqg_contract_fallback
    (unknownResultClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_urqg_quarantine_contract unknownResultClassificationDigest
      transcriptDigest partialArtifactQuarantineLedger benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _classificationProof _transcriptProof _quarantineProof
          _fingerprintProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_urqg_contract_audit
    (unknownResultClassificationDigest transcriptDigest
      partialArtifactQuarantineLedger benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_urqg_quarantine_contract unknownResultClassificationDigest
      transcriptDigest partialArtifactQuarantineLedger benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _classificationProof _transcriptProof _quarantineProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_urqg_checked_sat_publication_intro
    (quarantineContract separateCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) :
    quarantineContract -> separateCheckerEvidence -> checkedModel ->
    originalBenchmarkSat ->
    ay_urqg_checked_sat_publication quarantineContract
      separateCheckerEvidence checkedModel originalBenchmarkSat :=
  fun hcontract hchecker hchecked horiginal =>
    ay_urqg_conj_intro quarantineContract
      (ay_urqg_conj separateCheckerEvidence
        (ay_urqg_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_urqg_conj_intro separateCheckerEvidence
        (ay_urqg_conj checkedModel originalBenchmarkSat)
        hchecker
        (ay_urqg_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_urqg_checked_unsat_publication_intro
    (quarantineContract separateCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    quarantineContract -> separateCheckerEvidence -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_urqg_checked_unsat_publication quarantineContract
      separateCheckerEvidence checkedProof originalBenchmarkUnsat :=
  fun hcontract hchecker hchecked horiginal =>
    ay_urqg_conj_intro quarantineContract
      (ay_urqg_conj separateCheckerEvidence
        (ay_urqg_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_urqg_conj_intro separateCheckerEvidence
        (ay_urqg_conj checkedProof originalBenchmarkUnsat)
        hchecker
        (ay_urqg_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_urqg_checked_sat_publication_original_claim
    (quarantineContract separateCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_urqg_checked_sat_publication quarantineContract
      separateCheckerEvidence checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_urqg_conj_right checkedModel originalBenchmarkSat
      (ay_urqg_conj_right separateCheckerEvidence
        (ay_urqg_conj checkedModel originalBenchmarkSat)
        (ay_urqg_conj_right quarantineContract
          (ay_urqg_conj separateCheckerEvidence
            (ay_urqg_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_urqg_checked_unsat_publication_original_claim
    (quarantineContract separateCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_urqg_checked_unsat_publication quarantineContract
      separateCheckerEvidence checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_urqg_conj_right checkedProof originalBenchmarkUnsat
      (ay_urqg_conj_right separateCheckerEvidence
        (ay_urqg_conj checkedProof originalBenchmarkUnsat)
        (ay_urqg_conj_right quarantineContract
          (ay_urqg_conj separateCheckerEvidence
            (ay_urqg_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_urqg_only_checked_sat_evidence_may_publish
    (quarantineContract separateCheckerEvidence checkedModel
      originalBenchmarkSat : Prop) :
    ay_urqg_checked_sat_publication quarantineContract separateCheckerEvidence
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_urqg_checked_sat_publication_original_claim quarantineContract
    separateCheckerEvidence checkedModel originalBenchmarkSat

theorem ay_urqg_only_checked_unsat_evidence_may_publish
    (quarantineContract separateCheckerEvidence checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_urqg_checked_unsat_publication quarantineContract
      separateCheckerEvidence checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_urqg_checked_unsat_publication_original_claim quarantineContract
    separateCheckerEvidence checkedProof originalBenchmarkUnsat

theorem ay_urqg_no_claim_intro
    (classificationReason fallbackPath auditTrail : Prop) :
    classificationReason -> fallbackPath -> auditTrail ->
    ay_urqg_no_claim classificationReason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_urqg_conj_intro classificationReason
      (ay_urqg_conj fallbackPath auditTrail)
      hreason
      (ay_urqg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_urqg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_urqg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_urqg_conj_intro reason
      (ay_urqg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_urqg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_urqg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_urqg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_urqg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_urqg_conj_right reason
        (ay_urqg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_urqg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_urqg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_urqg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_urqg_conj_right reason
        (ay_urqg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_urqg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_urqg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_urqg_conj_intro reason
      (ay_urqg_conj fallbackPath recomputeObligation)
      hreason
      (ay_urqg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_urqg_quarantine_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_urqg_blocked_publication satFact unsatFact reason ->
    ay_urqg_recompute reason fallbackPath recomputeObligation ->
    ay_urqg_quarantine_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_urqg_conj_intro
      (ay_urqg_blocked_publication satFact unsatFact reason)
      (ay_urqg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_urqg_quarantine_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_urqg_quarantine_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_urqg_blocked_publication_no_sat satFact unsatFact reason
      (ay_urqg_conj_left
        (ay_urqg_blocked_publication satFact unsatFact reason)
        (ay_urqg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_urqg_quarantine_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_urqg_quarantine_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_urqg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_urqg_conj_left
        (ay_urqg_blocked_publication satFact unsatFact reason)
        (ay_urqg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_urqg_unknown_classification_no_sat
    (satFact unsatFact unknownClassification : Prop) :
    ay_urqg_blocked_publication satFact unsatFact unknownClassification ->
    satFact -> False :=
  ay_urqg_blocked_publication_no_sat satFact unsatFact unknownClassification

theorem ay_urqg_unknown_classification_no_unsat
    (satFact unsatFact unknownClassification : Prop) :
    ay_urqg_blocked_publication satFact unsatFact unknownClassification ->
    unsatFact -> False :=
  ay_urqg_blocked_publication_no_unsat satFact unsatFact unknownClassification

theorem ay_urqg_no_result_classification_forces_no_claim
    (noResultClassification fallbackPath auditTrail : Prop) :
    noResultClassification -> fallbackPath -> auditTrail ->
    ay_urqg_no_claim noResultClassification fallbackPath auditTrail :=
  ay_urqg_no_claim_intro noResultClassification fallbackPath auditTrail

theorem ay_urqg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_urqg_no_claim reason fallbackPath auditTrail :=
  ay_urqg_no_claim_intro reason fallbackPath auditTrail

theorem ay_urqg_classification_mismatch_forces_no_claim
    (classificationMismatch fallbackPath auditTrail : Prop) :
    classificationMismatch -> fallbackPath -> auditTrail ->
    ay_urqg_no_claim classificationMismatch fallbackPath auditTrail :=
  ay_urqg_mismatch_forces_no_claim classificationMismatch fallbackPath
    auditTrail

theorem ay_urqg_transcript_mismatch_forces_no_claim
    (transcriptMismatch fallbackPath auditTrail : Prop) :
    transcriptMismatch -> fallbackPath -> auditTrail ->
    ay_urqg_no_claim transcriptMismatch fallbackPath auditTrail :=
  ay_urqg_mismatch_forces_no_claim transcriptMismatch fallbackPath auditTrail

theorem ay_urqg_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_urqg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_urqg_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_urqg_quarantine_mismatch_forces_no_claim
    (quarantineMismatch fallbackPath auditTrail : Prop) :
    quarantineMismatch -> fallbackPath -> auditTrail ->
    ay_urqg_no_claim quarantineMismatch fallbackPath auditTrail :=
  ay_urqg_mismatch_forces_no_claim quarantineMismatch fallbackPath auditTrail

theorem ay_urqg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_urqg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_urqg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_urqg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_urqg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_urqg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_urqg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_urqg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_urqg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_urqg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_urqg_quarantine_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_urqg_quarantine_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_urqg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_urqg_quarantine_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_urqg_quarantine_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation
