-- SAT-COMP validator artifact timestamp independence core.
--
-- Artifact timestamps, filesystem mtimes, and cache arrival order are metadata.
-- They cannot justify SAT/UNSAT publication unless tied to replayed content
-- digests, solver build evidence, original formula fingerprint, and checker
-- transcript.

def ay_vati_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vati_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vati_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vati_disj satFact (ay_vati_disj unsatFact noClaimFact)

def ay_vati_content_evidence
    (contentDigest solverBuildEvidence originalFormulaFingerprint
      checkerTranscript : Prop) : Prop :=
  ay_vati_conj contentDigest
    (ay_vati_conj solverBuildEvidence
      (ay_vati_conj originalFormulaFingerprint checkerTranscript))

def ay_vati_metadata
    (artifactTimestamp filesystemMtime cacheArrivalOrder : Prop) : Prop :=
  ay_vati_conj artifactTimestamp
    (ay_vati_conj filesystemMtime cacheArrivalOrder)

def ay_vati_sat_claim
    (contentEvidence modelEvidence originalModel : Prop) : Prop :=
  ay_vati_conj contentEvidence
    (ay_vati_conj modelEvidence originalModel)

def ay_vati_unsat_claim
    (contentEvidence proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vati_conj contentEvidence
    (ay_vati_conj proofEvidence originalEmptyClause)

def ay_vati_no_claim
    (reason auditTrail diagnostic : Prop) : Prop :=
  ay_vati_conj reason (ay_vati_conj auditTrail diagnostic)

def ay_vati_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vati_conj reason
    (ay_vati_conj (satFact -> False) (unsatFact -> False))

def ay_vati_recompute
    (reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vati_conj reason (ay_vati_conj auditTrail fallbackPath)

def ay_vati_metadata_failure
    (satFact unsatFact reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vati_conj
    (ay_vati_blocked_publication satFact unsatFact reason)
    (ay_vati_recompute reason auditTrail fallbackPath)

theorem ay_vati_conj_intro (left right : Prop) :
    left -> right -> ay_vati_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vati_conj_left (left right : Prop) :
    ay_vati_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vati_conj_right (left right : Prop) :
    ay_vati_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vati_disj_left (left right : Prop) :
    left -> ay_vati_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vati_disj_right (left right : Prop) :
    right -> ay_vati_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vati_content_evidence_intro
    (contentDigest solverBuildEvidence originalFormulaFingerprint
      checkerTranscript : Prop) :
    contentDigest -> solverBuildEvidence -> originalFormulaFingerprint ->
    checkerTranscript ->
    ay_vati_content_evidence contentDigest solverBuildEvidence
      originalFormulaFingerprint checkerTranscript :=
  fun digestProof buildProof fingerprintProof transcriptProof =>
    ay_vati_conj_intro contentDigest
      (ay_vati_conj solverBuildEvidence
        (ay_vati_conj originalFormulaFingerprint checkerTranscript))
      digestProof
      (ay_vati_conj_intro solverBuildEvidence
        (ay_vati_conj originalFormulaFingerprint checkerTranscript)
        buildProof
        (ay_vati_conj_intro originalFormulaFingerprint checkerTranscript
          fingerprintProof transcriptProof))

theorem ay_vati_content_evidence_digest
    (contentDigest solverBuildEvidence originalFormulaFingerprint
      checkerTranscript : Prop) :
    ay_vati_content_evidence contentDigest solverBuildEvidence
      originalFormulaFingerprint checkerTranscript ->
    contentDigest :=
  fun evidence =>
    ay_vati_conj_left contentDigest
      (ay_vati_conj solverBuildEvidence
        (ay_vati_conj originalFormulaFingerprint checkerTranscript))
      evidence

theorem ay_vati_content_evidence_build
    (contentDigest solverBuildEvidence originalFormulaFingerprint
      checkerTranscript : Prop) :
    ay_vati_content_evidence contentDigest solverBuildEvidence
      originalFormulaFingerprint checkerTranscript ->
    solverBuildEvidence :=
  fun evidence =>
    ay_vati_conj_right contentDigest
      (ay_vati_conj solverBuildEvidence
        (ay_vati_conj originalFormulaFingerprint checkerTranscript))
      evidence solverBuildEvidence
      (fun buildProof _tail => buildProof)

theorem ay_vati_content_evidence_fingerprint
    (contentDigest solverBuildEvidence originalFormulaFingerprint
      checkerTranscript : Prop) :
    ay_vati_content_evidence contentDigest solverBuildEvidence
      originalFormulaFingerprint checkerTranscript ->
    originalFormulaFingerprint :=
  fun evidence =>
    ay_vati_conj_right contentDigest
      (ay_vati_conj solverBuildEvidence
        (ay_vati_conj originalFormulaFingerprint checkerTranscript))
      evidence originalFormulaFingerprint
      (fun _buildProof tail =>
        tail originalFormulaFingerprint
          (fun fingerprintProof _transcriptProof => fingerprintProof))

theorem ay_vati_content_evidence_transcript
    (contentDigest solverBuildEvidence originalFormulaFingerprint
      checkerTranscript : Prop) :
    ay_vati_content_evidence contentDigest solverBuildEvidence
      originalFormulaFingerprint checkerTranscript ->
    checkerTranscript :=
  fun evidence =>
    ay_vati_conj_right contentDigest
      (ay_vati_conj solverBuildEvidence
        (ay_vati_conj originalFormulaFingerprint checkerTranscript))
      evidence checkerTranscript
      (fun _buildProof tail =>
        tail checkerTranscript
          (fun _fingerprintProof transcriptProof => transcriptProof))

theorem ay_vati_metadata_intro
    (artifactTimestamp filesystemMtime cacheArrivalOrder : Prop) :
    artifactTimestamp -> filesystemMtime -> cacheArrivalOrder ->
    ay_vati_metadata artifactTimestamp filesystemMtime cacheArrivalOrder :=
  fun timestampProof mtimeProof arrivalProof =>
    ay_vati_conj_intro artifactTimestamp
      (ay_vati_conj filesystemMtime cacheArrivalOrder)
      timestampProof
      (ay_vati_conj_intro filesystemMtime cacheArrivalOrder mtimeProof
        arrivalProof)

theorem ay_vati_metadata_has_no_sat_power
    (artifactTimestamp filesystemMtime cacheArrivalOrder satFact : Prop) :
    ay_vati_metadata artifactTimestamp filesystemMtime cacheArrivalOrder ->
    (satFact -> False) ->
    satFact -> False :=
  fun _metadata blockSat satProof => blockSat satProof

theorem ay_vati_metadata_has_no_unsat_power
    (artifactTimestamp filesystemMtime cacheArrivalOrder unsatFact : Prop) :
    ay_vati_metadata artifactTimestamp filesystemMtime cacheArrivalOrder ->
    (unsatFact -> False) ->
    unsatFact -> False :=
  fun _metadata blockUnsat unsatProof => blockUnsat unsatProof

theorem ay_vati_sat_claim_intro
    (contentEvidence modelEvidence originalModel : Prop) :
    contentEvidence -> modelEvidence -> originalModel ->
    ay_vati_sat_claim contentEvidence modelEvidence originalModel :=
  fun contentProof modelProof originalProof =>
    ay_vati_conj_intro contentEvidence
      (ay_vati_conj modelEvidence originalModel)
      contentProof
      (ay_vati_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vati_sat_claim_content
    (contentEvidence modelEvidence originalModel : Prop) :
    ay_vati_sat_claim contentEvidence modelEvidence originalModel ->
    contentEvidence :=
  fun claim =>
    ay_vati_conj_left contentEvidence
      (ay_vati_conj modelEvidence originalModel) claim

theorem ay_vati_sat_claim_original_model
    (contentEvidence modelEvidence originalModel : Prop) :
    ay_vati_sat_claim contentEvidence modelEvidence originalModel ->
    originalModel :=
  fun claim =>
    ay_vati_conj_right contentEvidence
      (ay_vati_conj modelEvidence originalModel)
      claim originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vati_unsat_claim_intro
    (contentEvidence proofEvidence originalEmptyClause : Prop) :
    contentEvidence -> proofEvidence -> originalEmptyClause ->
    ay_vati_unsat_claim contentEvidence proofEvidence originalEmptyClause :=
  fun contentProof proofProof emptyProof =>
    ay_vati_conj_intro contentEvidence
      (ay_vati_conj proofEvidence originalEmptyClause)
      contentProof
      (ay_vati_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vati_unsat_claim_content
    (contentEvidence proofEvidence originalEmptyClause : Prop) :
    ay_vati_unsat_claim contentEvidence proofEvidence originalEmptyClause ->
    contentEvidence :=
  fun claim =>
    ay_vati_conj_left contentEvidence
      (ay_vati_conj proofEvidence originalEmptyClause) claim

theorem ay_vati_unsat_claim_original_empty_clause
    (contentEvidence proofEvidence originalEmptyClause : Prop) :
    ay_vati_unsat_claim contentEvidence proofEvidence originalEmptyClause ->
    originalEmptyClause :=
  fun claim =>
    ay_vati_conj_right contentEvidence
      (ay_vati_conj proofEvidence originalEmptyClause)
      claim originalEmptyClause
      (fun _proofEvidence emptyProof => emptyProof)

theorem ay_vati_accepted_sat_content_preserves_public_soundness
    (contentEvidence modelEvidence originalModel unsatFact noClaimFact :
      Prop) :
    ay_vati_sat_claim contentEvidence modelEvidence originalModel ->
    ay_vati_public_result originalModel unsatFact noClaimFact :=
  fun claim =>
    ay_vati_disj_left originalModel
      (ay_vati_disj unsatFact noClaimFact)
      (ay_vati_sat_claim_original_model contentEvidence modelEvidence
        originalModel claim)

theorem ay_vati_accepted_unsat_content_preserves_public_soundness
    (satFact contentEvidence proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_vati_unsat_claim contentEvidence proofEvidence originalEmptyClause ->
    ay_vati_public_result satFact originalEmptyClause noClaimFact :=
  fun claim =>
    ay_vati_disj_right satFact
      (ay_vati_disj originalEmptyClause noClaimFact)
      (ay_vati_disj_left originalEmptyClause noClaimFact
        (ay_vati_unsat_claim_original_empty_clause contentEvidence
          proofEvidence originalEmptyClause claim))

theorem ay_vati_no_claim_intro
    (reason auditTrail diagnostic : Prop) :
    reason -> auditTrail -> diagnostic ->
    ay_vati_no_claim reason auditTrail diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vati_conj_intro reason
      (ay_vati_conj auditTrail diagnostic)
      reasonProof
      (ay_vati_conj_intro auditTrail diagnostic auditProof diagnosticProof)

theorem ay_vati_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vati_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vati_conj_intro reason
      (ay_vati_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vati_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vati_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vati_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vati_conj_right reason
      (ay_vati_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vati_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vati_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vati_conj_right reason
      (ay_vati_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vati_recompute_intro
    (reason auditTrail fallbackPath : Prop) :
    reason -> auditTrail -> fallbackPath ->
    ay_vati_recompute reason auditTrail fallbackPath :=
  fun reasonProof auditProof pathProof =>
    ay_vati_conj_intro reason
      (ay_vati_conj auditTrail fallbackPath)
      reasonProof
      (ay_vati_conj_intro auditTrail fallbackPath auditProof pathProof)

theorem ay_vati_metadata_failure_intro
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vati_blocked_publication satFact unsatFact reason ->
    ay_vati_recompute reason auditTrail fallbackPath ->
    ay_vati_metadata_failure satFact unsatFact reason auditTrail
      fallbackPath :=
  fun blocked recompute =>
    ay_vati_conj_intro
      (ay_vati_blocked_publication satFact unsatFact reason)
      (ay_vati_recompute reason auditTrail fallbackPath)
      blocked recompute

theorem ay_vati_metadata_failure_blocks_sat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vati_metadata_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vati_blocked_publication_no_sat satFact unsatFact reason
      (ay_vati_conj_left
        (ay_vati_blocked_publication satFact unsatFact reason)
        (ay_vati_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vati_metadata_failure_blocks_unsat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vati_metadata_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vati_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vati_conj_left
        (ay_vati_blocked_publication satFact unsatFact reason)
        (ay_vati_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vati_metadata_failure_recompute
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vati_metadata_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    ay_vati_recompute reason auditTrail fallbackPath :=
  fun failure =>
    ay_vati_conj_right
      (ay_vati_blocked_publication satFact unsatFact reason)
      (ay_vati_recompute reason auditTrail fallbackPath)
      failure

theorem ay_vati_timestamp_drift_forces_no_claim
    (satFact unsatFact timestampDrift auditTrail fallbackPath : Prop) :
    timestampDrift -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vati_metadata_failure satFact unsatFact timestampDrift auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vati_metadata_failure_intro satFact unsatFact timestampDrift
      auditTrail fallbackPath
      (ay_vati_blocked_publication_intro satFact unsatFact timestampDrift
        reasonProof blockSat blockUnsat)
      (ay_vati_recompute_intro timestampDrift auditTrail fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vati_mtime_drift_forces_no_claim
    (satFact unsatFact mtimeDrift auditTrail fallbackPath : Prop) :
    mtimeDrift -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vati_metadata_failure satFact unsatFact mtimeDrift auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vati_metadata_failure_intro satFact unsatFact mtimeDrift auditTrail
      fallbackPath
      (ay_vati_blocked_publication_intro satFact unsatFact mtimeDrift
        reasonProof blockSat blockUnsat)
      (ay_vati_recompute_intro mtimeDrift auditTrail fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vati_arrival_order_drift_forces_no_claim
    (satFact unsatFact arrivalDrift auditTrail fallbackPath : Prop) :
    arrivalDrift -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vati_metadata_failure satFact unsatFact arrivalDrift auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vati_metadata_failure_intro satFact unsatFact arrivalDrift auditTrail
      fallbackPath
      (ay_vati_blocked_publication_intro satFact unsatFact arrivalDrift
        reasonProof blockSat blockUnsat)
      (ay_vati_recompute_intro arrivalDrift auditTrail fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vati_stale_metadata_cannot_bless_sat
    (satFact unsatFact staleMetadata auditTrail fallbackPath : Prop) :
    ay_vati_metadata_failure satFact unsatFact staleMetadata auditTrail
      fallbackPath ->
    satFact -> False :=
  ay_vati_metadata_failure_blocks_sat satFact unsatFact staleMetadata
    auditTrail fallbackPath

theorem ay_vati_stale_metadata_cannot_bless_unsat
    (satFact unsatFact staleMetadata auditTrail fallbackPath : Prop) :
    ay_vati_metadata_failure satFact unsatFact staleMetadata auditTrail
      fallbackPath ->
    unsatFact -> False :=
  ay_vati_metadata_failure_blocks_unsat satFact unsatFact staleMetadata
    auditTrail fallbackPath
