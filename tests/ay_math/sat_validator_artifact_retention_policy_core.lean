-- SAT-COMP validator artifact retention policy core.
--
-- Result artifacts may be pruned or retained for disk pressure only when
-- retained manifests, artifact digests, checker transcripts, formula
-- fingerprints, build configs, output-line evidence, and fallback diagnostics
-- agree.  Failed retention evidence yields no-claim/recompute only.

def ay_varp_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_varp_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_varp_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_varp_disj satFact (ay_varp_disj unsatFact noClaimFact)

def ay_varp_retention_contract
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy : Prop) : Prop :=
  forall result : Prop,
    (retainedManifests -> artifactDigests -> checkerTranscripts ->
      formulaFingerprints -> buildConfigs -> outputLineEvidence ->
      fallbackDiagnostics -> retentionPolicy -> result) ->
    result

def ay_varp_sat_publication
    (retentionContract modelEvidence originalModel : Prop) : Prop :=
  ay_varp_conj retentionContract
    (ay_varp_conj modelEvidence originalModel)

def ay_varp_unsat_publication
    (retentionContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_varp_conj retentionContract
    (ay_varp_conj proofEvidence originalEmptyClause)

def ay_varp_no_claim
    (reason fallbackDiagnostics auditTrail : Prop) : Prop :=
  ay_varp_conj reason (ay_varp_conj fallbackDiagnostics auditTrail)

def ay_varp_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_varp_conj reason
    (ay_varp_conj (satFact -> False) (unsatFact -> False))

def ay_varp_recompute
    (reason fallbackDiagnostics recomputeObligation : Prop) : Prop :=
  ay_varp_conj reason
    (ay_varp_conj fallbackDiagnostics recomputeObligation)

def ay_varp_retention_failure
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) : Prop :=
  ay_varp_conj
    (ay_varp_blocked_publication satFact unsatFact reason)
    (ay_varp_recompute reason fallbackDiagnostics recomputeObligation)

theorem ay_varp_conj_intro (left right : Prop) :
    left -> right -> ay_varp_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_varp_conj_left (left right : Prop) :
    ay_varp_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_varp_conj_right (left right : Prop) :
    ay_varp_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_varp_disj_left (left right : Prop) :
    left -> ay_varp_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_varp_disj_right (left right : Prop) :
    right -> ay_varp_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_varp_retention_contract_intro
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy : Prop) :
    retainedManifests -> artifactDigests -> checkerTranscripts ->
    formulaFingerprints -> buildConfigs -> outputLineEvidence ->
    fallbackDiagnostics -> retentionPolicy ->
    ay_varp_retention_contract retainedManifests artifactDigests
      checkerTranscripts formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy :=
  fun manifestProof digestProof transcriptProof fingerprintProof buildProof
      outputProof fallbackProof policyProof result build =>
    build manifestProof digestProof transcriptProof fingerprintProof buildProof
      outputProof fallbackProof policyProof

theorem ay_varp_retention_contract_manifests
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy : Prop) :
    ay_varp_retention_contract retainedManifests artifactDigests
      checkerTranscripts formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy ->
    retainedManifests :=
  fun contract =>
    contract retainedManifests
      (fun manifestProof _digestProof _transcriptProof _fingerprintProof
          _buildProof _outputProof _fallbackProof _policyProof =>
        manifestProof)

theorem ay_varp_retention_contract_artifact_digests
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy : Prop) :
    ay_varp_retention_contract retainedManifests artifactDigests
      checkerTranscripts formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy ->
    artifactDigests :=
  fun contract =>
    contract artifactDigests
      (fun _manifestProof digestProof _transcriptProof _fingerprintProof
          _buildProof _outputProof _fallbackProof _policyProof =>
        digestProof)

theorem ay_varp_retention_contract_transcripts
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy : Prop) :
    ay_varp_retention_contract retainedManifests artifactDigests
      checkerTranscripts formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _manifestProof _digestProof transcriptProof _fingerprintProof
          _buildProof _outputProof _fallbackProof _policyProof =>
        transcriptProof)

theorem ay_varp_retention_contract_formula_fingerprints
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy : Prop) :
    ay_varp_retention_contract retainedManifests artifactDigests
      checkerTranscripts formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy ->
    formulaFingerprints :=
  fun contract =>
    contract formulaFingerprints
      (fun _manifestProof _digestProof _transcriptProof fingerprintProof
          _buildProof _outputProof _fallbackProof _policyProof =>
        fingerprintProof)

theorem ay_varp_retention_contract_build_configs
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy : Prop) :
    ay_varp_retention_contract retainedManifests artifactDigests
      checkerTranscripts formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy ->
    buildConfigs :=
  fun contract =>
    contract buildConfigs
      (fun _manifestProof _digestProof _transcriptProof _fingerprintProof
          buildProof _outputProof _fallbackProof _policyProof =>
        buildProof)

theorem ay_varp_retention_contract_output_line
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy : Prop) :
    ay_varp_retention_contract retainedManifests artifactDigests
      checkerTranscripts formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy ->
    outputLineEvidence :=
  fun contract =>
    contract outputLineEvidence
      (fun _manifestProof _digestProof _transcriptProof _fingerprintProof
          _buildProof outputProof _fallbackProof _policyProof =>
        outputProof)

theorem ay_varp_retention_contract_fallback
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy : Prop) :
    ay_varp_retention_contract retainedManifests artifactDigests
      checkerTranscripts formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy ->
    fallbackDiagnostics :=
  fun contract =>
    contract fallbackDiagnostics
      (fun _manifestProof _digestProof _transcriptProof _fingerprintProof
          _buildProof _outputProof fallbackProof _policyProof =>
        fallbackProof)

theorem ay_varp_retention_contract_policy
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy : Prop) :
    ay_varp_retention_contract retainedManifests artifactDigests
      checkerTranscripts formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy ->
    retentionPolicy :=
  fun contract =>
    contract retentionPolicy
      (fun _manifestProof _digestProof _transcriptProof _fingerprintProof
          _buildProof _outputProof _fallbackProof policyProof =>
        policyProof)

theorem ay_varp_sat_publication_intro
    (retentionContract modelEvidence originalModel : Prop) :
    retentionContract -> modelEvidence -> originalModel ->
    ay_varp_sat_publication retentionContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_varp_conj_intro retentionContract
      (ay_varp_conj modelEvidence originalModel)
      contractProof
      (ay_varp_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_varp_sat_publication_original_model
    (retentionContract modelEvidence originalModel : Prop) :
    ay_varp_sat_publication retentionContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_varp_conj_right retentionContract
      (ay_varp_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_varp_unsat_publication_intro
    (retentionContract proofEvidence originalEmptyClause : Prop) :
    retentionContract -> proofEvidence -> originalEmptyClause ->
    ay_varp_unsat_publication retentionContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_varp_conj_intro retentionContract
      (ay_varp_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_varp_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_varp_unsat_publication_original_empty_clause
    (retentionContract proofEvidence originalEmptyClause : Prop) :
    ay_varp_unsat_publication retentionContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_varp_conj_right retentionContract
      (ay_varp_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_varp_accepted_retention_sat_sound
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy modelEvidence originalModel : Prop) :
    ay_varp_retention_contract retainedManifests artifactDigests
      checkerTranscripts formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_varp_accepted_retention_unsat_sound
    (retainedManifests artifactDigests checkerTranscripts
      formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy proofEvidence
      originalEmptyClause : Prop) :
    ay_varp_retention_contract retainedManifests artifactDigests
      checkerTranscripts formulaFingerprints buildConfigs outputLineEvidence
      fallbackDiagnostics retentionPolicy ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_varp_no_claim_intro
    (reason fallbackDiagnostics auditTrail : Prop) :
    reason -> fallbackDiagnostics -> auditTrail ->
    ay_varp_no_claim reason fallbackDiagnostics auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_varp_conj_intro reason
      (ay_varp_conj fallbackDiagnostics auditTrail)
      reasonProof
      (ay_varp_conj_intro fallbackDiagnostics auditTrail
        fallbackProof auditProof)

theorem ay_varp_no_claim_reason
    (reason fallbackDiagnostics auditTrail : Prop) :
    ay_varp_no_claim reason fallbackDiagnostics auditTrail -> reason :=
  fun noClaim =>
    ay_varp_conj_left reason
      (ay_varp_conj fallbackDiagnostics auditTrail)
      noClaim

theorem ay_varp_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_varp_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_varp_conj_intro reason
      (ay_varp_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_varp_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_varp_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_varp_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_varp_conj_right reason
      (ay_varp_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_varp_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_varp_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_varp_conj_right reason
      (ay_varp_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_varp_recompute_intro
    (reason fallbackDiagnostics recomputeObligation : Prop) :
    reason -> fallbackDiagnostics -> recomputeObligation ->
    ay_varp_recompute reason fallbackDiagnostics recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_varp_conj_intro reason
      (ay_varp_conj fallbackDiagnostics recomputeObligation)
      reasonProof
      (ay_varp_conj_intro fallbackDiagnostics recomputeObligation
        fallbackProof recomputeProof)

theorem ay_varp_retention_failure_intro
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_varp_retention_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_varp_conj_intro
      (ay_varp_blocked_publication satFact unsatFact reason)
      (ay_varp_recompute reason fallbackDiagnostics recomputeObligation)
      (ay_varp_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_varp_recompute_intro reason fallbackDiagnostics recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_varp_retention_failure_blocks_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_varp_retention_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_varp_blocked_publication_no_sat satFact unsatFact reason
      (ay_varp_conj_left
        (ay_varp_blocked_publication satFact unsatFact reason)
        (ay_varp_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_varp_retention_failure_blocks_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_varp_retention_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_varp_blocked_publication_no_unsat satFact unsatFact reason
      (ay_varp_conj_left
        (ay_varp_blocked_publication satFact unsatFact reason)
        (ay_varp_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_varp_retention_failure_recompute
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_varp_retention_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    ay_varp_recompute reason fallbackDiagnostics recomputeObligation :=
  fun failure =>
    ay_varp_conj_right
      (ay_varp_blocked_publication satFact unsatFact reason)
      (ay_varp_recompute reason fallbackDiagnostics recomputeObligation)
      failure

theorem ay_varp_over_pruning_forces_no_claim
    (satFact unsatFact overPruning fallbackDiagnostics
      recomputeObligation : Prop) :
    overPruning -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_varp_retention_failure satFact unsatFact overPruning
      fallbackDiagnostics recomputeObligation :=
  ay_varp_retention_failure_intro satFact unsatFact overPruning
    fallbackDiagnostics recomputeObligation

theorem ay_varp_missing_retained_artifact_forces_no_claim
    (satFact unsatFact missingRetainedArtifact fallbackDiagnostics
      recomputeObligation : Prop) :
    missingRetainedArtifact -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_varp_retention_failure satFact unsatFact missingRetainedArtifact
      fallbackDiagnostics recomputeObligation :=
  ay_varp_retention_failure_intro satFact unsatFact missingRetainedArtifact
    fallbackDiagnostics recomputeObligation

theorem ay_varp_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch fallbackDiagnostics
      recomputeObligation : Prop) :
    digestMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_varp_retention_failure satFact unsatFact digestMismatch
      fallbackDiagnostics recomputeObligation :=
  ay_varp_retention_failure_intro satFact unsatFact digestMismatch
    fallbackDiagnostics recomputeObligation

theorem ay_varp_stale_fingerprint_forces_no_claim
    (satFact unsatFact staleFingerprint fallbackDiagnostics
      recomputeObligation : Prop) :
    staleFingerprint -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_varp_retention_failure satFact unsatFact staleFingerprint
      fallbackDiagnostics recomputeObligation :=
  ay_varp_retention_failure_intro satFact unsatFact staleFingerprint
    fallbackDiagnostics recomputeObligation

theorem ay_varp_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackDiagnostics
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_varp_retention_failure satFact unsatFact missingTranscript
      fallbackDiagnostics recomputeObligation :=
  ay_varp_retention_failure_intro satFact unsatFact missingTranscript
    fallbackDiagnostics recomputeObligation

theorem ay_varp_failed_retention_cannot_bless_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_varp_retention_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  ay_varp_retention_failure_blocks_sat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation

theorem ay_varp_failed_retention_cannot_bless_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_varp_retention_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  ay_varp_retention_failure_blocks_unsat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation
