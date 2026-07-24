-- SAT-COMP validator run metadata reproducibility core.
--
-- Sequential-main public SAT/UNSAT claims may rely on run metadata only when
-- random seed, solver build ID, CLI flags, formula fingerprint, result
-- artifacts, checker transcripts, and output-line evidence agree.

def ay_vrmr_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrmr_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vrmr_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vrmr_disj satFact (ay_vrmr_disj unsatFact noClaimFact)

def ay_vrmr_metadata_contract
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics : Prop) :
    Prop :=
  forall result : Prop,
    (randomSeeds -> solverBuildIds -> cliFlags -> formulaFingerprints ->
      resultArtifacts -> checkerTranscripts -> outputLineEvidence ->
      fallbackDiagnostics -> result) ->
    result

def ay_vrmr_sat_publication
    (metadataContract modelEvidence originalModel : Prop) : Prop :=
  ay_vrmr_conj metadataContract
    (ay_vrmr_conj modelEvidence originalModel)

def ay_vrmr_unsat_publication
    (metadataContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vrmr_conj metadataContract
    (ay_vrmr_conj proofEvidence originalEmptyClause)

def ay_vrmr_no_claim
    (reason fallbackDiagnostics auditTrail : Prop) : Prop :=
  ay_vrmr_conj reason (ay_vrmr_conj fallbackDiagnostics auditTrail)

def ay_vrmr_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vrmr_conj reason
    (ay_vrmr_conj (satFact -> False) (unsatFact -> False))

def ay_vrmr_recompute
    (reason fallbackDiagnostics recomputeObligation : Prop) : Prop :=
  ay_vrmr_conj reason
    (ay_vrmr_conj fallbackDiagnostics recomputeObligation)

def ay_vrmr_metadata_failure
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) : Prop :=
  ay_vrmr_conj
    (ay_vrmr_blocked_publication satFact unsatFact reason)
    (ay_vrmr_recompute reason fallbackDiagnostics recomputeObligation)

theorem ay_vrmr_conj_intro (left right : Prop) :
    left -> right -> ay_vrmr_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrmr_conj_left (left right : Prop) :
    ay_vrmr_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrmr_conj_right (left right : Prop) :
    ay_vrmr_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrmr_disj_left (left right : Prop) :
    left -> ay_vrmr_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vrmr_disj_right (left right : Prop) :
    right -> ay_vrmr_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrmr_metadata_contract_intro
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics : Prop) :
    randomSeeds -> solverBuildIds -> cliFlags -> formulaFingerprints ->
    resultArtifacts -> checkerTranscripts -> outputLineEvidence ->
    fallbackDiagnostics ->
    ay_vrmr_metadata_contract randomSeeds solverBuildIds cliFlags
      formulaFingerprints resultArtifacts checkerTranscripts
      outputLineEvidence fallbackDiagnostics :=
  fun seedProof buildProof flagsProof fingerprintProof artifactProof
      transcriptProof outputProof fallbackProof result build =>
    build seedProof buildProof flagsProof fingerprintProof artifactProof
      transcriptProof outputProof fallbackProof

theorem ay_vrmr_metadata_contract_random_seeds
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics : Prop) :
    ay_vrmr_metadata_contract randomSeeds solverBuildIds cliFlags
      formulaFingerprints resultArtifacts checkerTranscripts
      outputLineEvidence fallbackDiagnostics ->
    randomSeeds :=
  fun contract =>
    contract randomSeeds
      (fun seedProof _buildProof _flagsProof _fingerprintProof
          _artifactProof _transcriptProof _outputProof _fallbackProof =>
        seedProof)

theorem ay_vrmr_metadata_contract_build_ids
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics : Prop) :
    ay_vrmr_metadata_contract randomSeeds solverBuildIds cliFlags
      formulaFingerprints resultArtifacts checkerTranscripts
      outputLineEvidence fallbackDiagnostics ->
    solverBuildIds :=
  fun contract =>
    contract solverBuildIds
      (fun _seedProof buildProof _flagsProof _fingerprintProof
          _artifactProof _transcriptProof _outputProof _fallbackProof =>
        buildProof)

theorem ay_vrmr_metadata_contract_cli_flags
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics : Prop) :
    ay_vrmr_metadata_contract randomSeeds solverBuildIds cliFlags
      formulaFingerprints resultArtifacts checkerTranscripts
      outputLineEvidence fallbackDiagnostics ->
    cliFlags :=
  fun contract =>
    contract cliFlags
      (fun _seedProof _buildProof flagsProof _fingerprintProof
          _artifactProof _transcriptProof _outputProof _fallbackProof =>
        flagsProof)

theorem ay_vrmr_metadata_contract_formula_fingerprints
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics : Prop) :
    ay_vrmr_metadata_contract randomSeeds solverBuildIds cliFlags
      formulaFingerprints resultArtifacts checkerTranscripts
      outputLineEvidence fallbackDiagnostics ->
    formulaFingerprints :=
  fun contract =>
    contract formulaFingerprints
      (fun _seedProof _buildProof _flagsProof fingerprintProof
          _artifactProof _transcriptProof _outputProof _fallbackProof =>
        fingerprintProof)

theorem ay_vrmr_metadata_contract_result_artifacts
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics : Prop) :
    ay_vrmr_metadata_contract randomSeeds solverBuildIds cliFlags
      formulaFingerprints resultArtifacts checkerTranscripts
      outputLineEvidence fallbackDiagnostics ->
    resultArtifacts :=
  fun contract =>
    contract resultArtifacts
      (fun _seedProof _buildProof _flagsProof _fingerprintProof
          artifactProof _transcriptProof _outputProof _fallbackProof =>
        artifactProof)

theorem ay_vrmr_metadata_contract_checker_transcripts
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics : Prop) :
    ay_vrmr_metadata_contract randomSeeds solverBuildIds cliFlags
      formulaFingerprints resultArtifacts checkerTranscripts
      outputLineEvidence fallbackDiagnostics ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _seedProof _buildProof _flagsProof _fingerprintProof
          _artifactProof transcriptProof _outputProof _fallbackProof =>
        transcriptProof)

theorem ay_vrmr_metadata_contract_output_line
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics : Prop) :
    ay_vrmr_metadata_contract randomSeeds solverBuildIds cliFlags
      formulaFingerprints resultArtifacts checkerTranscripts
      outputLineEvidence fallbackDiagnostics ->
    outputLineEvidence :=
  fun contract =>
    contract outputLineEvidence
      (fun _seedProof _buildProof _flagsProof _fingerprintProof
          _artifactProof _transcriptProof outputProof _fallbackProof =>
        outputProof)

theorem ay_vrmr_metadata_contract_fallback
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics : Prop) :
    ay_vrmr_metadata_contract randomSeeds solverBuildIds cliFlags
      formulaFingerprints resultArtifacts checkerTranscripts
      outputLineEvidence fallbackDiagnostics ->
    fallbackDiagnostics :=
  fun contract =>
    contract fallbackDiagnostics
      (fun _seedProof _buildProof _flagsProof _fingerprintProof
          _artifactProof _transcriptProof _outputProof fallbackProof =>
        fallbackProof)

theorem ay_vrmr_sat_publication_intro
    (metadataContract modelEvidence originalModel : Prop) :
    metadataContract -> modelEvidence -> originalModel ->
    ay_vrmr_sat_publication metadataContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vrmr_conj_intro metadataContract
      (ay_vrmr_conj modelEvidence originalModel)
      contractProof
      (ay_vrmr_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vrmr_sat_publication_original_model
    (metadataContract modelEvidence originalModel : Prop) :
    ay_vrmr_sat_publication metadataContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vrmr_conj_right metadataContract
      (ay_vrmr_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vrmr_unsat_publication_intro
    (metadataContract proofEvidence originalEmptyClause : Prop) :
    metadataContract -> proofEvidence -> originalEmptyClause ->
    ay_vrmr_unsat_publication metadataContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vrmr_conj_intro metadataContract
      (ay_vrmr_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vrmr_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vrmr_unsat_publication_original_empty_clause
    (metadataContract proofEvidence originalEmptyClause : Prop) :
    ay_vrmr_unsat_publication metadataContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vrmr_conj_right metadataContract
      (ay_vrmr_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vrmr_accepted_metadata_sat_sound
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics modelEvidence
      originalModel : Prop) :
    ay_vrmr_metadata_contract randomSeeds solverBuildIds cliFlags
      formulaFingerprints resultArtifacts checkerTranscripts
      outputLineEvidence fallbackDiagnostics ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vrmr_accepted_metadata_unsat_sound
    (randomSeeds solverBuildIds cliFlags formulaFingerprints resultArtifacts
      checkerTranscripts outputLineEvidence fallbackDiagnostics proofEvidence
      originalEmptyClause : Prop) :
    ay_vrmr_metadata_contract randomSeeds solverBuildIds cliFlags
      formulaFingerprints resultArtifacts checkerTranscripts
      outputLineEvidence fallbackDiagnostics ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vrmr_no_claim_intro
    (reason fallbackDiagnostics auditTrail : Prop) :
    reason -> fallbackDiagnostics -> auditTrail ->
    ay_vrmr_no_claim reason fallbackDiagnostics auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vrmr_conj_intro reason
      (ay_vrmr_conj fallbackDiagnostics auditTrail)
      reasonProof
      (ay_vrmr_conj_intro fallbackDiagnostics auditTrail
        fallbackProof auditProof)

theorem ay_vrmr_no_claim_reason
    (reason fallbackDiagnostics auditTrail : Prop) :
    ay_vrmr_no_claim reason fallbackDiagnostics auditTrail -> reason :=
  fun noClaim =>
    ay_vrmr_conj_left reason
      (ay_vrmr_conj fallbackDiagnostics auditTrail)
      noClaim

theorem ay_vrmr_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vrmr_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vrmr_conj_intro reason
      (ay_vrmr_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vrmr_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vrmr_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vrmr_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vrmr_conj_right reason
      (ay_vrmr_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vrmr_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vrmr_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vrmr_conj_right reason
      (ay_vrmr_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vrmr_recompute_intro
    (reason fallbackDiagnostics recomputeObligation : Prop) :
    reason -> fallbackDiagnostics -> recomputeObligation ->
    ay_vrmr_recompute reason fallbackDiagnostics recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vrmr_conj_intro reason
      (ay_vrmr_conj fallbackDiagnostics recomputeObligation)
      reasonProof
      (ay_vrmr_conj_intro fallbackDiagnostics recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vrmr_metadata_failure_intro
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vrmr_metadata_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vrmr_conj_intro
      (ay_vrmr_blocked_publication satFact unsatFact reason)
      (ay_vrmr_recompute reason fallbackDiagnostics recomputeObligation)
      (ay_vrmr_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vrmr_recompute_intro reason fallbackDiagnostics recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vrmr_metadata_failure_blocks_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vrmr_metadata_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vrmr_blocked_publication_no_sat satFact unsatFact reason
      (ay_vrmr_conj_left
        (ay_vrmr_blocked_publication satFact unsatFact reason)
        (ay_vrmr_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vrmr_metadata_failure_blocks_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vrmr_metadata_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vrmr_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vrmr_conj_left
        (ay_vrmr_blocked_publication satFact unsatFact reason)
        (ay_vrmr_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vrmr_metadata_failure_recompute
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vrmr_metadata_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    ay_vrmr_recompute reason fallbackDiagnostics recomputeObligation :=
  fun failure =>
    ay_vrmr_conj_right
      (ay_vrmr_blocked_publication satFact unsatFact reason)
      (ay_vrmr_recompute reason fallbackDiagnostics recomputeObligation)
      failure

theorem ay_vrmr_seed_drift_forces_no_claim
    (satFact unsatFact seedDrift fallbackDiagnostics
      recomputeObligation : Prop) :
    seedDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vrmr_metadata_failure satFact unsatFact seedDrift
      fallbackDiagnostics recomputeObligation :=
  ay_vrmr_metadata_failure_intro satFact unsatFact seedDrift
    fallbackDiagnostics recomputeObligation

theorem ay_vrmr_flag_drift_forces_no_claim
    (satFact unsatFact flagDrift fallbackDiagnostics
      recomputeObligation : Prop) :
    flagDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vrmr_metadata_failure satFact unsatFact flagDrift
      fallbackDiagnostics recomputeObligation :=
  ay_vrmr_metadata_failure_intro satFact unsatFact flagDrift
    fallbackDiagnostics recomputeObligation

theorem ay_vrmr_build_drift_forces_no_claim
    (satFact unsatFact buildDrift fallbackDiagnostics
      recomputeObligation : Prop) :
    buildDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vrmr_metadata_failure satFact unsatFact buildDrift
      fallbackDiagnostics recomputeObligation :=
  ay_vrmr_metadata_failure_intro satFact unsatFact buildDrift
    fallbackDiagnostics recomputeObligation

theorem ay_vrmr_stale_artifact_forces_no_claim
    (satFact unsatFact staleArtifact fallbackDiagnostics
      recomputeObligation : Prop) :
    staleArtifact -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vrmr_metadata_failure satFact unsatFact staleArtifact
      fallbackDiagnostics recomputeObligation :=
  ay_vrmr_metadata_failure_intro satFact unsatFact staleArtifact
    fallbackDiagnostics recomputeObligation

theorem ay_vrmr_transcript_mismatch_forces_no_claim
    (satFact unsatFact transcriptMismatch fallbackDiagnostics
      recomputeObligation : Prop) :
    transcriptMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vrmr_metadata_failure satFact unsatFact transcriptMismatch
      fallbackDiagnostics recomputeObligation :=
  ay_vrmr_metadata_failure_intro satFact unsatFact transcriptMismatch
    fallbackDiagnostics recomputeObligation

theorem ay_vrmr_missing_metadata_forces_no_claim
    (satFact unsatFact missingMetadata fallbackDiagnostics
      recomputeObligation : Prop) :
    missingMetadata -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vrmr_metadata_failure satFact unsatFact missingMetadata
      fallbackDiagnostics recomputeObligation :=
  ay_vrmr_metadata_failure_intro satFact unsatFact missingMetadata
    fallbackDiagnostics recomputeObligation

theorem ay_vrmr_failed_metadata_cannot_bless_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vrmr_metadata_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  ay_vrmr_metadata_failure_blocks_sat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation

theorem ay_vrmr_failed_metadata_cannot_bless_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vrmr_metadata_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  ay_vrmr_metadata_failure_blocks_unsat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation
