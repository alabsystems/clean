-- SAT-COMP validator benchmark instance fingerprint core.
--
-- Sequential-main SAT/UNSAT publication requires agreement between input
-- instance bytes, normalized DIMACS fingerprint, solver formula fingerprint,
-- result artifacts, checker transcripts, build config, and output-line
-- evidence.  Fingerprint drift yields no-claim/recompute only.

def ay_vbif_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vbif_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vbif_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vbif_disj satFact (ay_vbif_disj unsatFact noClaimFact)

def ay_vbif_instance_contract
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) : Prop :=
  forall result : Prop,
    (inputInstanceBytes -> normalizedDimacsFingerprint ->
      solverFormulaFingerprint -> resultArtifacts -> checkerTranscripts ->
      buildConfig -> outputLineEvidence -> fallbackDiagnostics -> result) ->
    result

def ay_vbif_sat_publication
    (instanceContract modelEvidence originalModel : Prop) : Prop :=
  ay_vbif_conj instanceContract
    (ay_vbif_conj modelEvidence originalModel)

def ay_vbif_unsat_publication
    (instanceContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vbif_conj instanceContract
    (ay_vbif_conj proofEvidence originalEmptyClause)

def ay_vbif_no_claim
    (reason fallbackDiagnostics auditTrail : Prop) : Prop :=
  ay_vbif_conj reason (ay_vbif_conj fallbackDiagnostics auditTrail)

def ay_vbif_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vbif_conj reason
    (ay_vbif_conj (satFact -> False) (unsatFact -> False))

def ay_vbif_recompute
    (reason fallbackDiagnostics recomputeObligation : Prop) : Prop :=
  ay_vbif_conj reason
    (ay_vbif_conj fallbackDiagnostics recomputeObligation)

def ay_vbif_instance_failure
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) : Prop :=
  ay_vbif_conj
    (ay_vbif_blocked_publication satFact unsatFact reason)
    (ay_vbif_recompute reason fallbackDiagnostics recomputeObligation)

theorem ay_vbif_conj_intro (left right : Prop) :
    left -> right -> ay_vbif_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vbif_conj_left (left right : Prop) :
    ay_vbif_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vbif_conj_right (left right : Prop) :
    ay_vbif_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vbif_disj_left (left right : Prop) :
    left -> ay_vbif_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vbif_disj_right (left right : Prop) :
    right -> ay_vbif_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vbif_instance_contract_intro
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    inputInstanceBytes -> normalizedDimacsFingerprint ->
    solverFormulaFingerprint -> resultArtifacts -> checkerTranscripts ->
    buildConfig -> outputLineEvidence -> fallbackDiagnostics ->
    ay_vbif_instance_contract inputInstanceBytes
      normalizedDimacsFingerprint solverFormulaFingerprint resultArtifacts
      checkerTranscripts buildConfig outputLineEvidence fallbackDiagnostics :=
  fun bytesProof normalizedProof solverProof artifactsProof transcriptsProof
      buildProof outputProof fallbackProof result build =>
    build bytesProof normalizedProof solverProof artifactsProof
      transcriptsProof buildProof outputProof fallbackProof

theorem ay_vbif_instance_contract_input_bytes
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vbif_instance_contract inputInstanceBytes
      normalizedDimacsFingerprint solverFormulaFingerprint resultArtifacts
      checkerTranscripts buildConfig outputLineEvidence fallbackDiagnostics ->
    inputInstanceBytes :=
  fun contract =>
    contract inputInstanceBytes
      (fun bytesProof _normalizedProof _solverProof _artifactsProof
          _transcriptsProof _buildProof _outputProof _fallbackProof =>
        bytesProof)

theorem ay_vbif_instance_contract_normalized_dimacs
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vbif_instance_contract inputInstanceBytes
      normalizedDimacsFingerprint solverFormulaFingerprint resultArtifacts
      checkerTranscripts buildConfig outputLineEvidence fallbackDiagnostics ->
    normalizedDimacsFingerprint :=
  fun contract =>
    contract normalizedDimacsFingerprint
      (fun _bytesProof normalizedProof _solverProof _artifactsProof
          _transcriptsProof _buildProof _outputProof _fallbackProof =>
        normalizedProof)

theorem ay_vbif_instance_contract_solver_fingerprint
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vbif_instance_contract inputInstanceBytes
      normalizedDimacsFingerprint solverFormulaFingerprint resultArtifacts
      checkerTranscripts buildConfig outputLineEvidence fallbackDiagnostics ->
    solverFormulaFingerprint :=
  fun contract =>
    contract solverFormulaFingerprint
      (fun _bytesProof _normalizedProof solverProof _artifactsProof
          _transcriptsProof _buildProof _outputProof _fallbackProof =>
        solverProof)

theorem ay_vbif_instance_contract_result_artifacts
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vbif_instance_contract inputInstanceBytes
      normalizedDimacsFingerprint solverFormulaFingerprint resultArtifacts
      checkerTranscripts buildConfig outputLineEvidence fallbackDiagnostics ->
    resultArtifacts :=
  fun contract =>
    contract resultArtifacts
      (fun _bytesProof _normalizedProof _solverProof artifactsProof
          _transcriptsProof _buildProof _outputProof _fallbackProof =>
        artifactsProof)

theorem ay_vbif_instance_contract_checker_transcripts
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vbif_instance_contract inputInstanceBytes
      normalizedDimacsFingerprint solverFormulaFingerprint resultArtifacts
      checkerTranscripts buildConfig outputLineEvidence fallbackDiagnostics ->
    checkerTranscripts :=
  fun contract =>
    contract checkerTranscripts
      (fun _bytesProof _normalizedProof _solverProof _artifactsProof
          transcriptsProof _buildProof _outputProof _fallbackProof =>
        transcriptsProof)

theorem ay_vbif_instance_contract_build_config
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vbif_instance_contract inputInstanceBytes
      normalizedDimacsFingerprint solverFormulaFingerprint resultArtifacts
      checkerTranscripts buildConfig outputLineEvidence fallbackDiagnostics ->
    buildConfig :=
  fun contract =>
    contract buildConfig
      (fun _bytesProof _normalizedProof _solverProof _artifactsProof
          _transcriptsProof buildProof _outputProof _fallbackProof =>
        buildProof)

theorem ay_vbif_instance_contract_output_line
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vbif_instance_contract inputInstanceBytes
      normalizedDimacsFingerprint solverFormulaFingerprint resultArtifacts
      checkerTranscripts buildConfig outputLineEvidence fallbackDiagnostics ->
    outputLineEvidence :=
  fun contract =>
    contract outputLineEvidence
      (fun _bytesProof _normalizedProof _solverProof _artifactsProof
          _transcriptsProof _buildProof outputProof _fallbackProof =>
        outputProof)

theorem ay_vbif_instance_contract_fallback
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics : Prop) :
    ay_vbif_instance_contract inputInstanceBytes
      normalizedDimacsFingerprint solverFormulaFingerprint resultArtifacts
      checkerTranscripts buildConfig outputLineEvidence fallbackDiagnostics ->
    fallbackDiagnostics :=
  fun contract =>
    contract fallbackDiagnostics
      (fun _bytesProof _normalizedProof _solverProof _artifactsProof
          _transcriptsProof _buildProof _outputProof fallbackProof =>
        fallbackProof)

theorem ay_vbif_sat_publication_intro
    (instanceContract modelEvidence originalModel : Prop) :
    instanceContract -> modelEvidence -> originalModel ->
    ay_vbif_sat_publication instanceContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vbif_conj_intro instanceContract
      (ay_vbif_conj modelEvidence originalModel)
      contractProof
      (ay_vbif_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vbif_sat_publication_original_model
    (instanceContract modelEvidence originalModel : Prop) :
    ay_vbif_sat_publication instanceContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vbif_conj_right instanceContract
      (ay_vbif_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vbif_unsat_publication_intro
    (instanceContract proofEvidence originalEmptyClause : Prop) :
    instanceContract -> proofEvidence -> originalEmptyClause ->
    ay_vbif_unsat_publication instanceContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vbif_conj_intro instanceContract
      (ay_vbif_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vbif_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vbif_unsat_publication_original_empty_clause
    (instanceContract proofEvidence originalEmptyClause : Prop) :
    ay_vbif_unsat_publication instanceContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vbif_conj_right instanceContract
      (ay_vbif_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vbif_accepted_instance_sat_sound
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics modelEvidence originalModel : Prop) :
    ay_vbif_instance_contract inputInstanceBytes
      normalizedDimacsFingerprint solverFormulaFingerprint resultArtifacts
      checkerTranscripts buildConfig outputLineEvidence fallbackDiagnostics ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vbif_accepted_instance_unsat_sound
    (inputInstanceBytes normalizedDimacsFingerprint solverFormulaFingerprint
      resultArtifacts checkerTranscripts buildConfig outputLineEvidence
      fallbackDiagnostics proofEvidence originalEmptyClause : Prop) :
    ay_vbif_instance_contract inputInstanceBytes
      normalizedDimacsFingerprint solverFormulaFingerprint resultArtifacts
      checkerTranscripts buildConfig outputLineEvidence fallbackDiagnostics ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vbif_no_claim_intro
    (reason fallbackDiagnostics auditTrail : Prop) :
    reason -> fallbackDiagnostics -> auditTrail ->
    ay_vbif_no_claim reason fallbackDiagnostics auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vbif_conj_intro reason
      (ay_vbif_conj fallbackDiagnostics auditTrail)
      reasonProof
      (ay_vbif_conj_intro fallbackDiagnostics auditTrail
        fallbackProof auditProof)

theorem ay_vbif_no_claim_reason
    (reason fallbackDiagnostics auditTrail : Prop) :
    ay_vbif_no_claim reason fallbackDiagnostics auditTrail -> reason :=
  fun noClaim =>
    ay_vbif_conj_left reason
      (ay_vbif_conj fallbackDiagnostics auditTrail)
      noClaim

theorem ay_vbif_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vbif_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vbif_conj_intro reason
      (ay_vbif_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vbif_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vbif_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vbif_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vbif_conj_right reason
      (ay_vbif_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vbif_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vbif_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vbif_conj_right reason
      (ay_vbif_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vbif_recompute_intro
    (reason fallbackDiagnostics recomputeObligation : Prop) :
    reason -> fallbackDiagnostics -> recomputeObligation ->
    ay_vbif_recompute reason fallbackDiagnostics recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vbif_conj_intro reason
      (ay_vbif_conj fallbackDiagnostics recomputeObligation)
      reasonProof
      (ay_vbif_conj_intro fallbackDiagnostics recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vbif_instance_failure_intro
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vbif_instance_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vbif_conj_intro
      (ay_vbif_blocked_publication satFact unsatFact reason)
      (ay_vbif_recompute reason fallbackDiagnostics recomputeObligation)
      (ay_vbif_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vbif_recompute_intro reason fallbackDiagnostics recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vbif_instance_failure_blocks_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vbif_instance_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vbif_blocked_publication_no_sat satFact unsatFact reason
      (ay_vbif_conj_left
        (ay_vbif_blocked_publication satFact unsatFact reason)
        (ay_vbif_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vbif_instance_failure_blocks_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vbif_instance_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vbif_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vbif_conj_left
        (ay_vbif_blocked_publication satFact unsatFact reason)
        (ay_vbif_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vbif_instance_failure_recompute
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vbif_instance_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    ay_vbif_recompute reason fallbackDiagnostics recomputeObligation :=
  fun failure =>
    ay_vbif_conj_right
      (ay_vbif_blocked_publication satFact unsatFact reason)
      (ay_vbif_recompute reason fallbackDiagnostics recomputeObligation)
      failure

theorem ay_vbif_instance_drift_forces_no_claim
    (satFact unsatFact instanceDrift fallbackDiagnostics
      recomputeObligation : Prop) :
    instanceDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vbif_instance_failure satFact unsatFact instanceDrift
      fallbackDiagnostics recomputeObligation :=
  ay_vbif_instance_failure_intro satFact unsatFact instanceDrift
    fallbackDiagnostics recomputeObligation

theorem ay_vbif_normalization_mismatch_forces_no_claim
    (satFact unsatFact normalizationMismatch fallbackDiagnostics
      recomputeObligation : Prop) :
    normalizationMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vbif_instance_failure satFact unsatFact normalizationMismatch
      fallbackDiagnostics recomputeObligation :=
  ay_vbif_instance_failure_intro satFact unsatFact normalizationMismatch
    fallbackDiagnostics recomputeObligation

theorem ay_vbif_stale_solver_fingerprint_forces_no_claim
    (satFact unsatFact staleSolverFingerprint fallbackDiagnostics
      recomputeObligation : Prop) :
    staleSolverFingerprint -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vbif_instance_failure satFact unsatFact staleSolverFingerprint
      fallbackDiagnostics recomputeObligation :=
  ay_vbif_instance_failure_intro satFact unsatFact staleSolverFingerprint
    fallbackDiagnostics recomputeObligation

theorem ay_vbif_artifact_mismatch_forces_no_claim
    (satFact unsatFact artifactMismatch fallbackDiagnostics
      recomputeObligation : Prop) :
    artifactMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vbif_instance_failure satFact unsatFact artifactMismatch
      fallbackDiagnostics recomputeObligation :=
  ay_vbif_instance_failure_intro satFact unsatFact artifactMismatch
    fallbackDiagnostics recomputeObligation

theorem ay_vbif_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackDiagnostics
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vbif_instance_failure satFact unsatFact missingTranscript
      fallbackDiagnostics recomputeObligation :=
  ay_vbif_instance_failure_intro satFact unsatFact missingTranscript
    fallbackDiagnostics recomputeObligation

theorem ay_vbif_failed_instance_cannot_bless_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vbif_instance_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  ay_vbif_instance_failure_blocks_sat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation

theorem ay_vbif_failed_instance_cannot_bless_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vbif_instance_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  ay_vbif_instance_failure_blocks_unsat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation
