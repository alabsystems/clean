-- SAT-COMP validator competition output line contract core.
--
-- Sequential-main public output lines may publish SAT/UNSAT only when result
-- token, artifact manifest, checker transcript, formula fingerprint, build
-- config, and fallback diagnostics agree.

def ay_vcol_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vcol_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vcol_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vcol_disj satFact (ay_vcol_disj unsatFact noClaimFact)

def ay_vcol_output_line_contract
    (resultToken artifactManifest checkerTranscript formulaFingerprint
      buildConfig fallbackDiagnostics outputLine : Prop) : Prop :=
  ay_vcol_conj resultToken
    (ay_vcol_conj artifactManifest
      (ay_vcol_conj checkerTranscript
        (ay_vcol_conj formulaFingerprint
          (ay_vcol_conj buildConfig
            (ay_vcol_conj fallbackDiagnostics outputLine)))))

def ay_vcol_sat_publication
    (lineContract modelEvidence originalModel : Prop) : Prop :=
  ay_vcol_conj lineContract
    (ay_vcol_conj modelEvidence originalModel)

def ay_vcol_unsat_publication
    (lineContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vcol_conj lineContract
    (ay_vcol_conj proofEvidence originalEmptyClause)

def ay_vcol_no_claim
    (reason fallbackDiagnostics auditTrail : Prop) : Prop :=
  ay_vcol_conj reason (ay_vcol_conj fallbackDiagnostics auditTrail)

def ay_vcol_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vcol_conj reason
    (ay_vcol_conj (satFact -> False) (unsatFact -> False))

def ay_vcol_recompute
    (reason fallbackDiagnostics recomputeObligation : Prop) : Prop :=
  ay_vcol_conj reason
    (ay_vcol_conj fallbackDiagnostics recomputeObligation)

def ay_vcol_output_failure
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) : Prop :=
  ay_vcol_conj
    (ay_vcol_blocked_publication satFact unsatFact reason)
    (ay_vcol_recompute reason fallbackDiagnostics recomputeObligation)

theorem ay_vcol_conj_intro (left right : Prop) :
    left -> right -> ay_vcol_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcol_conj_left (left right : Prop) :
    ay_vcol_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcol_conj_right (left right : Prop) :
    ay_vcol_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcol_disj_left (left right : Prop) :
    left -> ay_vcol_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vcol_disj_right (left right : Prop) :
    right -> ay_vcol_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcol_output_line_contract_intro
    (resultToken artifactManifest checkerTranscript formulaFingerprint
      buildConfig fallbackDiagnostics outputLine : Prop) :
    resultToken -> artifactManifest -> checkerTranscript ->
    formulaFingerprint -> buildConfig -> fallbackDiagnostics -> outputLine ->
    ay_vcol_output_line_contract resultToken artifactManifest
      checkerTranscript formulaFingerprint buildConfig fallbackDiagnostics
      outputLine :=
  fun tokenProof manifestProof transcriptProof fingerprintProof buildProof
      fallbackProof lineProof =>
    ay_vcol_conj_intro resultToken
      (ay_vcol_conj artifactManifest
        (ay_vcol_conj checkerTranscript
          (ay_vcol_conj formulaFingerprint
            (ay_vcol_conj buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine)))))
      tokenProof
      (ay_vcol_conj_intro artifactManifest
        (ay_vcol_conj checkerTranscript
          (ay_vcol_conj formulaFingerprint
            (ay_vcol_conj buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine))))
        manifestProof
        (ay_vcol_conj_intro checkerTranscript
          (ay_vcol_conj formulaFingerprint
            (ay_vcol_conj buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine)))
          transcriptProof
          (ay_vcol_conj_intro formulaFingerprint
            (ay_vcol_conj buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine))
            fingerprintProof
            (ay_vcol_conj_intro buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine)
              buildProof
              (ay_vcol_conj_intro fallbackDiagnostics outputLine
                fallbackProof lineProof)))))

theorem ay_vcol_output_line_contract_result_token
    (resultToken artifactManifest checkerTranscript formulaFingerprint
      buildConfig fallbackDiagnostics outputLine : Prop) :
    ay_vcol_output_line_contract resultToken artifactManifest
      checkerTranscript formulaFingerprint buildConfig fallbackDiagnostics
      outputLine ->
    resultToken :=
  fun contract =>
    ay_vcol_conj_left resultToken
      (ay_vcol_conj artifactManifest
        (ay_vcol_conj checkerTranscript
          (ay_vcol_conj formulaFingerprint
            (ay_vcol_conj buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine)))))
      contract

theorem ay_vcol_output_line_contract_manifest
    (resultToken artifactManifest checkerTranscript formulaFingerprint
      buildConfig fallbackDiagnostics outputLine : Prop) :
    ay_vcol_output_line_contract resultToken artifactManifest
      checkerTranscript formulaFingerprint buildConfig fallbackDiagnostics
      outputLine ->
    artifactManifest :=
  fun contract =>
    ay_vcol_conj_right resultToken
      (ay_vcol_conj artifactManifest
        (ay_vcol_conj checkerTranscript
          (ay_vcol_conj formulaFingerprint
            (ay_vcol_conj buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine)))))
      contract artifactManifest
      (fun manifestProof _tail => manifestProof)

theorem ay_vcol_output_line_contract_transcript
    (resultToken artifactManifest checkerTranscript formulaFingerprint
      buildConfig fallbackDiagnostics outputLine : Prop) :
    ay_vcol_output_line_contract resultToken artifactManifest
      checkerTranscript formulaFingerprint buildConfig fallbackDiagnostics
      outputLine ->
    checkerTranscript :=
  fun contract =>
    ay_vcol_conj_right resultToken
      (ay_vcol_conj artifactManifest
        (ay_vcol_conj checkerTranscript
          (ay_vcol_conj formulaFingerprint
            (ay_vcol_conj buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine)))))
      contract checkerTranscript
      (fun _manifestProof tail =>
        tail checkerTranscript
          (fun transcriptProof _tail2 => transcriptProof))

theorem ay_vcol_output_line_contract_fingerprint
    (resultToken artifactManifest checkerTranscript formulaFingerprint
      buildConfig fallbackDiagnostics outputLine : Prop) :
    ay_vcol_output_line_contract resultToken artifactManifest
      checkerTranscript formulaFingerprint buildConfig fallbackDiagnostics
      outputLine ->
    formulaFingerprint :=
  fun contract =>
    ay_vcol_conj_right resultToken
      (ay_vcol_conj artifactManifest
        (ay_vcol_conj checkerTranscript
          (ay_vcol_conj formulaFingerprint
            (ay_vcol_conj buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine)))))
      contract formulaFingerprint
      (fun _manifestProof tail =>
        tail formulaFingerprint
          (fun _transcriptProof tail2 =>
            tail2 formulaFingerprint
              (fun fingerprintProof _tail3 => fingerprintProof)))

theorem ay_vcol_output_line_contract_build_config
    (resultToken artifactManifest checkerTranscript formulaFingerprint
      buildConfig fallbackDiagnostics outputLine : Prop) :
    ay_vcol_output_line_contract resultToken artifactManifest
      checkerTranscript formulaFingerprint buildConfig fallbackDiagnostics
      outputLine ->
    buildConfig :=
  fun contract =>
    ay_vcol_conj_right resultToken
      (ay_vcol_conj artifactManifest
        (ay_vcol_conj checkerTranscript
          (ay_vcol_conj formulaFingerprint
            (ay_vcol_conj buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine)))))
      contract buildConfig
      (fun _manifestProof tail =>
        tail buildConfig
          (fun _transcriptProof tail2 =>
            tail2 buildConfig
              (fun _fingerprintProof tail3 =>
                tail3 buildConfig
                  (fun buildProof _tail4 => buildProof))))

theorem ay_vcol_output_line_contract_fallback
    (resultToken artifactManifest checkerTranscript formulaFingerprint
      buildConfig fallbackDiagnostics outputLine : Prop) :
    ay_vcol_output_line_contract resultToken artifactManifest
      checkerTranscript formulaFingerprint buildConfig fallbackDiagnostics
      outputLine ->
    fallbackDiagnostics :=
  fun contract =>
    ay_vcol_conj_right resultToken
      (ay_vcol_conj artifactManifest
        (ay_vcol_conj checkerTranscript
          (ay_vcol_conj formulaFingerprint
            (ay_vcol_conj buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine)))))
      contract fallbackDiagnostics
      (fun _manifestProof tail =>
        tail fallbackDiagnostics
          (fun _transcriptProof tail2 =>
            tail2 fallbackDiagnostics
              (fun _fingerprintProof tail3 =>
                tail3 fallbackDiagnostics
                  (fun _buildProof tail4 =>
                    tail4 fallbackDiagnostics
                      (fun fallbackProof _lineProof => fallbackProof)))))

theorem ay_vcol_output_line_contract_output_line
    (resultToken artifactManifest checkerTranscript formulaFingerprint
      buildConfig fallbackDiagnostics outputLine : Prop) :
    ay_vcol_output_line_contract resultToken artifactManifest
      checkerTranscript formulaFingerprint buildConfig fallbackDiagnostics
      outputLine ->
    outputLine :=
  fun contract =>
    ay_vcol_conj_right resultToken
      (ay_vcol_conj artifactManifest
        (ay_vcol_conj checkerTranscript
          (ay_vcol_conj formulaFingerprint
            (ay_vcol_conj buildConfig
              (ay_vcol_conj fallbackDiagnostics outputLine)))))
      contract outputLine
      (fun _manifestProof tail =>
        tail outputLine
          (fun _transcriptProof tail2 =>
            tail2 outputLine
              (fun _fingerprintProof tail3 =>
                tail3 outputLine
                  (fun _buildProof tail4 =>
                    tail4 outputLine
                      (fun _fallbackProof lineProof => lineProof)))))

theorem ay_vcol_sat_publication_intro
    (lineContract modelEvidence originalModel : Prop) :
    lineContract -> modelEvidence -> originalModel ->
    ay_vcol_sat_publication lineContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vcol_conj_intro lineContract
      (ay_vcol_conj modelEvidence originalModel)
      contractProof
      (ay_vcol_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vcol_sat_publication_original_model
    (lineContract modelEvidence originalModel : Prop) :
    ay_vcol_sat_publication lineContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vcol_conj_right lineContract
      (ay_vcol_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vcol_unsat_publication_intro
    (lineContract proofEvidence originalEmptyClause : Prop) :
    lineContract -> proofEvidence -> originalEmptyClause ->
    ay_vcol_unsat_publication lineContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vcol_conj_intro lineContract
      (ay_vcol_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vcol_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vcol_unsat_publication_original_empty_clause
    (lineContract proofEvidence originalEmptyClause : Prop) :
    ay_vcol_unsat_publication lineContract proofEvidence originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vcol_conj_right lineContract
      (ay_vcol_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vcol_accepted_output_line_sat_sound
    (resultToken artifactManifest checkerTranscript formulaFingerprint
      buildConfig fallbackDiagnostics outputLine modelEvidence
      originalModel : Prop) :
    ay_vcol_output_line_contract resultToken artifactManifest
      checkerTranscript formulaFingerprint buildConfig fallbackDiagnostics
      outputLine ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vcol_accepted_output_line_unsat_sound
    (resultToken artifactManifest checkerTranscript formulaFingerprint
      buildConfig fallbackDiagnostics outputLine proofEvidence
      originalEmptyClause : Prop) :
    ay_vcol_output_line_contract resultToken artifactManifest
      checkerTranscript formulaFingerprint buildConfig fallbackDiagnostics
      outputLine ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vcol_no_claim_intro
    (reason fallbackDiagnostics auditTrail : Prop) :
    reason -> fallbackDiagnostics -> auditTrail ->
    ay_vcol_no_claim reason fallbackDiagnostics auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vcol_conj_intro reason
      (ay_vcol_conj fallbackDiagnostics auditTrail)
      reasonProof
      (ay_vcol_conj_intro fallbackDiagnostics auditTrail
        fallbackProof auditProof)

theorem ay_vcol_no_claim_reason
    (reason fallbackDiagnostics auditTrail : Prop) :
    ay_vcol_no_claim reason fallbackDiagnostics auditTrail -> reason :=
  fun noClaim =>
    ay_vcol_conj_left reason
      (ay_vcol_conj fallbackDiagnostics auditTrail)
      noClaim

theorem ay_vcol_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vcol_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vcol_conj_intro reason
      (ay_vcol_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vcol_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vcol_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vcol_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vcol_conj_right reason
      (ay_vcol_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vcol_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vcol_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vcol_conj_right reason
      (ay_vcol_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vcol_recompute_intro
    (reason fallbackDiagnostics recomputeObligation : Prop) :
    reason -> fallbackDiagnostics -> recomputeObligation ->
    ay_vcol_recompute reason fallbackDiagnostics recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vcol_conj_intro reason
      (ay_vcol_conj fallbackDiagnostics recomputeObligation)
      reasonProof
      (ay_vcol_conj_intro fallbackDiagnostics recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vcol_output_failure_intro
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcol_output_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vcol_conj_intro
      (ay_vcol_blocked_publication satFact unsatFact reason)
      (ay_vcol_recompute reason fallbackDiagnostics recomputeObligation)
      (ay_vcol_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vcol_recompute_intro reason fallbackDiagnostics recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vcol_output_failure_blocks_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcol_output_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vcol_blocked_publication_no_sat satFact unsatFact reason
      (ay_vcol_conj_left
        (ay_vcol_blocked_publication satFact unsatFact reason)
        (ay_vcol_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vcol_output_failure_blocks_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcol_output_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vcol_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vcol_conj_left
        (ay_vcol_blocked_publication satFact unsatFact reason)
        (ay_vcol_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vcol_output_failure_recompute
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcol_output_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    ay_vcol_recompute reason fallbackDiagnostics recomputeObligation :=
  fun failure =>
    ay_vcol_conj_right
      (ay_vcol_blocked_publication satFact unsatFact reason)
      (ay_vcol_recompute reason fallbackDiagnostics recomputeObligation)
      failure

theorem ay_vcol_malformed_output_forces_no_claim
    (satFact unsatFact malformedOutput fallbackDiagnostics
      recomputeObligation : Prop) :
    malformedOutput -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcol_output_failure satFact unsatFact malformedOutput
      fallbackDiagnostics recomputeObligation :=
  ay_vcol_output_failure_intro satFact unsatFact malformedOutput
    fallbackDiagnostics recomputeObligation

theorem ay_vcol_result_token_mismatch_forces_no_claim
    (satFact unsatFact resultTokenMismatch fallbackDiagnostics
      recomputeObligation : Prop) :
    resultTokenMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcol_output_failure satFact unsatFact resultTokenMismatch
      fallbackDiagnostics recomputeObligation :=
  ay_vcol_output_failure_intro satFact unsatFact resultTokenMismatch
    fallbackDiagnostics recomputeObligation

theorem ay_vcol_stale_manifest_forces_no_claim
    (satFact unsatFact staleArtifactManifest fallbackDiagnostics
      recomputeObligation : Prop) :
    staleArtifactManifest -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcol_output_failure satFact unsatFact staleArtifactManifest
      fallbackDiagnostics recomputeObligation :=
  ay_vcol_output_failure_intro satFact unsatFact staleArtifactManifest
    fallbackDiagnostics recomputeObligation

theorem ay_vcol_checker_rejection_forces_no_claim
    (satFact unsatFact checkerRejection fallbackDiagnostics
      recomputeObligation : Prop) :
    checkerRejection -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcol_output_failure satFact unsatFact checkerRejection
      fallbackDiagnostics recomputeObligation :=
  ay_vcol_output_failure_intro satFact unsatFact checkerRejection
    fallbackDiagnostics recomputeObligation

theorem ay_vcol_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackDiagnostics
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vcol_output_failure satFact unsatFact missingTranscript
      fallbackDiagnostics recomputeObligation :=
  ay_vcol_output_failure_intro satFact unsatFact missingTranscript
    fallbackDiagnostics recomputeObligation

theorem ay_vcol_failed_output_cannot_bless_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcol_output_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  ay_vcol_output_failure_blocks_sat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation

theorem ay_vcol_failed_output_cannot_bless_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vcol_output_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  ay_vcol_output_failure_blocks_unsat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation
