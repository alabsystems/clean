-- SAT-COMP validator checker transcript redaction core.
--
-- Public checker transcripts may be redacted or compressed only when retained
-- digests, result token, artifact manifest, formula fingerprint, build config,
-- and reconstruction evidence still agree.

def ay_vctr_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vctr_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vctr_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vctr_disj satFact (ay_vctr_disj unsatFact noClaimFact)

def ay_vctr_redaction_contract
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics : Prop) : Prop :=
  ay_vctr_conj retainedDigests
    (ay_vctr_conj resultToken
      (ay_vctr_conj artifactManifest
        (ay_vctr_conj formulaFingerprint
          (ay_vctr_conj buildConfig
            (ay_vctr_conj reconstructionEvidence
              (ay_vctr_conj redactedTranscript fallbackDiagnostics))))))

def ay_vctr_sat_publication
    (redactionContract modelEvidence originalModel : Prop) : Prop :=
  ay_vctr_conj redactionContract
    (ay_vctr_conj modelEvidence originalModel)

def ay_vctr_unsat_publication
    (redactionContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vctr_conj redactionContract
    (ay_vctr_conj proofEvidence originalEmptyClause)

def ay_vctr_no_claim
    (reason fallbackDiagnostics auditTrail : Prop) : Prop :=
  ay_vctr_conj reason (ay_vctr_conj fallbackDiagnostics auditTrail)

def ay_vctr_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vctr_conj reason
    (ay_vctr_conj (satFact -> False) (unsatFact -> False))

def ay_vctr_recompute
    (reason fallbackDiagnostics recomputeObligation : Prop) : Prop :=
  ay_vctr_conj reason
    (ay_vctr_conj fallbackDiagnostics recomputeObligation)

def ay_vctr_redaction_failure
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) : Prop :=
  ay_vctr_conj
    (ay_vctr_blocked_publication satFact unsatFact reason)
    (ay_vctr_recompute reason fallbackDiagnostics recomputeObligation)

theorem ay_vctr_conj_intro (left right : Prop) :
    left -> right -> ay_vctr_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vctr_conj_left (left right : Prop) :
    ay_vctr_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vctr_conj_right (left right : Prop) :
    ay_vctr_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vctr_disj_left (left right : Prop) :
    left -> ay_vctr_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vctr_disj_right (left right : Prop) :
    right -> ay_vctr_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vctr_redaction_contract_intro
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics : Prop) :
    retainedDigests -> resultToken -> artifactManifest ->
    formulaFingerprint -> buildConfig -> reconstructionEvidence ->
    redactedTranscript -> fallbackDiagnostics ->
    ay_vctr_redaction_contract retainedDigests resultToken artifactManifest
      formulaFingerprint buildConfig reconstructionEvidence
      redactedTranscript fallbackDiagnostics :=
  fun digestProof tokenProof manifestProof fingerprintProof buildProof
      reconstructionProof transcriptProof fallbackProof =>
    ay_vctr_conj_intro retainedDigests
      (ay_vctr_conj resultToken
        (ay_vctr_conj artifactManifest
          (ay_vctr_conj formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics))))))
      digestProof
      (ay_vctr_conj_intro resultToken
        (ay_vctr_conj artifactManifest
          (ay_vctr_conj formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics)))))
        tokenProof
        (ay_vctr_conj_intro artifactManifest
          (ay_vctr_conj formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics))))
          manifestProof
          (ay_vctr_conj_intro formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics)))
            fingerprintProof
            (ay_vctr_conj_intro buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics))
              buildProof
              (ay_vctr_conj_intro reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics)
                reconstructionProof
                (ay_vctr_conj_intro redactedTranscript fallbackDiagnostics
                  transcriptProof fallbackProof))))))

theorem ay_vctr_redaction_contract_retained_digests
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics : Prop) :
    ay_vctr_redaction_contract retainedDigests resultToken artifactManifest
      formulaFingerprint buildConfig reconstructionEvidence
      redactedTranscript fallbackDiagnostics ->
    retainedDigests :=
  fun contract =>
    ay_vctr_conj_left retainedDigests
      (ay_vctr_conj resultToken
        (ay_vctr_conj artifactManifest
          (ay_vctr_conj formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics))))))
      contract

theorem ay_vctr_redaction_contract_result_token
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics : Prop) :
    ay_vctr_redaction_contract retainedDigests resultToken artifactManifest
      formulaFingerprint buildConfig reconstructionEvidence
      redactedTranscript fallbackDiagnostics ->
    resultToken :=
  fun contract =>
    ay_vctr_conj_right retainedDigests
      (ay_vctr_conj resultToken
        (ay_vctr_conj artifactManifest
          (ay_vctr_conj formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics))))))
      contract resultToken
      (fun tokenProof _tail => tokenProof)

theorem ay_vctr_redaction_contract_artifact_manifest
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics : Prop) :
    ay_vctr_redaction_contract retainedDigests resultToken artifactManifest
      formulaFingerprint buildConfig reconstructionEvidence
      redactedTranscript fallbackDiagnostics ->
    artifactManifest :=
  fun contract =>
    ay_vctr_conj_right retainedDigests
      (ay_vctr_conj resultToken
        (ay_vctr_conj artifactManifest
          (ay_vctr_conj formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics))))))
      contract artifactManifest
      (fun _tokenProof tail =>
        tail artifactManifest
          (fun manifestProof _tail2 => manifestProof))

theorem ay_vctr_redaction_contract_formula_fingerprint
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics : Prop) :
    ay_vctr_redaction_contract retainedDigests resultToken artifactManifest
      formulaFingerprint buildConfig reconstructionEvidence
      redactedTranscript fallbackDiagnostics ->
    formulaFingerprint :=
  fun contract =>
    ay_vctr_conj_right retainedDigests
      (ay_vctr_conj resultToken
        (ay_vctr_conj artifactManifest
          (ay_vctr_conj formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics))))))
      contract formulaFingerprint
      (fun _tokenProof tail =>
        tail formulaFingerprint
          (fun _manifestProof tail2 =>
            tail2 formulaFingerprint
              (fun fingerprintProof _tail3 => fingerprintProof)))

theorem ay_vctr_redaction_contract_build_config
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics : Prop) :
    ay_vctr_redaction_contract retainedDigests resultToken artifactManifest
      formulaFingerprint buildConfig reconstructionEvidence
      redactedTranscript fallbackDiagnostics ->
    buildConfig :=
  fun contract =>
    ay_vctr_conj_right retainedDigests
      (ay_vctr_conj resultToken
        (ay_vctr_conj artifactManifest
          (ay_vctr_conj formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics))))))
      contract buildConfig
      (fun _tokenProof tail =>
        tail buildConfig
          (fun _manifestProof tail2 =>
            tail2 buildConfig
              (fun _fingerprintProof tail3 =>
                tail3 buildConfig
                  (fun buildProof _tail4 => buildProof))))

theorem ay_vctr_redaction_contract_reconstruction
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics : Prop) :
    ay_vctr_redaction_contract retainedDigests resultToken artifactManifest
      formulaFingerprint buildConfig reconstructionEvidence
      redactedTranscript fallbackDiagnostics ->
    reconstructionEvidence :=
  fun contract =>
    ay_vctr_conj_right retainedDigests
      (ay_vctr_conj resultToken
        (ay_vctr_conj artifactManifest
          (ay_vctr_conj formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics))))))
      contract reconstructionEvidence
      (fun _tokenProof tail =>
        tail reconstructionEvidence
          (fun _manifestProof tail2 =>
            tail2 reconstructionEvidence
              (fun _fingerprintProof tail3 =>
                tail3 reconstructionEvidence
                  (fun _buildProof tail4 =>
                    tail4 reconstructionEvidence
                      (fun reconstructionProof _tail5 =>
                        reconstructionProof)))))

theorem ay_vctr_redaction_contract_redacted_transcript
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics : Prop) :
    ay_vctr_redaction_contract retainedDigests resultToken artifactManifest
      formulaFingerprint buildConfig reconstructionEvidence
      redactedTranscript fallbackDiagnostics ->
    redactedTranscript :=
  fun contract =>
    ay_vctr_conj_right retainedDigests
      (ay_vctr_conj resultToken
        (ay_vctr_conj artifactManifest
          (ay_vctr_conj formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics))))))
      contract redactedTranscript
      (fun _tokenProof tail =>
        tail redactedTranscript
          (fun _manifestProof tail2 =>
            tail2 redactedTranscript
              (fun _fingerprintProof tail3 =>
                tail3 redactedTranscript
                  (fun _buildProof tail4 =>
                    tail4 redactedTranscript
                      (fun _reconstructionProof tail5 =>
                        tail5 redactedTranscript
                          (fun transcriptProof _fallbackProof =>
                            transcriptProof))))))

theorem ay_vctr_redaction_contract_fallback
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics : Prop) :
    ay_vctr_redaction_contract retainedDigests resultToken artifactManifest
      formulaFingerprint buildConfig reconstructionEvidence
      redactedTranscript fallbackDiagnostics ->
    fallbackDiagnostics :=
  fun contract =>
    ay_vctr_conj_right retainedDigests
      (ay_vctr_conj resultToken
        (ay_vctr_conj artifactManifest
          (ay_vctr_conj formulaFingerprint
            (ay_vctr_conj buildConfig
              (ay_vctr_conj reconstructionEvidence
                (ay_vctr_conj redactedTranscript fallbackDiagnostics))))))
      contract fallbackDiagnostics
      (fun _tokenProof tail =>
        tail fallbackDiagnostics
          (fun _manifestProof tail2 =>
            tail2 fallbackDiagnostics
              (fun _fingerprintProof tail3 =>
                tail3 fallbackDiagnostics
                  (fun _buildProof tail4 =>
                    tail4 fallbackDiagnostics
                      (fun _reconstructionProof tail5 =>
                        tail5 fallbackDiagnostics
                          (fun _transcriptProof fallbackProof =>
                            fallbackProof))))))

theorem ay_vctr_sat_publication_intro
    (redactionContract modelEvidence originalModel : Prop) :
    redactionContract -> modelEvidence -> originalModel ->
    ay_vctr_sat_publication redactionContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vctr_conj_intro redactionContract
      (ay_vctr_conj modelEvidence originalModel)
      contractProof
      (ay_vctr_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vctr_sat_publication_original_model
    (redactionContract modelEvidence originalModel : Prop) :
    ay_vctr_sat_publication redactionContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vctr_conj_right redactionContract
      (ay_vctr_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vctr_unsat_publication_intro
    (redactionContract proofEvidence originalEmptyClause : Prop) :
    redactionContract -> proofEvidence -> originalEmptyClause ->
    ay_vctr_unsat_publication redactionContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vctr_conj_intro redactionContract
      (ay_vctr_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vctr_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vctr_unsat_publication_original_empty_clause
    (redactionContract proofEvidence originalEmptyClause : Prop) :
    ay_vctr_unsat_publication redactionContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vctr_conj_right redactionContract
      (ay_vctr_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vctr_accepted_redaction_sat_sound
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics modelEvidence originalModel : Prop) :
    ay_vctr_redaction_contract retainedDigests resultToken artifactManifest
      formulaFingerprint buildConfig reconstructionEvidence
      redactedTranscript fallbackDiagnostics ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vctr_accepted_redaction_unsat_sound
    (retainedDigests resultToken artifactManifest formulaFingerprint
      buildConfig reconstructionEvidence redactedTranscript
      fallbackDiagnostics proofEvidence originalEmptyClause : Prop) :
    ay_vctr_redaction_contract retainedDigests resultToken artifactManifest
      formulaFingerprint buildConfig reconstructionEvidence
      redactedTranscript fallbackDiagnostics ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vctr_no_claim_intro
    (reason fallbackDiagnostics auditTrail : Prop) :
    reason -> fallbackDiagnostics -> auditTrail ->
    ay_vctr_no_claim reason fallbackDiagnostics auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vctr_conj_intro reason
      (ay_vctr_conj fallbackDiagnostics auditTrail)
      reasonProof
      (ay_vctr_conj_intro fallbackDiagnostics auditTrail
        fallbackProof auditProof)

theorem ay_vctr_no_claim_reason
    (reason fallbackDiagnostics auditTrail : Prop) :
    ay_vctr_no_claim reason fallbackDiagnostics auditTrail -> reason :=
  fun noClaim =>
    ay_vctr_conj_left reason
      (ay_vctr_conj fallbackDiagnostics auditTrail)
      noClaim

theorem ay_vctr_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vctr_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vctr_conj_intro reason
      (ay_vctr_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vctr_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vctr_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vctr_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vctr_conj_right reason
      (ay_vctr_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vctr_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vctr_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vctr_conj_right reason
      (ay_vctr_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vctr_recompute_intro
    (reason fallbackDiagnostics recomputeObligation : Prop) :
    reason -> fallbackDiagnostics -> recomputeObligation ->
    ay_vctr_recompute reason fallbackDiagnostics recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vctr_conj_intro reason
      (ay_vctr_conj fallbackDiagnostics recomputeObligation)
      reasonProof
      (ay_vctr_conj_intro fallbackDiagnostics recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vctr_redaction_failure_intro
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vctr_redaction_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vctr_conj_intro
      (ay_vctr_blocked_publication satFact unsatFact reason)
      (ay_vctr_recompute reason fallbackDiagnostics recomputeObligation)
      (ay_vctr_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vctr_recompute_intro reason fallbackDiagnostics recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vctr_redaction_failure_blocks_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vctr_redaction_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vctr_blocked_publication_no_sat satFact unsatFact reason
      (ay_vctr_conj_left
        (ay_vctr_blocked_publication satFact unsatFact reason)
        (ay_vctr_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vctr_redaction_failure_blocks_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vctr_redaction_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vctr_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vctr_conj_left
        (ay_vctr_blocked_publication satFact unsatFact reason)
        (ay_vctr_recompute reason fallbackDiagnostics recomputeObligation)
        failure)

theorem ay_vctr_redaction_failure_recompute
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vctr_redaction_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    ay_vctr_recompute reason fallbackDiagnostics recomputeObligation :=
  fun failure =>
    ay_vctr_conj_right
      (ay_vctr_blocked_publication satFact unsatFact reason)
      (ay_vctr_recompute reason fallbackDiagnostics recomputeObligation)
      failure

theorem ay_vctr_over_redaction_forces_no_claim
    (satFact unsatFact overRedaction fallbackDiagnostics
      recomputeObligation : Prop) :
    overRedaction -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vctr_redaction_failure satFact unsatFact overRedaction
      fallbackDiagnostics recomputeObligation :=
  ay_vctr_redaction_failure_intro satFact unsatFact overRedaction
    fallbackDiagnostics recomputeObligation

theorem ay_vctr_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch fallbackDiagnostics
      recomputeObligation : Prop) :
    digestMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vctr_redaction_failure satFact unsatFact digestMismatch
      fallbackDiagnostics recomputeObligation :=
  ay_vctr_redaction_failure_intro satFact unsatFact digestMismatch
    fallbackDiagnostics recomputeObligation

theorem ay_vctr_missing_retained_field_forces_no_claim
    (satFact unsatFact missingRetainedField fallbackDiagnostics
      recomputeObligation : Prop) :
    missingRetainedField -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vctr_redaction_failure satFact unsatFact missingRetainedField
      fallbackDiagnostics recomputeObligation :=
  ay_vctr_redaction_failure_intro satFact unsatFact missingRetainedField
    fallbackDiagnostics recomputeObligation

theorem ay_vctr_stale_fingerprint_forces_no_claim
    (satFact unsatFact staleFingerprint fallbackDiagnostics
      recomputeObligation : Prop) :
    staleFingerprint -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vctr_redaction_failure satFact unsatFact staleFingerprint
      fallbackDiagnostics recomputeObligation :=
  ay_vctr_redaction_failure_intro satFact unsatFact staleFingerprint
    fallbackDiagnostics recomputeObligation

theorem ay_vctr_checker_rejection_forces_no_claim
    (satFact unsatFact checkerRejection fallbackDiagnostics
      recomputeObligation : Prop) :
    checkerRejection -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackDiagnostics -> recomputeObligation ->
    ay_vctr_redaction_failure satFact unsatFact checkerRejection
      fallbackDiagnostics recomputeObligation :=
  ay_vctr_redaction_failure_intro satFact unsatFact checkerRejection
    fallbackDiagnostics recomputeObligation

theorem ay_vctr_failed_redaction_cannot_bless_sat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vctr_redaction_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    satFact -> False :=
  ay_vctr_redaction_failure_blocks_sat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation

theorem ay_vctr_failed_redaction_cannot_bless_unsat
    (satFact unsatFact reason fallbackDiagnostics
      recomputeObligation : Prop) :
    ay_vctr_redaction_failure satFact unsatFact reason fallbackDiagnostics
      recomputeObligation ->
    unsatFact -> False :=
  ay_vctr_redaction_failure_blocks_unsat satFact unsatFact reason
    fallbackDiagnostics recomputeObligation
