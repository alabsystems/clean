-- SAT-COMP validator incremental cache epoch core.
--
-- Cached checker/model/proof results may accelerate sequential-main
-- validation only when cache epoch, formula fingerprint, artifact digest,
-- build configuration, and checker transcript evidence agree.

def ay_vice_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vice_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vice_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vice_disj satFact (ay_vice_disj unsatFact noClaimFact)

def ay_vice_epoch_contract
    (epochIds formulaFingerprints artifactDigests buildConfigs
      checkerTranscripts cachedResults fallbackBranch : Prop) : Prop :=
  ay_vice_conj epochIds
    (ay_vice_conj formulaFingerprints
      (ay_vice_conj artifactDigests
        (ay_vice_conj buildConfigs
          (ay_vice_conj checkerTranscripts
            (ay_vice_conj cachedResults fallbackBranch)))))

def ay_vice_sat_publication
    (epochContract modelEvidence originalModel : Prop) : Prop :=
  ay_vice_conj epochContract
    (ay_vice_conj modelEvidence originalModel)

def ay_vice_unsat_publication
    (epochContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vice_conj epochContract
    (ay_vice_conj proofEvidence originalEmptyClause)

def ay_vice_no_claim
    (reason fallbackBranch auditTrail : Prop) : Prop :=
  ay_vice_conj reason (ay_vice_conj fallbackBranch auditTrail)

def ay_vice_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vice_conj reason
    (ay_vice_conj (satFact -> False) (unsatFact -> False))

def ay_vice_recompute
    (reason fallbackBranch recomputeObligation : Prop) : Prop :=
  ay_vice_conj reason
    (ay_vice_conj fallbackBranch recomputeObligation)

def ay_vice_cache_failure
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    Prop :=
  ay_vice_conj
    (ay_vice_blocked_publication satFact unsatFact reason)
    (ay_vice_recompute reason fallbackBranch recomputeObligation)

theorem ay_vice_conj_intro (left right : Prop) :
    left -> right -> ay_vice_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vice_conj_left (left right : Prop) :
    ay_vice_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vice_conj_right (left right : Prop) :
    ay_vice_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vice_disj_left (left right : Prop) :
    left -> ay_vice_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vice_disj_right (left right : Prop) :
    right -> ay_vice_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vice_epoch_contract_intro
    (epochIds formulaFingerprints artifactDigests buildConfigs
      checkerTranscripts cachedResults fallbackBranch : Prop) :
    epochIds -> formulaFingerprints -> artifactDigests -> buildConfigs ->
    checkerTranscripts -> cachedResults -> fallbackBranch ->
    ay_vice_epoch_contract epochIds formulaFingerprints artifactDigests
      buildConfigs checkerTranscripts cachedResults fallbackBranch :=
  fun epochProof formulaProof digestProof buildProof transcriptProof
      cacheProof fallbackProof =>
    ay_vice_conj_intro epochIds
      (ay_vice_conj formulaFingerprints
        (ay_vice_conj artifactDigests
          (ay_vice_conj buildConfigs
            (ay_vice_conj checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch)))))
      epochProof
      (ay_vice_conj_intro formulaFingerprints
        (ay_vice_conj artifactDigests
          (ay_vice_conj buildConfigs
            (ay_vice_conj checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch))))
        formulaProof
        (ay_vice_conj_intro artifactDigests
          (ay_vice_conj buildConfigs
            (ay_vice_conj checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch)))
          digestProof
          (ay_vice_conj_intro buildConfigs
            (ay_vice_conj checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch))
            buildProof
            (ay_vice_conj_intro checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch)
              transcriptProof
              (ay_vice_conj_intro cachedResults fallbackBranch
                cacheProof fallbackProof)))))

theorem ay_vice_epoch_contract_epoch_ids
    (epochIds formulaFingerprints artifactDigests buildConfigs
      checkerTranscripts cachedResults fallbackBranch : Prop) :
    ay_vice_epoch_contract epochIds formulaFingerprints artifactDigests
      buildConfigs checkerTranscripts cachedResults fallbackBranch ->
    epochIds :=
  fun contract =>
    ay_vice_conj_left epochIds
      (ay_vice_conj formulaFingerprints
        (ay_vice_conj artifactDigests
          (ay_vice_conj buildConfigs
            (ay_vice_conj checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch)))))
      contract

theorem ay_vice_epoch_contract_formula_fingerprints
    (epochIds formulaFingerprints artifactDigests buildConfigs
      checkerTranscripts cachedResults fallbackBranch : Prop) :
    ay_vice_epoch_contract epochIds formulaFingerprints artifactDigests
      buildConfigs checkerTranscripts cachedResults fallbackBranch ->
    formulaFingerprints :=
  fun contract =>
    ay_vice_conj_right epochIds
      (ay_vice_conj formulaFingerprints
        (ay_vice_conj artifactDigests
          (ay_vice_conj buildConfigs
            (ay_vice_conj checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch)))))
      contract formulaFingerprints
      (fun formulaProof _tail => formulaProof)

theorem ay_vice_epoch_contract_artifact_digests
    (epochIds formulaFingerprints artifactDigests buildConfigs
      checkerTranscripts cachedResults fallbackBranch : Prop) :
    ay_vice_epoch_contract epochIds formulaFingerprints artifactDigests
      buildConfigs checkerTranscripts cachedResults fallbackBranch ->
    artifactDigests :=
  fun contract =>
    ay_vice_conj_right epochIds
      (ay_vice_conj formulaFingerprints
        (ay_vice_conj artifactDigests
          (ay_vice_conj buildConfigs
            (ay_vice_conj checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch)))))
      contract artifactDigests
      (fun _formulaProof tail =>
        tail artifactDigests
          (fun digestProof _tail2 => digestProof))

theorem ay_vice_epoch_contract_build_configs
    (epochIds formulaFingerprints artifactDigests buildConfigs
      checkerTranscripts cachedResults fallbackBranch : Prop) :
    ay_vice_epoch_contract epochIds formulaFingerprints artifactDigests
      buildConfigs checkerTranscripts cachedResults fallbackBranch ->
    buildConfigs :=
  fun contract =>
    ay_vice_conj_right epochIds
      (ay_vice_conj formulaFingerprints
        (ay_vice_conj artifactDigests
          (ay_vice_conj buildConfigs
            (ay_vice_conj checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch)))))
      contract buildConfigs
      (fun _formulaProof tail =>
        tail buildConfigs
          (fun _digestProof tail2 =>
            tail2 buildConfigs
              (fun buildProof _tail3 => buildProof)))

theorem ay_vice_epoch_contract_checker_transcripts
    (epochIds formulaFingerprints artifactDigests buildConfigs
      checkerTranscripts cachedResults fallbackBranch : Prop) :
    ay_vice_epoch_contract epochIds formulaFingerprints artifactDigests
      buildConfigs checkerTranscripts cachedResults fallbackBranch ->
    checkerTranscripts :=
  fun contract =>
    ay_vice_conj_right epochIds
      (ay_vice_conj formulaFingerprints
        (ay_vice_conj artifactDigests
          (ay_vice_conj buildConfigs
            (ay_vice_conj checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch)))))
      contract checkerTranscripts
      (fun _formulaProof tail =>
        tail checkerTranscripts
          (fun _digestProof tail2 =>
            tail2 checkerTranscripts
              (fun _buildProof tail3 =>
                tail3 checkerTranscripts
                  (fun transcriptProof _tail4 => transcriptProof))))

theorem ay_vice_epoch_contract_cached_results
    (epochIds formulaFingerprints artifactDigests buildConfigs
      checkerTranscripts cachedResults fallbackBranch : Prop) :
    ay_vice_epoch_contract epochIds formulaFingerprints artifactDigests
      buildConfigs checkerTranscripts cachedResults fallbackBranch ->
    cachedResults :=
  fun contract =>
    ay_vice_conj_right epochIds
      (ay_vice_conj formulaFingerprints
        (ay_vice_conj artifactDigests
          (ay_vice_conj buildConfigs
            (ay_vice_conj checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch)))))
      contract cachedResults
      (fun _formulaProof tail =>
        tail cachedResults
          (fun _digestProof tail2 =>
            tail2 cachedResults
              (fun _buildProof tail3 =>
                tail3 cachedResults
                  (fun _transcriptProof tail4 =>
                    tail4 cachedResults
                      (fun cacheProof _fallbackProof => cacheProof)))))

theorem ay_vice_epoch_contract_fallback
    (epochIds formulaFingerprints artifactDigests buildConfigs
      checkerTranscripts cachedResults fallbackBranch : Prop) :
    ay_vice_epoch_contract epochIds formulaFingerprints artifactDigests
      buildConfigs checkerTranscripts cachedResults fallbackBranch ->
    fallbackBranch :=
  fun contract =>
    ay_vice_conj_right epochIds
      (ay_vice_conj formulaFingerprints
        (ay_vice_conj artifactDigests
          (ay_vice_conj buildConfigs
            (ay_vice_conj checkerTranscripts
              (ay_vice_conj cachedResults fallbackBranch)))))
      contract fallbackBranch
      (fun _formulaProof tail =>
        tail fallbackBranch
          (fun _digestProof tail2 =>
            tail2 fallbackBranch
              (fun _buildProof tail3 =>
                tail3 fallbackBranch
                  (fun _transcriptProof tail4 =>
                    tail4 fallbackBranch
                      (fun _cacheProof fallbackProof => fallbackProof)))))

theorem ay_vice_sat_publication_intro
    (epochContract modelEvidence originalModel : Prop) :
    epochContract -> modelEvidence -> originalModel ->
    ay_vice_sat_publication epochContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vice_conj_intro epochContract
      (ay_vice_conj modelEvidence originalModel)
      contractProof
      (ay_vice_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vice_sat_publication_original_model
    (epochContract modelEvidence originalModel : Prop) :
    ay_vice_sat_publication epochContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vice_conj_right epochContract
      (ay_vice_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vice_unsat_publication_intro
    (epochContract proofEvidence originalEmptyClause : Prop) :
    epochContract -> proofEvidence -> originalEmptyClause ->
    ay_vice_unsat_publication epochContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vice_conj_intro epochContract
      (ay_vice_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vice_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vice_unsat_publication_original_empty_clause
    (epochContract proofEvidence originalEmptyClause : Prop) :
    ay_vice_unsat_publication epochContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vice_conj_right epochContract
      (ay_vice_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vice_accepted_epoch_sat_sound
    (epochIds formulaFingerprints artifactDigests buildConfigs
      checkerTranscripts cachedResults fallbackBranch modelEvidence
      originalModel : Prop) :
    ay_vice_epoch_contract epochIds formulaFingerprints artifactDigests
      buildConfigs checkerTranscripts cachedResults fallbackBranch ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vice_accepted_epoch_unsat_sound
    (epochIds formulaFingerprints artifactDigests buildConfigs
      checkerTranscripts cachedResults fallbackBranch proofEvidence
      originalEmptyClause : Prop) :
    ay_vice_epoch_contract epochIds formulaFingerprints artifactDigests
      buildConfigs checkerTranscripts cachedResults fallbackBranch ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vice_no_claim_intro
    (reason fallbackBranch auditTrail : Prop) :
    reason -> fallbackBranch -> auditTrail ->
    ay_vice_no_claim reason fallbackBranch auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vice_conj_intro reason
      (ay_vice_conj fallbackBranch auditTrail)
      reasonProof
      (ay_vice_conj_intro fallbackBranch auditTrail
        fallbackProof auditProof)

theorem ay_vice_no_claim_reason
    (reason fallbackBranch auditTrail : Prop) :
    ay_vice_no_claim reason fallbackBranch auditTrail -> reason :=
  fun noClaim =>
    ay_vice_conj_left reason
      (ay_vice_conj fallbackBranch auditTrail)
      noClaim

theorem ay_vice_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vice_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vice_conj_intro reason
      (ay_vice_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vice_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vice_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vice_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vice_conj_right reason
      (ay_vice_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vice_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vice_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vice_conj_right reason
      (ay_vice_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vice_recompute_intro
    (reason fallbackBranch recomputeObligation : Prop) :
    reason -> fallbackBranch -> recomputeObligation ->
    ay_vice_recompute reason fallbackBranch recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vice_conj_intro reason
      (ay_vice_conj fallbackBranch recomputeObligation)
      reasonProof
      (ay_vice_conj_intro fallbackBranch recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vice_cache_failure_intro
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vice_cache_failure satFact unsatFact reason fallbackBranch
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vice_conj_intro
      (ay_vice_blocked_publication satFact unsatFact reason)
      (ay_vice_recompute reason fallbackBranch recomputeObligation)
      (ay_vice_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vice_recompute_intro reason fallbackBranch recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vice_cache_failure_blocks_sat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vice_cache_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vice_blocked_publication_no_sat satFact unsatFact reason
      (ay_vice_conj_left
        (ay_vice_blocked_publication satFact unsatFact reason)
        (ay_vice_recompute reason fallbackBranch recomputeObligation)
        failure)

theorem ay_vice_cache_failure_blocks_unsat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vice_cache_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vice_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vice_conj_left
        (ay_vice_blocked_publication satFact unsatFact reason)
        (ay_vice_recompute reason fallbackBranch recomputeObligation)
        failure)

theorem ay_vice_cache_failure_recompute
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vice_cache_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    ay_vice_recompute reason fallbackBranch recomputeObligation :=
  fun failure =>
    ay_vice_conj_right
      (ay_vice_blocked_publication satFact unsatFact reason)
      (ay_vice_recompute reason fallbackBranch recomputeObligation)
      failure

theorem ay_vice_epoch_drift_forces_no_claim
    (satFact unsatFact epochDrift fallbackBranch recomputeObligation : Prop) :
    epochDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vice_cache_failure satFact unsatFact epochDrift fallbackBranch
      recomputeObligation :=
  ay_vice_cache_failure_intro satFact unsatFact epochDrift fallbackBranch
    recomputeObligation

theorem ay_vice_stale_digest_forces_no_claim
    (satFact unsatFact staleArtifactDigest fallbackBranch
      recomputeObligation : Prop) :
    staleArtifactDigest -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vice_cache_failure satFact unsatFact staleArtifactDigest
      fallbackBranch recomputeObligation :=
  ay_vice_cache_failure_intro satFact unsatFact staleArtifactDigest
    fallbackBranch recomputeObligation

theorem ay_vice_formula_mismatch_forces_no_claim
    (satFact unsatFact formulaMismatch fallbackBranch
      recomputeObligation : Prop) :
    formulaMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vice_cache_failure satFact unsatFact formulaMismatch fallbackBranch
      recomputeObligation :=
  ay_vice_cache_failure_intro satFact unsatFact formulaMismatch
    fallbackBranch recomputeObligation

theorem ay_vice_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackBranch recomputeObligation : Prop) :
    buildMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vice_cache_failure satFact unsatFact buildMismatch fallbackBranch
      recomputeObligation :=
  ay_vice_cache_failure_intro satFact unsatFact buildMismatch fallbackBranch
    recomputeObligation

theorem ay_vice_missing_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackBranch
      recomputeObligation : Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vice_cache_failure satFact unsatFact missingTranscript fallbackBranch
      recomputeObligation :=
  ay_vice_cache_failure_intro satFact unsatFact missingTranscript
    fallbackBranch recomputeObligation

theorem ay_vice_failed_cache_cannot_bless_sat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vice_cache_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    satFact -> False :=
  ay_vice_cache_failure_blocks_sat satFact unsatFact reason fallbackBranch
    recomputeObligation

theorem ay_vice_failed_cache_cannot_bless_unsat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vice_cache_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    unsatFact -> False :=
  ay_vice_cache_failure_blocks_unsat satFact unsatFact reason fallbackBranch
    recomputeObligation
