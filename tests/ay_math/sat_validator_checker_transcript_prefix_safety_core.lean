-- SAT-COMP validator checker transcript prefix safety core.
--
-- Checker transcript prefixes and cached partial validation may be reused only
-- when transcript digest, replay boundary, certificate digest, solver build
-- evidence, original formula fingerprint, reconstruction map, and fallback
-- branch are accepted.  Full replay remains required for SAT/UNSAT soundness.

def ay_vctp_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vctp_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vctp_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vctp_disj satFact (ay_vctp_disj unsatFact noClaimFact)

def ay_vctp_prefix_contract
    (transcriptDigest replayBoundary certificateDigest solverBuildEvidence
      originalFormulaFingerprint reconstructionMap fallbackBranch : Prop) :
    Prop :=
  ay_vctp_conj transcriptDigest
    (ay_vctp_conj replayBoundary
      (ay_vctp_conj certificateDigest
        (ay_vctp_conj solverBuildEvidence
          (ay_vctp_conj originalFormulaFingerprint
            (ay_vctp_conj reconstructionMap fallbackBranch)))))

def ay_vctp_full_sat_replay
    (prefixContract fullReplay modelEvidence originalModel : Prop) : Prop :=
  ay_vctp_conj prefixContract
    (ay_vctp_conj fullReplay
      (ay_vctp_conj modelEvidence originalModel))

def ay_vctp_full_unsat_replay
    (prefixContract fullReplay proofEvidence originalEmptyClause : Prop) :
    Prop :=
  ay_vctp_conj prefixContract
    (ay_vctp_conj fullReplay
      (ay_vctp_conj proofEvidence originalEmptyClause))

def ay_vctp_no_claim
    (prefixContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vctp_conj prefixContract
    (ay_vctp_conj diagnostic noSemanticClaim)

def ay_vctp_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vctp_conj reason
    (ay_vctp_conj (satFact -> False) (unsatFact -> False))

def ay_vctp_recompute
    (reason fallbackBranch fallbackPath : Prop) : Prop :=
  ay_vctp_conj reason (ay_vctp_conj fallbackBranch fallbackPath)

def ay_vctp_prefix_failure
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) : Prop :=
  ay_vctp_conj
    (ay_vctp_blocked_publication satFact unsatFact reason)
    (ay_vctp_recompute reason fallbackBranch fallbackPath)

theorem ay_vctp_conj_intro (left right : Prop) :
    left -> right -> ay_vctp_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vctp_conj_left (left right : Prop) :
    ay_vctp_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vctp_conj_right (left right : Prop) :
    ay_vctp_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vctp_disj_left (left right : Prop) :
    left -> ay_vctp_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vctp_disj_right (left right : Prop) :
    right -> ay_vctp_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vctp_prefix_contract_intro
    (transcriptDigest replayBoundary certificateDigest solverBuildEvidence
      originalFormulaFingerprint reconstructionMap fallbackBranch : Prop) :
    transcriptDigest -> replayBoundary -> certificateDigest ->
    solverBuildEvidence -> originalFormulaFingerprint -> reconstructionMap ->
    fallbackBranch ->
    ay_vctp_prefix_contract transcriptDigest replayBoundary
      certificateDigest solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch :=
  fun transcriptProof boundaryProof certDigestProof buildProof
      fingerprintProof reconstructionProof fallbackProof =>
    ay_vctp_conj_intro transcriptDigest
      (ay_vctp_conj replayBoundary
        (ay_vctp_conj certificateDigest
          (ay_vctp_conj solverBuildEvidence
            (ay_vctp_conj originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch)))))
      transcriptProof
      (ay_vctp_conj_intro replayBoundary
        (ay_vctp_conj certificateDigest
          (ay_vctp_conj solverBuildEvidence
            (ay_vctp_conj originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch))))
        boundaryProof
        (ay_vctp_conj_intro certificateDigest
          (ay_vctp_conj solverBuildEvidence
            (ay_vctp_conj originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch)))
          certDigestProof
          (ay_vctp_conj_intro solverBuildEvidence
            (ay_vctp_conj originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch))
            buildProof
            (ay_vctp_conj_intro originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch)
              fingerprintProof
              (ay_vctp_conj_intro reconstructionMap fallbackBranch
                reconstructionProof fallbackProof)))))

theorem ay_vctp_prefix_contract_transcript_digest
    (transcriptDigest replayBoundary certificateDigest solverBuildEvidence
      originalFormulaFingerprint reconstructionMap fallbackBranch : Prop) :
    ay_vctp_prefix_contract transcriptDigest replayBoundary
      certificateDigest solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    transcriptDigest :=
  fun contract =>
    ay_vctp_conj_left transcriptDigest
      (ay_vctp_conj replayBoundary
        (ay_vctp_conj certificateDigest
          (ay_vctp_conj solverBuildEvidence
            (ay_vctp_conj originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch)))))
      contract

theorem ay_vctp_prefix_contract_boundary
    (transcriptDigest replayBoundary certificateDigest solverBuildEvidence
      originalFormulaFingerprint reconstructionMap fallbackBranch : Prop) :
    ay_vctp_prefix_contract transcriptDigest replayBoundary
      certificateDigest solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    replayBoundary :=
  fun contract =>
    ay_vctp_conj_right transcriptDigest
      (ay_vctp_conj replayBoundary
        (ay_vctp_conj certificateDigest
          (ay_vctp_conj solverBuildEvidence
            (ay_vctp_conj originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch)))))
      contract replayBoundary
      (fun boundaryProof _tail => boundaryProof)

theorem ay_vctp_prefix_contract_certificate_digest
    (transcriptDigest replayBoundary certificateDigest solverBuildEvidence
      originalFormulaFingerprint reconstructionMap fallbackBranch : Prop) :
    ay_vctp_prefix_contract transcriptDigest replayBoundary
      certificateDigest solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    certificateDigest :=
  fun contract =>
    ay_vctp_conj_right transcriptDigest
      (ay_vctp_conj replayBoundary
        (ay_vctp_conj certificateDigest
          (ay_vctp_conj solverBuildEvidence
            (ay_vctp_conj originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch)))))
      contract certificateDigest
      (fun _boundaryProof tail =>
        tail certificateDigest
          (fun certDigestProof _tail2 => certDigestProof))

theorem ay_vctp_prefix_contract_build
    (transcriptDigest replayBoundary certificateDigest solverBuildEvidence
      originalFormulaFingerprint reconstructionMap fallbackBranch : Prop) :
    ay_vctp_prefix_contract transcriptDigest replayBoundary
      certificateDigest solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    solverBuildEvidence :=
  fun contract =>
    ay_vctp_conj_right transcriptDigest
      (ay_vctp_conj replayBoundary
        (ay_vctp_conj certificateDigest
          (ay_vctp_conj solverBuildEvidence
            (ay_vctp_conj originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch)))))
      contract solverBuildEvidence
      (fun _boundaryProof tail =>
        tail solverBuildEvidence
          (fun _certDigestProof tail2 =>
            tail2 solverBuildEvidence
              (fun buildProof _tail3 => buildProof)))

theorem ay_vctp_prefix_contract_fingerprint
    (transcriptDigest replayBoundary certificateDigest solverBuildEvidence
      originalFormulaFingerprint reconstructionMap fallbackBranch : Prop) :
    ay_vctp_prefix_contract transcriptDigest replayBoundary
      certificateDigest solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    originalFormulaFingerprint :=
  fun contract =>
    ay_vctp_conj_right transcriptDigest
      (ay_vctp_conj replayBoundary
        (ay_vctp_conj certificateDigest
          (ay_vctp_conj solverBuildEvidence
            (ay_vctp_conj originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch)))))
      contract originalFormulaFingerprint
      (fun _boundaryProof tail =>
        tail originalFormulaFingerprint
          (fun _certDigestProof tail2 =>
            tail2 originalFormulaFingerprint
              (fun _buildProof tail3 =>
                tail3 originalFormulaFingerprint
                  (fun fingerprintProof _tail4 => fingerprintProof))))

theorem ay_vctp_prefix_contract_reconstruction
    (transcriptDigest replayBoundary certificateDigest solverBuildEvidence
      originalFormulaFingerprint reconstructionMap fallbackBranch : Prop) :
    ay_vctp_prefix_contract transcriptDigest replayBoundary
      certificateDigest solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    reconstructionMap :=
  fun contract =>
    ay_vctp_conj_right transcriptDigest
      (ay_vctp_conj replayBoundary
        (ay_vctp_conj certificateDigest
          (ay_vctp_conj solverBuildEvidence
            (ay_vctp_conj originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch)))))
      contract reconstructionMap
      (fun _boundaryProof tail =>
        tail reconstructionMap
          (fun _certDigestProof tail2 =>
            tail2 reconstructionMap
              (fun _buildProof tail3 =>
                tail3 reconstructionMap
                  (fun _fingerprintProof tail4 =>
                    tail4 reconstructionMap
                      (fun reconstructionProof _fallbackProof =>
                        reconstructionProof)))))

theorem ay_vctp_prefix_contract_fallback
    (transcriptDigest replayBoundary certificateDigest solverBuildEvidence
      originalFormulaFingerprint reconstructionMap fallbackBranch : Prop) :
    ay_vctp_prefix_contract transcriptDigest replayBoundary
      certificateDigest solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    fallbackBranch :=
  fun contract =>
    ay_vctp_conj_right transcriptDigest
      (ay_vctp_conj replayBoundary
        (ay_vctp_conj certificateDigest
          (ay_vctp_conj solverBuildEvidence
            (ay_vctp_conj originalFormulaFingerprint
              (ay_vctp_conj reconstructionMap fallbackBranch)))))
      contract fallbackBranch
      (fun _boundaryProof tail =>
        tail fallbackBranch
          (fun _certDigestProof tail2 =>
            tail2 fallbackBranch
              (fun _buildProof tail3 =>
                tail3 fallbackBranch
                  (fun _fingerprintProof tail4 =>
                    tail4 fallbackBranch
                      (fun _reconstructionProof fallbackProof =>
                        fallbackProof)))))

theorem ay_vctp_full_sat_replay_intro
    (prefixContract fullReplay modelEvidence originalModel : Prop) :
    prefixContract -> fullReplay -> modelEvidence -> originalModel ->
    ay_vctp_full_sat_replay prefixContract fullReplay modelEvidence
      originalModel :=
  fun contractProof replayProof modelProof originalProof =>
    ay_vctp_conj_intro prefixContract
      (ay_vctp_conj fullReplay
        (ay_vctp_conj modelEvidence originalModel))
      contractProof
      (ay_vctp_conj_intro fullReplay
        (ay_vctp_conj modelEvidence originalModel)
        replayProof
        (ay_vctp_conj_intro modelEvidence originalModel modelProof
          originalProof))

theorem ay_vctp_full_sat_replay_original_model
    (prefixContract fullReplay modelEvidence originalModel : Prop) :
    ay_vctp_full_sat_replay prefixContract fullReplay modelEvidence
      originalModel ->
    originalModel :=
  fun replay =>
    ay_vctp_conj_right prefixContract
      (ay_vctp_conj fullReplay
        (ay_vctp_conj modelEvidence originalModel))
      replay originalModel
      (fun _fullReplay tail =>
        tail originalModel
          (fun _modelProof originalProof => originalProof))

theorem ay_vctp_full_unsat_replay_intro
    (prefixContract fullReplay proofEvidence originalEmptyClause : Prop) :
    prefixContract -> fullReplay -> proofEvidence -> originalEmptyClause ->
    ay_vctp_full_unsat_replay prefixContract fullReplay proofEvidence
      originalEmptyClause :=
  fun contractProof replayProof proofProof emptyProof =>
    ay_vctp_conj_intro prefixContract
      (ay_vctp_conj fullReplay
        (ay_vctp_conj proofEvidence originalEmptyClause))
      contractProof
      (ay_vctp_conj_intro fullReplay
        (ay_vctp_conj proofEvidence originalEmptyClause)
        replayProof
        (ay_vctp_conj_intro proofEvidence originalEmptyClause proofProof
          emptyProof))

theorem ay_vctp_full_unsat_replay_original_empty_clause
    (prefixContract fullReplay proofEvidence originalEmptyClause : Prop) :
    ay_vctp_full_unsat_replay prefixContract fullReplay proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun replay =>
    ay_vctp_conj_right prefixContract
      (ay_vctp_conj fullReplay
        (ay_vctp_conj proofEvidence originalEmptyClause))
      replay originalEmptyClause
      (fun _fullReplay tail =>
        tail originalEmptyClause
          (fun _proofEvidence emptyProof => emptyProof))

theorem ay_vctp_accepted_prefix_sat_after_full_replay
    (prefixContract fullReplay modelEvidence originalModel unsatFact
      noClaimFact : Prop) :
    ay_vctp_full_sat_replay prefixContract fullReplay modelEvidence
      originalModel ->
    ay_vctp_public_result originalModel unsatFact noClaimFact :=
  fun replay =>
    ay_vctp_disj_left originalModel
      (ay_vctp_disj unsatFact noClaimFact)
      (ay_vctp_full_sat_replay_original_model prefixContract fullReplay
        modelEvidence originalModel replay)

theorem ay_vctp_accepted_prefix_unsat_after_full_replay
    (satFact prefixContract fullReplay proofEvidence originalEmptyClause
      noClaimFact : Prop) :
    ay_vctp_full_unsat_replay prefixContract fullReplay proofEvidence
      originalEmptyClause ->
    ay_vctp_public_result satFact originalEmptyClause noClaimFact :=
  fun replay =>
    ay_vctp_disj_right satFact
      (ay_vctp_disj originalEmptyClause noClaimFact)
      (ay_vctp_disj_left originalEmptyClause noClaimFact
        (ay_vctp_full_unsat_replay_original_empty_clause prefixContract
          fullReplay proofEvidence originalEmptyClause replay))

theorem ay_vctp_no_claim_intro
    (prefixContract diagnostic noSemanticClaim : Prop) :
    prefixContract -> diagnostic -> noSemanticClaim ->
    ay_vctp_no_claim prefixContract diagnostic noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_vctp_conj_intro prefixContract
      (ay_vctp_conj diagnostic noSemanticClaim)
      contractProof
      (ay_vctp_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vctp_no_claim_no_semantic_claim
    (prefixContract diagnostic noSemanticClaim : Prop) :
    ay_vctp_no_claim prefixContract diagnostic noSemanticClaim ->
    noSemanticClaim :=
  fun claim =>
    ay_vctp_conj_right prefixContract
      (ay_vctp_conj diagnostic noSemanticClaim)
      claim noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vctp_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vctp_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vctp_conj_intro reason
      (ay_vctp_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vctp_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vctp_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vctp_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vctp_conj_right reason
      (ay_vctp_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vctp_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vctp_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vctp_conj_right reason
      (ay_vctp_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vctp_recompute_intro
    (reason fallbackBranch fallbackPath : Prop) :
    reason -> fallbackBranch -> fallbackPath ->
    ay_vctp_recompute reason fallbackBranch fallbackPath :=
  fun reasonProof fallbackProof pathProof =>
    ay_vctp_conj_intro reason
      (ay_vctp_conj fallbackBranch fallbackPath)
      reasonProof
      (ay_vctp_conj_intro fallbackBranch fallbackPath fallbackProof
        pathProof)

theorem ay_vctp_prefix_failure_intro
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vctp_blocked_publication satFact unsatFact reason ->
    ay_vctp_recompute reason fallbackBranch fallbackPath ->
    ay_vctp_prefix_failure satFact unsatFact reason fallbackBranch
      fallbackPath :=
  fun blocked recompute =>
    ay_vctp_conj_intro
      (ay_vctp_blocked_publication satFact unsatFact reason)
      (ay_vctp_recompute reason fallbackBranch fallbackPath)
      blocked recompute

theorem ay_vctp_prefix_failure_blocks_sat
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vctp_prefix_failure satFact unsatFact reason fallbackBranch
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vctp_blocked_publication_no_sat satFact unsatFact reason
      (ay_vctp_conj_left
        (ay_vctp_blocked_publication satFact unsatFact reason)
        (ay_vctp_recompute reason fallbackBranch fallbackPath)
        failure)

theorem ay_vctp_prefix_failure_blocks_unsat
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vctp_prefix_failure satFact unsatFact reason fallbackBranch
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vctp_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vctp_conj_left
        (ay_vctp_blocked_publication satFact unsatFact reason)
        (ay_vctp_recompute reason fallbackBranch fallbackPath)
        failure)

theorem ay_vctp_prefix_failure_recompute
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vctp_prefix_failure satFact unsatFact reason fallbackBranch
      fallbackPath ->
    ay_vctp_recompute reason fallbackBranch fallbackPath :=
  fun failure =>
    ay_vctp_conj_right
      (ay_vctp_blocked_publication satFact unsatFact reason)
      (ay_vctp_recompute reason fallbackBranch fallbackPath)
      failure

theorem ay_vctp_prefix_truncation_forces_no_claim
    (satFact unsatFact prefixTruncation fallbackBranch fallbackPath : Prop) :
    prefixTruncation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> fallbackPath ->
    ay_vctp_prefix_failure satFact unsatFact prefixTruncation
      fallbackBranch fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vctp_prefix_failure_intro satFact unsatFact prefixTruncation
      fallbackBranch fallbackPath
      (ay_vctp_blocked_publication_intro satFact unsatFact
        prefixTruncation reasonProof blockSat blockUnsat)
      (ay_vctp_recompute_intro prefixTruncation fallbackBranch fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vctp_boundary_drift_forces_no_claim
    (satFact unsatFact boundaryDrift fallbackBranch fallbackPath : Prop) :
    boundaryDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> fallbackPath ->
    ay_vctp_prefix_failure satFact unsatFact boundaryDrift fallbackBranch
      fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vctp_prefix_failure_intro satFact unsatFact boundaryDrift
      fallbackBranch fallbackPath
      (ay_vctp_blocked_publication_intro satFact unsatFact boundaryDrift
        reasonProof blockSat blockUnsat)
      (ay_vctp_recompute_intro boundaryDrift fallbackBranch fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vctp_stale_partial_cannot_bless_sat
    (satFact unsatFact stalePartial fallbackBranch fallbackPath : Prop) :
    ay_vctp_prefix_failure satFact unsatFact stalePartial fallbackBranch
      fallbackPath ->
    satFact -> False :=
  ay_vctp_prefix_failure_blocks_sat satFact unsatFact stalePartial
    fallbackBranch fallbackPath

theorem ay_vctp_stale_partial_cannot_bless_unsat
    (satFact unsatFact stalePartial fallbackBranch fallbackPath : Prop) :
    ay_vctp_prefix_failure satFact unsatFact stalePartial fallbackBranch
      fallbackPath ->
    unsatFact -> False :=
  ay_vctp_prefix_failure_blocks_unsat satFact unsatFact stalePartial
    fallbackBranch fallbackPath
