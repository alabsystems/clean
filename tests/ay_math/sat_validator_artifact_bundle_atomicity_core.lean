-- SAT-COMP validator artifact bundle atomicity core.
--
-- A result artifact bundle is publishable only when result kind, exit code,
-- certificate digest, checker transcript, solver build evidence, formula
-- fingerprint, reconstruction map, and no-claim/recompute branch are
-- atomically consistent.

def ay_vaba_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vaba_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vaba_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vaba_disj satFact (ay_vaba_disj unsatFact noClaimFact)

def ay_vaba_atomic_contract
    (resultKind exitCode certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) : Prop :=
  ay_vaba_conj resultKind
    (ay_vaba_conj exitCode
      (ay_vaba_conj certificateDigest
        (ay_vaba_conj checkerTranscript
          (ay_vaba_conj solverBuildEvidence
            (ay_vaba_conj originalFormulaFingerprint
              (ay_vaba_conj reconstructionMap fallbackBranch))))))

def ay_vaba_sat_bundle
    (atomicContract modelEvidence originalModel : Prop) : Prop :=
  ay_vaba_conj atomicContract
    (ay_vaba_conj modelEvidence originalModel)

def ay_vaba_unsat_bundle
    (atomicContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vaba_conj atomicContract
    (ay_vaba_conj proofEvidence originalEmptyClause)

def ay_vaba_no_claim_bundle
    (atomicContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vaba_conj atomicContract
    (ay_vaba_conj diagnostic noSemanticClaim)

def ay_vaba_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vaba_conj reason
    (ay_vaba_conj (satFact -> False) (unsatFact -> False))

def ay_vaba_recompute
    (reason fallbackBranch fallbackPath : Prop) : Prop :=
  ay_vaba_conj reason (ay_vaba_conj fallbackBranch fallbackPath)

def ay_vaba_atomic_failure
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) : Prop :=
  ay_vaba_conj
    (ay_vaba_blocked_publication satFact unsatFact reason)
    (ay_vaba_recompute reason fallbackBranch fallbackPath)

theorem ay_vaba_conj_intro (left right : Prop) :
    left -> right -> ay_vaba_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vaba_conj_left (left right : Prop) :
    ay_vaba_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vaba_conj_right (left right : Prop) :
    ay_vaba_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vaba_disj_left (left right : Prop) :
    left -> ay_vaba_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vaba_disj_right (left right : Prop) :
    right -> ay_vaba_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vaba_atomic_contract_intro
    (resultKind exitCode certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    resultKind -> exitCode -> certificateDigest -> checkerTranscript ->
    solverBuildEvidence -> originalFormulaFingerprint -> reconstructionMap ->
    fallbackBranch ->
    ay_vaba_atomic_contract resultKind exitCode certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch :=
  fun kindProof exitProof digestProof transcriptProof buildProof
      fingerprintProof reconstructionProof fallbackProof =>
    ay_vaba_conj_intro resultKind
      (ay_vaba_conj exitCode
        (ay_vaba_conj certificateDigest
          (ay_vaba_conj checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch))))))
      kindProof
      (ay_vaba_conj_intro exitCode
        (ay_vaba_conj certificateDigest
          (ay_vaba_conj checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch)))))
        exitProof
        (ay_vaba_conj_intro certificateDigest
          (ay_vaba_conj checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch))))
          digestProof
          (ay_vaba_conj_intro checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch)))
            transcriptProof
            (ay_vaba_conj_intro solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch))
              buildProof
              (ay_vaba_conj_intro originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch)
                fingerprintProof
                (ay_vaba_conj_intro reconstructionMap fallbackBranch
                  reconstructionProof fallbackProof))))))

theorem ay_vaba_atomic_contract_kind
    (resultKind exitCode certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vaba_atomic_contract resultKind exitCode certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    resultKind :=
  fun contract =>
    ay_vaba_conj_left resultKind
      (ay_vaba_conj exitCode
        (ay_vaba_conj certificateDigest
          (ay_vaba_conj checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch))))))
      contract

theorem ay_vaba_atomic_contract_exit
    (resultKind exitCode certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vaba_atomic_contract resultKind exitCode certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    exitCode :=
  fun contract =>
    ay_vaba_conj_right resultKind
      (ay_vaba_conj exitCode
        (ay_vaba_conj certificateDigest
          (ay_vaba_conj checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch))))))
      contract exitCode
      (fun exitProof _tail => exitProof)

theorem ay_vaba_atomic_contract_digest
    (resultKind exitCode certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vaba_atomic_contract resultKind exitCode certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    certificateDigest :=
  fun contract =>
    ay_vaba_conj_right resultKind
      (ay_vaba_conj exitCode
        (ay_vaba_conj certificateDigest
          (ay_vaba_conj checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch))))))
      contract certificateDigest
      (fun _exitProof tail =>
        tail certificateDigest (fun digestProof _tail2 => digestProof))

theorem ay_vaba_atomic_contract_transcript
    (resultKind exitCode certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vaba_atomic_contract resultKind exitCode certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    checkerTranscript :=
  fun contract =>
    ay_vaba_conj_right resultKind
      (ay_vaba_conj exitCode
        (ay_vaba_conj certificateDigest
          (ay_vaba_conj checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch))))))
      contract checkerTranscript
      (fun _exitProof tail =>
        tail checkerTranscript
          (fun _digestProof tail2 =>
            tail2 checkerTranscript
              (fun transcriptProof _tail3 => transcriptProof)))

theorem ay_vaba_atomic_contract_build
    (resultKind exitCode certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vaba_atomic_contract resultKind exitCode certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    solverBuildEvidence :=
  fun contract =>
    ay_vaba_conj_right resultKind
      (ay_vaba_conj exitCode
        (ay_vaba_conj certificateDigest
          (ay_vaba_conj checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch))))))
      contract solverBuildEvidence
      (fun _exitProof tail =>
        tail solverBuildEvidence
          (fun _digestProof tail2 =>
            tail2 solverBuildEvidence
              (fun _transcriptProof tail3 =>
                tail3 solverBuildEvidence
                  (fun buildProof _tail4 => buildProof))))

theorem ay_vaba_atomic_contract_fingerprint
    (resultKind exitCode certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vaba_atomic_contract resultKind exitCode certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    originalFormulaFingerprint :=
  fun contract =>
    ay_vaba_conj_right resultKind
      (ay_vaba_conj exitCode
        (ay_vaba_conj certificateDigest
          (ay_vaba_conj checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch))))))
      contract originalFormulaFingerprint
      (fun _exitProof tail =>
        tail originalFormulaFingerprint
          (fun _digestProof tail2 =>
            tail2 originalFormulaFingerprint
              (fun _transcriptProof tail3 =>
                tail3 originalFormulaFingerprint
                  (fun _buildProof tail4 =>
                    tail4 originalFormulaFingerprint
                      (fun fingerprintProof _tail5 =>
                        fingerprintProof)))))

theorem ay_vaba_atomic_contract_reconstruction
    (resultKind exitCode certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vaba_atomic_contract resultKind exitCode certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    reconstructionMap :=
  fun contract =>
    ay_vaba_conj_right resultKind
      (ay_vaba_conj exitCode
        (ay_vaba_conj certificateDigest
          (ay_vaba_conj checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch))))))
      contract reconstructionMap
      (fun _exitProof tail =>
        tail reconstructionMap
          (fun _digestProof tail2 =>
            tail2 reconstructionMap
              (fun _transcriptProof tail3 =>
                tail3 reconstructionMap
                  (fun _buildProof tail4 =>
                    tail4 reconstructionMap
                      (fun _fingerprintProof tail5 =>
                        tail5 reconstructionMap
                          (fun reconstructionProof _fallbackProof =>
                            reconstructionProof))))))

theorem ay_vaba_atomic_contract_fallback
    (resultKind exitCode certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vaba_atomic_contract resultKind exitCode certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    fallbackBranch :=
  fun contract =>
    ay_vaba_conj_right resultKind
      (ay_vaba_conj exitCode
        (ay_vaba_conj certificateDigest
          (ay_vaba_conj checkerTranscript
            (ay_vaba_conj solverBuildEvidence
              (ay_vaba_conj originalFormulaFingerprint
                (ay_vaba_conj reconstructionMap fallbackBranch))))))
      contract fallbackBranch
      (fun _exitProof tail =>
        tail fallbackBranch
          (fun _digestProof tail2 =>
            tail2 fallbackBranch
              (fun _transcriptProof tail3 =>
                tail3 fallbackBranch
                  (fun _buildProof tail4 =>
                    tail4 fallbackBranch
                      (fun _fingerprintProof tail5 =>
                        tail5 fallbackBranch
                          (fun _reconstructionProof fallbackProof =>
                            fallbackProof))))))

theorem ay_vaba_sat_bundle_intro
    (atomicContract modelEvidence originalModel : Prop) :
    atomicContract -> modelEvidence -> originalModel ->
    ay_vaba_sat_bundle atomicContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vaba_conj_intro atomicContract
      (ay_vaba_conj modelEvidence originalModel)
      contractProof
      (ay_vaba_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vaba_sat_bundle_contract
    (atomicContract modelEvidence originalModel : Prop) :
    ay_vaba_sat_bundle atomicContract modelEvidence originalModel ->
    atomicContract :=
  fun bundle =>
    ay_vaba_conj_left atomicContract
      (ay_vaba_conj modelEvidence originalModel) bundle

theorem ay_vaba_sat_bundle_original_model
    (atomicContract modelEvidence originalModel : Prop) :
    ay_vaba_sat_bundle atomicContract modelEvidence originalModel ->
    originalModel :=
  fun bundle =>
    ay_vaba_conj_right atomicContract
      (ay_vaba_conj modelEvidence originalModel)
      bundle originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vaba_unsat_bundle_intro
    (atomicContract proofEvidence originalEmptyClause : Prop) :
    atomicContract -> proofEvidence -> originalEmptyClause ->
    ay_vaba_unsat_bundle atomicContract proofEvidence originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vaba_conj_intro atomicContract
      (ay_vaba_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vaba_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vaba_unsat_bundle_contract
    (atomicContract proofEvidence originalEmptyClause : Prop) :
    ay_vaba_unsat_bundle atomicContract proofEvidence originalEmptyClause ->
    atomicContract :=
  fun bundle =>
    ay_vaba_conj_left atomicContract
      (ay_vaba_conj proofEvidence originalEmptyClause) bundle

theorem ay_vaba_unsat_bundle_original_empty_clause
    (atomicContract proofEvidence originalEmptyClause : Prop) :
    ay_vaba_unsat_bundle atomicContract proofEvidence originalEmptyClause ->
    originalEmptyClause :=
  fun bundle =>
    ay_vaba_conj_right atomicContract
      (ay_vaba_conj proofEvidence originalEmptyClause)
      bundle originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vaba_no_claim_bundle_intro
    (atomicContract diagnostic noSemanticClaim : Prop) :
    atomicContract -> diagnostic -> noSemanticClaim ->
    ay_vaba_no_claim_bundle atomicContract diagnostic noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_vaba_conj_intro atomicContract
      (ay_vaba_conj diagnostic noSemanticClaim)
      contractProof
      (ay_vaba_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vaba_no_claim_bundle_no_semantic_claim
    (atomicContract diagnostic noSemanticClaim : Prop) :
    ay_vaba_no_claim_bundle atomicContract diagnostic noSemanticClaim ->
    noSemanticClaim :=
  fun bundle =>
    ay_vaba_conj_right atomicContract
      (ay_vaba_conj diagnostic noSemanticClaim)
      bundle noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vaba_accepted_sat_bundle_preserves_soundness
    (atomicContract modelEvidence originalModel unsatFact noClaimFact :
      Prop) :
    ay_vaba_sat_bundle atomicContract modelEvidence originalModel ->
    ay_vaba_public_result originalModel unsatFact noClaimFact :=
  fun bundle =>
    ay_vaba_disj_left originalModel
      (ay_vaba_disj unsatFact noClaimFact)
      (ay_vaba_sat_bundle_original_model atomicContract modelEvidence
        originalModel bundle)

theorem ay_vaba_accepted_unsat_bundle_preserves_soundness
    (satFact atomicContract proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_vaba_unsat_bundle atomicContract proofEvidence originalEmptyClause ->
    ay_vaba_public_result satFact originalEmptyClause noClaimFact :=
  fun bundle =>
    ay_vaba_disj_right satFact
      (ay_vaba_disj originalEmptyClause noClaimFact)
      (ay_vaba_disj_left originalEmptyClause noClaimFact
        (ay_vaba_unsat_bundle_original_empty_clause atomicContract
          proofEvidence originalEmptyClause bundle))

theorem ay_vaba_no_claim_bundle_public_no_claim
    (satFact unsatFact atomicContract diagnostic noSemanticClaim : Prop) :
    ay_vaba_no_claim_bundle atomicContract diagnostic noSemanticClaim ->
    ay_vaba_public_result satFact unsatFact noSemanticClaim :=
  fun bundle =>
    ay_vaba_disj_right satFact
      (ay_vaba_disj unsatFact noSemanticClaim)
      (ay_vaba_disj_right unsatFact noSemanticClaim
        (ay_vaba_no_claim_bundle_no_semantic_claim atomicContract
          diagnostic noSemanticClaim bundle))

theorem ay_vaba_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vaba_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vaba_conj_intro reason
      (ay_vaba_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vaba_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vaba_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vaba_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vaba_conj_right reason
      (ay_vaba_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vaba_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vaba_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vaba_conj_right reason
      (ay_vaba_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vaba_recompute_intro
    (reason fallbackBranch fallbackPath : Prop) :
    reason -> fallbackBranch -> fallbackPath ->
    ay_vaba_recompute reason fallbackBranch fallbackPath :=
  fun reasonProof fallbackProof pathProof =>
    ay_vaba_conj_intro reason
      (ay_vaba_conj fallbackBranch fallbackPath)
      reasonProof
      (ay_vaba_conj_intro fallbackBranch fallbackPath fallbackProof
        pathProof)

theorem ay_vaba_atomic_failure_intro
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vaba_blocked_publication satFact unsatFact reason ->
    ay_vaba_recompute reason fallbackBranch fallbackPath ->
    ay_vaba_atomic_failure satFact unsatFact reason fallbackBranch
      fallbackPath :=
  fun blocked recompute =>
    ay_vaba_conj_intro
      (ay_vaba_blocked_publication satFact unsatFact reason)
      (ay_vaba_recompute reason fallbackBranch fallbackPath)
      blocked recompute

theorem ay_vaba_atomic_failure_blocks_sat
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vaba_atomic_failure satFact unsatFact reason fallbackBranch
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vaba_blocked_publication_no_sat satFact unsatFact reason
      (ay_vaba_conj_left
        (ay_vaba_blocked_publication satFact unsatFact reason)
        (ay_vaba_recompute reason fallbackBranch fallbackPath)
        failure)

theorem ay_vaba_atomic_failure_blocks_unsat
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vaba_atomic_failure satFact unsatFact reason fallbackBranch
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vaba_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vaba_conj_left
        (ay_vaba_blocked_publication satFact unsatFact reason)
        (ay_vaba_recompute reason fallbackBranch fallbackPath)
        failure)

theorem ay_vaba_atomic_failure_recompute
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vaba_atomic_failure satFact unsatFact reason fallbackBranch
      fallbackPath ->
    ay_vaba_recompute reason fallbackBranch fallbackPath :=
  fun failure =>
    ay_vaba_conj_right
      (ay_vaba_blocked_publication satFact unsatFact reason)
      (ay_vaba_recompute reason fallbackBranch fallbackPath)
      failure

theorem ay_vaba_partial_bundle_forces_no_claim
    (satFact unsatFact partialBundle fallbackBranch fallbackPath : Prop) :
    partialBundle -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> fallbackPath ->
    ay_vaba_atomic_failure satFact unsatFact partialBundle fallbackBranch
      fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vaba_atomic_failure_intro satFact unsatFact partialBundle
      fallbackBranch fallbackPath
      (ay_vaba_blocked_publication_intro satFact unsatFact partialBundle
        reasonProof blockSat blockUnsat)
      (ay_vaba_recompute_intro partialBundle fallbackBranch fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vaba_mixed_bundle_forces_no_claim
    (satFact unsatFact mixedBundle fallbackBranch fallbackPath : Prop) :
    mixedBundle -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> fallbackPath ->
    ay_vaba_atomic_failure satFact unsatFact mixedBundle fallbackBranch
      fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vaba_atomic_failure_intro satFact unsatFact mixedBundle
      fallbackBranch fallbackPath
      (ay_vaba_blocked_publication_intro satFact unsatFact mixedBundle
        reasonProof blockSat blockUnsat)
      (ay_vaba_recompute_intro mixedBundle fallbackBranch fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vaba_cross_run_splicing_forces_no_claim
    (satFact unsatFact crossRunSplicing fallbackBranch fallbackPath : Prop) :
    crossRunSplicing -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> fallbackPath ->
    ay_vaba_atomic_failure satFact unsatFact crossRunSplicing
      fallbackBranch fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vaba_atomic_failure_intro satFact unsatFact crossRunSplicing
      fallbackBranch fallbackPath
      (ay_vaba_blocked_publication_intro satFact unsatFact
        crossRunSplicing reasonProof blockSat blockUnsat)
      (ay_vaba_recompute_intro crossRunSplicing fallbackBranch fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vaba_cross_run_splicing_cannot_bless_sat
    (satFact unsatFact crossRunSplicing fallbackBranch fallbackPath : Prop) :
    ay_vaba_atomic_failure satFact unsatFact crossRunSplicing
      fallbackBranch fallbackPath ->
    satFact -> False :=
  ay_vaba_atomic_failure_blocks_sat satFact unsatFact crossRunSplicing
    fallbackBranch fallbackPath

theorem ay_vaba_cross_run_splicing_cannot_bless_unsat
    (satFact unsatFact crossRunSplicing fallbackBranch fallbackPath : Prop) :
    ay_vaba_atomic_failure satFact unsatFact crossRunSplicing
      fallbackBranch fallbackPath ->
    unsatFact -> False :=
  ay_vaba_atomic_failure_blocks_unsat satFact unsatFact crossRunSplicing
    fallbackBranch fallbackPath
