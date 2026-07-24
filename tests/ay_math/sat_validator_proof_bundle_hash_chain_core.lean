-- SAT-COMP validator proof bundle hash-chain core.
--
-- Streamed proof/model bundles may publish SAT/UNSAT only when hash-chain
-- roots, chunk digests, certificate digest, checker transcript, solver
-- build/config evidence, original formula fingerprint, reconstruction map,
-- and fallback/no-claim branch are accepted.

def ay_vpbh_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vpbh_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vpbh_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vpbh_disj satFact (ay_vpbh_disj unsatFact noClaimFact)

def ay_vpbh_hash_chain_contract
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) : Prop :=
  ay_vpbh_conj chainRoot
    (ay_vpbh_conj chunkDigests
      (ay_vpbh_conj certificateDigest
        (ay_vpbh_conj checkerTranscript
          (ay_vpbh_conj solverBuildConfig
            (ay_vpbh_conj originalFormulaFingerprint
              (ay_vpbh_conj reconstructionMap fallbackBranch))))))

def ay_vpbh_sat_publication
    (hashChainContract modelCertificate originalModel : Prop) : Prop :=
  ay_vpbh_conj hashChainContract
    (ay_vpbh_conj modelCertificate originalModel)

def ay_vpbh_unsat_publication
    (hashChainContract proofCertificate originalEmptyClause : Prop) : Prop :=
  ay_vpbh_conj hashChainContract
    (ay_vpbh_conj proofCertificate originalEmptyClause)

def ay_vpbh_no_claim
    (reason fallbackBranch auditTrail : Prop) : Prop :=
  ay_vpbh_conj reason (ay_vpbh_conj fallbackBranch auditTrail)

def ay_vpbh_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vpbh_conj reason
    (ay_vpbh_conj (satFact -> False) (unsatFact -> False))

def ay_vpbh_recompute
    (reason fallbackBranch recomputeObligation : Prop) : Prop :=
  ay_vpbh_conj reason
    (ay_vpbh_conj fallbackBranch recomputeObligation)

def ay_vpbh_chain_failure
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    Prop :=
  ay_vpbh_conj
    (ay_vpbh_blocked_publication satFact unsatFact reason)
    (ay_vpbh_recompute reason fallbackBranch recomputeObligation)

theorem ay_vpbh_conj_intro (left right : Prop) :
    left -> right -> ay_vpbh_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vpbh_conj_left (left right : Prop) :
    ay_vpbh_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vpbh_conj_right (left right : Prop) :
    ay_vpbh_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vpbh_disj_left (left right : Prop) :
    left -> ay_vpbh_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vpbh_disj_right (left right : Prop) :
    right -> ay_vpbh_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vpbh_hash_chain_contract_intro
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    chainRoot -> chunkDigests -> certificateDigest -> checkerTranscript ->
    solverBuildConfig -> originalFormulaFingerprint -> reconstructionMap ->
    fallbackBranch ->
    ay_vpbh_hash_chain_contract chainRoot chunkDigests certificateDigest
      checkerTranscript solverBuildConfig originalFormulaFingerprint
      reconstructionMap fallbackBranch :=
  fun rootProof chunkProof certProof transcriptProof buildProof
      fingerprintProof reconstructionProof fallbackProof =>
    ay_vpbh_conj_intro chainRoot
      (ay_vpbh_conj chunkDigests
        (ay_vpbh_conj certificateDigest
          (ay_vpbh_conj checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch))))))
      rootProof
      (ay_vpbh_conj_intro chunkDigests
        (ay_vpbh_conj certificateDigest
          (ay_vpbh_conj checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch)))))
        chunkProof
        (ay_vpbh_conj_intro certificateDigest
          (ay_vpbh_conj checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch))))
          certProof
          (ay_vpbh_conj_intro checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch)))
            transcriptProof
            (ay_vpbh_conj_intro solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch))
              buildProof
              (ay_vpbh_conj_intro originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch)
                fingerprintProof
                (ay_vpbh_conj_intro reconstructionMap fallbackBranch
                  reconstructionProof fallbackProof))))))

theorem ay_vpbh_hash_chain_contract_root
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vpbh_hash_chain_contract chainRoot chunkDigests certificateDigest
      checkerTranscript solverBuildConfig originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    chainRoot :=
  fun contract =>
    ay_vpbh_conj_left chainRoot
      (ay_vpbh_conj chunkDigests
        (ay_vpbh_conj certificateDigest
          (ay_vpbh_conj checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch))))))
      contract

theorem ay_vpbh_hash_chain_contract_chunks
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vpbh_hash_chain_contract chainRoot chunkDigests certificateDigest
      checkerTranscript solverBuildConfig originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    chunkDigests :=
  fun contract =>
    ay_vpbh_conj_right chainRoot
      (ay_vpbh_conj chunkDigests
        (ay_vpbh_conj certificateDigest
          (ay_vpbh_conj checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch))))))
      contract chunkDigests
      (fun chunkProof _tail => chunkProof)

theorem ay_vpbh_hash_chain_contract_certificate_digest
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vpbh_hash_chain_contract chainRoot chunkDigests certificateDigest
      checkerTranscript solverBuildConfig originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    certificateDigest :=
  fun contract =>
    ay_vpbh_conj_right chainRoot
      (ay_vpbh_conj chunkDigests
        (ay_vpbh_conj certificateDigest
          (ay_vpbh_conj checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch))))))
      contract certificateDigest
      (fun _chunkProof tail =>
        tail certificateDigest
          (fun certProof _tail2 => certProof))

theorem ay_vpbh_hash_chain_contract_checker_transcript
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vpbh_hash_chain_contract chainRoot chunkDigests certificateDigest
      checkerTranscript solverBuildConfig originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    checkerTranscript :=
  fun contract =>
    ay_vpbh_conj_right chainRoot
      (ay_vpbh_conj chunkDigests
        (ay_vpbh_conj certificateDigest
          (ay_vpbh_conj checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch))))))
      contract checkerTranscript
      (fun _chunkProof tail =>
        tail checkerTranscript
          (fun _certProof tail2 =>
            tail2 checkerTranscript
              (fun transcriptProof _tail3 => transcriptProof)))

theorem ay_vpbh_hash_chain_contract_build_config
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vpbh_hash_chain_contract chainRoot chunkDigests certificateDigest
      checkerTranscript solverBuildConfig originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    solverBuildConfig :=
  fun contract =>
    ay_vpbh_conj_right chainRoot
      (ay_vpbh_conj chunkDigests
        (ay_vpbh_conj certificateDigest
          (ay_vpbh_conj checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch))))))
      contract solverBuildConfig
      (fun _chunkProof tail =>
        tail solverBuildConfig
          (fun _certProof tail2 =>
            tail2 solverBuildConfig
              (fun _transcriptProof tail3 =>
                tail3 solverBuildConfig
                  (fun buildProof _tail4 => buildProof))))

theorem ay_vpbh_hash_chain_contract_formula_fingerprint
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vpbh_hash_chain_contract chainRoot chunkDigests certificateDigest
      checkerTranscript solverBuildConfig originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    originalFormulaFingerprint :=
  fun contract =>
    ay_vpbh_conj_right chainRoot
      (ay_vpbh_conj chunkDigests
        (ay_vpbh_conj certificateDigest
          (ay_vpbh_conj checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch))))))
      contract originalFormulaFingerprint
      (fun _chunkProof tail =>
        tail originalFormulaFingerprint
          (fun _certProof tail2 =>
            tail2 originalFormulaFingerprint
              (fun _transcriptProof tail3 =>
                tail3 originalFormulaFingerprint
                  (fun _buildProof tail4 =>
                    tail4 originalFormulaFingerprint
                      (fun fingerprintProof _tail5 => fingerprintProof)))))

theorem ay_vpbh_hash_chain_contract_reconstruction
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vpbh_hash_chain_contract chainRoot chunkDigests certificateDigest
      checkerTranscript solverBuildConfig originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    reconstructionMap :=
  fun contract =>
    ay_vpbh_conj_right chainRoot
      (ay_vpbh_conj chunkDigests
        (ay_vpbh_conj certificateDigest
          (ay_vpbh_conj checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch))))))
      contract reconstructionMap
      (fun _chunkProof tail =>
        tail reconstructionMap
          (fun _certProof tail2 =>
            tail2 reconstructionMap
              (fun _transcriptProof tail3 =>
                tail3 reconstructionMap
                  (fun _buildProof tail4 =>
                    tail4 reconstructionMap
                      (fun _fingerprintProof tail5 =>
                        tail5 reconstructionMap
                          (fun reconstructionProof _fallbackProof =>
                            reconstructionProof))))))

theorem ay_vpbh_hash_chain_contract_fallback
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vpbh_hash_chain_contract chainRoot chunkDigests certificateDigest
      checkerTranscript solverBuildConfig originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    fallbackBranch :=
  fun contract =>
    ay_vpbh_conj_right chainRoot
      (ay_vpbh_conj chunkDigests
        (ay_vpbh_conj certificateDigest
          (ay_vpbh_conj checkerTranscript
            (ay_vpbh_conj solverBuildConfig
              (ay_vpbh_conj originalFormulaFingerprint
                (ay_vpbh_conj reconstructionMap fallbackBranch))))))
      contract fallbackBranch
      (fun _chunkProof tail =>
        tail fallbackBranch
          (fun _certProof tail2 =>
            tail2 fallbackBranch
              (fun _transcriptProof tail3 =>
                tail3 fallbackBranch
                  (fun _buildProof tail4 =>
                    tail4 fallbackBranch
                      (fun _fingerprintProof tail5 =>
                        tail5 fallbackBranch
                          (fun _reconstructionProof fallbackProof =>
                            fallbackProof))))))

theorem ay_vpbh_sat_publication_intro
    (hashChainContract modelCertificate originalModel : Prop) :
    hashChainContract -> modelCertificate -> originalModel ->
    ay_vpbh_sat_publication hashChainContract modelCertificate originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vpbh_conj_intro hashChainContract
      (ay_vpbh_conj modelCertificate originalModel)
      contractProof
      (ay_vpbh_conj_intro modelCertificate originalModel
        modelProof originalProof)

theorem ay_vpbh_sat_publication_original_model
    (hashChainContract modelCertificate originalModel : Prop) :
    ay_vpbh_sat_publication hashChainContract modelCertificate originalModel ->
    originalModel :=
  fun publication =>
    ay_vpbh_conj_right hashChainContract
      (ay_vpbh_conj modelCertificate originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vpbh_unsat_publication_intro
    (hashChainContract proofCertificate originalEmptyClause : Prop) :
    hashChainContract -> proofCertificate -> originalEmptyClause ->
    ay_vpbh_unsat_publication hashChainContract proofCertificate
      originalEmptyClause :=
  fun contractProof proofCert originalProof =>
    ay_vpbh_conj_intro hashChainContract
      (ay_vpbh_conj proofCertificate originalEmptyClause)
      contractProof
      (ay_vpbh_conj_intro proofCertificate originalEmptyClause
        proofCert originalProof)

theorem ay_vpbh_unsat_publication_original_empty_clause
    (hashChainContract proofCertificate originalEmptyClause : Prop) :
    ay_vpbh_unsat_publication hashChainContract proofCertificate
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vpbh_conj_right hashChainContract
      (ay_vpbh_conj proofCertificate originalEmptyClause)
      publication originalEmptyClause
      (fun _proofCert originalProof => originalProof)

theorem ay_vpbh_accepted_hash_chain_sat_sound
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch modelCertificate originalModel : Prop) :
    ay_vpbh_hash_chain_contract chainRoot chunkDigests certificateDigest
      checkerTranscript solverBuildConfig originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    modelCertificate -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vpbh_accepted_hash_chain_unsat_sound
    (chainRoot chunkDigests certificateDigest checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch proofCertificate originalEmptyClause : Prop) :
    ay_vpbh_hash_chain_contract chainRoot chunkDigests certificateDigest
      checkerTranscript solverBuildConfig originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    proofCertificate -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofCert originalProof => originalProof

theorem ay_vpbh_no_claim_intro
    (reason fallbackBranch auditTrail : Prop) :
    reason -> fallbackBranch -> auditTrail ->
    ay_vpbh_no_claim reason fallbackBranch auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vpbh_conj_intro reason
      (ay_vpbh_conj fallbackBranch auditTrail)
      reasonProof
      (ay_vpbh_conj_intro fallbackBranch auditTrail
        fallbackProof auditProof)

theorem ay_vpbh_no_claim_reason
    (reason fallbackBranch auditTrail : Prop) :
    ay_vpbh_no_claim reason fallbackBranch auditTrail -> reason :=
  fun noClaim =>
    ay_vpbh_conj_left reason
      (ay_vpbh_conj fallbackBranch auditTrail)
      noClaim

theorem ay_vpbh_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vpbh_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vpbh_conj_intro reason
      (ay_vpbh_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vpbh_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vpbh_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vpbh_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vpbh_conj_right reason
      (ay_vpbh_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vpbh_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vpbh_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vpbh_conj_right reason
      (ay_vpbh_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vpbh_recompute_intro
    (reason fallbackBranch recomputeObligation : Prop) :
    reason -> fallbackBranch -> recomputeObligation ->
    ay_vpbh_recompute reason fallbackBranch recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vpbh_conj_intro reason
      (ay_vpbh_conj fallbackBranch recomputeObligation)
      reasonProof
      (ay_vpbh_conj_intro fallbackBranch recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vpbh_chain_failure_intro
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vpbh_chain_failure satFact unsatFact reason fallbackBranch
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vpbh_conj_intro
      (ay_vpbh_blocked_publication satFact unsatFact reason)
      (ay_vpbh_recompute reason fallbackBranch recomputeObligation)
      (ay_vpbh_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vpbh_recompute_intro reason fallbackBranch recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vpbh_chain_failure_blocks_sat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vpbh_chain_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vpbh_blocked_publication_no_sat satFact unsatFact reason
      (ay_vpbh_conj_left
        (ay_vpbh_blocked_publication satFact unsatFact reason)
        (ay_vpbh_recompute reason fallbackBranch recomputeObligation)
        failure)

theorem ay_vpbh_chain_failure_blocks_unsat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vpbh_chain_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vpbh_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vpbh_conj_left
        (ay_vpbh_blocked_publication satFact unsatFact reason)
        (ay_vpbh_recompute reason fallbackBranch recomputeObligation)
        failure)

theorem ay_vpbh_chain_failure_recompute
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vpbh_chain_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    ay_vpbh_recompute reason fallbackBranch recomputeObligation :=
  fun failure =>
    ay_vpbh_conj_right
      (ay_vpbh_blocked_publication satFact unsatFact reason)
      (ay_vpbh_recompute reason fallbackBranch recomputeObligation)
      failure

theorem ay_vpbh_chain_break_forces_no_claim
    (satFact unsatFact chainBreak fallbackBranch recomputeObligation : Prop) :
    chainBreak -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vpbh_chain_failure satFact unsatFact chainBreak fallbackBranch
      recomputeObligation :=
  ay_vpbh_chain_failure_intro satFact unsatFact chainBreak fallbackBranch
    recomputeObligation

theorem ay_vpbh_chunk_drift_forces_no_claim
    (satFact unsatFact chunkDrift fallbackBranch recomputeObligation : Prop) :
    chunkDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vpbh_chain_failure satFact unsatFact chunkDrift fallbackBranch
      recomputeObligation :=
  ay_vpbh_chain_failure_intro satFact unsatFact chunkDrift fallbackBranch
    recomputeObligation

theorem ay_vpbh_stale_chain_cannot_bless_sat
    (satFact unsatFact staleBundleChain fallbackBranch
      recomputeObligation : Prop) :
    ay_vpbh_chain_failure satFact unsatFact staleBundleChain fallbackBranch
      recomputeObligation ->
    satFact -> False :=
  ay_vpbh_chain_failure_blocks_sat satFact unsatFact staleBundleChain
    fallbackBranch recomputeObligation

theorem ay_vpbh_stale_chain_cannot_bless_unsat
    (satFact unsatFact staleBundleChain fallbackBranch
      recomputeObligation : Prop) :
    ay_vpbh_chain_failure satFact unsatFact staleBundleChain fallbackBranch
      recomputeObligation ->
    unsatFact -> False :=
  ay_vpbh_chain_failure_blocks_unsat satFact unsatFact staleBundleChain
    fallbackBranch recomputeObligation
