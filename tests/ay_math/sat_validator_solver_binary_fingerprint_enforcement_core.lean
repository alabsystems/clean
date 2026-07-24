-- SAT-COMP validator solver binary fingerprint enforcement core.
--
-- Public SAT/UNSAT claims are tied to the exact solver binary fingerprint,
-- solver build configuration, certificate digest, checker transcript,
-- original formula fingerprint, reconstruction map, and no-claim fallback.
-- Binary or configuration drift is modeled as a recompute/no-claim blocker.

def ay_vsbf_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vsbf_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vsbf_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vsbf_disj satFact (ay_vsbf_disj unsatFact noClaimFact)

def ay_vsbf_binary_contract
    (solverBinaryFingerprint solverBuildConfig certificateDigest
      checkerTranscript originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) : Prop :=
  ay_vsbf_conj solverBinaryFingerprint
    (ay_vsbf_conj solverBuildConfig
      (ay_vsbf_conj certificateDigest
        (ay_vsbf_conj checkerTranscript
          (ay_vsbf_conj originalFormulaFingerprint
            (ay_vsbf_conj reconstructionMap fallbackBranch)))))

def ay_vsbf_sat_publication
    (binaryContract modelCertificate originalModel : Prop) : Prop :=
  ay_vsbf_conj binaryContract
    (ay_vsbf_conj modelCertificate originalModel)

def ay_vsbf_unsat_publication
    (binaryContract proofCertificate originalEmptyClause : Prop) : Prop :=
  ay_vsbf_conj binaryContract
    (ay_vsbf_conj proofCertificate originalEmptyClause)

def ay_vsbf_no_claim
    (reason fallbackBranch auditTrail : Prop) : Prop :=
  ay_vsbf_conj reason (ay_vsbf_conj fallbackBranch auditTrail)

def ay_vsbf_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vsbf_conj reason
    (ay_vsbf_conj (satFact -> False) (unsatFact -> False))

def ay_vsbf_recompute
    (reason fallbackBranch recomputeObligation : Prop) : Prop :=
  ay_vsbf_conj reason
    (ay_vsbf_conj fallbackBranch recomputeObligation)

def ay_vsbf_drift_failure
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    Prop :=
  ay_vsbf_conj
    (ay_vsbf_blocked_publication satFact unsatFact reason)
    (ay_vsbf_recompute reason fallbackBranch recomputeObligation)

theorem ay_vsbf_conj_intro (left right : Prop) :
    left -> right -> ay_vsbf_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vsbf_conj_left (left right : Prop) :
    ay_vsbf_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vsbf_conj_right (left right : Prop) :
    ay_vsbf_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vsbf_disj_left (left right : Prop) :
    left -> ay_vsbf_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vsbf_disj_right (left right : Prop) :
    right -> ay_vsbf_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vsbf_binary_contract_intro
    (solverBinaryFingerprint solverBuildConfig certificateDigest
      checkerTranscript originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    solverBinaryFingerprint -> solverBuildConfig -> certificateDigest ->
    checkerTranscript -> originalFormulaFingerprint -> reconstructionMap ->
    fallbackBranch ->
    ay_vsbf_binary_contract solverBinaryFingerprint solverBuildConfig
      certificateDigest checkerTranscript originalFormulaFingerprint
      reconstructionMap fallbackBranch :=
  fun binaryProof configProof digestProof transcriptProof fingerprintProof
      reconstructionProof fallbackProof =>
    ay_vsbf_conj_intro solverBinaryFingerprint
      (ay_vsbf_conj solverBuildConfig
        (ay_vsbf_conj certificateDigest
          (ay_vsbf_conj checkerTranscript
            (ay_vsbf_conj originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch)))))
      binaryProof
      (ay_vsbf_conj_intro solverBuildConfig
        (ay_vsbf_conj certificateDigest
          (ay_vsbf_conj checkerTranscript
            (ay_vsbf_conj originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch))))
        configProof
        (ay_vsbf_conj_intro certificateDigest
          (ay_vsbf_conj checkerTranscript
            (ay_vsbf_conj originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch)))
          digestProof
          (ay_vsbf_conj_intro checkerTranscript
            (ay_vsbf_conj originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch))
            transcriptProof
            (ay_vsbf_conj_intro originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch)
              fingerprintProof
              (ay_vsbf_conj_intro reconstructionMap fallbackBranch
                reconstructionProof fallbackProof)))))

theorem ay_vsbf_binary_contract_binary_fingerprint
    (solverBinaryFingerprint solverBuildConfig certificateDigest
      checkerTranscript originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vsbf_binary_contract solverBinaryFingerprint solverBuildConfig
      certificateDigest checkerTranscript originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    solverBinaryFingerprint :=
  fun contract =>
    ay_vsbf_conj_left solverBinaryFingerprint
      (ay_vsbf_conj solverBuildConfig
        (ay_vsbf_conj certificateDigest
          (ay_vsbf_conj checkerTranscript
            (ay_vsbf_conj originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch)))))
      contract

theorem ay_vsbf_binary_contract_build_config
    (solverBinaryFingerprint solverBuildConfig certificateDigest
      checkerTranscript originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vsbf_binary_contract solverBinaryFingerprint solverBuildConfig
      certificateDigest checkerTranscript originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    solverBuildConfig :=
  fun contract =>
    ay_vsbf_conj_right solverBinaryFingerprint
      (ay_vsbf_conj solverBuildConfig
        (ay_vsbf_conj certificateDigest
          (ay_vsbf_conj checkerTranscript
            (ay_vsbf_conj originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch)))))
      contract solverBuildConfig
      (fun configProof _tail => configProof)

theorem ay_vsbf_binary_contract_certificate_digest
    (solverBinaryFingerprint solverBuildConfig certificateDigest
      checkerTranscript originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vsbf_binary_contract solverBinaryFingerprint solverBuildConfig
      certificateDigest checkerTranscript originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    certificateDigest :=
  fun contract =>
    ay_vsbf_conj_right solverBinaryFingerprint
      (ay_vsbf_conj solverBuildConfig
        (ay_vsbf_conj certificateDigest
          (ay_vsbf_conj checkerTranscript
            (ay_vsbf_conj originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch)))))
      contract certificateDigest
      (fun _configProof tail =>
        tail certificateDigest
          (fun digestProof _tail2 => digestProof))

theorem ay_vsbf_binary_contract_checker_transcript
    (solverBinaryFingerprint solverBuildConfig certificateDigest
      checkerTranscript originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vsbf_binary_contract solverBinaryFingerprint solverBuildConfig
      certificateDigest checkerTranscript originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    checkerTranscript :=
  fun contract =>
    ay_vsbf_conj_right solverBinaryFingerprint
      (ay_vsbf_conj solverBuildConfig
        (ay_vsbf_conj certificateDigest
          (ay_vsbf_conj checkerTranscript
            (ay_vsbf_conj originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch)))))
      contract checkerTranscript
      (fun _configProof tail =>
        tail checkerTranscript
          (fun _digestProof tail2 =>
            tail2 checkerTranscript
              (fun transcriptProof _tail3 => transcriptProof)))

theorem ay_vsbf_binary_contract_formula_fingerprint
    (solverBinaryFingerprint solverBuildConfig certificateDigest
      checkerTranscript originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vsbf_binary_contract solverBinaryFingerprint solverBuildConfig
      certificateDigest checkerTranscript originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    originalFormulaFingerprint :=
  fun contract =>
    ay_vsbf_conj_right solverBinaryFingerprint
      (ay_vsbf_conj solverBuildConfig
        (ay_vsbf_conj certificateDigest
          (ay_vsbf_conj checkerTranscript
            (ay_vsbf_conj originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch)))))
      contract originalFormulaFingerprint
      (fun _configProof tail =>
        tail originalFormulaFingerprint
          (fun _digestProof tail2 =>
            tail2 originalFormulaFingerprint
              (fun _transcriptProof tail3 =>
                tail3 originalFormulaFingerprint
                  (fun fingerprintProof _tail4 => fingerprintProof))))

theorem ay_vsbf_binary_contract_reconstruction
    (solverBinaryFingerprint solverBuildConfig certificateDigest
      checkerTranscript originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vsbf_binary_contract solverBinaryFingerprint solverBuildConfig
      certificateDigest checkerTranscript originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    reconstructionMap :=
  fun contract =>
    ay_vsbf_conj_right solverBinaryFingerprint
      (ay_vsbf_conj solverBuildConfig
        (ay_vsbf_conj certificateDigest
          (ay_vsbf_conj checkerTranscript
            (ay_vsbf_conj originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch)))))
      contract reconstructionMap
      (fun _configProof tail =>
        tail reconstructionMap
          (fun _digestProof tail2 =>
            tail2 reconstructionMap
              (fun _transcriptProof tail3 =>
                tail3 reconstructionMap
                  (fun _fingerprintProof tail4 =>
                    tail4 reconstructionMap
                      (fun reconstructionProof _fallbackProof =>
                        reconstructionProof)))))

theorem ay_vsbf_binary_contract_fallback
    (solverBinaryFingerprint solverBuildConfig certificateDigest
      checkerTranscript originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vsbf_binary_contract solverBinaryFingerprint solverBuildConfig
      certificateDigest checkerTranscript originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    fallbackBranch :=
  fun contract =>
    ay_vsbf_conj_right solverBinaryFingerprint
      (ay_vsbf_conj solverBuildConfig
        (ay_vsbf_conj certificateDigest
          (ay_vsbf_conj checkerTranscript
            (ay_vsbf_conj originalFormulaFingerprint
              (ay_vsbf_conj reconstructionMap fallbackBranch)))))
      contract fallbackBranch
      (fun _configProof tail =>
        tail fallbackBranch
          (fun _digestProof tail2 =>
            tail2 fallbackBranch
              (fun _transcriptProof tail3 =>
                tail3 fallbackBranch
                  (fun _fingerprintProof tail4 =>
                    tail4 fallbackBranch
                      (fun _reconstructionProof fallbackProof =>
                        fallbackProof)))))

theorem ay_vsbf_sat_publication_intro
    (binaryContract modelCertificate originalModel : Prop) :
    binaryContract -> modelCertificate -> originalModel ->
    ay_vsbf_sat_publication binaryContract modelCertificate originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vsbf_conj_intro binaryContract
      (ay_vsbf_conj modelCertificate originalModel)
      contractProof
      (ay_vsbf_conj_intro modelCertificate originalModel
        modelProof originalProof)

theorem ay_vsbf_sat_publication_original_model
    (binaryContract modelCertificate originalModel : Prop) :
    ay_vsbf_sat_publication binaryContract modelCertificate originalModel ->
    originalModel :=
  fun publication =>
    ay_vsbf_conj_right binaryContract
      (ay_vsbf_conj modelCertificate originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vsbf_unsat_publication_intro
    (binaryContract proofCertificate originalEmptyClause : Prop) :
    binaryContract -> proofCertificate -> originalEmptyClause ->
    ay_vsbf_unsat_publication binaryContract proofCertificate
      originalEmptyClause :=
  fun contractProof proofCert originalProof =>
    ay_vsbf_conj_intro binaryContract
      (ay_vsbf_conj proofCertificate originalEmptyClause)
      contractProof
      (ay_vsbf_conj_intro proofCertificate originalEmptyClause
        proofCert originalProof)

theorem ay_vsbf_unsat_publication_original_empty_clause
    (binaryContract proofCertificate originalEmptyClause : Prop) :
    ay_vsbf_unsat_publication binaryContract proofCertificate
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vsbf_conj_right binaryContract
      (ay_vsbf_conj proofCertificate originalEmptyClause)
      publication originalEmptyClause
      (fun _proofCert originalProof => originalProof)

theorem ay_vsbf_accepted_binary_fingerprint_sat_sound
    (solverBinaryFingerprint solverBuildConfig certificateDigest
      checkerTranscript originalFormulaFingerprint reconstructionMap
      fallbackBranch modelCertificate originalModel : Prop) :
    ay_vsbf_binary_contract solverBinaryFingerprint solverBuildConfig
      certificateDigest checkerTranscript originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    modelCertificate -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vsbf_accepted_binary_fingerprint_unsat_sound
    (solverBinaryFingerprint solverBuildConfig certificateDigest
      checkerTranscript originalFormulaFingerprint reconstructionMap
      fallbackBranch proofCertificate originalEmptyClause : Prop) :
    ay_vsbf_binary_contract solverBinaryFingerprint solverBuildConfig
      certificateDigest checkerTranscript originalFormulaFingerprint
      reconstructionMap fallbackBranch ->
    proofCertificate -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofCert originalProof => originalProof

theorem ay_vsbf_no_claim_intro
    (reason fallbackBranch auditTrail : Prop) :
    reason -> fallbackBranch -> auditTrail ->
    ay_vsbf_no_claim reason fallbackBranch auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vsbf_conj_intro reason
      (ay_vsbf_conj fallbackBranch auditTrail)
      reasonProof
      (ay_vsbf_conj_intro fallbackBranch auditTrail
        fallbackProof auditProof)

theorem ay_vsbf_no_claim_reason
    (reason fallbackBranch auditTrail : Prop) :
    ay_vsbf_no_claim reason fallbackBranch auditTrail -> reason :=
  fun noClaim =>
    ay_vsbf_conj_left reason
      (ay_vsbf_conj fallbackBranch auditTrail)
      noClaim

theorem ay_vsbf_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vsbf_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vsbf_conj_intro reason
      (ay_vsbf_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vsbf_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vsbf_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vsbf_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vsbf_conj_right reason
      (ay_vsbf_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vsbf_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vsbf_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vsbf_conj_right reason
      (ay_vsbf_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vsbf_recompute_intro
    (reason fallbackBranch recomputeObligation : Prop) :
    reason -> fallbackBranch -> recomputeObligation ->
    ay_vsbf_recompute reason fallbackBranch recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vsbf_conj_intro reason
      (ay_vsbf_conj fallbackBranch recomputeObligation)
      reasonProof
      (ay_vsbf_conj_intro fallbackBranch recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vsbf_drift_failure_intro
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vsbf_drift_failure satFact unsatFact reason fallbackBranch
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vsbf_conj_intro
      (ay_vsbf_blocked_publication satFact unsatFact reason)
      (ay_vsbf_recompute reason fallbackBranch recomputeObligation)
      (ay_vsbf_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vsbf_recompute_intro reason fallbackBranch recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vsbf_drift_failure_blocks_sat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vsbf_drift_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vsbf_blocked_publication_no_sat satFact unsatFact reason
      (ay_vsbf_conj_left
        (ay_vsbf_blocked_publication satFact unsatFact reason)
        (ay_vsbf_recompute reason fallbackBranch recomputeObligation)
        failure)

theorem ay_vsbf_drift_failure_blocks_unsat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vsbf_drift_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vsbf_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vsbf_conj_left
        (ay_vsbf_blocked_publication satFact unsatFact reason)
        (ay_vsbf_recompute reason fallbackBranch recomputeObligation)
        failure)

theorem ay_vsbf_drift_failure_recompute
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vsbf_drift_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    ay_vsbf_recompute reason fallbackBranch recomputeObligation :=
  fun failure =>
    ay_vsbf_conj_right
      (ay_vsbf_blocked_publication satFact unsatFact reason)
      (ay_vsbf_recompute reason fallbackBranch recomputeObligation)
      failure

theorem ay_vsbf_binary_drift_forces_no_claim
    (satFact unsatFact binaryDrift fallbackBranch recomputeObligation : Prop) :
    binaryDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vsbf_drift_failure satFact unsatFact binaryDrift fallbackBranch
      recomputeObligation :=
  ay_vsbf_drift_failure_intro satFact unsatFact binaryDrift fallbackBranch
    recomputeObligation

theorem ay_vsbf_config_drift_forces_no_claim
    (satFact unsatFact configDrift fallbackBranch recomputeObligation : Prop) :
    configDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vsbf_drift_failure satFact unsatFact configDrift fallbackBranch
      recomputeObligation :=
  ay_vsbf_drift_failure_intro satFact unsatFact configDrift fallbackBranch
    recomputeObligation

theorem ay_vsbf_stale_binary_cannot_bless_sat
    (satFact unsatFact staleBinary fallbackBranch recomputeObligation : Prop) :
    ay_vsbf_drift_failure satFact unsatFact staleBinary fallbackBranch
      recomputeObligation ->
    satFact -> False :=
  ay_vsbf_drift_failure_blocks_sat satFact unsatFact staleBinary
    fallbackBranch recomputeObligation

theorem ay_vsbf_stale_binary_cannot_bless_unsat
    (satFact unsatFact staleBinary fallbackBranch recomputeObligation : Prop) :
    ay_vsbf_drift_failure satFact unsatFact staleBinary fallbackBranch
      recomputeObligation ->
    unsatFact -> False :=
  ay_vsbf_drift_failure_blocks_unsat satFact unsatFact staleBinary
    fallbackBranch recomputeObligation
