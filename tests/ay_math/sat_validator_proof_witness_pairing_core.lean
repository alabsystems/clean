-- SAT-COMP validator proof/witness artifact pairing core.
--
-- Public result bundles may pair witness/proof artifacts only when result kind,
-- original input fingerprint, solver build identity, artifact digest, checker
-- replay transcript, reconstruction handle, exit-code mapping, and fallback
-- audit evidence agree.

def ay_vpwp_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vpwp_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vpwp_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vpwp_disj satFact (ay_vpwp_disj unsatFact noClaimFact)

def ay_vpwp_pairing_contract
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) : Prop :=
  ay_vpwp_conj resultKind
    (ay_vpwp_conj originalFingerprint
      (ay_vpwp_conj solverBuildIdentity
        (ay_vpwp_conj artifactDigest
          (ay_vpwp_conj checkerReplayTranscript
            (ay_vpwp_conj reconstructionHandle
              (ay_vpwp_conj exitCodeMapping fallbackAudit))))))

def ay_vpwp_sat_pair
    (pairingContract witnessArtifact originalModel : Prop) : Prop :=
  ay_vpwp_conj pairingContract
    (ay_vpwp_conj witnessArtifact originalModel)

def ay_vpwp_unsat_pair
    (pairingContract proofArtifact originalEmptyClause : Prop) : Prop :=
  ay_vpwp_conj pairingContract
    (ay_vpwp_conj proofArtifact originalEmptyClause)

def ay_vpwp_no_claim_pair
    (pairingContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vpwp_conj pairingContract
    (ay_vpwp_conj diagnostic noSemanticClaim)

def ay_vpwp_pair_validation
    (pairingContract checkerAccepted publicEvidence : Prop) : Prop :=
  ay_vpwp_conj pairingContract
    (ay_vpwp_conj checkerAccepted publicEvidence)

def ay_vpwp_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vpwp_conj reason
    (ay_vpwp_conj (satFact -> False) (unsatFact -> False))

def ay_vpwp_recompute
    (reason fallbackAudit fallbackPath : Prop) : Prop :=
  ay_vpwp_conj reason (ay_vpwp_conj fallbackAudit fallbackPath)

def ay_vpwp_pairing_failure
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) : Prop :=
  ay_vpwp_conj
    (ay_vpwp_blocked_publication satFact unsatFact reason)
    (ay_vpwp_recompute reason fallbackAudit fallbackPath)

theorem ay_vpwp_conj_intro (left right : Prop) :
    left -> right -> ay_vpwp_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vpwp_conj_left (left right : Prop) :
    ay_vpwp_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vpwp_conj_right (left right : Prop) :
    ay_vpwp_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vpwp_disj_left (left right : Prop) :
    left -> ay_vpwp_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vpwp_disj_right (left right : Prop) :
    right -> ay_vpwp_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vpwp_pairing_contract_intro
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    resultKind -> originalFingerprint -> solverBuildIdentity ->
    artifactDigest -> checkerReplayTranscript -> reconstructionHandle ->
    exitCodeMapping -> fallbackAudit ->
    ay_vpwp_pairing_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit :=
  fun kindProof fingerprintProof buildProof digestProof replayProof
      reconstructionProof mappingProof auditProof =>
    ay_vpwp_conj_intro resultKind
      (ay_vpwp_conj originalFingerprint
        (ay_vpwp_conj solverBuildIdentity
          (ay_vpwp_conj artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit))))))
      kindProof
      (ay_vpwp_conj_intro originalFingerprint
        (ay_vpwp_conj solverBuildIdentity
          (ay_vpwp_conj artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit)))))
        fingerprintProof
        (ay_vpwp_conj_intro solverBuildIdentity
          (ay_vpwp_conj artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit))))
          buildProof
          (ay_vpwp_conj_intro artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit)))
            digestProof
            (ay_vpwp_conj_intro checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit))
              replayProof
              (ay_vpwp_conj_intro reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit)
                reconstructionProof
                (ay_vpwp_conj_intro exitCodeMapping fallbackAudit
                  mappingProof auditProof))))))

theorem ay_vpwp_pairing_contract_kind
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vpwp_pairing_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    resultKind :=
  fun contract =>
    ay_vpwp_conj_left resultKind
      (ay_vpwp_conj originalFingerprint
        (ay_vpwp_conj solverBuildIdentity
          (ay_vpwp_conj artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit))))))
      contract

theorem ay_vpwp_pairing_contract_fingerprint
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vpwp_pairing_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    originalFingerprint :=
  fun contract =>
    ay_vpwp_conj_right resultKind
      (ay_vpwp_conj originalFingerprint
        (ay_vpwp_conj solverBuildIdentity
          (ay_vpwp_conj artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit))))))
      contract originalFingerprint
      (fun fingerprintProof _tail => fingerprintProof)

theorem ay_vpwp_pairing_contract_build
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vpwp_pairing_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    solverBuildIdentity :=
  fun contract =>
    ay_vpwp_conj_right resultKind
      (ay_vpwp_conj originalFingerprint
        (ay_vpwp_conj solverBuildIdentity
          (ay_vpwp_conj artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit))))))
      contract solverBuildIdentity
      (fun _fingerprintProof tail =>
        tail solverBuildIdentity (fun buildProof _tail2 => buildProof))

theorem ay_vpwp_pairing_contract_digest
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vpwp_pairing_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    artifactDigest :=
  fun contract =>
    ay_vpwp_conj_right resultKind
      (ay_vpwp_conj originalFingerprint
        (ay_vpwp_conj solverBuildIdentity
          (ay_vpwp_conj artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit))))))
      contract artifactDigest
      (fun _fingerprintProof tail =>
        tail artifactDigest
          (fun _buildProof tail2 =>
            tail2 artifactDigest (fun digestProof _tail3 => digestProof)))

theorem ay_vpwp_pairing_contract_replay
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vpwp_pairing_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    checkerReplayTranscript :=
  fun contract =>
    ay_vpwp_conj_right resultKind
      (ay_vpwp_conj originalFingerprint
        (ay_vpwp_conj solverBuildIdentity
          (ay_vpwp_conj artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit))))))
      contract checkerReplayTranscript
      (fun _fingerprintProof tail =>
        tail checkerReplayTranscript
          (fun _buildProof tail2 =>
            tail2 checkerReplayTranscript
              (fun _digestProof tail3 =>
                tail3 checkerReplayTranscript
                  (fun replayProof _tail4 => replayProof))))

theorem ay_vpwp_pairing_contract_reconstruction
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vpwp_pairing_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    reconstructionHandle :=
  fun contract =>
    ay_vpwp_conj_right resultKind
      (ay_vpwp_conj originalFingerprint
        (ay_vpwp_conj solverBuildIdentity
          (ay_vpwp_conj artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit))))))
      contract reconstructionHandle
      (fun _fingerprintProof tail =>
        tail reconstructionHandle
          (fun _buildProof tail2 =>
            tail2 reconstructionHandle
              (fun _digestProof tail3 =>
                tail3 reconstructionHandle
                  (fun _replayProof tail4 =>
                    tail4 reconstructionHandle
                      (fun reconstructionProof _tail5 =>
                        reconstructionProof)))))

theorem ay_vpwp_pairing_contract_mapping
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vpwp_pairing_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    exitCodeMapping :=
  fun contract =>
    ay_vpwp_conj_right resultKind
      (ay_vpwp_conj originalFingerprint
        (ay_vpwp_conj solverBuildIdentity
          (ay_vpwp_conj artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit))))))
      contract exitCodeMapping
      (fun _fingerprintProof tail =>
        tail exitCodeMapping
          (fun _buildProof tail2 =>
            tail2 exitCodeMapping
              (fun _digestProof tail3 =>
                tail3 exitCodeMapping
                  (fun _replayProof tail4 =>
                    tail4 exitCodeMapping
                      (fun _reconstructionProof tail5 =>
                        tail5 exitCodeMapping
                          (fun mappingProof _auditProof =>
                            mappingProof))))))

theorem ay_vpwp_pairing_contract_fallback
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vpwp_pairing_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    fallbackAudit :=
  fun contract =>
    ay_vpwp_conj_right resultKind
      (ay_vpwp_conj originalFingerprint
        (ay_vpwp_conj solverBuildIdentity
          (ay_vpwp_conj artifactDigest
            (ay_vpwp_conj checkerReplayTranscript
              (ay_vpwp_conj reconstructionHandle
                (ay_vpwp_conj exitCodeMapping fallbackAudit))))))
      contract fallbackAudit
      (fun _fingerprintProof tail =>
        tail fallbackAudit
          (fun _buildProof tail2 =>
            tail2 fallbackAudit
              (fun _digestProof tail3 =>
                tail3 fallbackAudit
                  (fun _replayProof tail4 =>
                    tail4 fallbackAudit
                      (fun _reconstructionProof tail5 =>
                        tail5 fallbackAudit
                          (fun _mappingProof auditProof =>
                            auditProof))))))

theorem ay_vpwp_sat_pair_intro
    (pairingContract witnessArtifact originalModel : Prop) :
    pairingContract -> witnessArtifact -> originalModel ->
    ay_vpwp_sat_pair pairingContract witnessArtifact originalModel :=
  fun contractProof witnessProof modelProof =>
    ay_vpwp_conj_intro pairingContract
      (ay_vpwp_conj witnessArtifact originalModel)
      contractProof
      (ay_vpwp_conj_intro witnessArtifact originalModel witnessProof
        modelProof)

theorem ay_vpwp_sat_pair_contract
    (pairingContract witnessArtifact originalModel : Prop) :
    ay_vpwp_sat_pair pairingContract witnessArtifact originalModel ->
    pairingContract :=
  fun pair =>
    ay_vpwp_conj_left pairingContract
      (ay_vpwp_conj witnessArtifact originalModel) pair

theorem ay_vpwp_sat_pair_original_model
    (pairingContract witnessArtifact originalModel : Prop) :
    ay_vpwp_sat_pair pairingContract witnessArtifact originalModel ->
    originalModel :=
  fun pair =>
    ay_vpwp_conj_right pairingContract
      (ay_vpwp_conj witnessArtifact originalModel)
      pair originalModel
      (fun _witnessProof modelProof => modelProof)

theorem ay_vpwp_unsat_pair_intro
    (pairingContract proofArtifact originalEmptyClause : Prop) :
    pairingContract -> proofArtifact -> originalEmptyClause ->
    ay_vpwp_unsat_pair pairingContract proofArtifact originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vpwp_conj_intro pairingContract
      (ay_vpwp_conj proofArtifact originalEmptyClause)
      contractProof
      (ay_vpwp_conj_intro proofArtifact originalEmptyClause proofProof
        emptyProof)

theorem ay_vpwp_unsat_pair_contract
    (pairingContract proofArtifact originalEmptyClause : Prop) :
    ay_vpwp_unsat_pair pairingContract proofArtifact originalEmptyClause ->
    pairingContract :=
  fun pair =>
    ay_vpwp_conj_left pairingContract
      (ay_vpwp_conj proofArtifact originalEmptyClause) pair

theorem ay_vpwp_unsat_pair_original_empty_clause
    (pairingContract proofArtifact originalEmptyClause : Prop) :
    ay_vpwp_unsat_pair pairingContract proofArtifact originalEmptyClause ->
    originalEmptyClause :=
  fun pair =>
    ay_vpwp_conj_right pairingContract
      (ay_vpwp_conj proofArtifact originalEmptyClause)
      pair originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vpwp_no_claim_pair_intro
    (pairingContract diagnostic noSemanticClaim : Prop) :
    pairingContract -> diagnostic -> noSemanticClaim ->
    ay_vpwp_no_claim_pair pairingContract diagnostic noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_vpwp_conj_intro pairingContract
      (ay_vpwp_conj diagnostic noSemanticClaim)
      contractProof
      (ay_vpwp_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vpwp_no_claim_pair_no_semantic_claim
    (pairingContract diagnostic noSemanticClaim : Prop) :
    ay_vpwp_no_claim_pair pairingContract diagnostic noSemanticClaim ->
    noSemanticClaim :=
  fun pair =>
    ay_vpwp_conj_right pairingContract
      (ay_vpwp_conj diagnostic noSemanticClaim)
      pair noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vpwp_pair_validation_intro
    (pairingContract checkerAccepted publicEvidence : Prop) :
    pairingContract -> checkerAccepted -> publicEvidence ->
    ay_vpwp_pair_validation pairingContract checkerAccepted publicEvidence :=
  fun contractProof checkerProof publicProof =>
    ay_vpwp_conj_intro pairingContract
      (ay_vpwp_conj checkerAccepted publicEvidence)
      contractProof
      (ay_vpwp_conj_intro checkerAccepted publicEvidence checkerProof
        publicProof)

theorem ay_vpwp_pair_validation_public_evidence
    (pairingContract checkerAccepted publicEvidence : Prop) :
    ay_vpwp_pair_validation pairingContract checkerAccepted publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vpwp_conj_right pairingContract
      (ay_vpwp_conj checkerAccepted publicEvidence)
      validation publicEvidence
      (fun _checkerProof publicProof => publicProof)

theorem ay_vpwp_accepted_sat_pair_validates_witness
    (pairingContract witnessArtifact originalModel unsatFact noClaimFact :
      Prop) :
    ay_vpwp_sat_pair pairingContract witnessArtifact originalModel ->
    ay_vpwp_public_result originalModel unsatFact noClaimFact :=
  fun pair =>
    ay_vpwp_disj_left originalModel
      (ay_vpwp_disj unsatFact noClaimFact)
      (ay_vpwp_sat_pair_original_model pairingContract witnessArtifact
        originalModel pair)

theorem ay_vpwp_accepted_unsat_pair_validates_proof
    (satFact pairingContract proofArtifact originalEmptyClause noClaimFact :
      Prop) :
    ay_vpwp_unsat_pair pairingContract proofArtifact originalEmptyClause ->
    ay_vpwp_public_result satFact originalEmptyClause noClaimFact :=
  fun pair =>
    ay_vpwp_disj_right satFact
      (ay_vpwp_disj originalEmptyClause noClaimFact)
      (ay_vpwp_disj_left originalEmptyClause noClaimFact
        (ay_vpwp_unsat_pair_original_empty_clause pairingContract
          proofArtifact originalEmptyClause pair))

theorem ay_vpwp_accepted_no_claim_pair_preserves_result
    (satFact unsatFact pairingContract diagnostic noSemanticClaim : Prop) :
    ay_vpwp_no_claim_pair pairingContract diagnostic noSemanticClaim ->
    ay_vpwp_public_result satFact unsatFact noSemanticClaim :=
  fun pair =>
    ay_vpwp_disj_right satFact
      (ay_vpwp_disj unsatFact noSemanticClaim)
      (ay_vpwp_disj_right unsatFact noSemanticClaim
        (ay_vpwp_no_claim_pair_no_semantic_claim pairingContract
          diagnostic noSemanticClaim pair))

theorem ay_vpwp_sat_pair_supports_validation
    (pairingContract witnessArtifact originalModel checkerAccepted : Prop) :
    ay_vpwp_sat_pair pairingContract witnessArtifact originalModel ->
    checkerAccepted ->
    ay_vpwp_pair_validation pairingContract checkerAccepted originalModel :=
  fun pair checkerProof =>
    ay_vpwp_pair_validation_intro pairingContract checkerAccepted
      originalModel
      (ay_vpwp_sat_pair_contract pairingContract witnessArtifact
        originalModel pair)
      checkerProof
      (ay_vpwp_sat_pair_original_model pairingContract witnessArtifact
        originalModel pair)

theorem ay_vpwp_unsat_pair_supports_validation
    (pairingContract proofArtifact originalEmptyClause checkerAccepted :
      Prop) :
    ay_vpwp_unsat_pair pairingContract proofArtifact originalEmptyClause ->
    checkerAccepted ->
    ay_vpwp_pair_validation pairingContract checkerAccepted
      originalEmptyClause :=
  fun pair checkerProof =>
    ay_vpwp_pair_validation_intro pairingContract checkerAccepted
      originalEmptyClause
      (ay_vpwp_unsat_pair_contract pairingContract proofArtifact
        originalEmptyClause pair)
      checkerProof
      (ay_vpwp_unsat_pair_original_empty_clause pairingContract
        proofArtifact originalEmptyClause pair)

theorem ay_vpwp_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vpwp_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vpwp_conj_intro reason
      (ay_vpwp_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vpwp_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vpwp_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vpwp_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vpwp_conj_right reason
      (ay_vpwp_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vpwp_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vpwp_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vpwp_conj_right reason
      (ay_vpwp_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vpwp_recompute_intro
    (reason fallbackAudit fallbackPath : Prop) :
    reason -> fallbackAudit -> fallbackPath ->
    ay_vpwp_recompute reason fallbackAudit fallbackPath :=
  fun reasonProof auditProof pathProof =>
    ay_vpwp_conj_intro reason
      (ay_vpwp_conj fallbackAudit fallbackPath)
      reasonProof
      (ay_vpwp_conj_intro fallbackAudit fallbackPath auditProof pathProof)

theorem ay_vpwp_pairing_failure_intro
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vpwp_blocked_publication satFact unsatFact reason ->
    ay_vpwp_recompute reason fallbackAudit fallbackPath ->
    ay_vpwp_pairing_failure satFact unsatFact reason fallbackAudit
      fallbackPath :=
  fun blocked recompute =>
    ay_vpwp_conj_intro
      (ay_vpwp_blocked_publication satFact unsatFact reason)
      (ay_vpwp_recompute reason fallbackAudit fallbackPath)
      blocked recompute

theorem ay_vpwp_pairing_failure_blocks_sat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vpwp_pairing_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vpwp_blocked_publication_no_sat satFact unsatFact reason
      (ay_vpwp_conj_left
        (ay_vpwp_blocked_publication satFact unsatFact reason)
        (ay_vpwp_recompute reason fallbackAudit fallbackPath)
        failure)

theorem ay_vpwp_pairing_failure_blocks_unsat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vpwp_pairing_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vpwp_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vpwp_conj_left
        (ay_vpwp_blocked_publication satFact unsatFact reason)
        (ay_vpwp_recompute reason fallbackAudit fallbackPath)
        failure)

theorem ay_vpwp_pairing_failure_recompute
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vpwp_pairing_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    ay_vpwp_recompute reason fallbackAudit fallbackPath :=
  fun failure =>
    ay_vpwp_conj_right
      (ay_vpwp_blocked_publication satFact unsatFact reason)
      (ay_vpwp_recompute reason fallbackAudit fallbackPath)
      failure

theorem ay_vpwp_cross_kind_pairing_forces_no_claim
    (satFact unsatFact crossKind fallbackAudit fallbackPath : Prop) :
    crossKind -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vpwp_pairing_failure satFact unsatFact crossKind fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vpwp_pairing_failure_intro satFact unsatFact crossKind
      fallbackAudit fallbackPath
      (ay_vpwp_blocked_publication_intro satFact unsatFact crossKind
        reasonProof blockSat blockUnsat)
      (ay_vpwp_recompute_intro crossKind fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vpwp_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch fallbackAudit fallbackPath : Prop) :
    digestMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vpwp_pairing_failure satFact unsatFact digestMismatch fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vpwp_pairing_failure_intro satFact unsatFact digestMismatch
      fallbackAudit fallbackPath
      (ay_vpwp_blocked_publication_intro satFact unsatFact digestMismatch
        reasonProof blockSat blockUnsat)
      (ay_vpwp_recompute_intro digestMismatch fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vpwp_missing_counterpart_forces_no_claim
    (satFact unsatFact missingCounterpart fallbackAudit fallbackPath : Prop) :
    missingCounterpart -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vpwp_pairing_failure satFact unsatFact missingCounterpart
      fallbackAudit fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vpwp_pairing_failure_intro satFact unsatFact missingCounterpart
      fallbackAudit fallbackPath
      (ay_vpwp_blocked_publication_intro satFact unsatFact
        missingCounterpart reasonProof blockSat blockUnsat)
      (ay_vpwp_recompute_intro missingCounterpart fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vpwp_replay_gap_forces_no_claim
    (satFact unsatFact replayGap fallbackAudit fallbackPath : Prop) :
    replayGap -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vpwp_pairing_failure satFact unsatFact replayGap fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vpwp_pairing_failure_intro satFact unsatFact replayGap fallbackAudit
      fallbackPath
      (ay_vpwp_blocked_publication_intro satFact unsatFact replayGap
        reasonProof blockSat blockUnsat)
      (ay_vpwp_recompute_intro replayGap fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vpwp_reconstruction_gap_forces_no_claim
    (satFact unsatFact reconstructionGap fallbackAudit fallbackPath : Prop) :
    reconstructionGap -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vpwp_pairing_failure satFact unsatFact reconstructionGap
      fallbackAudit fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vpwp_pairing_failure_intro satFact unsatFact reconstructionGap
      fallbackAudit fallbackPath
      (ay_vpwp_blocked_publication_intro satFact unsatFact
        reconstructionGap reasonProof blockSat blockUnsat)
      (ay_vpwp_recompute_intro reconstructionGap fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vpwp_stale_build_forces_no_claim
    (satFact unsatFact staleBuild fallbackAudit fallbackPath : Prop) :
    staleBuild -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vpwp_pairing_failure satFact unsatFact staleBuild fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vpwp_pairing_failure_intro satFact unsatFact staleBuild fallbackAudit
      fallbackPath
      (ay_vpwp_blocked_publication_intro satFact unsatFact staleBuild
        reasonProof blockSat blockUnsat)
      (ay_vpwp_recompute_intro staleBuild fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vpwp_mapping_mismatch_forces_no_claim
    (satFact unsatFact mappingMismatch fallbackAudit fallbackPath : Prop) :
    mappingMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vpwp_pairing_failure satFact unsatFact mappingMismatch
      fallbackAudit fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vpwp_pairing_failure_intro satFact unsatFact mappingMismatch
      fallbackAudit fallbackPath
      (ay_vpwp_blocked_publication_intro satFact unsatFact mappingMismatch
        reasonProof blockSat blockUnsat)
      (ay_vpwp_recompute_intro mappingMismatch fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vpwp_audit_contradiction_forces_no_claim
    (satFact unsatFact auditContradiction fallbackAudit fallbackPath : Prop) :
    auditContradiction -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vpwp_pairing_failure satFact unsatFact auditContradiction
      fallbackAudit fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vpwp_pairing_failure_intro satFact unsatFact auditContradiction
      fallbackAudit fallbackPath
      (ay_vpwp_blocked_publication_intro satFact unsatFact
        auditContradiction reasonProof blockSat blockUnsat)
      (ay_vpwp_recompute_intro auditContradiction fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vpwp_failure_cannot_publish_sat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vpwp_pairing_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    satFact -> False :=
  ay_vpwp_pairing_failure_blocks_sat satFact unsatFact reason fallbackAudit
    fallbackPath

theorem ay_vpwp_failure_cannot_publish_unsat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vpwp_pairing_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    unsatFact -> False :=
  ay_vpwp_pairing_failure_blocks_unsat satFact unsatFact reason fallbackAudit
    fallbackPath
