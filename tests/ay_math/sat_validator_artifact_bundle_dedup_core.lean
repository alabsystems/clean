-- SAT-COMP validator artifact bundle deduplication core.
--
-- Duplicate witness/proof/manifest artifacts can be coalesced only when the
-- original input fingerprint, solver build identity, artifact digest, replay
-- transcript, reconstruction handle, exit-code mapping, and fallback audit
-- evidence agree.  Failed deduplication downgrades to no-claim/recompute.

def ay_vabd_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vabd_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vabd_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vabd_disj satFact (ay_vabd_disj unsatFact noClaimFact)

def ay_vabd_dedup_contract
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit representativeArtifact : Prop) : Prop :=
  ay_vabd_conj originalFingerprint
    (ay_vabd_conj solverBuildIdentity
      (ay_vabd_conj artifactDigest
        (ay_vabd_conj checkerReplayTranscript
          (ay_vabd_conj reconstructionHandle
            (ay_vabd_conj exitCodeMapping
              (ay_vabd_conj fallbackAudit representativeArtifact))))))

def ay_vabd_sat_dedup
    (dedupContract modelEvidence originalModel : Prop) : Prop :=
  ay_vabd_conj dedupContract
    (ay_vabd_conj modelEvidence originalModel)

def ay_vabd_unsat_dedup
    (dedupContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vabd_conj dedupContract
    (ay_vabd_conj proofEvidence originalEmptyClause)

def ay_vabd_no_claim_dedup
    (dedupContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vabd_conj dedupContract
    (ay_vabd_conj diagnostic noSemanticClaim)

def ay_vabd_dedup_validation
    (dedupContract checkerAccepted publicEvidence : Prop) : Prop :=
  ay_vabd_conj dedupContract
    (ay_vabd_conj checkerAccepted publicEvidence)

def ay_vabd_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vabd_conj reason
    (ay_vabd_conj (satFact -> False) (unsatFact -> False))

def ay_vabd_recompute
    (reason fallbackAudit fallbackPath : Prop) : Prop :=
  ay_vabd_conj reason (ay_vabd_conj fallbackAudit fallbackPath)

def ay_vabd_dedup_failure
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) : Prop :=
  ay_vabd_conj
    (ay_vabd_blocked_publication satFact unsatFact reason)
    (ay_vabd_recompute reason fallbackAudit fallbackPath)

theorem ay_vabd_conj_intro (left right : Prop) :
    left -> right -> ay_vabd_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vabd_conj_left (left right : Prop) :
    ay_vabd_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vabd_conj_right (left right : Prop) :
    ay_vabd_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vabd_disj_left (left right : Prop) :
    left -> ay_vabd_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vabd_disj_right (left right : Prop) :
    right -> ay_vabd_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vabd_dedup_contract_intro
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit representativeArtifact : Prop) :
    originalFingerprint -> solverBuildIdentity -> artifactDigest ->
    checkerReplayTranscript -> reconstructionHandle -> exitCodeMapping ->
    fallbackAudit -> representativeArtifact ->
    ay_vabd_dedup_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping fallbackAudit representativeArtifact :=
  fun fingerprintProof buildProof digestProof replayProof reconstructionProof
      mappingProof auditProof representativeProof =>
    ay_vabd_conj_intro originalFingerprint
      (ay_vabd_conj solverBuildIdentity
        (ay_vabd_conj artifactDigest
          (ay_vabd_conj checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact))))))
      fingerprintProof
      (ay_vabd_conj_intro solverBuildIdentity
        (ay_vabd_conj artifactDigest
          (ay_vabd_conj checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact)))))
        buildProof
        (ay_vabd_conj_intro artifactDigest
          (ay_vabd_conj checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact))))
          digestProof
          (ay_vabd_conj_intro checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact)))
            replayProof
            (ay_vabd_conj_intro reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact))
              reconstructionProof
              (ay_vabd_conj_intro exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact)
                mappingProof
                (ay_vabd_conj_intro fallbackAudit representativeArtifact
                  auditProof representativeProof))))))

theorem ay_vabd_dedup_contract_fingerprint
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit representativeArtifact : Prop) :
    ay_vabd_dedup_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping fallbackAudit representativeArtifact ->
    originalFingerprint :=
  fun contract =>
    ay_vabd_conj_left originalFingerprint
      (ay_vabd_conj solverBuildIdentity
        (ay_vabd_conj artifactDigest
          (ay_vabd_conj checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact))))))
      contract

theorem ay_vabd_dedup_contract_build
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit representativeArtifact : Prop) :
    ay_vabd_dedup_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping fallbackAudit representativeArtifact ->
    solverBuildIdentity :=
  fun contract =>
    ay_vabd_conj_right originalFingerprint
      (ay_vabd_conj solverBuildIdentity
        (ay_vabd_conj artifactDigest
          (ay_vabd_conj checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact))))))
      contract solverBuildIdentity
      (fun buildProof _tail => buildProof)

theorem ay_vabd_dedup_contract_digest
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit representativeArtifact : Prop) :
    ay_vabd_dedup_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping fallbackAudit representativeArtifact ->
    artifactDigest :=
  fun contract =>
    ay_vabd_conj_right originalFingerprint
      (ay_vabd_conj solverBuildIdentity
        (ay_vabd_conj artifactDigest
          (ay_vabd_conj checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact))))))
      contract artifactDigest
      (fun _buildProof tail =>
        tail artifactDigest (fun digestProof _tail2 => digestProof))

theorem ay_vabd_dedup_contract_replay
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit representativeArtifact : Prop) :
    ay_vabd_dedup_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping fallbackAudit representativeArtifact ->
    checkerReplayTranscript :=
  fun contract =>
    ay_vabd_conj_right originalFingerprint
      (ay_vabd_conj solverBuildIdentity
        (ay_vabd_conj artifactDigest
          (ay_vabd_conj checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact))))))
      contract checkerReplayTranscript
      (fun _buildProof tail =>
        tail checkerReplayTranscript
          (fun _digestProof tail2 =>
            tail2 checkerReplayTranscript
              (fun replayProof _tail3 => replayProof)))

theorem ay_vabd_dedup_contract_reconstruction
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit representativeArtifact : Prop) :
    ay_vabd_dedup_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping fallbackAudit representativeArtifact ->
    reconstructionHandle :=
  fun contract =>
    ay_vabd_conj_right originalFingerprint
      (ay_vabd_conj solverBuildIdentity
        (ay_vabd_conj artifactDigest
          (ay_vabd_conj checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact))))))
      contract reconstructionHandle
      (fun _buildProof tail =>
        tail reconstructionHandle
          (fun _digestProof tail2 =>
            tail2 reconstructionHandle
              (fun _replayProof tail3 =>
                tail3 reconstructionHandle
                  (fun reconstructionProof _tail4 =>
                    reconstructionProof))))

theorem ay_vabd_dedup_contract_mapping
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit representativeArtifact : Prop) :
    ay_vabd_dedup_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping fallbackAudit representativeArtifact ->
    exitCodeMapping :=
  fun contract =>
    ay_vabd_conj_right originalFingerprint
      (ay_vabd_conj solverBuildIdentity
        (ay_vabd_conj artifactDigest
          (ay_vabd_conj checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact))))))
      contract exitCodeMapping
      (fun _buildProof tail =>
        tail exitCodeMapping
          (fun _digestProof tail2 =>
            tail2 exitCodeMapping
              (fun _replayProof tail3 =>
                tail3 exitCodeMapping
                  (fun _reconstructionProof tail4 =>
                    tail4 exitCodeMapping
                      (fun mappingProof _tail5 => mappingProof)))))

theorem ay_vabd_dedup_contract_fallback
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit representativeArtifact : Prop) :
    ay_vabd_dedup_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping fallbackAudit representativeArtifact ->
    fallbackAudit :=
  fun contract =>
    ay_vabd_conj_right originalFingerprint
      (ay_vabd_conj solverBuildIdentity
        (ay_vabd_conj artifactDigest
          (ay_vabd_conj checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact))))))
      contract fallbackAudit
      (fun _buildProof tail =>
        tail fallbackAudit
          (fun _digestProof tail2 =>
            tail2 fallbackAudit
              (fun _replayProof tail3 =>
                tail3 fallbackAudit
                  (fun _reconstructionProof tail4 =>
                    tail4 fallbackAudit
                      (fun _mappingProof tail5 =>
                        tail5 fallbackAudit
                          (fun auditProof _representativeProof =>
                            auditProof))))))

theorem ay_vabd_dedup_contract_representative
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit representativeArtifact : Prop) :
    ay_vabd_dedup_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping fallbackAudit representativeArtifact ->
    representativeArtifact :=
  fun contract =>
    ay_vabd_conj_right originalFingerprint
      (ay_vabd_conj solverBuildIdentity
        (ay_vabd_conj artifactDigest
          (ay_vabd_conj checkerReplayTranscript
            (ay_vabd_conj reconstructionHandle
              (ay_vabd_conj exitCodeMapping
                (ay_vabd_conj fallbackAudit representativeArtifact))))))
      contract representativeArtifact
      (fun _buildProof tail =>
        tail representativeArtifact
          (fun _digestProof tail2 =>
            tail2 representativeArtifact
              (fun _replayProof tail3 =>
                tail3 representativeArtifact
                  (fun _reconstructionProof tail4 =>
                    tail4 representativeArtifact
                      (fun _mappingProof tail5 =>
                        tail5 representativeArtifact
                          (fun _auditProof representativeProof =>
                            representativeProof))))))

theorem ay_vabd_sat_dedup_intro
    (dedupContract modelEvidence originalModel : Prop) :
    dedupContract -> modelEvidence -> originalModel ->
    ay_vabd_sat_dedup dedupContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vabd_conj_intro dedupContract
      (ay_vabd_conj modelEvidence originalModel)
      contractProof
      (ay_vabd_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vabd_sat_dedup_contract
    (dedupContract modelEvidence originalModel : Prop) :
    ay_vabd_sat_dedup dedupContract modelEvidence originalModel ->
    dedupContract :=
  fun dedup =>
    ay_vabd_conj_left dedupContract
      (ay_vabd_conj modelEvidence originalModel) dedup

theorem ay_vabd_sat_dedup_original_model
    (dedupContract modelEvidence originalModel : Prop) :
    ay_vabd_sat_dedup dedupContract modelEvidence originalModel ->
    originalModel :=
  fun dedup =>
    ay_vabd_conj_right dedupContract
      (ay_vabd_conj modelEvidence originalModel)
      dedup originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vabd_unsat_dedup_intro
    (dedupContract proofEvidence originalEmptyClause : Prop) :
    dedupContract -> proofEvidence -> originalEmptyClause ->
    ay_vabd_unsat_dedup dedupContract proofEvidence originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vabd_conj_intro dedupContract
      (ay_vabd_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vabd_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vabd_unsat_dedup_contract
    (dedupContract proofEvidence originalEmptyClause : Prop) :
    ay_vabd_unsat_dedup dedupContract proofEvidence originalEmptyClause ->
    dedupContract :=
  fun dedup =>
    ay_vabd_conj_left dedupContract
      (ay_vabd_conj proofEvidence originalEmptyClause) dedup

theorem ay_vabd_unsat_dedup_original_empty_clause
    (dedupContract proofEvidence originalEmptyClause : Prop) :
    ay_vabd_unsat_dedup dedupContract proofEvidence originalEmptyClause ->
    originalEmptyClause :=
  fun dedup =>
    ay_vabd_conj_right dedupContract
      (ay_vabd_conj proofEvidence originalEmptyClause)
      dedup originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vabd_no_claim_dedup_intro
    (dedupContract diagnostic noSemanticClaim : Prop) :
    dedupContract -> diagnostic -> noSemanticClaim ->
    ay_vabd_no_claim_dedup dedupContract diagnostic noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_vabd_conj_intro dedupContract
      (ay_vabd_conj diagnostic noSemanticClaim)
      contractProof
      (ay_vabd_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vabd_no_claim_dedup_no_semantic_claim
    (dedupContract diagnostic noSemanticClaim : Prop) :
    ay_vabd_no_claim_dedup dedupContract diagnostic noSemanticClaim ->
    noSemanticClaim :=
  fun dedup =>
    ay_vabd_conj_right dedupContract
      (ay_vabd_conj diagnostic noSemanticClaim)
      dedup noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vabd_dedup_validation_intro
    (dedupContract checkerAccepted publicEvidence : Prop) :
    dedupContract -> checkerAccepted -> publicEvidence ->
    ay_vabd_dedup_validation dedupContract checkerAccepted publicEvidence :=
  fun contractProof checkerProof publicProof =>
    ay_vabd_conj_intro dedupContract
      (ay_vabd_conj checkerAccepted publicEvidence)
      contractProof
      (ay_vabd_conj_intro checkerAccepted publicEvidence checkerProof
        publicProof)

theorem ay_vabd_dedup_validation_public_evidence
    (dedupContract checkerAccepted publicEvidence : Prop) :
    ay_vabd_dedup_validation dedupContract checkerAccepted publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vabd_conj_right dedupContract
      (ay_vabd_conj checkerAccepted publicEvidence)
      validation publicEvidence
      (fun _checkerProof publicProof => publicProof)

theorem ay_vabd_accepted_sat_dedup_preserves_result
    (dedupContract modelEvidence originalModel unsatFact noClaimFact : Prop) :
    ay_vabd_sat_dedup dedupContract modelEvidence originalModel ->
    ay_vabd_public_result originalModel unsatFact noClaimFact :=
  fun dedup =>
    ay_vabd_disj_left originalModel
      (ay_vabd_disj unsatFact noClaimFact)
      (ay_vabd_sat_dedup_original_model dedupContract modelEvidence
        originalModel dedup)

theorem ay_vabd_accepted_unsat_dedup_preserves_result
    (satFact dedupContract proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_vabd_unsat_dedup dedupContract proofEvidence originalEmptyClause ->
    ay_vabd_public_result satFact originalEmptyClause noClaimFact :=
  fun dedup =>
    ay_vabd_disj_right satFact
      (ay_vabd_disj originalEmptyClause noClaimFact)
      (ay_vabd_disj_left originalEmptyClause noClaimFact
        (ay_vabd_unsat_dedup_original_empty_clause dedupContract
          proofEvidence originalEmptyClause dedup))

theorem ay_vabd_accepted_no_claim_dedup_preserves_result
    (satFact unsatFact dedupContract diagnostic noSemanticClaim : Prop) :
    ay_vabd_no_claim_dedup dedupContract diagnostic noSemanticClaim ->
    ay_vabd_public_result satFact unsatFact noSemanticClaim :=
  fun dedup =>
    ay_vabd_disj_right satFact
      (ay_vabd_disj unsatFact noSemanticClaim)
      (ay_vabd_disj_right unsatFact noSemanticClaim
        (ay_vabd_no_claim_dedup_no_semantic_claim dedupContract diagnostic
          noSemanticClaim dedup))

theorem ay_vabd_sat_dedup_supports_validation
    (dedupContract modelEvidence originalModel checkerAccepted : Prop) :
    ay_vabd_sat_dedup dedupContract modelEvidence originalModel ->
    checkerAccepted ->
    ay_vabd_dedup_validation dedupContract checkerAccepted originalModel :=
  fun dedup checkerProof =>
    ay_vabd_dedup_validation_intro dedupContract checkerAccepted
      originalModel
      (ay_vabd_sat_dedup_contract dedupContract modelEvidence
        originalModel dedup)
      checkerProof
      (ay_vabd_sat_dedup_original_model dedupContract modelEvidence
        originalModel dedup)

theorem ay_vabd_unsat_dedup_supports_validation
    (dedupContract proofEvidence originalEmptyClause checkerAccepted : Prop) :
    ay_vabd_unsat_dedup dedupContract proofEvidence originalEmptyClause ->
    checkerAccepted ->
    ay_vabd_dedup_validation dedupContract checkerAccepted
      originalEmptyClause :=
  fun dedup checkerProof =>
    ay_vabd_dedup_validation_intro dedupContract checkerAccepted
      originalEmptyClause
      (ay_vabd_unsat_dedup_contract dedupContract proofEvidence
        originalEmptyClause dedup)
      checkerProof
      (ay_vabd_unsat_dedup_original_empty_clause dedupContract
        proofEvidence originalEmptyClause dedup)

theorem ay_vabd_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vabd_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vabd_conj_intro reason
      (ay_vabd_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vabd_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vabd_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vabd_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vabd_conj_right reason
      (ay_vabd_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vabd_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vabd_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vabd_conj_right reason
      (ay_vabd_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vabd_recompute_intro
    (reason fallbackAudit fallbackPath : Prop) :
    reason -> fallbackAudit -> fallbackPath ->
    ay_vabd_recompute reason fallbackAudit fallbackPath :=
  fun reasonProof auditProof pathProof =>
    ay_vabd_conj_intro reason
      (ay_vabd_conj fallbackAudit fallbackPath)
      reasonProof
      (ay_vabd_conj_intro fallbackAudit fallbackPath auditProof pathProof)

theorem ay_vabd_dedup_failure_intro
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vabd_blocked_publication satFact unsatFact reason ->
    ay_vabd_recompute reason fallbackAudit fallbackPath ->
    ay_vabd_dedup_failure satFact unsatFact reason fallbackAudit
      fallbackPath :=
  fun blocked recompute =>
    ay_vabd_conj_intro
      (ay_vabd_blocked_publication satFact unsatFact reason)
      (ay_vabd_recompute reason fallbackAudit fallbackPath)
      blocked recompute

theorem ay_vabd_dedup_failure_blocks_sat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vabd_dedup_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vabd_blocked_publication_no_sat satFact unsatFact reason
      (ay_vabd_conj_left
        (ay_vabd_blocked_publication satFact unsatFact reason)
        (ay_vabd_recompute reason fallbackAudit fallbackPath)
        failure)

theorem ay_vabd_dedup_failure_blocks_unsat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vabd_dedup_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vabd_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vabd_conj_left
        (ay_vabd_blocked_publication satFact unsatFact reason)
        (ay_vabd_recompute reason fallbackAudit fallbackPath)
        failure)

theorem ay_vabd_dedup_failure_recompute
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vabd_dedup_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    ay_vabd_recompute reason fallbackAudit fallbackPath :=
  fun failure =>
    ay_vabd_conj_right
      (ay_vabd_blocked_publication satFact unsatFact reason)
      (ay_vabd_recompute reason fallbackAudit fallbackPath)
      failure

theorem ay_vabd_digest_collision_forces_no_claim
    (satFact unsatFact digestCollision fallbackAudit fallbackPath : Prop) :
    digestCollision -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vabd_dedup_failure satFact unsatFact digestCollision fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vabd_dedup_failure_intro satFact unsatFact digestCollision
      fallbackAudit fallbackPath
      (ay_vabd_blocked_publication_intro satFact unsatFact digestCollision
        reasonProof blockSat blockUnsat)
      (ay_vabd_recompute_intro digestCollision fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vabd_missing_representative_forces_no_claim
    (satFact unsatFact missingRepresentative fallbackAudit fallbackPath :
      Prop) :
    missingRepresentative -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vabd_dedup_failure satFact unsatFact missingRepresentative
      fallbackAudit fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vabd_dedup_failure_intro satFact unsatFact missingRepresentative
      fallbackAudit fallbackPath
      (ay_vabd_blocked_publication_intro satFact unsatFact
        missingRepresentative reasonProof blockSat blockUnsat)
      (ay_vabd_recompute_intro missingRepresentative fallbackAudit
        fallbackPath reasonProof auditProof pathProof)

theorem ay_vabd_field_loss_forces_no_claim
    (satFact unsatFact fieldLoss fallbackAudit fallbackPath : Prop) :
    fieldLoss -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vabd_dedup_failure satFact unsatFact fieldLoss fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vabd_dedup_failure_intro satFact unsatFact fieldLoss fallbackAudit
      fallbackPath
      (ay_vabd_blocked_publication_intro satFact unsatFact fieldLoss
        reasonProof blockSat blockUnsat)
      (ay_vabd_recompute_intro fieldLoss fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vabd_replay_gap_forces_no_claim
    (satFact unsatFact replayGap fallbackAudit fallbackPath : Prop) :
    replayGap -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vabd_dedup_failure satFact unsatFact replayGap fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vabd_dedup_failure_intro satFact unsatFact replayGap fallbackAudit
      fallbackPath
      (ay_vabd_blocked_publication_intro satFact unsatFact replayGap
        reasonProof blockSat blockUnsat)
      (ay_vabd_recompute_intro replayGap fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vabd_reconstruction_gap_forces_no_claim
    (satFact unsatFact reconstructionGap fallbackAudit fallbackPath : Prop) :
    reconstructionGap -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vabd_dedup_failure satFact unsatFact reconstructionGap
      fallbackAudit fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vabd_dedup_failure_intro satFact unsatFact reconstructionGap
      fallbackAudit fallbackPath
      (ay_vabd_blocked_publication_intro satFact unsatFact
        reconstructionGap reasonProof blockSat blockUnsat)
      (ay_vabd_recompute_intro reconstructionGap fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vabd_mapping_mismatch_forces_no_claim
    (satFact unsatFact mappingMismatch fallbackAudit fallbackPath : Prop) :
    mappingMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vabd_dedup_failure satFact unsatFact mappingMismatch fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vabd_dedup_failure_intro satFact unsatFact mappingMismatch
      fallbackAudit fallbackPath
      (ay_vabd_blocked_publication_intro satFact unsatFact mappingMismatch
        reasonProof blockSat blockUnsat)
      (ay_vabd_recompute_intro mappingMismatch fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vabd_stale_build_forces_no_claim
    (satFact unsatFact staleBuild fallbackAudit fallbackPath : Prop) :
    staleBuild -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vabd_dedup_failure satFact unsatFact staleBuild fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vabd_dedup_failure_intro satFact unsatFact staleBuild fallbackAudit
      fallbackPath
      (ay_vabd_blocked_publication_intro satFact unsatFact staleBuild
        reasonProof blockSat blockUnsat)
      (ay_vabd_recompute_intro staleBuild fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vabd_audit_contradiction_forces_no_claim
    (satFact unsatFact auditContradiction fallbackAudit fallbackPath : Prop) :
    auditContradiction -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vabd_dedup_failure satFact unsatFact auditContradiction
      fallbackAudit fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vabd_dedup_failure_intro satFact unsatFact auditContradiction
      fallbackAudit fallbackPath
      (ay_vabd_blocked_publication_intro satFact unsatFact
        auditContradiction reasonProof blockSat blockUnsat)
      (ay_vabd_recompute_intro auditContradiction fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vabd_failure_cannot_publish_sat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vabd_dedup_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    satFact -> False :=
  ay_vabd_dedup_failure_blocks_sat satFact unsatFact reason fallbackAudit
    fallbackPath

theorem ay_vabd_failure_cannot_publish_unsat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vabd_dedup_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    unsatFact -> False :=
  ay_vabd_dedup_failure_blocks_unsat satFact unsatFact reason fallbackAudit
    fallbackPath
