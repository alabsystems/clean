-- SAT-COMP validator artifact-retention quorum core.
--
-- A public result remains auditable when a quorum of retained artifacts
-- includes original input fingerprint, solver build identity, artifact digest,
-- checker replay transcript, manifest entry, and fallback/no-claim audit
-- record.  Quorum loss or disagreement downgrades to no-claim/recompute.

def ay_varq_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_varq_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_varq_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_varq_disj satFact (ay_varq_disj unsatFact noClaimFact)

def ay_varq_quorum_contract
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript manifestEntry fallbackAuditRecord : Prop) :
    Prop :=
  ay_varq_conj originalFingerprint
    (ay_varq_conj solverBuildIdentity
      (ay_varq_conj artifactDigest
        (ay_varq_conj checkerReplayTranscript
          (ay_varq_conj manifestEntry fallbackAuditRecord))))

def ay_varq_sat_quorum
    (quorumContract modelEvidence originalModel : Prop) : Prop :=
  ay_varq_conj quorumContract
    (ay_varq_conj modelEvidence originalModel)

def ay_varq_unsat_quorum
    (quorumContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_varq_conj quorumContract
    (ay_varq_conj proofEvidence originalEmptyClause)

def ay_varq_no_claim_quorum
    (quorumContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_varq_conj quorumContract
    (ay_varq_conj diagnostic noSemanticClaim)

def ay_varq_quorum_validation
    (quorumContract checkerAccepted publicEvidence : Prop) : Prop :=
  ay_varq_conj quorumContract
    (ay_varq_conj checkerAccepted publicEvidence)

def ay_varq_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_varq_conj reason
    (ay_varq_conj (satFact -> False) (unsatFact -> False))

def ay_varq_recompute
    (reason fallbackAuditRecord fallbackPath : Prop) : Prop :=
  ay_varq_conj reason (ay_varq_conj fallbackAuditRecord fallbackPath)

def ay_varq_quorum_failure
    (satFact unsatFact reason fallbackAuditRecord fallbackPath : Prop) :
    Prop :=
  ay_varq_conj
    (ay_varq_blocked_publication satFact unsatFact reason)
    (ay_varq_recompute reason fallbackAuditRecord fallbackPath)

theorem ay_varq_conj_intro (left right : Prop) :
    left -> right -> ay_varq_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_varq_conj_left (left right : Prop) :
    ay_varq_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_varq_conj_right (left right : Prop) :
    ay_varq_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_varq_disj_left (left right : Prop) :
    left -> ay_varq_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_varq_disj_right (left right : Prop) :
    right -> ay_varq_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_varq_quorum_contract_intro
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript manifestEntry fallbackAuditRecord : Prop) :
    originalFingerprint -> solverBuildIdentity -> artifactDigest ->
    checkerReplayTranscript -> manifestEntry -> fallbackAuditRecord ->
    ay_varq_quorum_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript manifestEntry
      fallbackAuditRecord :=
  fun fingerprintProof buildProof digestProof transcriptProof manifestProof
      fallbackProof =>
    ay_varq_conj_intro originalFingerprint
      (ay_varq_conj solverBuildIdentity
        (ay_varq_conj artifactDigest
          (ay_varq_conj checkerReplayTranscript
            (ay_varq_conj manifestEntry fallbackAuditRecord))))
      fingerprintProof
      (ay_varq_conj_intro solverBuildIdentity
        (ay_varq_conj artifactDigest
          (ay_varq_conj checkerReplayTranscript
            (ay_varq_conj manifestEntry fallbackAuditRecord)))
        buildProof
        (ay_varq_conj_intro artifactDigest
          (ay_varq_conj checkerReplayTranscript
            (ay_varq_conj manifestEntry fallbackAuditRecord))
          digestProof
          (ay_varq_conj_intro checkerReplayTranscript
            (ay_varq_conj manifestEntry fallbackAuditRecord)
            transcriptProof
            (ay_varq_conj_intro manifestEntry fallbackAuditRecord
              manifestProof fallbackProof))))

theorem ay_varq_quorum_contract_fingerprint
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript manifestEntry fallbackAuditRecord : Prop) :
    ay_varq_quorum_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript manifestEntry
      fallbackAuditRecord ->
    originalFingerprint :=
  fun contract =>
    ay_varq_conj_left originalFingerprint
      (ay_varq_conj solverBuildIdentity
        (ay_varq_conj artifactDigest
          (ay_varq_conj checkerReplayTranscript
            (ay_varq_conj manifestEntry fallbackAuditRecord))))
      contract

theorem ay_varq_quorum_contract_build
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript manifestEntry fallbackAuditRecord : Prop) :
    ay_varq_quorum_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript manifestEntry
      fallbackAuditRecord ->
    solverBuildIdentity :=
  fun contract =>
    ay_varq_conj_right originalFingerprint
      (ay_varq_conj solverBuildIdentity
        (ay_varq_conj artifactDigest
          (ay_varq_conj checkerReplayTranscript
            (ay_varq_conj manifestEntry fallbackAuditRecord))))
      contract solverBuildIdentity
      (fun buildProof _tail => buildProof)

theorem ay_varq_quorum_contract_digest
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript manifestEntry fallbackAuditRecord : Prop) :
    ay_varq_quorum_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript manifestEntry
      fallbackAuditRecord ->
    artifactDigest :=
  fun contract =>
    ay_varq_conj_right originalFingerprint
      (ay_varq_conj solverBuildIdentity
        (ay_varq_conj artifactDigest
          (ay_varq_conj checkerReplayTranscript
            (ay_varq_conj manifestEntry fallbackAuditRecord))))
      contract artifactDigest
      (fun _buildProof tail =>
        tail artifactDigest (fun digestProof _tail2 => digestProof))

theorem ay_varq_quorum_contract_transcript
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript manifestEntry fallbackAuditRecord : Prop) :
    ay_varq_quorum_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript manifestEntry
      fallbackAuditRecord ->
    checkerReplayTranscript :=
  fun contract =>
    ay_varq_conj_right originalFingerprint
      (ay_varq_conj solverBuildIdentity
        (ay_varq_conj artifactDigest
          (ay_varq_conj checkerReplayTranscript
            (ay_varq_conj manifestEntry fallbackAuditRecord))))
      contract checkerReplayTranscript
      (fun _buildProof tail =>
        tail checkerReplayTranscript
          (fun _digestProof tail2 =>
            tail2 checkerReplayTranscript
              (fun transcriptProof _tail3 => transcriptProof)))

theorem ay_varq_quorum_contract_manifest
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript manifestEntry fallbackAuditRecord : Prop) :
    ay_varq_quorum_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript manifestEntry
      fallbackAuditRecord ->
    manifestEntry :=
  fun contract =>
    ay_varq_conj_right originalFingerprint
      (ay_varq_conj solverBuildIdentity
        (ay_varq_conj artifactDigest
          (ay_varq_conj checkerReplayTranscript
            (ay_varq_conj manifestEntry fallbackAuditRecord))))
      contract manifestEntry
      (fun _buildProof tail =>
        tail manifestEntry
          (fun _digestProof tail2 =>
            tail2 manifestEntry
              (fun _transcriptProof tail3 =>
                tail3 manifestEntry
                  (fun manifestProof _fallbackProof => manifestProof))))

theorem ay_varq_quorum_contract_fallback
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript manifestEntry fallbackAuditRecord : Prop) :
    ay_varq_quorum_contract originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript manifestEntry
      fallbackAuditRecord ->
    fallbackAuditRecord :=
  fun contract =>
    ay_varq_conj_right originalFingerprint
      (ay_varq_conj solverBuildIdentity
        (ay_varq_conj artifactDigest
          (ay_varq_conj checkerReplayTranscript
            (ay_varq_conj manifestEntry fallbackAuditRecord))))
      contract fallbackAuditRecord
      (fun _buildProof tail =>
        tail fallbackAuditRecord
          (fun _digestProof tail2 =>
            tail2 fallbackAuditRecord
              (fun _transcriptProof tail3 =>
                tail3 fallbackAuditRecord
                  (fun _manifestProof fallbackProof => fallbackProof))))

theorem ay_varq_sat_quorum_intro
    (quorumContract modelEvidence originalModel : Prop) :
    quorumContract -> modelEvidence -> originalModel ->
    ay_varq_sat_quorum quorumContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_varq_conj_intro quorumContract
      (ay_varq_conj modelEvidence originalModel)
      contractProof
      (ay_varq_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_varq_sat_quorum_contract
    (quorumContract modelEvidence originalModel : Prop) :
    ay_varq_sat_quorum quorumContract modelEvidence originalModel ->
    quorumContract :=
  fun quorum =>
    ay_varq_conj_left quorumContract
      (ay_varq_conj modelEvidence originalModel) quorum

theorem ay_varq_sat_quorum_original_model
    (quorumContract modelEvidence originalModel : Prop) :
    ay_varq_sat_quorum quorumContract modelEvidence originalModel ->
    originalModel :=
  fun quorum =>
    ay_varq_conj_right quorumContract
      (ay_varq_conj modelEvidence originalModel)
      quorum originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_varq_unsat_quorum_intro
    (quorumContract proofEvidence originalEmptyClause : Prop) :
    quorumContract -> proofEvidence -> originalEmptyClause ->
    ay_varq_unsat_quorum quorumContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_varq_conj_intro quorumContract
      (ay_varq_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_varq_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_varq_unsat_quorum_contract
    (quorumContract proofEvidence originalEmptyClause : Prop) :
    ay_varq_unsat_quorum quorumContract proofEvidence
      originalEmptyClause ->
    quorumContract :=
  fun quorum =>
    ay_varq_conj_left quorumContract
      (ay_varq_conj proofEvidence originalEmptyClause) quorum

theorem ay_varq_unsat_quorum_original_empty_clause
    (quorumContract proofEvidence originalEmptyClause : Prop) :
    ay_varq_unsat_quorum quorumContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun quorum =>
    ay_varq_conj_right quorumContract
      (ay_varq_conj proofEvidence originalEmptyClause)
      quorum originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_varq_no_claim_quorum_intro
    (quorumContract diagnostic noSemanticClaim : Prop) :
    quorumContract -> diagnostic -> noSemanticClaim ->
    ay_varq_no_claim_quorum quorumContract diagnostic noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_varq_conj_intro quorumContract
      (ay_varq_conj diagnostic noSemanticClaim)
      contractProof
      (ay_varq_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_varq_no_claim_quorum_no_semantic_claim
    (quorumContract diagnostic noSemanticClaim : Prop) :
    ay_varq_no_claim_quorum quorumContract diagnostic noSemanticClaim ->
    noSemanticClaim :=
  fun quorum =>
    ay_varq_conj_right quorumContract
      (ay_varq_conj diagnostic noSemanticClaim)
      quorum noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_varq_quorum_validation_intro
    (quorumContract checkerAccepted publicEvidence : Prop) :
    quorumContract -> checkerAccepted -> publicEvidence ->
    ay_varq_quorum_validation quorumContract checkerAccepted
      publicEvidence :=
  fun contractProof checkerProof publicProof =>
    ay_varq_conj_intro quorumContract
      (ay_varq_conj checkerAccepted publicEvidence)
      contractProof
      (ay_varq_conj_intro checkerAccepted publicEvidence checkerProof
        publicProof)

theorem ay_varq_quorum_validation_public_evidence
    (quorumContract checkerAccepted publicEvidence : Prop) :
    ay_varq_quorum_validation quorumContract checkerAccepted
      publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_varq_conj_right quorumContract
      (ay_varq_conj checkerAccepted publicEvidence)
      validation publicEvidence
      (fun _checkerProof publicProof => publicProof)

theorem ay_varq_sat_quorum_validates_same_result
    (quorumContract modelEvidence originalModel unsatFact noClaimFact :
      Prop) :
    ay_varq_sat_quorum quorumContract modelEvidence originalModel ->
    ay_varq_public_result originalModel unsatFact noClaimFact :=
  fun quorum =>
    ay_varq_disj_left originalModel
      (ay_varq_disj unsatFact noClaimFact)
      (ay_varq_sat_quorum_original_model quorumContract modelEvidence
        originalModel quorum)

theorem ay_varq_unsat_quorum_validates_same_result
    (satFact quorumContract proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_varq_unsat_quorum quorumContract proofEvidence
      originalEmptyClause ->
    ay_varq_public_result satFact originalEmptyClause noClaimFact :=
  fun quorum =>
    ay_varq_disj_right satFact
      (ay_varq_disj originalEmptyClause noClaimFact)
      (ay_varq_disj_left originalEmptyClause noClaimFact
        (ay_varq_unsat_quorum_original_empty_clause quorumContract
          proofEvidence originalEmptyClause quorum))

theorem ay_varq_no_claim_quorum_validates_same_result
    (satFact unsatFact quorumContract diagnostic noSemanticClaim : Prop) :
    ay_varq_no_claim_quorum quorumContract diagnostic noSemanticClaim ->
    ay_varq_public_result satFact unsatFact noSemanticClaim :=
  fun quorum =>
    ay_varq_disj_right satFact
      (ay_varq_disj unsatFact noSemanticClaim)
      (ay_varq_disj_right unsatFact noSemanticClaim
        (ay_varq_no_claim_quorum_no_semantic_claim quorumContract
          diagnostic noSemanticClaim quorum))

theorem ay_varq_sat_quorum_supports_validation
    (quorumContract modelEvidence originalModel checkerAccepted : Prop) :
    ay_varq_sat_quorum quorumContract modelEvidence originalModel ->
    checkerAccepted ->
    ay_varq_quorum_validation quorumContract checkerAccepted originalModel :=
  fun quorum checkerProof =>
    ay_varq_quorum_validation_intro quorumContract checkerAccepted
      originalModel
      (ay_varq_sat_quorum_contract quorumContract modelEvidence
        originalModel quorum)
      checkerProof
      (ay_varq_sat_quorum_original_model quorumContract modelEvidence
        originalModel quorum)

theorem ay_varq_unsat_quorum_supports_validation
    (quorumContract proofEvidence originalEmptyClause checkerAccepted : Prop) :
    ay_varq_unsat_quorum quorumContract proofEvidence
      originalEmptyClause ->
    checkerAccepted ->
    ay_varq_quorum_validation quorumContract checkerAccepted
      originalEmptyClause :=
  fun quorum checkerProof =>
    ay_varq_quorum_validation_intro quorumContract checkerAccepted
      originalEmptyClause
      (ay_varq_unsat_quorum_contract quorumContract proofEvidence
        originalEmptyClause quorum)
      checkerProof
      (ay_varq_unsat_quorum_original_empty_clause quorumContract
        proofEvidence originalEmptyClause quorum)

theorem ay_varq_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_varq_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_varq_conj_intro reason
      (ay_varq_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_varq_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_varq_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_varq_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_varq_conj_right reason
      (ay_varq_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_varq_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_varq_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_varq_conj_right reason
      (ay_varq_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_varq_recompute_intro
    (reason fallbackAuditRecord fallbackPath : Prop) :
    reason -> fallbackAuditRecord -> fallbackPath ->
    ay_varq_recompute reason fallbackAuditRecord fallbackPath :=
  fun reasonProof fallbackProof pathProof =>
    ay_varq_conj_intro reason
      (ay_varq_conj fallbackAuditRecord fallbackPath)
      reasonProof
      (ay_varq_conj_intro fallbackAuditRecord fallbackPath fallbackProof
        pathProof)

theorem ay_varq_quorum_failure_intro
    (satFact unsatFact reason fallbackAuditRecord fallbackPath : Prop) :
    ay_varq_blocked_publication satFact unsatFact reason ->
    ay_varq_recompute reason fallbackAuditRecord fallbackPath ->
    ay_varq_quorum_failure satFact unsatFact reason fallbackAuditRecord
      fallbackPath :=
  fun blocked recompute =>
    ay_varq_conj_intro
      (ay_varq_blocked_publication satFact unsatFact reason)
      (ay_varq_recompute reason fallbackAuditRecord fallbackPath)
      blocked recompute

theorem ay_varq_quorum_failure_blocks_sat
    (satFact unsatFact reason fallbackAuditRecord fallbackPath : Prop) :
    ay_varq_quorum_failure satFact unsatFact reason fallbackAuditRecord
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_varq_blocked_publication_no_sat satFact unsatFact reason
      (ay_varq_conj_left
        (ay_varq_blocked_publication satFact unsatFact reason)
        (ay_varq_recompute reason fallbackAuditRecord fallbackPath)
        failure)

theorem ay_varq_quorum_failure_blocks_unsat
    (satFact unsatFact reason fallbackAuditRecord fallbackPath : Prop) :
    ay_varq_quorum_failure satFact unsatFact reason fallbackAuditRecord
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_varq_blocked_publication_no_unsat satFact unsatFact reason
      (ay_varq_conj_left
        (ay_varq_blocked_publication satFact unsatFact reason)
        (ay_varq_recompute reason fallbackAuditRecord fallbackPath)
        failure)

theorem ay_varq_quorum_failure_recompute
    (satFact unsatFact reason fallbackAuditRecord fallbackPath : Prop) :
    ay_varq_quorum_failure satFact unsatFact reason fallbackAuditRecord
      fallbackPath ->
    ay_varq_recompute reason fallbackAuditRecord fallbackPath :=
  fun failure =>
    ay_varq_conj_right
      (ay_varq_blocked_publication satFact unsatFact reason)
      (ay_varq_recompute reason fallbackAuditRecord fallbackPath)
      failure

theorem ay_varq_quorum_loss_forces_no_claim
    (satFact unsatFact quorumLoss fallbackAuditRecord fallbackPath : Prop) :
    quorumLoss -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAuditRecord -> fallbackPath ->
    ay_varq_quorum_failure satFact unsatFact quorumLoss
      fallbackAuditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_varq_quorum_failure_intro satFact unsatFact quorumLoss
      fallbackAuditRecord fallbackPath
      (ay_varq_blocked_publication_intro satFact unsatFact quorumLoss
        reasonProof blockSat blockUnsat)
      (ay_varq_recompute_intro quorumLoss fallbackAuditRecord fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_varq_digest_disagreement_forces_no_claim
    (satFact unsatFact digestDisagreement fallbackAuditRecord fallbackPath :
      Prop) :
    digestDisagreement -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAuditRecord -> fallbackPath ->
    ay_varq_quorum_failure satFact unsatFact digestDisagreement
      fallbackAuditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_varq_quorum_failure_intro satFact unsatFact digestDisagreement
      fallbackAuditRecord fallbackPath
      (ay_varq_blocked_publication_intro satFact unsatFact
        digestDisagreement reasonProof blockSat blockUnsat)
      (ay_varq_recompute_intro digestDisagreement fallbackAuditRecord
        fallbackPath reasonProof fallbackProof pathProof)

theorem ay_varq_stale_manifest_entry_forces_no_claim
    (satFact unsatFact staleManifest fallbackAuditRecord fallbackPath :
      Prop) :
    staleManifest -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAuditRecord -> fallbackPath ->
    ay_varq_quorum_failure satFact unsatFact staleManifest
      fallbackAuditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_varq_quorum_failure_intro satFact unsatFact staleManifest
      fallbackAuditRecord fallbackPath
      (ay_varq_blocked_publication_intro satFact unsatFact staleManifest
        reasonProof blockSat blockUnsat)
      (ay_varq_recompute_intro staleManifest fallbackAuditRecord
        fallbackPath reasonProof fallbackProof pathProof)

theorem ay_varq_missing_replay_transcript_forces_no_claim
    (satFact unsatFact missingTranscript fallbackAuditRecord fallbackPath :
      Prop) :
    missingTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAuditRecord -> fallbackPath ->
    ay_varq_quorum_failure satFact unsatFact missingTranscript
      fallbackAuditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_varq_quorum_failure_intro satFact unsatFact missingTranscript
      fallbackAuditRecord fallbackPath
      (ay_varq_blocked_publication_intro satFact unsatFact
        missingTranscript reasonProof blockSat blockUnsat)
      (ay_varq_recompute_intro missingTranscript fallbackAuditRecord
        fallbackPath reasonProof fallbackProof pathProof)

theorem ay_varq_missing_fallback_record_forces_no_claim
    (satFact unsatFact missingFallback fallbackAuditRecord fallbackPath :
      Prop) :
    missingFallback -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAuditRecord -> fallbackPath ->
    ay_varq_quorum_failure satFact unsatFact missingFallback
      fallbackAuditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_varq_quorum_failure_intro satFact unsatFact missingFallback
      fallbackAuditRecord fallbackPath
      (ay_varq_blocked_publication_intro satFact unsatFact missingFallback
        reasonProof blockSat blockUnsat)
      (ay_varq_recompute_intro missingFallback fallbackAuditRecord
        fallbackPath reasonProof fallbackProof pathProof)

theorem ay_varq_audit_contradiction_forces_no_claim
    (satFact unsatFact auditContradiction fallbackAuditRecord fallbackPath :
      Prop) :
    auditContradiction -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAuditRecord -> fallbackPath ->
    ay_varq_quorum_failure satFact unsatFact auditContradiction
      fallbackAuditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_varq_quorum_failure_intro satFact unsatFact auditContradiction
      fallbackAuditRecord fallbackPath
      (ay_varq_blocked_publication_intro satFact unsatFact
        auditContradiction reasonProof blockSat blockUnsat)
      (ay_varq_recompute_intro auditContradiction fallbackAuditRecord
        fallbackPath reasonProof fallbackProof pathProof)

theorem ay_varq_failure_cannot_publish_sat
    (satFact unsatFact reason fallbackAuditRecord fallbackPath : Prop) :
    ay_varq_quorum_failure satFact unsatFact reason fallbackAuditRecord
      fallbackPath ->
    satFact -> False :=
  ay_varq_quorum_failure_blocks_sat satFact unsatFact reason
    fallbackAuditRecord fallbackPath

theorem ay_varq_failure_cannot_publish_unsat
    (satFact unsatFact reason fallbackAuditRecord fallbackPath : Prop) :
    ay_varq_quorum_failure satFact unsatFact reason fallbackAuditRecord
      fallbackPath ->
    unsatFact -> False :=
  ay_varq_quorum_failure_blocks_unsat satFact unsatFact reason
    fallbackAuditRecord fallbackPath
