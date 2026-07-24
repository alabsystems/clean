-- SAT-COMP validator cross-platform exit-code replay core.
--
-- Public SAT/UNSAT/no-claim results are portable across platforms only when
-- exit-code mapping, platform/runtime fingerprint, checker replay transcript,
-- artifact digest, solver-build evidence, and retained audit record agree.
-- Drift or rejection downgrades to no-claim/recompute and blocks SAT/UNSAT.

def ay_vcpe_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vcpe_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vcpe_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vcpe_disj satFact (ay_vcpe_disj unsatFact noClaimFact)

def ay_vcpe_cross_platform_contract
    (exitCodeMapping platformRuntimeFingerprint checkerReplayTranscript
      artifactDigest solverBuildEvidence retainedAuditRecord : Prop) : Prop :=
  ay_vcpe_conj exitCodeMapping
    (ay_vcpe_conj platformRuntimeFingerprint
      (ay_vcpe_conj checkerReplayTranscript
        (ay_vcpe_conj artifactDigest
          (ay_vcpe_conj solverBuildEvidence retainedAuditRecord))))

def ay_vcpe_sat_replay
    (crossPlatformContract modelEvidence originalModel : Prop) : Prop :=
  ay_vcpe_conj crossPlatformContract
    (ay_vcpe_conj modelEvidence originalModel)

def ay_vcpe_unsat_replay
    (crossPlatformContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vcpe_conj crossPlatformContract
    (ay_vcpe_conj proofEvidence originalEmptyClause)

def ay_vcpe_no_claim_replay
    (crossPlatformContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vcpe_conj crossPlatformContract
    (ay_vcpe_conj diagnostic noSemanticClaim)

def ay_vcpe_ported_validation
    (crossPlatformContract checkerAccepted publicEvidence : Prop) : Prop :=
  ay_vcpe_conj crossPlatformContract
    (ay_vcpe_conj checkerAccepted publicEvidence)

def ay_vcpe_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vcpe_conj reason
    (ay_vcpe_conj (satFact -> False) (unsatFact -> False))

def ay_vcpe_recompute
    (reason auditRecord fallbackPath : Prop) : Prop :=
  ay_vcpe_conj reason (ay_vcpe_conj auditRecord fallbackPath)

def ay_vcpe_cross_platform_failure
    (satFact unsatFact reason auditRecord fallbackPath : Prop) : Prop :=
  ay_vcpe_conj
    (ay_vcpe_blocked_publication satFact unsatFact reason)
    (ay_vcpe_recompute reason auditRecord fallbackPath)

theorem ay_vcpe_conj_intro (left right : Prop) :
    left -> right -> ay_vcpe_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcpe_conj_left (left right : Prop) :
    ay_vcpe_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcpe_conj_right (left right : Prop) :
    ay_vcpe_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcpe_disj_left (left right : Prop) :
    left -> ay_vcpe_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vcpe_disj_right (left right : Prop) :
    right -> ay_vcpe_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcpe_cross_platform_contract_intro
    (exitCodeMapping platformRuntimeFingerprint checkerReplayTranscript
      artifactDigest solverBuildEvidence retainedAuditRecord : Prop) :
    exitCodeMapping -> platformRuntimeFingerprint ->
    checkerReplayTranscript -> artifactDigest -> solverBuildEvidence ->
    retainedAuditRecord ->
    ay_vcpe_cross_platform_contract exitCodeMapping
      platformRuntimeFingerprint checkerReplayTranscript artifactDigest
      solverBuildEvidence retainedAuditRecord :=
  fun mappingProof platformProof transcriptProof digestProof buildProof
      auditProof =>
    ay_vcpe_conj_intro exitCodeMapping
      (ay_vcpe_conj platformRuntimeFingerprint
        (ay_vcpe_conj checkerReplayTranscript
          (ay_vcpe_conj artifactDigest
            (ay_vcpe_conj solverBuildEvidence retainedAuditRecord))))
      mappingProof
      (ay_vcpe_conj_intro platformRuntimeFingerprint
        (ay_vcpe_conj checkerReplayTranscript
          (ay_vcpe_conj artifactDigest
            (ay_vcpe_conj solverBuildEvidence retainedAuditRecord)))
        platformProof
        (ay_vcpe_conj_intro checkerReplayTranscript
          (ay_vcpe_conj artifactDigest
            (ay_vcpe_conj solverBuildEvidence retainedAuditRecord))
          transcriptProof
          (ay_vcpe_conj_intro artifactDigest
            (ay_vcpe_conj solverBuildEvidence retainedAuditRecord)
            digestProof
            (ay_vcpe_conj_intro solverBuildEvidence retainedAuditRecord
              buildProof auditProof))))

theorem ay_vcpe_cross_platform_contract_mapping
    (exitCodeMapping platformRuntimeFingerprint checkerReplayTranscript
      artifactDigest solverBuildEvidence retainedAuditRecord : Prop) :
    ay_vcpe_cross_platform_contract exitCodeMapping
      platformRuntimeFingerprint checkerReplayTranscript artifactDigest
      solverBuildEvidence retainedAuditRecord ->
    exitCodeMapping :=
  fun contract =>
    ay_vcpe_conj_left exitCodeMapping
      (ay_vcpe_conj platformRuntimeFingerprint
        (ay_vcpe_conj checkerReplayTranscript
          (ay_vcpe_conj artifactDigest
            (ay_vcpe_conj solverBuildEvidence retainedAuditRecord))))
      contract

theorem ay_vcpe_cross_platform_contract_platform
    (exitCodeMapping platformRuntimeFingerprint checkerReplayTranscript
      artifactDigest solverBuildEvidence retainedAuditRecord : Prop) :
    ay_vcpe_cross_platform_contract exitCodeMapping
      platformRuntimeFingerprint checkerReplayTranscript artifactDigest
      solverBuildEvidence retainedAuditRecord ->
    platformRuntimeFingerprint :=
  fun contract =>
    ay_vcpe_conj_right exitCodeMapping
      (ay_vcpe_conj platformRuntimeFingerprint
        (ay_vcpe_conj checkerReplayTranscript
          (ay_vcpe_conj artifactDigest
            (ay_vcpe_conj solverBuildEvidence retainedAuditRecord))))
      contract platformRuntimeFingerprint
      (fun platformProof _tail => platformProof)

theorem ay_vcpe_cross_platform_contract_transcript
    (exitCodeMapping platformRuntimeFingerprint checkerReplayTranscript
      artifactDigest solverBuildEvidence retainedAuditRecord : Prop) :
    ay_vcpe_cross_platform_contract exitCodeMapping
      platformRuntimeFingerprint checkerReplayTranscript artifactDigest
      solverBuildEvidence retainedAuditRecord ->
    checkerReplayTranscript :=
  fun contract =>
    ay_vcpe_conj_right exitCodeMapping
      (ay_vcpe_conj platformRuntimeFingerprint
        (ay_vcpe_conj checkerReplayTranscript
          (ay_vcpe_conj artifactDigest
            (ay_vcpe_conj solverBuildEvidence retainedAuditRecord))))
      contract checkerReplayTranscript
      (fun _platformProof tail =>
        tail checkerReplayTranscript
          (fun transcriptProof _tail2 => transcriptProof))

theorem ay_vcpe_cross_platform_contract_digest
    (exitCodeMapping platformRuntimeFingerprint checkerReplayTranscript
      artifactDigest solverBuildEvidence retainedAuditRecord : Prop) :
    ay_vcpe_cross_platform_contract exitCodeMapping
      platformRuntimeFingerprint checkerReplayTranscript artifactDigest
      solverBuildEvidence retainedAuditRecord ->
    artifactDigest :=
  fun contract =>
    ay_vcpe_conj_right exitCodeMapping
      (ay_vcpe_conj platformRuntimeFingerprint
        (ay_vcpe_conj checkerReplayTranscript
          (ay_vcpe_conj artifactDigest
            (ay_vcpe_conj solverBuildEvidence retainedAuditRecord))))
      contract artifactDigest
      (fun _platformProof tail =>
        tail artifactDigest
          (fun _transcriptProof tail2 =>
            tail2 artifactDigest (fun digestProof _tail3 => digestProof)))

theorem ay_vcpe_cross_platform_contract_build
    (exitCodeMapping platformRuntimeFingerprint checkerReplayTranscript
      artifactDigest solverBuildEvidence retainedAuditRecord : Prop) :
    ay_vcpe_cross_platform_contract exitCodeMapping
      platformRuntimeFingerprint checkerReplayTranscript artifactDigest
      solverBuildEvidence retainedAuditRecord ->
    solverBuildEvidence :=
  fun contract =>
    ay_vcpe_conj_right exitCodeMapping
      (ay_vcpe_conj platformRuntimeFingerprint
        (ay_vcpe_conj checkerReplayTranscript
          (ay_vcpe_conj artifactDigest
            (ay_vcpe_conj solverBuildEvidence retainedAuditRecord))))
      contract solverBuildEvidence
      (fun _platformProof tail =>
        tail solverBuildEvidence
          (fun _transcriptProof tail2 =>
            tail2 solverBuildEvidence
              (fun _digestProof tail3 =>
                tail3 solverBuildEvidence
                  (fun buildProof _auditProof => buildProof))))

theorem ay_vcpe_cross_platform_contract_audit
    (exitCodeMapping platformRuntimeFingerprint checkerReplayTranscript
      artifactDigest solverBuildEvidence retainedAuditRecord : Prop) :
    ay_vcpe_cross_platform_contract exitCodeMapping
      platformRuntimeFingerprint checkerReplayTranscript artifactDigest
      solverBuildEvidence retainedAuditRecord ->
    retainedAuditRecord :=
  fun contract =>
    ay_vcpe_conj_right exitCodeMapping
      (ay_vcpe_conj platformRuntimeFingerprint
        (ay_vcpe_conj checkerReplayTranscript
          (ay_vcpe_conj artifactDigest
            (ay_vcpe_conj solverBuildEvidence retainedAuditRecord))))
      contract retainedAuditRecord
      (fun _platformProof tail =>
        tail retainedAuditRecord
          (fun _transcriptProof tail2 =>
            tail2 retainedAuditRecord
              (fun _digestProof tail3 =>
                tail3 retainedAuditRecord
                  (fun _buildProof auditProof => auditProof))))

theorem ay_vcpe_sat_replay_intro
    (crossPlatformContract modelEvidence originalModel : Prop) :
    crossPlatformContract -> modelEvidence -> originalModel ->
    ay_vcpe_sat_replay crossPlatformContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vcpe_conj_intro crossPlatformContract
      (ay_vcpe_conj modelEvidence originalModel)
      contractProof
      (ay_vcpe_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vcpe_sat_replay_contract
    (crossPlatformContract modelEvidence originalModel : Prop) :
    ay_vcpe_sat_replay crossPlatformContract modelEvidence originalModel ->
    crossPlatformContract :=
  fun replay =>
    ay_vcpe_conj_left crossPlatformContract
      (ay_vcpe_conj modelEvidence originalModel) replay

theorem ay_vcpe_sat_replay_original_model
    (crossPlatformContract modelEvidence originalModel : Prop) :
    ay_vcpe_sat_replay crossPlatformContract modelEvidence originalModel ->
    originalModel :=
  fun replay =>
    ay_vcpe_conj_right crossPlatformContract
      (ay_vcpe_conj modelEvidence originalModel)
      replay originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vcpe_unsat_replay_intro
    (crossPlatformContract proofEvidence originalEmptyClause : Prop) :
    crossPlatformContract -> proofEvidence -> originalEmptyClause ->
    ay_vcpe_unsat_replay crossPlatformContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vcpe_conj_intro crossPlatformContract
      (ay_vcpe_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vcpe_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vcpe_unsat_replay_contract
    (crossPlatformContract proofEvidence originalEmptyClause : Prop) :
    ay_vcpe_unsat_replay crossPlatformContract proofEvidence
      originalEmptyClause ->
    crossPlatformContract :=
  fun replay =>
    ay_vcpe_conj_left crossPlatformContract
      (ay_vcpe_conj proofEvidence originalEmptyClause) replay

theorem ay_vcpe_unsat_replay_original_empty_clause
    (crossPlatformContract proofEvidence originalEmptyClause : Prop) :
    ay_vcpe_unsat_replay crossPlatformContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun replay =>
    ay_vcpe_conj_right crossPlatformContract
      (ay_vcpe_conj proofEvidence originalEmptyClause)
      replay originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vcpe_no_claim_replay_intro
    (crossPlatformContract diagnostic noSemanticClaim : Prop) :
    crossPlatformContract -> diagnostic -> noSemanticClaim ->
    ay_vcpe_no_claim_replay crossPlatformContract diagnostic
      noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_vcpe_conj_intro crossPlatformContract
      (ay_vcpe_conj diagnostic noSemanticClaim)
      contractProof
      (ay_vcpe_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vcpe_no_claim_replay_no_semantic_claim
    (crossPlatformContract diagnostic noSemanticClaim : Prop) :
    ay_vcpe_no_claim_replay crossPlatformContract diagnostic
      noSemanticClaim ->
    noSemanticClaim :=
  fun replay =>
    ay_vcpe_conj_right crossPlatformContract
      (ay_vcpe_conj diagnostic noSemanticClaim)
      replay noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vcpe_ported_validation_intro
    (crossPlatformContract checkerAccepted publicEvidence : Prop) :
    crossPlatformContract -> checkerAccepted -> publicEvidence ->
    ay_vcpe_ported_validation crossPlatformContract checkerAccepted
      publicEvidence :=
  fun contractProof checkerProof publicProof =>
    ay_vcpe_conj_intro crossPlatformContract
      (ay_vcpe_conj checkerAccepted publicEvidence)
      contractProof
      (ay_vcpe_conj_intro checkerAccepted publicEvidence checkerProof
        publicProof)

theorem ay_vcpe_ported_validation_public_evidence
    (crossPlatformContract checkerAccepted publicEvidence : Prop) :
    ay_vcpe_ported_validation crossPlatformContract checkerAccepted
      publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vcpe_conj_right crossPlatformContract
      (ay_vcpe_conj checkerAccepted publicEvidence)
      validation publicEvidence
      (fun _checkerProof publicProof => publicProof)

theorem ay_vcpe_accepted_sat_replay_preserves_result
    (crossPlatformContract modelEvidence originalModel unsatFact
      noClaimFact : Prop) :
    ay_vcpe_sat_replay crossPlatformContract modelEvidence originalModel ->
    ay_vcpe_public_result originalModel unsatFact noClaimFact :=
  fun replay =>
    ay_vcpe_disj_left originalModel
      (ay_vcpe_disj unsatFact noClaimFact)
      (ay_vcpe_sat_replay_original_model crossPlatformContract
        modelEvidence originalModel replay)

theorem ay_vcpe_accepted_unsat_replay_preserves_result
    (satFact crossPlatformContract proofEvidence originalEmptyClause
      noClaimFact : Prop) :
    ay_vcpe_unsat_replay crossPlatformContract proofEvidence
      originalEmptyClause ->
    ay_vcpe_public_result satFact originalEmptyClause noClaimFact :=
  fun replay =>
    ay_vcpe_disj_right satFact
      (ay_vcpe_disj originalEmptyClause noClaimFact)
      (ay_vcpe_disj_left originalEmptyClause noClaimFact
        (ay_vcpe_unsat_replay_original_empty_clause crossPlatformContract
          proofEvidence originalEmptyClause replay))

theorem ay_vcpe_accepted_no_claim_replay_preserves_result
    (satFact unsatFact crossPlatformContract diagnostic noSemanticClaim :
      Prop) :
    ay_vcpe_no_claim_replay crossPlatformContract diagnostic
      noSemanticClaim ->
    ay_vcpe_public_result satFact unsatFact noSemanticClaim :=
  fun replay =>
    ay_vcpe_disj_right satFact
      (ay_vcpe_disj unsatFact noSemanticClaim)
      (ay_vcpe_disj_right unsatFact noSemanticClaim
        (ay_vcpe_no_claim_replay_no_semantic_claim crossPlatformContract
          diagnostic noSemanticClaim replay))

theorem ay_vcpe_sat_replay_supports_ported_validation
    (crossPlatformContract modelEvidence originalModel checkerAccepted :
      Prop) :
    ay_vcpe_sat_replay crossPlatformContract modelEvidence originalModel ->
    checkerAccepted ->
    ay_vcpe_ported_validation crossPlatformContract checkerAccepted
      originalModel :=
  fun replay checkerProof =>
    ay_vcpe_ported_validation_intro crossPlatformContract checkerAccepted
      originalModel
      (ay_vcpe_sat_replay_contract crossPlatformContract modelEvidence
        originalModel replay)
      checkerProof
      (ay_vcpe_sat_replay_original_model crossPlatformContract modelEvidence
        originalModel replay)

theorem ay_vcpe_unsat_replay_supports_ported_validation
    (crossPlatformContract proofEvidence originalEmptyClause checkerAccepted :
      Prop) :
    ay_vcpe_unsat_replay crossPlatformContract proofEvidence
      originalEmptyClause ->
    checkerAccepted ->
    ay_vcpe_ported_validation crossPlatformContract checkerAccepted
      originalEmptyClause :=
  fun replay checkerProof =>
    ay_vcpe_ported_validation_intro crossPlatformContract checkerAccepted
      originalEmptyClause
      (ay_vcpe_unsat_replay_contract crossPlatformContract proofEvidence
        originalEmptyClause replay)
      checkerProof
      (ay_vcpe_unsat_replay_original_empty_clause crossPlatformContract
        proofEvidence originalEmptyClause replay)

theorem ay_vcpe_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vcpe_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vcpe_conj_intro reason
      (ay_vcpe_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vcpe_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vcpe_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vcpe_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vcpe_conj_right reason
      (ay_vcpe_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vcpe_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vcpe_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vcpe_conj_right reason
      (ay_vcpe_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vcpe_recompute_intro
    (reason auditRecord fallbackPath : Prop) :
    reason -> auditRecord -> fallbackPath ->
    ay_vcpe_recompute reason auditRecord fallbackPath :=
  fun reasonProof auditProof fallbackProof =>
    ay_vcpe_conj_intro reason
      (ay_vcpe_conj auditRecord fallbackPath)
      reasonProof
      (ay_vcpe_conj_intro auditRecord fallbackPath auditProof fallbackProof)

theorem ay_vcpe_cross_platform_failure_intro
    (satFact unsatFact reason auditRecord fallbackPath : Prop) :
    ay_vcpe_blocked_publication satFact unsatFact reason ->
    ay_vcpe_recompute reason auditRecord fallbackPath ->
    ay_vcpe_cross_platform_failure satFact unsatFact reason auditRecord
      fallbackPath :=
  fun blocked recompute =>
    ay_vcpe_conj_intro
      (ay_vcpe_blocked_publication satFact unsatFact reason)
      (ay_vcpe_recompute reason auditRecord fallbackPath)
      blocked recompute

theorem ay_vcpe_cross_platform_failure_blocks_sat
    (satFact unsatFact reason auditRecord fallbackPath : Prop) :
    ay_vcpe_cross_platform_failure satFact unsatFact reason auditRecord
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vcpe_blocked_publication_no_sat satFact unsatFact reason
      (ay_vcpe_conj_left
        (ay_vcpe_blocked_publication satFact unsatFact reason)
        (ay_vcpe_recompute reason auditRecord fallbackPath)
        failure)

theorem ay_vcpe_cross_platform_failure_blocks_unsat
    (satFact unsatFact reason auditRecord fallbackPath : Prop) :
    ay_vcpe_cross_platform_failure satFact unsatFact reason auditRecord
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vcpe_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vcpe_conj_left
        (ay_vcpe_blocked_publication satFact unsatFact reason)
        (ay_vcpe_recompute reason auditRecord fallbackPath)
        failure)

theorem ay_vcpe_cross_platform_failure_recompute
    (satFact unsatFact reason auditRecord fallbackPath : Prop) :
    ay_vcpe_cross_platform_failure satFact unsatFact reason auditRecord
      fallbackPath ->
    ay_vcpe_recompute reason auditRecord fallbackPath :=
  fun failure =>
    ay_vcpe_conj_right
      (ay_vcpe_blocked_publication satFact unsatFact reason)
      (ay_vcpe_recompute reason auditRecord fallbackPath)
      failure

theorem ay_vcpe_platform_drift_forces_no_claim
    (satFact unsatFact platformDrift auditRecord fallbackPath : Prop) :
    platformDrift -> (satFact -> False) -> (unsatFact -> False) ->
    auditRecord -> fallbackPath ->
    ay_vcpe_cross_platform_failure satFact unsatFact platformDrift
      auditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vcpe_cross_platform_failure_intro satFact unsatFact platformDrift
      auditRecord fallbackPath
      (ay_vcpe_blocked_publication_intro satFact unsatFact platformDrift
        reasonProof blockSat blockUnsat)
      (ay_vcpe_recompute_intro platformDrift auditRecord fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vcpe_missing_mapping_forces_no_claim
    (satFact unsatFact missingMapping auditRecord fallbackPath : Prop) :
    missingMapping -> (satFact -> False) -> (unsatFact -> False) ->
    auditRecord -> fallbackPath ->
    ay_vcpe_cross_platform_failure satFact unsatFact missingMapping
      auditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vcpe_cross_platform_failure_intro satFact unsatFact missingMapping
      auditRecord fallbackPath
      (ay_vcpe_blocked_publication_intro satFact unsatFact missingMapping
        reasonProof blockSat blockUnsat)
      (ay_vcpe_recompute_intro missingMapping auditRecord fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vcpe_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch auditRecord fallbackPath : Prop) :
    digestMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    auditRecord -> fallbackPath ->
    ay_vcpe_cross_platform_failure satFact unsatFact digestMismatch
      auditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vcpe_cross_platform_failure_intro satFact unsatFact digestMismatch
      auditRecord fallbackPath
      (ay_vcpe_blocked_publication_intro satFact unsatFact digestMismatch
        reasonProof blockSat blockUnsat)
      (ay_vcpe_recompute_intro digestMismatch auditRecord fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vcpe_checker_rejection_forces_no_claim
    (satFact unsatFact checkerRejection auditRecord fallbackPath : Prop) :
    checkerRejection -> (satFact -> False) -> (unsatFact -> False) ->
    auditRecord -> fallbackPath ->
    ay_vcpe_cross_platform_failure satFact unsatFact checkerRejection
      auditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vcpe_cross_platform_failure_intro satFact unsatFact checkerRejection
      auditRecord fallbackPath
      (ay_vcpe_blocked_publication_intro satFact unsatFact checkerRejection
        reasonProof blockSat blockUnsat)
      (ay_vcpe_recompute_intro checkerRejection auditRecord fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vcpe_stale_build_evidence_forces_no_claim
    (satFact unsatFact staleBuildEvidence auditRecord fallbackPath : Prop) :
    staleBuildEvidence -> (satFact -> False) -> (unsatFact -> False) ->
    auditRecord -> fallbackPath ->
    ay_vcpe_cross_platform_failure satFact unsatFact staleBuildEvidence
      auditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vcpe_cross_platform_failure_intro satFact unsatFact staleBuildEvidence
      auditRecord fallbackPath
      (ay_vcpe_blocked_publication_intro satFact unsatFact
        staleBuildEvidence reasonProof blockSat blockUnsat)
      (ay_vcpe_recompute_intro staleBuildEvidence auditRecord fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vcpe_audit_contradiction_forces_no_claim
    (satFact unsatFact auditContradiction auditRecord fallbackPath : Prop) :
    auditContradiction -> (satFact -> False) -> (unsatFact -> False) ->
    auditRecord -> fallbackPath ->
    ay_vcpe_cross_platform_failure satFact unsatFact auditContradiction
      auditRecord fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vcpe_cross_platform_failure_intro satFact unsatFact auditContradiction
      auditRecord fallbackPath
      (ay_vcpe_blocked_publication_intro satFact unsatFact
        auditContradiction reasonProof blockSat blockUnsat)
      (ay_vcpe_recompute_intro auditContradiction auditRecord fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vcpe_failure_cannot_publish_sat
    (satFact unsatFact reason auditRecord fallbackPath : Prop) :
    ay_vcpe_cross_platform_failure satFact unsatFact reason auditRecord
      fallbackPath ->
    satFact -> False :=
  ay_vcpe_cross_platform_failure_blocks_sat satFact unsatFact reason
    auditRecord fallbackPath

theorem ay_vcpe_failure_cannot_publish_unsat
    (satFact unsatFact reason auditRecord fallbackPath : Prop) :
    ay_vcpe_cross_platform_failure satFact unsatFact reason auditRecord
      fallbackPath ->
    unsatFact -> False :=
  ay_vcpe_cross_platform_failure_blocks_unsat satFact unsatFact reason
    auditRecord fallbackPath
