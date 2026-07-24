-- SAT-COMP validator result-schema migration core.
--
-- Older result bundles/manifests can be migrated to a new schema only when
-- schema mapping, original input fingerprint, solver build identity, artifact
-- digest, replay transcript, exit-code mapping, reconstruction handle, and
-- fallback audit evidence agree.

def ay_vrsm_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrsm_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vrsm_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vrsm_disj satFact (ay_vrsm_disj unsatFact noClaimFact)

def ay_vrsm_migration_contract
    (schemaMapping originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript exitCodeMapping reconstructionHandle
      fallbackAudit : Prop) : Prop :=
  ay_vrsm_conj schemaMapping
    (ay_vrsm_conj originalFingerprint
      (ay_vrsm_conj solverBuildIdentity
        (ay_vrsm_conj artifactDigest
          (ay_vrsm_conj checkerReplayTranscript
            (ay_vrsm_conj exitCodeMapping
              (ay_vrsm_conj reconstructionHandle fallbackAudit))))))

def ay_vrsm_sat_migration
    (migrationContract modelEvidence originalModel : Prop) : Prop :=
  ay_vrsm_conj migrationContract
    (ay_vrsm_conj modelEvidence originalModel)

def ay_vrsm_unsat_migration
    (migrationContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vrsm_conj migrationContract
    (ay_vrsm_conj proofEvidence originalEmptyClause)

def ay_vrsm_no_claim_migration
    (migrationContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vrsm_conj migrationContract
    (ay_vrsm_conj diagnostic noSemanticClaim)

def ay_vrsm_migrated_validation
    (migrationContract checkerAccepted publicEvidence : Prop) : Prop :=
  ay_vrsm_conj migrationContract
    (ay_vrsm_conj checkerAccepted publicEvidence)

def ay_vrsm_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vrsm_conj reason
    (ay_vrsm_conj (satFact -> False) (unsatFact -> False))

def ay_vrsm_recompute
    (reason fallbackAudit fallbackPath : Prop) : Prop :=
  ay_vrsm_conj reason (ay_vrsm_conj fallbackAudit fallbackPath)

def ay_vrsm_migration_failure
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) : Prop :=
  ay_vrsm_conj
    (ay_vrsm_blocked_publication satFact unsatFact reason)
    (ay_vrsm_recompute reason fallbackAudit fallbackPath)

theorem ay_vrsm_conj_intro (left right : Prop) :
    left -> right -> ay_vrsm_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrsm_conj_left (left right : Prop) :
    ay_vrsm_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrsm_conj_right (left right : Prop) :
    ay_vrsm_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrsm_disj_left (left right : Prop) :
    left -> ay_vrsm_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vrsm_disj_right (left right : Prop) :
    right -> ay_vrsm_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrsm_migration_contract_intro
    (schemaMapping originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript exitCodeMapping reconstructionHandle
      fallbackAudit : Prop) :
    schemaMapping -> originalFingerprint -> solverBuildIdentity ->
    artifactDigest -> checkerReplayTranscript -> exitCodeMapping ->
    reconstructionHandle -> fallbackAudit ->
    ay_vrsm_migration_contract schemaMapping originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      exitCodeMapping reconstructionHandle fallbackAudit :=
  fun schemaProof fingerprintProof buildProof digestProof replayProof
      mappingProof reconstructionProof fallbackProof =>
    ay_vrsm_conj_intro schemaMapping
      (ay_vrsm_conj originalFingerprint
        (ay_vrsm_conj solverBuildIdentity
          (ay_vrsm_conj artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit))))))
      schemaProof
      (ay_vrsm_conj_intro originalFingerprint
        (ay_vrsm_conj solverBuildIdentity
          (ay_vrsm_conj artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit)))))
        fingerprintProof
        (ay_vrsm_conj_intro solverBuildIdentity
          (ay_vrsm_conj artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit))))
          buildProof
          (ay_vrsm_conj_intro artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit)))
            digestProof
            (ay_vrsm_conj_intro checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit))
              replayProof
              (ay_vrsm_conj_intro exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit)
                mappingProof
                (ay_vrsm_conj_intro reconstructionHandle fallbackAudit
                  reconstructionProof fallbackProof))))))

theorem ay_vrsm_migration_contract_schema
    (schemaMapping originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript exitCodeMapping reconstructionHandle
      fallbackAudit : Prop) :
    ay_vrsm_migration_contract schemaMapping originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      exitCodeMapping reconstructionHandle fallbackAudit ->
    schemaMapping :=
  fun contract =>
    ay_vrsm_conj_left schemaMapping
      (ay_vrsm_conj originalFingerprint
        (ay_vrsm_conj solverBuildIdentity
          (ay_vrsm_conj artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit))))))
      contract

theorem ay_vrsm_migration_contract_fingerprint
    (schemaMapping originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript exitCodeMapping reconstructionHandle
      fallbackAudit : Prop) :
    ay_vrsm_migration_contract schemaMapping originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      exitCodeMapping reconstructionHandle fallbackAudit ->
    originalFingerprint :=
  fun contract =>
    ay_vrsm_conj_right schemaMapping
      (ay_vrsm_conj originalFingerprint
        (ay_vrsm_conj solverBuildIdentity
          (ay_vrsm_conj artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit))))))
      contract originalFingerprint
      (fun fingerprintProof _tail => fingerprintProof)

theorem ay_vrsm_migration_contract_build
    (schemaMapping originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript exitCodeMapping reconstructionHandle
      fallbackAudit : Prop) :
    ay_vrsm_migration_contract schemaMapping originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      exitCodeMapping reconstructionHandle fallbackAudit ->
    solverBuildIdentity :=
  fun contract =>
    ay_vrsm_conj_right schemaMapping
      (ay_vrsm_conj originalFingerprint
        (ay_vrsm_conj solverBuildIdentity
          (ay_vrsm_conj artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit))))))
      contract solverBuildIdentity
      (fun _fingerprintProof tail =>
        tail solverBuildIdentity (fun buildProof _tail2 => buildProof))

theorem ay_vrsm_migration_contract_digest
    (schemaMapping originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript exitCodeMapping reconstructionHandle
      fallbackAudit : Prop) :
    ay_vrsm_migration_contract schemaMapping originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      exitCodeMapping reconstructionHandle fallbackAudit ->
    artifactDigest :=
  fun contract =>
    ay_vrsm_conj_right schemaMapping
      (ay_vrsm_conj originalFingerprint
        (ay_vrsm_conj solverBuildIdentity
          (ay_vrsm_conj artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit))))))
      contract artifactDigest
      (fun _fingerprintProof tail =>
        tail artifactDigest
          (fun _buildProof tail2 =>
            tail2 artifactDigest (fun digestProof _tail3 => digestProof)))

theorem ay_vrsm_migration_contract_replay
    (schemaMapping originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript exitCodeMapping reconstructionHandle
      fallbackAudit : Prop) :
    ay_vrsm_migration_contract schemaMapping originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      exitCodeMapping reconstructionHandle fallbackAudit ->
    checkerReplayTranscript :=
  fun contract =>
    ay_vrsm_conj_right schemaMapping
      (ay_vrsm_conj originalFingerprint
        (ay_vrsm_conj solverBuildIdentity
          (ay_vrsm_conj artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit))))))
      contract checkerReplayTranscript
      (fun _fingerprintProof tail =>
        tail checkerReplayTranscript
          (fun _buildProof tail2 =>
            tail2 checkerReplayTranscript
              (fun _digestProof tail3 =>
                tail3 checkerReplayTranscript
                  (fun replayProof _tail4 => replayProof))))

theorem ay_vrsm_migration_contract_mapping
    (schemaMapping originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript exitCodeMapping reconstructionHandle
      fallbackAudit : Prop) :
    ay_vrsm_migration_contract schemaMapping originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      exitCodeMapping reconstructionHandle fallbackAudit ->
    exitCodeMapping :=
  fun contract =>
    ay_vrsm_conj_right schemaMapping
      (ay_vrsm_conj originalFingerprint
        (ay_vrsm_conj solverBuildIdentity
          (ay_vrsm_conj artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit))))))
      contract exitCodeMapping
      (fun _fingerprintProof tail =>
        tail exitCodeMapping
          (fun _buildProof tail2 =>
            tail2 exitCodeMapping
              (fun _digestProof tail3 =>
                tail3 exitCodeMapping
                  (fun _replayProof tail4 =>
                    tail4 exitCodeMapping
                      (fun mappingProof _tail5 => mappingProof)))))

theorem ay_vrsm_migration_contract_reconstruction
    (schemaMapping originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript exitCodeMapping reconstructionHandle
      fallbackAudit : Prop) :
    ay_vrsm_migration_contract schemaMapping originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      exitCodeMapping reconstructionHandle fallbackAudit ->
    reconstructionHandle :=
  fun contract =>
    ay_vrsm_conj_right schemaMapping
      (ay_vrsm_conj originalFingerprint
        (ay_vrsm_conj solverBuildIdentity
          (ay_vrsm_conj artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit))))))
      contract reconstructionHandle
      (fun _fingerprintProof tail =>
        tail reconstructionHandle
          (fun _buildProof tail2 =>
            tail2 reconstructionHandle
              (fun _digestProof tail3 =>
                tail3 reconstructionHandle
                  (fun _replayProof tail4 =>
                    tail4 reconstructionHandle
                      (fun _mappingProof tail5 =>
                        tail5 reconstructionHandle
                          (fun reconstructionProof _fallbackProof =>
                            reconstructionProof))))))

theorem ay_vrsm_migration_contract_fallback
    (schemaMapping originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript exitCodeMapping reconstructionHandle
      fallbackAudit : Prop) :
    ay_vrsm_migration_contract schemaMapping originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      exitCodeMapping reconstructionHandle fallbackAudit ->
    fallbackAudit :=
  fun contract =>
    ay_vrsm_conj_right schemaMapping
      (ay_vrsm_conj originalFingerprint
        (ay_vrsm_conj solverBuildIdentity
          (ay_vrsm_conj artifactDigest
            (ay_vrsm_conj checkerReplayTranscript
              (ay_vrsm_conj exitCodeMapping
                (ay_vrsm_conj reconstructionHandle fallbackAudit))))))
      contract fallbackAudit
      (fun _fingerprintProof tail =>
        tail fallbackAudit
          (fun _buildProof tail2 =>
            tail2 fallbackAudit
              (fun _digestProof tail3 =>
                tail3 fallbackAudit
                  (fun _replayProof tail4 =>
                    tail4 fallbackAudit
                      (fun _mappingProof tail5 =>
                        tail5 fallbackAudit
                          (fun _reconstructionProof fallbackProof =>
                            fallbackProof))))))

theorem ay_vrsm_sat_migration_intro
    (migrationContract modelEvidence originalModel : Prop) :
    migrationContract -> modelEvidence -> originalModel ->
    ay_vrsm_sat_migration migrationContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vrsm_conj_intro migrationContract
      (ay_vrsm_conj modelEvidence originalModel)
      contractProof
      (ay_vrsm_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vrsm_sat_migration_contract
    (migrationContract modelEvidence originalModel : Prop) :
    ay_vrsm_sat_migration migrationContract modelEvidence originalModel ->
    migrationContract :=
  fun migration =>
    ay_vrsm_conj_left migrationContract
      (ay_vrsm_conj modelEvidence originalModel) migration

theorem ay_vrsm_sat_migration_original_model
    (migrationContract modelEvidence originalModel : Prop) :
    ay_vrsm_sat_migration migrationContract modelEvidence originalModel ->
    originalModel :=
  fun migration =>
    ay_vrsm_conj_right migrationContract
      (ay_vrsm_conj modelEvidence originalModel)
      migration originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vrsm_unsat_migration_intro
    (migrationContract proofEvidence originalEmptyClause : Prop) :
    migrationContract -> proofEvidence -> originalEmptyClause ->
    ay_vrsm_unsat_migration migrationContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vrsm_conj_intro migrationContract
      (ay_vrsm_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vrsm_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vrsm_unsat_migration_contract
    (migrationContract proofEvidence originalEmptyClause : Prop) :
    ay_vrsm_unsat_migration migrationContract proofEvidence
      originalEmptyClause ->
    migrationContract :=
  fun migration =>
    ay_vrsm_conj_left migrationContract
      (ay_vrsm_conj proofEvidence originalEmptyClause) migration

theorem ay_vrsm_unsat_migration_original_empty_clause
    (migrationContract proofEvidence originalEmptyClause : Prop) :
    ay_vrsm_unsat_migration migrationContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun migration =>
    ay_vrsm_conj_right migrationContract
      (ay_vrsm_conj proofEvidence originalEmptyClause)
      migration originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vrsm_no_claim_migration_intro
    (migrationContract diagnostic noSemanticClaim : Prop) :
    migrationContract -> diagnostic -> noSemanticClaim ->
    ay_vrsm_no_claim_migration migrationContract diagnostic
      noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_vrsm_conj_intro migrationContract
      (ay_vrsm_conj diagnostic noSemanticClaim)
      contractProof
      (ay_vrsm_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vrsm_no_claim_migration_no_semantic_claim
    (migrationContract diagnostic noSemanticClaim : Prop) :
    ay_vrsm_no_claim_migration migrationContract diagnostic
      noSemanticClaim ->
    noSemanticClaim :=
  fun migration =>
    ay_vrsm_conj_right migrationContract
      (ay_vrsm_conj diagnostic noSemanticClaim)
      migration noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vrsm_migrated_validation_intro
    (migrationContract checkerAccepted publicEvidence : Prop) :
    migrationContract -> checkerAccepted -> publicEvidence ->
    ay_vrsm_migrated_validation migrationContract checkerAccepted
      publicEvidence :=
  fun contractProof checkerProof publicProof =>
    ay_vrsm_conj_intro migrationContract
      (ay_vrsm_conj checkerAccepted publicEvidence)
      contractProof
      (ay_vrsm_conj_intro checkerAccepted publicEvidence checkerProof
        publicProof)

theorem ay_vrsm_migrated_validation_public_evidence
    (migrationContract checkerAccepted publicEvidence : Prop) :
    ay_vrsm_migrated_validation migrationContract checkerAccepted
      publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vrsm_conj_right migrationContract
      (ay_vrsm_conj checkerAccepted publicEvidence)
      validation publicEvidence
      (fun _checkerProof publicProof => publicProof)

theorem ay_vrsm_accepted_sat_migration_preserves_result
    (migrationContract modelEvidence originalModel unsatFact noClaimFact :
      Prop) :
    ay_vrsm_sat_migration migrationContract modelEvidence originalModel ->
    ay_vrsm_public_result originalModel unsatFact noClaimFact :=
  fun migration =>
    ay_vrsm_disj_left originalModel
      (ay_vrsm_disj unsatFact noClaimFact)
      (ay_vrsm_sat_migration_original_model migrationContract modelEvidence
        originalModel migration)

theorem ay_vrsm_accepted_unsat_migration_preserves_result
    (satFact migrationContract proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_vrsm_unsat_migration migrationContract proofEvidence
      originalEmptyClause ->
    ay_vrsm_public_result satFact originalEmptyClause noClaimFact :=
  fun migration =>
    ay_vrsm_disj_right satFact
      (ay_vrsm_disj originalEmptyClause noClaimFact)
      (ay_vrsm_disj_left originalEmptyClause noClaimFact
        (ay_vrsm_unsat_migration_original_empty_clause migrationContract
          proofEvidence originalEmptyClause migration))

theorem ay_vrsm_accepted_no_claim_migration_preserves_result
    (satFact unsatFact migrationContract diagnostic noSemanticClaim : Prop) :
    ay_vrsm_no_claim_migration migrationContract diagnostic noSemanticClaim ->
    ay_vrsm_public_result satFact unsatFact noSemanticClaim :=
  fun migration =>
    ay_vrsm_disj_right satFact
      (ay_vrsm_disj unsatFact noSemanticClaim)
      (ay_vrsm_disj_right unsatFact noSemanticClaim
        (ay_vrsm_no_claim_migration_no_semantic_claim migrationContract
          diagnostic noSemanticClaim migration))

theorem ay_vrsm_sat_migration_supports_validation
    (migrationContract modelEvidence originalModel checkerAccepted : Prop) :
    ay_vrsm_sat_migration migrationContract modelEvidence originalModel ->
    checkerAccepted ->
    ay_vrsm_migrated_validation migrationContract checkerAccepted
      originalModel :=
  fun migration checkerProof =>
    ay_vrsm_migrated_validation_intro migrationContract checkerAccepted
      originalModel
      (ay_vrsm_sat_migration_contract migrationContract modelEvidence
        originalModel migration)
      checkerProof
      (ay_vrsm_sat_migration_original_model migrationContract modelEvidence
        originalModel migration)

theorem ay_vrsm_unsat_migration_supports_validation
    (migrationContract proofEvidence originalEmptyClause checkerAccepted :
      Prop) :
    ay_vrsm_unsat_migration migrationContract proofEvidence
      originalEmptyClause ->
    checkerAccepted ->
    ay_vrsm_migrated_validation migrationContract checkerAccepted
      originalEmptyClause :=
  fun migration checkerProof =>
    ay_vrsm_migrated_validation_intro migrationContract checkerAccepted
      originalEmptyClause
      (ay_vrsm_unsat_migration_contract migrationContract proofEvidence
        originalEmptyClause migration)
      checkerProof
      (ay_vrsm_unsat_migration_original_empty_clause migrationContract
        proofEvidence originalEmptyClause migration)

theorem ay_vrsm_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vrsm_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vrsm_conj_intro reason
      (ay_vrsm_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vrsm_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vrsm_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vrsm_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vrsm_conj_right reason
      (ay_vrsm_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vrsm_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vrsm_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vrsm_conj_right reason
      (ay_vrsm_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vrsm_recompute_intro
    (reason fallbackAudit fallbackPath : Prop) :
    reason -> fallbackAudit -> fallbackPath ->
    ay_vrsm_recompute reason fallbackAudit fallbackPath :=
  fun reasonProof auditProof pathProof =>
    ay_vrsm_conj_intro reason
      (ay_vrsm_conj fallbackAudit fallbackPath)
      reasonProof
      (ay_vrsm_conj_intro fallbackAudit fallbackPath auditProof pathProof)

theorem ay_vrsm_migration_failure_intro
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrsm_blocked_publication satFact unsatFact reason ->
    ay_vrsm_recompute reason fallbackAudit fallbackPath ->
    ay_vrsm_migration_failure satFact unsatFact reason fallbackAudit
      fallbackPath :=
  fun blocked recompute =>
    ay_vrsm_conj_intro
      (ay_vrsm_blocked_publication satFact unsatFact reason)
      (ay_vrsm_recompute reason fallbackAudit fallbackPath)
      blocked recompute

theorem ay_vrsm_migration_failure_blocks_sat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrsm_migration_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vrsm_blocked_publication_no_sat satFact unsatFact reason
      (ay_vrsm_conj_left
        (ay_vrsm_blocked_publication satFact unsatFact reason)
        (ay_vrsm_recompute reason fallbackAudit fallbackPath)
        failure)

theorem ay_vrsm_migration_failure_blocks_unsat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrsm_migration_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vrsm_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vrsm_conj_left
        (ay_vrsm_blocked_publication satFact unsatFact reason)
        (ay_vrsm_recompute reason fallbackAudit fallbackPath)
        failure)

theorem ay_vrsm_migration_failure_recompute
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrsm_migration_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    ay_vrsm_recompute reason fallbackAudit fallbackPath :=
  fun failure =>
    ay_vrsm_conj_right
      (ay_vrsm_blocked_publication satFact unsatFact reason)
      (ay_vrsm_recompute reason fallbackAudit fallbackPath)
      failure

theorem ay_vrsm_missing_schema_mapping_forces_no_claim
    (satFact unsatFact missingSchema fallbackAudit fallbackPath : Prop) :
    missingSchema -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vrsm_migration_failure satFact unsatFact missingSchema fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vrsm_migration_failure_intro satFact unsatFact missingSchema
      fallbackAudit fallbackPath
      (ay_vrsm_blocked_publication_intro satFact unsatFact missingSchema
        reasonProof blockSat blockUnsat)
      (ay_vrsm_recompute_intro missingSchema fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vrsm_field_loss_forces_no_claim
    (satFact unsatFact fieldLoss fallbackAudit fallbackPath : Prop) :
    fieldLoss -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vrsm_migration_failure satFact unsatFact fieldLoss fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vrsm_migration_failure_intro satFact unsatFact fieldLoss
      fallbackAudit fallbackPath
      (ay_vrsm_blocked_publication_intro satFact unsatFact fieldLoss
        reasonProof blockSat blockUnsat)
      (ay_vrsm_recompute_intro fieldLoss fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vrsm_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch fallbackAudit fallbackPath : Prop) :
    digestMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vrsm_migration_failure satFact unsatFact digestMismatch
      fallbackAudit fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vrsm_migration_failure_intro satFact unsatFact digestMismatch
      fallbackAudit fallbackPath
      (ay_vrsm_blocked_publication_intro satFact unsatFact digestMismatch
        reasonProof blockSat blockUnsat)
      (ay_vrsm_recompute_intro digestMismatch fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vrsm_replay_gap_forces_no_claim
    (satFact unsatFact replayGap fallbackAudit fallbackPath : Prop) :
    replayGap -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vrsm_migration_failure satFact unsatFact replayGap fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vrsm_migration_failure_intro satFact unsatFact replayGap
      fallbackAudit fallbackPath
      (ay_vrsm_blocked_publication_intro satFact unsatFact replayGap
        reasonProof blockSat blockUnsat)
      (ay_vrsm_recompute_intro replayGap fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vrsm_exit_code_mismatch_forces_no_claim
    (satFact unsatFact exitMismatch fallbackAudit fallbackPath : Prop) :
    exitMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vrsm_migration_failure satFact unsatFact exitMismatch fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vrsm_migration_failure_intro satFact unsatFact exitMismatch
      fallbackAudit fallbackPath
      (ay_vrsm_blocked_publication_intro satFact unsatFact exitMismatch
        reasonProof blockSat blockUnsat)
      (ay_vrsm_recompute_intro exitMismatch fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vrsm_stale_build_forces_no_claim
    (satFact unsatFact staleBuild fallbackAudit fallbackPath : Prop) :
    staleBuild -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vrsm_migration_failure satFact unsatFact staleBuild fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vrsm_migration_failure_intro satFact unsatFact staleBuild
      fallbackAudit fallbackPath
      (ay_vrsm_blocked_publication_intro satFact unsatFact staleBuild
        reasonProof blockSat blockUnsat)
      (ay_vrsm_recompute_intro staleBuild fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vrsm_missing_reconstruction_forces_no_claim
    (satFact unsatFact missingReconstruction fallbackAudit fallbackPath :
      Prop) :
    missingReconstruction -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vrsm_migration_failure satFact unsatFact missingReconstruction
      fallbackAudit fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vrsm_migration_failure_intro satFact unsatFact missingReconstruction
      fallbackAudit fallbackPath
      (ay_vrsm_blocked_publication_intro satFact unsatFact
        missingReconstruction reasonProof blockSat blockUnsat)
      (ay_vrsm_recompute_intro missingReconstruction fallbackAudit
        fallbackPath reasonProof auditProof pathProof)

theorem ay_vrsm_audit_contradiction_forces_no_claim
    (satFact unsatFact auditContradiction fallbackAudit fallbackPath :
      Prop) :
    auditContradiction -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vrsm_migration_failure satFact unsatFact auditContradiction
      fallbackAudit fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vrsm_migration_failure_intro satFact unsatFact auditContradiction
      fallbackAudit fallbackPath
      (ay_vrsm_blocked_publication_intro satFact unsatFact
        auditContradiction reasonProof blockSat blockUnsat)
      (ay_vrsm_recompute_intro auditContradiction fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vrsm_failure_cannot_publish_sat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrsm_migration_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    satFact -> False :=
  ay_vrsm_migration_failure_blocks_sat satFact unsatFact reason fallbackAudit
    fallbackPath

theorem ay_vrsm_failure_cannot_publish_unsat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrsm_migration_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    unsatFact -> False :=
  ay_vrsm_migration_failure_blocks_unsat satFact unsatFact reason
    fallbackAudit fallbackPath
