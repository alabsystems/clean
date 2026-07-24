-- SAT-COMP validator artifact digest rotation core.
--
-- Rotating public artifact digest roots is sound only when old-root
-- membership, new-root membership, migration audit, retained replay and
-- reconstruction evidence, exit-code contract, and no-claim fallback agree.
-- Broken rotation evidence downgrades to no-claim/recompute.

def ay_vadr_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vadr_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vadr_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vadr_disj satFact (ay_vadr_disj unsatFact noClaimFact)

def ay_vadr_retained_evidence
    (replayTranscript reconstructionEvidence exitCodeContract auditTrail :
      Prop) : Prop :=
  ay_vadr_conj replayTranscript
    (ay_vadr_conj reconstructionEvidence
      (ay_vadr_conj exitCodeContract auditTrail))

def ay_vadr_rotation_contract
    (oldRootMembership newRootMembership migrationAudit retainedEvidence
      noClaimFallback : Prop) : Prop :=
  ay_vadr_conj oldRootMembership
    (ay_vadr_conj newRootMembership
      (ay_vadr_conj migrationAudit
        (ay_vadr_conj retainedEvidence noClaimFallback)))

def ay_vadr_sat_artifact
    (rotationContract modelEvidence originalModel : Prop) : Prop :=
  ay_vadr_conj rotationContract
    (ay_vadr_conj modelEvidence originalModel)

def ay_vadr_unsat_artifact
    (rotationContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vadr_conj rotationContract
    (ay_vadr_conj proofEvidence originalEmptyClause)

def ay_vadr_no_claim_artifact
    (rotationContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vadr_conj rotationContract
    (ay_vadr_conj diagnostic noSemanticClaim)

def ay_vadr_later_validation
    (rotationContract checkerReplay publicEvidence : Prop) : Prop :=
  ay_vadr_conj rotationContract
    (ay_vadr_conj checkerReplay publicEvidence)

def ay_vadr_blocked_validation
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vadr_conj reason
    (ay_vadr_conj (satFact -> False) (unsatFact -> False))

def ay_vadr_recompute
    (reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vadr_conj reason (ay_vadr_conj auditTrail fallbackPath)

def ay_vadr_rotation_failure
    (satFact unsatFact reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vadr_conj
    (ay_vadr_blocked_validation satFact unsatFact reason)
    (ay_vadr_recompute reason auditTrail fallbackPath)

theorem ay_vadr_conj_intro (left right : Prop) :
    left -> right -> ay_vadr_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vadr_conj_left (left right : Prop) :
    ay_vadr_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vadr_conj_right (left right : Prop) :
    ay_vadr_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vadr_disj_left (left right : Prop) :
    left -> ay_vadr_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vadr_disj_right (left right : Prop) :
    right -> ay_vadr_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vadr_retained_evidence_intro
    (replayTranscript reconstructionEvidence exitCodeContract auditTrail :
      Prop) :
    replayTranscript -> reconstructionEvidence -> exitCodeContract ->
    auditTrail ->
    ay_vadr_retained_evidence replayTranscript reconstructionEvidence
      exitCodeContract auditTrail :=
  fun replayProof reconstructionProof exitProof auditProof =>
    ay_vadr_conj_intro replayTranscript
      (ay_vadr_conj reconstructionEvidence
        (ay_vadr_conj exitCodeContract auditTrail))
      replayProof
      (ay_vadr_conj_intro reconstructionEvidence
        (ay_vadr_conj exitCodeContract auditTrail)
        reconstructionProof
        (ay_vadr_conj_intro exitCodeContract auditTrail exitProof
          auditProof))

theorem ay_vadr_retained_evidence_replay
    (replayTranscript reconstructionEvidence exitCodeContract auditTrail :
      Prop) :
    ay_vadr_retained_evidence replayTranscript reconstructionEvidence
      exitCodeContract auditTrail ->
    replayTranscript :=
  fun retained =>
    ay_vadr_conj_left replayTranscript
      (ay_vadr_conj reconstructionEvidence
        (ay_vadr_conj exitCodeContract auditTrail))
      retained

theorem ay_vadr_retained_evidence_reconstruction
    (replayTranscript reconstructionEvidence exitCodeContract auditTrail :
      Prop) :
    ay_vadr_retained_evidence replayTranscript reconstructionEvidence
      exitCodeContract auditTrail ->
    reconstructionEvidence :=
  fun retained =>
    ay_vadr_conj_right replayTranscript
      (ay_vadr_conj reconstructionEvidence
        (ay_vadr_conj exitCodeContract auditTrail))
      retained reconstructionEvidence
      (fun reconstructionProof _tail => reconstructionProof)

theorem ay_vadr_retained_evidence_exit
    (replayTranscript reconstructionEvidence exitCodeContract auditTrail :
      Prop) :
    ay_vadr_retained_evidence replayTranscript reconstructionEvidence
      exitCodeContract auditTrail ->
    exitCodeContract :=
  fun retained =>
    ay_vadr_conj_right replayTranscript
      (ay_vadr_conj reconstructionEvidence
        (ay_vadr_conj exitCodeContract auditTrail))
      retained exitCodeContract
      (fun _reconstructionProof tail =>
        tail exitCodeContract (fun exitProof _auditProof => exitProof))

theorem ay_vadr_retained_evidence_audit
    (replayTranscript reconstructionEvidence exitCodeContract auditTrail :
      Prop) :
    ay_vadr_retained_evidence replayTranscript reconstructionEvidence
      exitCodeContract auditTrail ->
    auditTrail :=
  fun retained =>
    ay_vadr_conj_right replayTranscript
      (ay_vadr_conj reconstructionEvidence
        (ay_vadr_conj exitCodeContract auditTrail))
      retained auditTrail
      (fun _reconstructionProof tail =>
        tail auditTrail (fun _exitProof auditProof => auditProof))

theorem ay_vadr_rotation_contract_intro
    (oldRootMembership newRootMembership migrationAudit retainedEvidence
      noClaimFallback : Prop) :
    oldRootMembership -> newRootMembership -> migrationAudit ->
    retainedEvidence -> noClaimFallback ->
    ay_vadr_rotation_contract oldRootMembership newRootMembership
      migrationAudit retainedEvidence noClaimFallback :=
  fun oldProof newProof migrationProof retainedProof fallbackProof =>
    ay_vadr_conj_intro oldRootMembership
      (ay_vadr_conj newRootMembership
        (ay_vadr_conj migrationAudit
          (ay_vadr_conj retainedEvidence noClaimFallback)))
      oldProof
      (ay_vadr_conj_intro newRootMembership
        (ay_vadr_conj migrationAudit
          (ay_vadr_conj retainedEvidence noClaimFallback))
        newProof
        (ay_vadr_conj_intro migrationAudit
          (ay_vadr_conj retainedEvidence noClaimFallback)
          migrationProof
          (ay_vadr_conj_intro retainedEvidence noClaimFallback
            retainedProof fallbackProof)))

theorem ay_vadr_rotation_contract_old_root
    (oldRootMembership newRootMembership migrationAudit retainedEvidence
      noClaimFallback : Prop) :
    ay_vadr_rotation_contract oldRootMembership newRootMembership
      migrationAudit retainedEvidence noClaimFallback ->
    oldRootMembership :=
  fun contract =>
    ay_vadr_conj_left oldRootMembership
      (ay_vadr_conj newRootMembership
        (ay_vadr_conj migrationAudit
          (ay_vadr_conj retainedEvidence noClaimFallback)))
      contract

theorem ay_vadr_rotation_contract_new_root
    (oldRootMembership newRootMembership migrationAudit retainedEvidence
      noClaimFallback : Prop) :
    ay_vadr_rotation_contract oldRootMembership newRootMembership
      migrationAudit retainedEvidence noClaimFallback ->
    newRootMembership :=
  fun contract =>
    ay_vadr_conj_right oldRootMembership
      (ay_vadr_conj newRootMembership
        (ay_vadr_conj migrationAudit
          (ay_vadr_conj retainedEvidence noClaimFallback)))
      contract newRootMembership
      (fun newProof _tail => newProof)

theorem ay_vadr_rotation_contract_migration
    (oldRootMembership newRootMembership migrationAudit retainedEvidence
      noClaimFallback : Prop) :
    ay_vadr_rotation_contract oldRootMembership newRootMembership
      migrationAudit retainedEvidence noClaimFallback ->
    migrationAudit :=
  fun contract =>
    ay_vadr_conj_right oldRootMembership
      (ay_vadr_conj newRootMembership
        (ay_vadr_conj migrationAudit
          (ay_vadr_conj retainedEvidence noClaimFallback)))
      contract migrationAudit
      (fun _newProof tail =>
        tail migrationAudit (fun migrationProof _tail2 => migrationProof))

theorem ay_vadr_rotation_contract_retained
    (oldRootMembership newRootMembership migrationAudit retainedEvidence
      noClaimFallback : Prop) :
    ay_vadr_rotation_contract oldRootMembership newRootMembership
      migrationAudit retainedEvidence noClaimFallback ->
    retainedEvidence :=
  fun contract =>
    ay_vadr_conj_right oldRootMembership
      (ay_vadr_conj newRootMembership
        (ay_vadr_conj migrationAudit
          (ay_vadr_conj retainedEvidence noClaimFallback)))
      contract retainedEvidence
      (fun _newProof tail =>
        tail retainedEvidence
          (fun _migrationProof tail2 =>
            tail2 retainedEvidence
              (fun retainedProof _fallbackProof => retainedProof)))

theorem ay_vadr_rotation_contract_fallback
    (oldRootMembership newRootMembership migrationAudit retainedEvidence
      noClaimFallback : Prop) :
    ay_vadr_rotation_contract oldRootMembership newRootMembership
      migrationAudit retainedEvidence noClaimFallback ->
    noClaimFallback :=
  fun contract =>
    ay_vadr_conj_right oldRootMembership
      (ay_vadr_conj newRootMembership
        (ay_vadr_conj migrationAudit
          (ay_vadr_conj retainedEvidence noClaimFallback)))
      contract noClaimFallback
      (fun _newProof tail =>
        tail noClaimFallback
          (fun _migrationProof tail2 =>
            tail2 noClaimFallback
              (fun _retainedProof fallbackProof => fallbackProof)))

theorem ay_vadr_sat_artifact_intro
    (rotationContract modelEvidence originalModel : Prop) :
    rotationContract -> modelEvidence -> originalModel ->
    ay_vadr_sat_artifact rotationContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vadr_conj_intro rotationContract
      (ay_vadr_conj modelEvidence originalModel)
      contractProof
      (ay_vadr_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vadr_sat_artifact_contract
    (rotationContract modelEvidence originalModel : Prop) :
    ay_vadr_sat_artifact rotationContract modelEvidence originalModel ->
    rotationContract :=
  fun artifact =>
    ay_vadr_conj_left rotationContract
      (ay_vadr_conj modelEvidence originalModel) artifact

theorem ay_vadr_sat_artifact_original_model
    (rotationContract modelEvidence originalModel : Prop) :
    ay_vadr_sat_artifact rotationContract modelEvidence originalModel ->
    originalModel :=
  fun artifact =>
    ay_vadr_conj_right rotationContract
      (ay_vadr_conj modelEvidence originalModel)
      artifact originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vadr_unsat_artifact_intro
    (rotationContract proofEvidence originalEmptyClause : Prop) :
    rotationContract -> proofEvidence -> originalEmptyClause ->
    ay_vadr_unsat_artifact rotationContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vadr_conj_intro rotationContract
      (ay_vadr_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vadr_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vadr_unsat_artifact_contract
    (rotationContract proofEvidence originalEmptyClause : Prop) :
    ay_vadr_unsat_artifact rotationContract proofEvidence
      originalEmptyClause ->
    rotationContract :=
  fun artifact =>
    ay_vadr_conj_left rotationContract
      (ay_vadr_conj proofEvidence originalEmptyClause) artifact

theorem ay_vadr_unsat_artifact_original_empty_clause
    (rotationContract proofEvidence originalEmptyClause : Prop) :
    ay_vadr_unsat_artifact rotationContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun artifact =>
    ay_vadr_conj_right rotationContract
      (ay_vadr_conj proofEvidence originalEmptyClause)
      artifact originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vadr_no_claim_artifact_intro
    (rotationContract diagnostic noSemanticClaim : Prop) :
    rotationContract -> diagnostic -> noSemanticClaim ->
    ay_vadr_no_claim_artifact rotationContract diagnostic
      noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_vadr_conj_intro rotationContract
      (ay_vadr_conj diagnostic noSemanticClaim)
      contractProof
      (ay_vadr_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vadr_no_claim_artifact_no_semantic_claim
    (rotationContract diagnostic noSemanticClaim : Prop) :
    ay_vadr_no_claim_artifact rotationContract diagnostic
      noSemanticClaim ->
    noSemanticClaim :=
  fun artifact =>
    ay_vadr_conj_right rotationContract
      (ay_vadr_conj diagnostic noSemanticClaim)
      artifact noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vadr_later_validation_intro
    (rotationContract checkerReplay publicEvidence : Prop) :
    rotationContract -> checkerReplay -> publicEvidence ->
    ay_vadr_later_validation rotationContract checkerReplay
      publicEvidence :=
  fun contractProof replayProof publicProof =>
    ay_vadr_conj_intro rotationContract
      (ay_vadr_conj checkerReplay publicEvidence)
      contractProof
      (ay_vadr_conj_intro checkerReplay publicEvidence replayProof
        publicProof)

theorem ay_vadr_later_validation_public_evidence
    (rotationContract checkerReplay publicEvidence : Prop) :
    ay_vadr_later_validation rotationContract checkerReplay
      publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vadr_conj_right rotationContract
      (ay_vadr_conj checkerReplay publicEvidence)
      validation publicEvidence
      (fun _replayProof publicProof => publicProof)

theorem ay_vadr_sat_rotation_preserves_later_validation
    (rotationContract modelEvidence originalModel checkerReplay : Prop) :
    ay_vadr_sat_artifact rotationContract modelEvidence originalModel ->
    checkerReplay ->
    ay_vadr_later_validation rotationContract checkerReplay originalModel :=
  fun artifact replayProof =>
    ay_vadr_later_validation_intro rotationContract checkerReplay
      originalModel
      (ay_vadr_sat_artifact_contract rotationContract modelEvidence
        originalModel artifact)
      replayProof
      (ay_vadr_sat_artifact_original_model rotationContract modelEvidence
        originalModel artifact)

theorem ay_vadr_unsat_rotation_preserves_later_validation
    (rotationContract proofEvidence originalEmptyClause checkerReplay : Prop) :
    ay_vadr_unsat_artifact rotationContract proofEvidence
      originalEmptyClause ->
    checkerReplay ->
    ay_vadr_later_validation rotationContract checkerReplay
      originalEmptyClause :=
  fun artifact replayProof =>
    ay_vadr_later_validation_intro rotationContract checkerReplay
      originalEmptyClause
      (ay_vadr_unsat_artifact_contract rotationContract proofEvidence
        originalEmptyClause artifact)
      replayProof
      (ay_vadr_unsat_artifact_original_empty_clause rotationContract
        proofEvidence originalEmptyClause artifact)

theorem ay_vadr_no_claim_rotation_preserves_later_validation
    (rotationContract diagnostic noSemanticClaim checkerReplay : Prop) :
    ay_vadr_no_claim_artifact rotationContract diagnostic noSemanticClaim ->
    checkerReplay ->
    ay_vadr_later_validation rotationContract checkerReplay
      noSemanticClaim :=
  fun artifact replayProof =>
    ay_vadr_later_validation_intro rotationContract checkerReplay
      noSemanticClaim
      (ay_vadr_conj_left rotationContract
        (ay_vadr_conj diagnostic noSemanticClaim) artifact)
      replayProof
      (ay_vadr_no_claim_artifact_no_semantic_claim rotationContract
        diagnostic noSemanticClaim artifact)

theorem ay_vadr_sat_public_result_from_rotation
    (rotationContract modelEvidence originalModel unsatFact noClaimFact :
      Prop) :
    ay_vadr_sat_artifact rotationContract modelEvidence originalModel ->
    ay_vadr_public_result originalModel unsatFact noClaimFact :=
  fun artifact =>
    ay_vadr_disj_left originalModel
      (ay_vadr_disj unsatFact noClaimFact)
      (ay_vadr_sat_artifact_original_model rotationContract modelEvidence
        originalModel artifact)

theorem ay_vadr_unsat_public_result_from_rotation
    (satFact rotationContract proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_vadr_unsat_artifact rotationContract proofEvidence
      originalEmptyClause ->
    ay_vadr_public_result satFact originalEmptyClause noClaimFact :=
  fun artifact =>
    ay_vadr_disj_right satFact
      (ay_vadr_disj originalEmptyClause noClaimFact)
      (ay_vadr_disj_left originalEmptyClause noClaimFact
        (ay_vadr_unsat_artifact_original_empty_clause rotationContract
          proofEvidence originalEmptyClause artifact))

theorem ay_vadr_no_claim_public_result_from_rotation
    (satFact unsatFact rotationContract diagnostic noSemanticClaim : Prop) :
    ay_vadr_no_claim_artifact rotationContract diagnostic noSemanticClaim ->
    ay_vadr_public_result satFact unsatFact noSemanticClaim :=
  fun artifact =>
    ay_vadr_disj_right satFact
      (ay_vadr_disj unsatFact noSemanticClaim)
      (ay_vadr_disj_right unsatFact noSemanticClaim
        (ay_vadr_no_claim_artifact_no_semantic_claim rotationContract
          diagnostic noSemanticClaim artifact))

theorem ay_vadr_blocked_validation_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vadr_blocked_validation satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vadr_conj_intro reason
      (ay_vadr_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vadr_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vadr_blocked_validation_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vadr_blocked_validation satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vadr_conj_right reason
      (ay_vadr_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vadr_blocked_validation_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vadr_blocked_validation satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vadr_conj_right reason
      (ay_vadr_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vadr_recompute_intro
    (reason auditTrail fallbackPath : Prop) :
    reason -> auditTrail -> fallbackPath ->
    ay_vadr_recompute reason auditTrail fallbackPath :=
  fun reasonProof auditProof fallbackProof =>
    ay_vadr_conj_intro reason
      (ay_vadr_conj auditTrail fallbackPath)
      reasonProof
      (ay_vadr_conj_intro auditTrail fallbackPath auditProof fallbackProof)

theorem ay_vadr_rotation_failure_intro
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vadr_blocked_validation satFact unsatFact reason ->
    ay_vadr_recompute reason auditTrail fallbackPath ->
    ay_vadr_rotation_failure satFact unsatFact reason auditTrail
      fallbackPath :=
  fun blocked recompute =>
    ay_vadr_conj_intro
      (ay_vadr_blocked_validation satFact unsatFact reason)
      (ay_vadr_recompute reason auditTrail fallbackPath)
      blocked recompute

theorem ay_vadr_rotation_failure_blocks_sat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vadr_rotation_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vadr_blocked_validation_no_sat satFact unsatFact reason
      (ay_vadr_conj_left
        (ay_vadr_blocked_validation satFact unsatFact reason)
        (ay_vadr_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vadr_rotation_failure_blocks_unsat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vadr_rotation_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vadr_blocked_validation_no_unsat satFact unsatFact reason
      (ay_vadr_conj_left
        (ay_vadr_blocked_validation satFact unsatFact reason)
        (ay_vadr_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vadr_rotation_failure_recompute
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vadr_rotation_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    ay_vadr_recompute reason auditTrail fallbackPath :=
  fun failure =>
    ay_vadr_conj_right
      (ay_vadr_blocked_validation satFact unsatFact reason)
      (ay_vadr_recompute reason auditTrail fallbackPath)
      failure

theorem ay_vadr_missing_migration_link_forces_no_claim
    (satFact unsatFact missingMigration auditTrail fallbackPath : Prop) :
    missingMigration -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vadr_rotation_failure satFact unsatFact missingMigration auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vadr_rotation_failure_intro satFact unsatFact missingMigration
      auditTrail fallbackPath
      (ay_vadr_blocked_validation_intro satFact unsatFact missingMigration
        reasonProof blockSat blockUnsat)
      (ay_vadr_recompute_intro missingMigration auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vadr_stale_old_root_forces_no_claim
    (satFact unsatFact staleOldRoot auditTrail fallbackPath : Prop) :
    staleOldRoot -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vadr_rotation_failure satFact unsatFact staleOldRoot auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vadr_rotation_failure_intro satFact unsatFact staleOldRoot
      auditTrail fallbackPath
      (ay_vadr_blocked_validation_intro satFact unsatFact staleOldRoot
        reasonProof blockSat blockUnsat)
      (ay_vadr_recompute_intro staleOldRoot auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vadr_missing_retained_evidence_forces_no_claim
    (satFact unsatFact missingRetained auditTrail fallbackPath : Prop) :
    missingRetained -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vadr_rotation_failure satFact unsatFact missingRetained auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vadr_rotation_failure_intro satFact unsatFact missingRetained
      auditTrail fallbackPath
      (ay_vadr_blocked_validation_intro satFact unsatFact missingRetained
        reasonProof blockSat blockUnsat)
      (ay_vadr_recompute_intro missingRetained auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vadr_contradictory_audit_forces_no_claim
    (satFact unsatFact contradictoryAudit auditTrail fallbackPath : Prop) :
    contradictoryAudit -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vadr_rotation_failure satFact unsatFact contradictoryAudit auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vadr_rotation_failure_intro satFact unsatFact contradictoryAudit
      auditTrail fallbackPath
      (ay_vadr_blocked_validation_intro satFact unsatFact contradictoryAudit
        reasonProof blockSat blockUnsat)
      (ay_vadr_recompute_intro contradictoryAudit auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vadr_failure_cannot_validate_sat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vadr_rotation_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    satFact -> False :=
  ay_vadr_rotation_failure_blocks_sat satFact unsatFact reason auditTrail
    fallbackPath

theorem ay_vadr_failure_cannot_validate_unsat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vadr_rotation_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    unsatFact -> False :=
  ay_vadr_rotation_failure_blocks_unsat satFact unsatFact reason auditTrail
    fallbackPath
