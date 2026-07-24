-- SAT-COMP validator public artifact retention core.
--
-- Public SAT/UNSAT/no-claim results must retain enough artifacts for later
-- validation: manifest digest, replay transcript, reconstruction evidence,
-- exit-code state, and audit trail.  Missing retention downgrades to
-- no-claim/recompute and cannot retroactively validate a SAT/UNSAT claim.

def ay_vpar_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vpar_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vpar_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vpar_disj satFact (ay_vpar_disj unsatFact noClaimFact)

def ay_vpar_retained_artifacts
    (manifestDigest replayTranscript reconstructionEvidence exitCodeState
      auditTrail : Prop) : Prop :=
  ay_vpar_conj manifestDigest
    (ay_vpar_conj replayTranscript
      (ay_vpar_conj reconstructionEvidence
        (ay_vpar_conj exitCodeState auditTrail)))

def ay_vpar_sat_retention
    (retainedArtifacts modelEvidence originalModel : Prop) : Prop :=
  ay_vpar_conj retainedArtifacts
    (ay_vpar_conj modelEvidence originalModel)

def ay_vpar_unsat_retention
    (retainedArtifacts proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vpar_conj retainedArtifacts
    (ay_vpar_conj proofEvidence originalEmptyClause)

def ay_vpar_no_claim_retention
    (retainedArtifacts diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vpar_conj retainedArtifacts
    (ay_vpar_conj diagnostic noSemanticClaim)

def ay_vpar_later_validation
    (retainedArtifacts checkerReplay reconstruction publicEvidence : Prop) :
    Prop :=
  ay_vpar_conj retainedArtifacts
    (ay_vpar_conj checkerReplay
      (ay_vpar_conj reconstruction publicEvidence))

def ay_vpar_blocked_claim
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vpar_conj reason
    (ay_vpar_conj (satFact -> False) (unsatFact -> False))

def ay_vpar_recompute
    (reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vpar_conj reason (ay_vpar_conj auditTrail fallbackPath)

def ay_vpar_retention_failure
    (satFact unsatFact reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vpar_conj
    (ay_vpar_blocked_claim satFact unsatFact reason)
    (ay_vpar_recompute reason auditTrail fallbackPath)

theorem ay_vpar_conj_intro (left right : Prop) :
    left -> right -> ay_vpar_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vpar_conj_left (left right : Prop) :
    ay_vpar_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vpar_conj_right (left right : Prop) :
    ay_vpar_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vpar_disj_left (left right : Prop) :
    left -> ay_vpar_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vpar_disj_right (left right : Prop) :
    right -> ay_vpar_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vpar_retained_artifacts_intro
    (manifestDigest replayTranscript reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    manifestDigest -> replayTranscript -> reconstructionEvidence ->
    exitCodeState -> auditTrail ->
    ay_vpar_retained_artifacts manifestDigest replayTranscript
      reconstructionEvidence exitCodeState auditTrail :=
  fun digestProof replayProof reconstructionProof exitProof auditProof =>
    ay_vpar_conj_intro manifestDigest
      (ay_vpar_conj replayTranscript
        (ay_vpar_conj reconstructionEvidence
          (ay_vpar_conj exitCodeState auditTrail)))
      digestProof
      (ay_vpar_conj_intro replayTranscript
        (ay_vpar_conj reconstructionEvidence
          (ay_vpar_conj exitCodeState auditTrail))
        replayProof
        (ay_vpar_conj_intro reconstructionEvidence
          (ay_vpar_conj exitCodeState auditTrail)
          reconstructionProof
          (ay_vpar_conj_intro exitCodeState auditTrail exitProof
            auditProof)))

theorem ay_vpar_retained_artifacts_digest
    (manifestDigest replayTranscript reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    ay_vpar_retained_artifacts manifestDigest replayTranscript
      reconstructionEvidence exitCodeState auditTrail ->
    manifestDigest :=
  fun retained =>
    ay_vpar_conj_left manifestDigest
      (ay_vpar_conj replayTranscript
        (ay_vpar_conj reconstructionEvidence
          (ay_vpar_conj exitCodeState auditTrail)))
      retained

theorem ay_vpar_retained_artifacts_replay
    (manifestDigest replayTranscript reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    ay_vpar_retained_artifacts manifestDigest replayTranscript
      reconstructionEvidence exitCodeState auditTrail ->
    replayTranscript :=
  fun retained =>
    ay_vpar_conj_right manifestDigest
      (ay_vpar_conj replayTranscript
        (ay_vpar_conj reconstructionEvidence
          (ay_vpar_conj exitCodeState auditTrail)))
      retained replayTranscript
      (fun replayProof _tail => replayProof)

theorem ay_vpar_retained_artifacts_reconstruction
    (manifestDigest replayTranscript reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    ay_vpar_retained_artifacts manifestDigest replayTranscript
      reconstructionEvidence exitCodeState auditTrail ->
    reconstructionEvidence :=
  fun retained =>
    ay_vpar_conj_right manifestDigest
      (ay_vpar_conj replayTranscript
        (ay_vpar_conj reconstructionEvidence
          (ay_vpar_conj exitCodeState auditTrail)))
      retained reconstructionEvidence
      (fun _replayProof tail =>
        tail reconstructionEvidence
          (fun reconstructionProof _tail2 => reconstructionProof))

theorem ay_vpar_retained_artifacts_exit
    (manifestDigest replayTranscript reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    ay_vpar_retained_artifacts manifestDigest replayTranscript
      reconstructionEvidence exitCodeState auditTrail ->
    exitCodeState :=
  fun retained =>
    ay_vpar_conj_right manifestDigest
      (ay_vpar_conj replayTranscript
        (ay_vpar_conj reconstructionEvidence
          (ay_vpar_conj exitCodeState auditTrail)))
      retained exitCodeState
      (fun _replayProof tail =>
        tail exitCodeState
          (fun _reconstructionProof tail2 =>
            tail2 exitCodeState
              (fun exitProof _auditProof => exitProof)))

theorem ay_vpar_retained_artifacts_audit
    (manifestDigest replayTranscript reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    ay_vpar_retained_artifacts manifestDigest replayTranscript
      reconstructionEvidence exitCodeState auditTrail ->
    auditTrail :=
  fun retained =>
    ay_vpar_conj_right manifestDigest
      (ay_vpar_conj replayTranscript
        (ay_vpar_conj reconstructionEvidence
          (ay_vpar_conj exitCodeState auditTrail)))
      retained auditTrail
      (fun _replayProof tail =>
        tail auditTrail
          (fun _reconstructionProof tail2 =>
            tail2 auditTrail
              (fun _exitProof auditProof => auditProof)))

theorem ay_vpar_sat_retention_intro
    (retainedArtifacts modelEvidence originalModel : Prop) :
    retainedArtifacts -> modelEvidence -> originalModel ->
    ay_vpar_sat_retention retainedArtifacts modelEvidence originalModel :=
  fun retainedProof modelProof originalProof =>
    ay_vpar_conj_intro retainedArtifacts
      (ay_vpar_conj modelEvidence originalModel)
      retainedProof
      (ay_vpar_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vpar_sat_retention_artifacts
    (retainedArtifacts modelEvidence originalModel : Prop) :
    ay_vpar_sat_retention retainedArtifacts modelEvidence originalModel ->
    retainedArtifacts :=
  fun retention =>
    ay_vpar_conj_left retainedArtifacts
      (ay_vpar_conj modelEvidence originalModel) retention

theorem ay_vpar_sat_retention_model_evidence
    (retainedArtifacts modelEvidence originalModel : Prop) :
    ay_vpar_sat_retention retainedArtifacts modelEvidence originalModel ->
    modelEvidence :=
  fun retention =>
    ay_vpar_conj_right retainedArtifacts
      (ay_vpar_conj modelEvidence originalModel)
      retention modelEvidence
      (fun modelProof _originalProof => modelProof)

theorem ay_vpar_sat_retention_original_model
    (retainedArtifacts modelEvidence originalModel : Prop) :
    ay_vpar_sat_retention retainedArtifacts modelEvidence originalModel ->
    originalModel :=
  fun retention =>
    ay_vpar_conj_right retainedArtifacts
      (ay_vpar_conj modelEvidence originalModel)
      retention originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vpar_unsat_retention_intro
    (retainedArtifacts proofEvidence originalEmptyClause : Prop) :
    retainedArtifacts -> proofEvidence -> originalEmptyClause ->
    ay_vpar_unsat_retention retainedArtifacts proofEvidence
      originalEmptyClause :=
  fun retainedProof proofEvidenceProof emptyClauseProof =>
    ay_vpar_conj_intro retainedArtifacts
      (ay_vpar_conj proofEvidence originalEmptyClause)
      retainedProof
      (ay_vpar_conj_intro proofEvidence originalEmptyClause
        proofEvidenceProof emptyClauseProof)

theorem ay_vpar_unsat_retention_artifacts
    (retainedArtifacts proofEvidence originalEmptyClause : Prop) :
    ay_vpar_unsat_retention retainedArtifacts proofEvidence
      originalEmptyClause ->
    retainedArtifacts :=
  fun retention =>
    ay_vpar_conj_left retainedArtifacts
      (ay_vpar_conj proofEvidence originalEmptyClause) retention

theorem ay_vpar_unsat_retention_proof_evidence
    (retainedArtifacts proofEvidence originalEmptyClause : Prop) :
    ay_vpar_unsat_retention retainedArtifacts proofEvidence
      originalEmptyClause ->
    proofEvidence :=
  fun retention =>
    ay_vpar_conj_right retainedArtifacts
      (ay_vpar_conj proofEvidence originalEmptyClause)
      retention proofEvidence
      (fun proofEvidenceProof _emptyClauseProof => proofEvidenceProof)

theorem ay_vpar_unsat_retention_original_empty_clause
    (retainedArtifacts proofEvidence originalEmptyClause : Prop) :
    ay_vpar_unsat_retention retainedArtifacts proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun retention =>
    ay_vpar_conj_right retainedArtifacts
      (ay_vpar_conj proofEvidence originalEmptyClause)
      retention originalEmptyClause
      (fun _proofEvidenceProof emptyClauseProof => emptyClauseProof)

theorem ay_vpar_no_claim_retention_intro
    (retainedArtifacts diagnostic noSemanticClaim : Prop) :
    retainedArtifacts -> diagnostic -> noSemanticClaim ->
    ay_vpar_no_claim_retention retainedArtifacts diagnostic
      noSemanticClaim :=
  fun retainedProof diagnosticProof noClaimProof =>
    ay_vpar_conj_intro retainedArtifacts
      (ay_vpar_conj diagnostic noSemanticClaim)
      retainedProof
      (ay_vpar_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vpar_no_claim_retention_no_semantic_claim
    (retainedArtifacts diagnostic noSemanticClaim : Prop) :
    ay_vpar_no_claim_retention retainedArtifacts diagnostic
      noSemanticClaim ->
    noSemanticClaim :=
  fun retention =>
    ay_vpar_conj_right retainedArtifacts
      (ay_vpar_conj diagnostic noSemanticClaim)
      retention noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vpar_later_validation_intro
    (retainedArtifacts checkerReplay reconstruction publicEvidence : Prop) :
    retainedArtifacts -> checkerReplay -> reconstruction ->
    publicEvidence ->
    ay_vpar_later_validation retainedArtifacts checkerReplay
      reconstruction publicEvidence :=
  fun retainedProof replayProof reconstructionProof publicProof =>
    ay_vpar_conj_intro retainedArtifacts
      (ay_vpar_conj checkerReplay
        (ay_vpar_conj reconstruction publicEvidence))
      retainedProof
      (ay_vpar_conj_intro checkerReplay
        (ay_vpar_conj reconstruction publicEvidence)
        replayProof
        (ay_vpar_conj_intro reconstruction publicEvidence
          reconstructionProof publicProof))

theorem ay_vpar_later_validation_artifacts
    (retainedArtifacts checkerReplay reconstruction publicEvidence : Prop) :
    ay_vpar_later_validation retainedArtifacts checkerReplay
      reconstruction publicEvidence ->
    retainedArtifacts :=
  fun validation =>
    ay_vpar_conj_left retainedArtifacts
      (ay_vpar_conj checkerReplay
        (ay_vpar_conj reconstruction publicEvidence))
      validation

theorem ay_vpar_later_validation_public_evidence
    (retainedArtifacts checkerReplay reconstruction publicEvidence : Prop) :
    ay_vpar_later_validation retainedArtifacts checkerReplay
      reconstruction publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vpar_conj_right retainedArtifacts
      (ay_vpar_conj checkerReplay
        (ay_vpar_conj reconstruction publicEvidence))
      validation publicEvidence
      (fun _replayProof tail =>
        tail publicEvidence
          (fun _reconstructionProof publicProof => publicProof))

theorem ay_vpar_retained_sat_supports_later_validation
    (retainedArtifacts modelEvidence originalModel checkerReplay
      reconstruction : Prop) :
    ay_vpar_sat_retention retainedArtifacts modelEvidence originalModel ->
    checkerReplay -> reconstruction ->
    ay_vpar_later_validation retainedArtifacts checkerReplay reconstruction
      originalModel :=
  fun retention replayProof reconstructionProof =>
    ay_vpar_later_validation_intro retainedArtifacts checkerReplay
      reconstruction originalModel
      (ay_vpar_sat_retention_artifacts retainedArtifacts modelEvidence
        originalModel retention)
      replayProof reconstructionProof
      (ay_vpar_sat_retention_original_model retainedArtifacts modelEvidence
        originalModel retention)

theorem ay_vpar_retained_unsat_supports_later_validation
    (retainedArtifacts proofEvidence originalEmptyClause checkerReplay
      reconstruction : Prop) :
    ay_vpar_unsat_retention retainedArtifacts proofEvidence
      originalEmptyClause ->
    checkerReplay -> reconstruction ->
    ay_vpar_later_validation retainedArtifacts checkerReplay reconstruction
      originalEmptyClause :=
  fun retention replayProof reconstructionProof =>
    ay_vpar_later_validation_intro retainedArtifacts checkerReplay
      reconstruction originalEmptyClause
      (ay_vpar_unsat_retention_artifacts retainedArtifacts proofEvidence
        originalEmptyClause retention)
      replayProof reconstructionProof
      (ay_vpar_unsat_retention_original_empty_clause retainedArtifacts
        proofEvidence originalEmptyClause retention)

theorem ay_vpar_sat_public_result_from_retention
    (retainedArtifacts modelEvidence originalModel unsatFact noClaimFact :
      Prop) :
    ay_vpar_sat_retention retainedArtifacts modelEvidence originalModel ->
    ay_vpar_public_result originalModel unsatFact noClaimFact :=
  fun retention =>
    ay_vpar_disj_left originalModel
      (ay_vpar_disj unsatFact noClaimFact)
      (ay_vpar_sat_retention_original_model retainedArtifacts modelEvidence
        originalModel retention)

theorem ay_vpar_unsat_public_result_from_retention
    (satFact retainedArtifacts proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_vpar_unsat_retention retainedArtifacts proofEvidence
      originalEmptyClause ->
    ay_vpar_public_result satFact originalEmptyClause noClaimFact :=
  fun retention =>
    ay_vpar_disj_right satFact
      (ay_vpar_disj originalEmptyClause noClaimFact)
      (ay_vpar_disj_left originalEmptyClause noClaimFact
        (ay_vpar_unsat_retention_original_empty_clause retainedArtifacts
          proofEvidence originalEmptyClause retention))

theorem ay_vpar_no_claim_public_result_from_retention
    (satFact unsatFact retainedArtifacts diagnostic noSemanticClaim : Prop) :
    ay_vpar_no_claim_retention retainedArtifacts diagnostic
      noSemanticClaim ->
    ay_vpar_public_result satFact unsatFact noSemanticClaim :=
  fun retention =>
    ay_vpar_disj_right satFact
      (ay_vpar_disj unsatFact noSemanticClaim)
      (ay_vpar_disj_right unsatFact noSemanticClaim
        (ay_vpar_no_claim_retention_no_semantic_claim retainedArtifacts
          diagnostic noSemanticClaim retention))

theorem ay_vpar_blocked_claim_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vpar_blocked_claim satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vpar_conj_intro reason
      (ay_vpar_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vpar_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vpar_blocked_claim_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vpar_blocked_claim satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vpar_conj_right reason
      (ay_vpar_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vpar_blocked_claim_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vpar_blocked_claim satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vpar_conj_right reason
      (ay_vpar_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vpar_recompute_intro
    (reason auditTrail fallbackPath : Prop) :
    reason -> auditTrail -> fallbackPath ->
    ay_vpar_recompute reason auditTrail fallbackPath :=
  fun reasonProof auditProof fallbackProof =>
    ay_vpar_conj_intro reason
      (ay_vpar_conj auditTrail fallbackPath)
      reasonProof
      (ay_vpar_conj_intro auditTrail fallbackPath auditProof fallbackProof)

theorem ay_vpar_retention_failure_intro
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vpar_blocked_claim satFact unsatFact reason ->
    ay_vpar_recompute reason auditTrail fallbackPath ->
    ay_vpar_retention_failure satFact unsatFact reason auditTrail
      fallbackPath :=
  fun blocked recompute =>
    ay_vpar_conj_intro
      (ay_vpar_blocked_claim satFact unsatFact reason)
      (ay_vpar_recompute reason auditTrail fallbackPath)
      blocked recompute

theorem ay_vpar_retention_failure_blocks_sat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vpar_retention_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vpar_blocked_claim_no_sat satFact unsatFact reason
      (ay_vpar_conj_left
        (ay_vpar_blocked_claim satFact unsatFact reason)
        (ay_vpar_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vpar_retention_failure_blocks_unsat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vpar_retention_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vpar_blocked_claim_no_unsat satFact unsatFact reason
      (ay_vpar_conj_left
        (ay_vpar_blocked_claim satFact unsatFact reason)
        (ay_vpar_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vpar_retention_failure_recompute
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vpar_retention_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    ay_vpar_recompute reason auditTrail fallbackPath :=
  fun failure =>
    ay_vpar_conj_right
      (ay_vpar_blocked_claim satFact unsatFact reason)
      (ay_vpar_recompute reason auditTrail fallbackPath)
      failure

theorem ay_vpar_missing_artifacts_downgrade_to_no_claim
    (satFact unsatFact missingArtifacts auditTrail fallbackPath : Prop) :
    missingArtifacts -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vpar_retention_failure satFact unsatFact missingArtifacts auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vpar_retention_failure_intro satFact unsatFact missingArtifacts
      auditTrail fallbackPath
      (ay_vpar_blocked_claim_intro satFact unsatFact missingArtifacts
        reasonProof blockSat blockUnsat)
      (ay_vpar_recompute_intro missingArtifacts auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vpar_missing_artifacts_cannot_retroactively_publish_sat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vpar_retention_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    satFact -> False :=
  ay_vpar_retention_failure_blocks_sat satFact unsatFact reason auditTrail
    fallbackPath

theorem ay_vpar_missing_artifacts_cannot_retroactively_publish_unsat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vpar_retention_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    unsatFact -> False :=
  ay_vpar_retention_failure_blocks_unsat satFact unsatFact reason auditTrail
    fallbackPath
