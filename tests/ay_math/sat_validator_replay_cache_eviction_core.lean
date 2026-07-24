-- SAT-COMP validator replay cache eviction core.
--
-- Evicting replay/cache artifacts is safe only when public claims retain
-- independent manifest, digest, reconstruction, exit-code, and audit evidence.
-- Future validation must either rehydrate/replay from retained data or
-- downgrade to no-claim/recompute.

def ay_vrce_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrce_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vrce_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vrce_disj satFact (ay_vrce_disj unsatFact noClaimFact)

def ay_vrce_retained_independent_evidence
    (manifestDigest digestRoot reconstructionEvidence exitCodeState
      auditTrail : Prop) : Prop :=
  ay_vrce_conj manifestDigest
    (ay_vrce_conj digestRoot
      (ay_vrce_conj reconstructionEvidence
        (ay_vrce_conj exitCodeState auditTrail)))

def ay_vrce_eviction_audit
    (removedReplay cacheEpoch auditTrail evictionReason : Prop) : Prop :=
  ay_vrce_conj removedReplay
    (ay_vrce_conj cacheEpoch
      (ay_vrce_conj auditTrail evictionReason))

def ay_vrce_sat_public_claim
    (retainedEvidence evictionAudit modelEvidence originalModel : Prop) :
    Prop :=
  ay_vrce_conj retainedEvidence
    (ay_vrce_conj evictionAudit
      (ay_vrce_conj modelEvidence originalModel))

def ay_vrce_unsat_public_claim
    (retainedEvidence evictionAudit proofEvidence originalEmptyClause : Prop) :
    Prop :=
  ay_vrce_conj retainedEvidence
    (ay_vrce_conj evictionAudit
      (ay_vrce_conj proofEvidence originalEmptyClause))

def ay_vrce_rehydrated_validation
    (retainedEvidence rehydratedReplay checkerReplay publicEvidence : Prop) :
    Prop :=
  ay_vrce_conj retainedEvidence
    (ay_vrce_conj rehydratedReplay
      (ay_vrce_conj checkerReplay publicEvidence))

def ay_vrce_no_claim
    (reason auditTrail diagnostic : Prop) : Prop :=
  ay_vrce_conj reason (ay_vrce_conj auditTrail diagnostic)

def ay_vrce_recompute
    (reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vrce_conj reason (ay_vrce_conj auditTrail fallbackPath)

def ay_vrce_blocked_validation
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vrce_conj reason
    (ay_vrce_conj (satFact -> False) (unsatFact -> False))

def ay_vrce_eviction_failure
    (satFact unsatFact reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vrce_conj
    (ay_vrce_blocked_validation satFact unsatFact reason)
    (ay_vrce_recompute reason auditTrail fallbackPath)

theorem ay_vrce_conj_intro (left right : Prop) :
    left -> right -> ay_vrce_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrce_conj_left (left right : Prop) :
    ay_vrce_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrce_conj_right (left right : Prop) :
    ay_vrce_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrce_disj_left (left right : Prop) :
    left -> ay_vrce_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vrce_disj_right (left right : Prop) :
    right -> ay_vrce_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrce_retained_independent_evidence_intro
    (manifestDigest digestRoot reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    manifestDigest -> digestRoot -> reconstructionEvidence ->
    exitCodeState -> auditTrail ->
    ay_vrce_retained_independent_evidence manifestDigest digestRoot
      reconstructionEvidence exitCodeState auditTrail :=
  fun manifestProof digestProof reconstructionProof exitProof auditProof =>
    ay_vrce_conj_intro manifestDigest
      (ay_vrce_conj digestRoot
        (ay_vrce_conj reconstructionEvidence
          (ay_vrce_conj exitCodeState auditTrail)))
      manifestProof
      (ay_vrce_conj_intro digestRoot
        (ay_vrce_conj reconstructionEvidence
          (ay_vrce_conj exitCodeState auditTrail))
        digestProof
        (ay_vrce_conj_intro reconstructionEvidence
          (ay_vrce_conj exitCodeState auditTrail)
          reconstructionProof
          (ay_vrce_conj_intro exitCodeState auditTrail exitProof
            auditProof)))

theorem ay_vrce_retained_independent_evidence_manifest
    (manifestDigest digestRoot reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    ay_vrce_retained_independent_evidence manifestDigest digestRoot
      reconstructionEvidence exitCodeState auditTrail ->
    manifestDigest :=
  fun retained =>
    ay_vrce_conj_left manifestDigest
      (ay_vrce_conj digestRoot
        (ay_vrce_conj reconstructionEvidence
          (ay_vrce_conj exitCodeState auditTrail)))
      retained

theorem ay_vrce_retained_independent_evidence_digest
    (manifestDigest digestRoot reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    ay_vrce_retained_independent_evidence manifestDigest digestRoot
      reconstructionEvidence exitCodeState auditTrail ->
    digestRoot :=
  fun retained =>
    ay_vrce_conj_right manifestDigest
      (ay_vrce_conj digestRoot
        (ay_vrce_conj reconstructionEvidence
          (ay_vrce_conj exitCodeState auditTrail)))
      retained digestRoot
      (fun digestProof _tail => digestProof)

theorem ay_vrce_retained_independent_evidence_reconstruction
    (manifestDigest digestRoot reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    ay_vrce_retained_independent_evidence manifestDigest digestRoot
      reconstructionEvidence exitCodeState auditTrail ->
    reconstructionEvidence :=
  fun retained =>
    ay_vrce_conj_right manifestDigest
      (ay_vrce_conj digestRoot
        (ay_vrce_conj reconstructionEvidence
          (ay_vrce_conj exitCodeState auditTrail)))
      retained reconstructionEvidence
      (fun _digestProof tail =>
        tail reconstructionEvidence
          (fun reconstructionProof _tail2 => reconstructionProof))

theorem ay_vrce_retained_independent_evidence_exit
    (manifestDigest digestRoot reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    ay_vrce_retained_independent_evidence manifestDigest digestRoot
      reconstructionEvidence exitCodeState auditTrail ->
    exitCodeState :=
  fun retained =>
    ay_vrce_conj_right manifestDigest
      (ay_vrce_conj digestRoot
        (ay_vrce_conj reconstructionEvidence
          (ay_vrce_conj exitCodeState auditTrail)))
      retained exitCodeState
      (fun _digestProof tail =>
        tail exitCodeState
          (fun _reconstructionProof tail2 =>
            tail2 exitCodeState
              (fun exitProof _auditProof => exitProof)))

theorem ay_vrce_retained_independent_evidence_audit
    (manifestDigest digestRoot reconstructionEvidence exitCodeState
      auditTrail : Prop) :
    ay_vrce_retained_independent_evidence manifestDigest digestRoot
      reconstructionEvidence exitCodeState auditTrail ->
    auditTrail :=
  fun retained =>
    ay_vrce_conj_right manifestDigest
      (ay_vrce_conj digestRoot
        (ay_vrce_conj reconstructionEvidence
          (ay_vrce_conj exitCodeState auditTrail)))
      retained auditTrail
      (fun _digestProof tail =>
        tail auditTrail
          (fun _reconstructionProof tail2 =>
            tail2 auditTrail
              (fun _exitProof auditProof => auditProof)))

theorem ay_vrce_eviction_audit_intro
    (removedReplay cacheEpoch auditTrail evictionReason : Prop) :
    removedReplay -> cacheEpoch -> auditTrail -> evictionReason ->
    ay_vrce_eviction_audit removedReplay cacheEpoch auditTrail
      evictionReason :=
  fun removedProof epochProof auditProof reasonProof =>
    ay_vrce_conj_intro removedReplay
      (ay_vrce_conj cacheEpoch
        (ay_vrce_conj auditTrail evictionReason))
      removedProof
      (ay_vrce_conj_intro cacheEpoch
        (ay_vrce_conj auditTrail evictionReason)
        epochProof
        (ay_vrce_conj_intro auditTrail evictionReason auditProof
          reasonProof))

theorem ay_vrce_eviction_audit_removed_replay
    (removedReplay cacheEpoch auditTrail evictionReason : Prop) :
    ay_vrce_eviction_audit removedReplay cacheEpoch auditTrail
      evictionReason ->
    removedReplay :=
  fun audit =>
    ay_vrce_conj_left removedReplay
      (ay_vrce_conj cacheEpoch
        (ay_vrce_conj auditTrail evictionReason))
      audit

theorem ay_vrce_eviction_audit_trail
    (removedReplay cacheEpoch auditTrail evictionReason : Prop) :
    ay_vrce_eviction_audit removedReplay cacheEpoch auditTrail
      evictionReason ->
    auditTrail :=
  fun audit =>
    ay_vrce_conj_right removedReplay
      (ay_vrce_conj cacheEpoch
        (ay_vrce_conj auditTrail evictionReason))
      audit auditTrail
      (fun _epochProof tail =>
        tail auditTrail (fun auditProof _reasonProof => auditProof))

theorem ay_vrce_sat_public_claim_intro
    (retainedEvidence evictionAudit modelEvidence originalModel : Prop) :
    retainedEvidence -> evictionAudit -> modelEvidence -> originalModel ->
    ay_vrce_sat_public_claim retainedEvidence evictionAudit modelEvidence
      originalModel :=
  fun retainedProof auditProof modelProof originalProof =>
    ay_vrce_conj_intro retainedEvidence
      (ay_vrce_conj evictionAudit
        (ay_vrce_conj modelEvidence originalModel))
      retainedProof
      (ay_vrce_conj_intro evictionAudit
        (ay_vrce_conj modelEvidence originalModel)
        auditProof
        (ay_vrce_conj_intro modelEvidence originalModel modelProof
          originalProof))

theorem ay_vrce_sat_public_claim_retained
    (retainedEvidence evictionAudit modelEvidence originalModel : Prop) :
    ay_vrce_sat_public_claim retainedEvidence evictionAudit modelEvidence
      originalModel ->
    retainedEvidence :=
  fun claim =>
    ay_vrce_conj_left retainedEvidence
      (ay_vrce_conj evictionAudit
        (ay_vrce_conj modelEvidence originalModel))
      claim

theorem ay_vrce_sat_public_claim_original_model
    (retainedEvidence evictionAudit modelEvidence originalModel : Prop) :
    ay_vrce_sat_public_claim retainedEvidence evictionAudit modelEvidence
      originalModel ->
    originalModel :=
  fun claim =>
    ay_vrce_conj_right retainedEvidence
      (ay_vrce_conj evictionAudit
        (ay_vrce_conj modelEvidence originalModel))
      claim originalModel
      (fun _auditProof tail =>
        tail originalModel
          (fun _modelProof originalProof => originalProof))

theorem ay_vrce_unsat_public_claim_intro
    (retainedEvidence evictionAudit proofEvidence originalEmptyClause : Prop) :
    retainedEvidence -> evictionAudit -> proofEvidence ->
    originalEmptyClause ->
    ay_vrce_unsat_public_claim retainedEvidence evictionAudit proofEvidence
      originalEmptyClause :=
  fun retainedProof auditProof proofEvidenceProof emptyClauseProof =>
    ay_vrce_conj_intro retainedEvidence
      (ay_vrce_conj evictionAudit
        (ay_vrce_conj proofEvidence originalEmptyClause))
      retainedProof
      (ay_vrce_conj_intro evictionAudit
        (ay_vrce_conj proofEvidence originalEmptyClause)
        auditProof
        (ay_vrce_conj_intro proofEvidence originalEmptyClause
          proofEvidenceProof emptyClauseProof))

theorem ay_vrce_unsat_public_claim_retained
    (retainedEvidence evictionAudit proofEvidence originalEmptyClause : Prop) :
    ay_vrce_unsat_public_claim retainedEvidence evictionAudit proofEvidence
      originalEmptyClause ->
    retainedEvidence :=
  fun claim =>
    ay_vrce_conj_left retainedEvidence
      (ay_vrce_conj evictionAudit
        (ay_vrce_conj proofEvidence originalEmptyClause))
      claim

theorem ay_vrce_unsat_public_claim_original_empty_clause
    (retainedEvidence evictionAudit proofEvidence originalEmptyClause : Prop) :
    ay_vrce_unsat_public_claim retainedEvidence evictionAudit proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun claim =>
    ay_vrce_conj_right retainedEvidence
      (ay_vrce_conj evictionAudit
        (ay_vrce_conj proofEvidence originalEmptyClause))
      claim originalEmptyClause
      (fun _auditProof tail =>
        tail originalEmptyClause
          (fun _proofEvidenceProof emptyClauseProof => emptyClauseProof))

theorem ay_vrce_rehydrated_validation_intro
    (retainedEvidence rehydratedReplay checkerReplay publicEvidence : Prop) :
    retainedEvidence -> rehydratedReplay -> checkerReplay ->
    publicEvidence ->
    ay_vrce_rehydrated_validation retainedEvidence rehydratedReplay
      checkerReplay publicEvidence :=
  fun retainedProof rehydratedProof checkerProof publicProof =>
    ay_vrce_conj_intro retainedEvidence
      (ay_vrce_conj rehydratedReplay
        (ay_vrce_conj checkerReplay publicEvidence))
      retainedProof
      (ay_vrce_conj_intro rehydratedReplay
        (ay_vrce_conj checkerReplay publicEvidence)
        rehydratedProof
        (ay_vrce_conj_intro checkerReplay publicEvidence checkerProof
          publicProof))

theorem ay_vrce_rehydrated_validation_public_evidence
    (retainedEvidence rehydratedReplay checkerReplay publicEvidence : Prop) :
    ay_vrce_rehydrated_validation retainedEvidence rehydratedReplay
      checkerReplay publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vrce_conj_right retainedEvidence
      (ay_vrce_conj rehydratedReplay
        (ay_vrce_conj checkerReplay publicEvidence))
      validation publicEvidence
      (fun _rehydratedProof tail =>
        tail publicEvidence (fun _checkerProof publicProof => publicProof))

theorem ay_vrce_evicted_sat_claim_remains_sound
    (retainedEvidence evictionAudit modelEvidence originalModel unsatFact
      noClaimFact : Prop) :
    ay_vrce_sat_public_claim retainedEvidence evictionAudit modelEvidence
      originalModel ->
    ay_vrce_public_result originalModel unsatFact noClaimFact :=
  fun claim =>
    ay_vrce_disj_left originalModel
      (ay_vrce_disj unsatFact noClaimFact)
      (ay_vrce_sat_public_claim_original_model retainedEvidence
        evictionAudit modelEvidence originalModel claim)

theorem ay_vrce_evicted_unsat_claim_remains_sound
    (satFact retainedEvidence evictionAudit proofEvidence originalEmptyClause
      noClaimFact : Prop) :
    ay_vrce_unsat_public_claim retainedEvidence evictionAudit proofEvidence
      originalEmptyClause ->
    ay_vrce_public_result satFact originalEmptyClause noClaimFact :=
  fun claim =>
    ay_vrce_disj_right satFact
      (ay_vrce_disj originalEmptyClause noClaimFact)
      (ay_vrce_disj_left originalEmptyClause noClaimFact
        (ay_vrce_unsat_public_claim_original_empty_clause retainedEvidence
          evictionAudit proofEvidence originalEmptyClause claim))

theorem ay_vrce_rehydration_validates_sat_claim
    (retainedEvidence rehydratedReplay checkerReplay originalModel unsatFact
      noClaimFact : Prop) :
    ay_vrce_rehydrated_validation retainedEvidence rehydratedReplay
      checkerReplay originalModel ->
    ay_vrce_public_result originalModel unsatFact noClaimFact :=
  fun validation =>
    ay_vrce_disj_left originalModel
      (ay_vrce_disj unsatFact noClaimFact)
      (ay_vrce_rehydrated_validation_public_evidence retainedEvidence
        rehydratedReplay checkerReplay originalModel validation)

theorem ay_vrce_rehydration_validates_unsat_claim
    (satFact retainedEvidence rehydratedReplay checkerReplay
      originalEmptyClause noClaimFact : Prop) :
    ay_vrce_rehydrated_validation retainedEvidence rehydratedReplay
      checkerReplay originalEmptyClause ->
    ay_vrce_public_result satFact originalEmptyClause noClaimFact :=
  fun validation =>
    ay_vrce_disj_right satFact
      (ay_vrce_disj originalEmptyClause noClaimFact)
      (ay_vrce_disj_left originalEmptyClause noClaimFact
        (ay_vrce_rehydrated_validation_public_evidence retainedEvidence
          rehydratedReplay checkerReplay originalEmptyClause validation))

theorem ay_vrce_no_claim_intro
    (reason auditTrail diagnostic : Prop) :
    reason -> auditTrail -> diagnostic ->
    ay_vrce_no_claim reason auditTrail diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vrce_conj_intro reason
      (ay_vrce_conj auditTrail diagnostic)
      reasonProof
      (ay_vrce_conj_intro auditTrail diagnostic auditProof diagnosticProof)

theorem ay_vrce_recompute_intro
    (reason auditTrail fallbackPath : Prop) :
    reason -> auditTrail -> fallbackPath ->
    ay_vrce_recompute reason auditTrail fallbackPath :=
  fun reasonProof auditProof fallbackProof =>
    ay_vrce_conj_intro reason
      (ay_vrce_conj auditTrail fallbackPath)
      reasonProof
      (ay_vrce_conj_intro auditTrail fallbackPath auditProof fallbackProof)

theorem ay_vrce_blocked_validation_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vrce_blocked_validation satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vrce_conj_intro reason
      (ay_vrce_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vrce_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vrce_blocked_validation_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vrce_blocked_validation satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vrce_conj_right reason
      (ay_vrce_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vrce_blocked_validation_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vrce_blocked_validation satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vrce_conj_right reason
      (ay_vrce_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vrce_eviction_failure_intro
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrce_blocked_validation satFact unsatFact reason ->
    ay_vrce_recompute reason auditTrail fallbackPath ->
    ay_vrce_eviction_failure satFact unsatFact reason auditTrail
      fallbackPath :=
  fun blocked recompute =>
    ay_vrce_conj_intro
      (ay_vrce_blocked_validation satFact unsatFact reason)
      (ay_vrce_recompute reason auditTrail fallbackPath)
      blocked recompute

theorem ay_vrce_eviction_failure_blocks_sat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrce_eviction_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vrce_blocked_validation_no_sat satFact unsatFact reason
      (ay_vrce_conj_left
        (ay_vrce_blocked_validation satFact unsatFact reason)
        (ay_vrce_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vrce_eviction_failure_blocks_unsat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrce_eviction_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vrce_blocked_validation_no_unsat satFact unsatFact reason
      (ay_vrce_conj_left
        (ay_vrce_blocked_validation satFact unsatFact reason)
        (ay_vrce_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vrce_eviction_failure_recompute
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrce_eviction_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    ay_vrce_recompute reason auditTrail fallbackPath :=
  fun failure =>
    ay_vrce_conj_right
      (ay_vrce_blocked_validation satFact unsatFact reason)
      (ay_vrce_recompute reason auditTrail fallbackPath)
      failure

theorem ay_vrce_missing_retained_evidence_forces_no_claim
    (satFact unsatFact missingRetained auditTrail fallbackPath : Prop) :
    missingRetained -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrce_eviction_failure satFact unsatFact missingRetained auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrce_eviction_failure_intro satFact unsatFact missingRetained
      auditTrail fallbackPath
      (ay_vrce_blocked_validation_intro satFact unsatFact missingRetained
        reasonProof blockSat blockUnsat)
      (ay_vrce_recompute_intro missingRetained auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrce_failed_rehydration_forces_no_claim
    (satFact unsatFact failedRehydration auditTrail fallbackPath : Prop) :
    failedRehydration -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrce_eviction_failure satFact unsatFact failedRehydration auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrce_eviction_failure_intro satFact unsatFact failedRehydration
      auditTrail fallbackPath
      (ay_vrce_blocked_validation_intro satFact unsatFact failedRehydration
        reasonProof blockSat blockUnsat)
      (ay_vrce_recompute_intro failedRehydration auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrce_failure_cannot_validate_sat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrce_eviction_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    satFact -> False :=
  ay_vrce_eviction_failure_blocks_sat satFact unsatFact reason auditTrail
    fallbackPath

theorem ay_vrce_failure_cannot_validate_unsat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrce_eviction_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    unsatFact -> False :=
  ay_vrce_eviction_failure_blocks_unsat satFact unsatFact reason auditTrail
    fallbackPath
