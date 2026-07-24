-- SAT-COMP validator result bundle portability core.
--
-- A ay SAT/UNSAT/no-claim result bundle may move between runs or machines only
-- when solver build id, formula fingerprint, manifest digest, replay and
-- reconstruction evidence, exit-code contract, and audit trail all agree.
-- Drift or missing evidence downgrades to no-claim/recompute.

def ay_vrbp_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrbp_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vrbp_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vrbp_disj satFact (ay_vrbp_disj unsatFact noClaimFact)

def ay_vrbp_portability_contract
    (solverBuildId formulaFingerprint manifestDigest replayEvidence
      reconstructionEvidence exitCodeContract auditTrail : Prop) : Prop :=
  ay_vrbp_conj solverBuildId
    (ay_vrbp_conj formulaFingerprint
      (ay_vrbp_conj manifestDigest
        (ay_vrbp_conj replayEvidence
          (ay_vrbp_conj reconstructionEvidence
            (ay_vrbp_conj exitCodeContract auditTrail)))))

def ay_vrbp_sat_bundle
    (portabilityContract modelEvidence originalModel : Prop) : Prop :=
  ay_vrbp_conj portabilityContract
    (ay_vrbp_conj modelEvidence originalModel)

def ay_vrbp_unsat_bundle
    (portabilityContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vrbp_conj portabilityContract
    (ay_vrbp_conj proofEvidence originalEmptyClause)

def ay_vrbp_no_claim_bundle
    (portabilityContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vrbp_conj portabilityContract
    (ay_vrbp_conj diagnostic noSemanticClaim)

def ay_vrbp_ported_validation
    (portabilityContract checkerReplay publicEvidence : Prop) : Prop :=
  ay_vrbp_conj portabilityContract
    (ay_vrbp_conj checkerReplay publicEvidence)

def ay_vrbp_blocked_validation
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vrbp_conj reason
    (ay_vrbp_conj (satFact -> False) (unsatFact -> False))

def ay_vrbp_recompute
    (reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vrbp_conj reason (ay_vrbp_conj auditTrail fallbackPath)

def ay_vrbp_portability_failure
    (satFact unsatFact reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vrbp_conj
    (ay_vrbp_blocked_validation satFact unsatFact reason)
    (ay_vrbp_recompute reason auditTrail fallbackPath)

theorem ay_vrbp_conj_intro (left right : Prop) :
    left -> right -> ay_vrbp_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrbp_conj_left (left right : Prop) :
    ay_vrbp_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrbp_conj_right (left right : Prop) :
    ay_vrbp_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrbp_disj_left (left right : Prop) :
    left -> ay_vrbp_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vrbp_disj_right (left right : Prop) :
    right -> ay_vrbp_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrbp_portability_contract_intro
    (solverBuildId formulaFingerprint manifestDigest replayEvidence
      reconstructionEvidence exitCodeContract auditTrail : Prop) :
    solverBuildId -> formulaFingerprint -> manifestDigest ->
    replayEvidence -> reconstructionEvidence -> exitCodeContract ->
    auditTrail ->
    ay_vrbp_portability_contract solverBuildId formulaFingerprint
      manifestDigest replayEvidence reconstructionEvidence exitCodeContract
      auditTrail :=
  fun buildProof fingerprintProof digestProof replayProof reconstructionProof
      exitProof auditProof =>
    ay_vrbp_conj_intro solverBuildId
      (ay_vrbp_conj formulaFingerprint
        (ay_vrbp_conj manifestDigest
          (ay_vrbp_conj replayEvidence
            (ay_vrbp_conj reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail)))))
      buildProof
      (ay_vrbp_conj_intro formulaFingerprint
        (ay_vrbp_conj manifestDigest
          (ay_vrbp_conj replayEvidence
            (ay_vrbp_conj reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail))))
        fingerprintProof
        (ay_vrbp_conj_intro manifestDigest
          (ay_vrbp_conj replayEvidence
            (ay_vrbp_conj reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail)))
          digestProof
          (ay_vrbp_conj_intro replayEvidence
            (ay_vrbp_conj reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail))
            replayProof
            (ay_vrbp_conj_intro reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail)
              reconstructionProof
              (ay_vrbp_conj_intro exitCodeContract auditTrail exitProof
                auditProof)))))

theorem ay_vrbp_portability_contract_build
    (solverBuildId formulaFingerprint manifestDigest replayEvidence
      reconstructionEvidence exitCodeContract auditTrail : Prop) :
    ay_vrbp_portability_contract solverBuildId formulaFingerprint
      manifestDigest replayEvidence reconstructionEvidence exitCodeContract
      auditTrail ->
    solverBuildId :=
  fun contract =>
    ay_vrbp_conj_left solverBuildId
      (ay_vrbp_conj formulaFingerprint
        (ay_vrbp_conj manifestDigest
          (ay_vrbp_conj replayEvidence
            (ay_vrbp_conj reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail)))))
      contract

theorem ay_vrbp_portability_contract_fingerprint
    (solverBuildId formulaFingerprint manifestDigest replayEvidence
      reconstructionEvidence exitCodeContract auditTrail : Prop) :
    ay_vrbp_portability_contract solverBuildId formulaFingerprint
      manifestDigest replayEvidence reconstructionEvidence exitCodeContract
      auditTrail ->
    formulaFingerprint :=
  fun contract =>
    ay_vrbp_conj_right solverBuildId
      (ay_vrbp_conj formulaFingerprint
        (ay_vrbp_conj manifestDigest
          (ay_vrbp_conj replayEvidence
            (ay_vrbp_conj reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail)))))
      contract formulaFingerprint
      (fun fingerprintProof _tail => fingerprintProof)

theorem ay_vrbp_portability_contract_digest
    (solverBuildId formulaFingerprint manifestDigest replayEvidence
      reconstructionEvidence exitCodeContract auditTrail : Prop) :
    ay_vrbp_portability_contract solverBuildId formulaFingerprint
      manifestDigest replayEvidence reconstructionEvidence exitCodeContract
      auditTrail ->
    manifestDigest :=
  fun contract =>
    ay_vrbp_conj_right solverBuildId
      (ay_vrbp_conj formulaFingerprint
        (ay_vrbp_conj manifestDigest
          (ay_vrbp_conj replayEvidence
            (ay_vrbp_conj reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail)))))
      contract manifestDigest
      (fun _fingerprintProof tail =>
        tail manifestDigest (fun digestProof _tail2 => digestProof))

theorem ay_vrbp_portability_contract_replay
    (solverBuildId formulaFingerprint manifestDigest replayEvidence
      reconstructionEvidence exitCodeContract auditTrail : Prop) :
    ay_vrbp_portability_contract solverBuildId formulaFingerprint
      manifestDigest replayEvidence reconstructionEvidence exitCodeContract
      auditTrail ->
    replayEvidence :=
  fun contract =>
    ay_vrbp_conj_right solverBuildId
      (ay_vrbp_conj formulaFingerprint
        (ay_vrbp_conj manifestDigest
          (ay_vrbp_conj replayEvidence
            (ay_vrbp_conj reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail)))))
      contract replayEvidence
      (fun _fingerprintProof tail =>
        tail replayEvidence
          (fun _digestProof tail2 =>
            tail2 replayEvidence (fun replayProof _tail3 => replayProof)))

theorem ay_vrbp_portability_contract_reconstruction
    (solverBuildId formulaFingerprint manifestDigest replayEvidence
      reconstructionEvidence exitCodeContract auditTrail : Prop) :
    ay_vrbp_portability_contract solverBuildId formulaFingerprint
      manifestDigest replayEvidence reconstructionEvidence exitCodeContract
      auditTrail ->
    reconstructionEvidence :=
  fun contract =>
    ay_vrbp_conj_right solverBuildId
      (ay_vrbp_conj formulaFingerprint
        (ay_vrbp_conj manifestDigest
          (ay_vrbp_conj replayEvidence
            (ay_vrbp_conj reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail)))))
      contract reconstructionEvidence
      (fun _fingerprintProof tail =>
        tail reconstructionEvidence
          (fun _digestProof tail2 =>
            tail2 reconstructionEvidence
              (fun _replayProof tail3 =>
                tail3 reconstructionEvidence
                  (fun reconstructionProof _tail4 =>
                    reconstructionProof))))

theorem ay_vrbp_portability_contract_exit
    (solverBuildId formulaFingerprint manifestDigest replayEvidence
      reconstructionEvidence exitCodeContract auditTrail : Prop) :
    ay_vrbp_portability_contract solverBuildId formulaFingerprint
      manifestDigest replayEvidence reconstructionEvidence exitCodeContract
      auditTrail ->
    exitCodeContract :=
  fun contract =>
    ay_vrbp_conj_right solverBuildId
      (ay_vrbp_conj formulaFingerprint
        (ay_vrbp_conj manifestDigest
          (ay_vrbp_conj replayEvidence
            (ay_vrbp_conj reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail)))))
      contract exitCodeContract
      (fun _fingerprintProof tail =>
        tail exitCodeContract
          (fun _digestProof tail2 =>
            tail2 exitCodeContract
              (fun _replayProof tail3 =>
                tail3 exitCodeContract
                  (fun _reconstructionProof tail4 =>
                    tail4 exitCodeContract
                      (fun exitProof _auditProof => exitProof)))))

theorem ay_vrbp_portability_contract_audit
    (solverBuildId formulaFingerprint manifestDigest replayEvidence
      reconstructionEvidence exitCodeContract auditTrail : Prop) :
    ay_vrbp_portability_contract solverBuildId formulaFingerprint
      manifestDigest replayEvidence reconstructionEvidence exitCodeContract
      auditTrail ->
    auditTrail :=
  fun contract =>
    ay_vrbp_conj_right solverBuildId
      (ay_vrbp_conj formulaFingerprint
        (ay_vrbp_conj manifestDigest
          (ay_vrbp_conj replayEvidence
            (ay_vrbp_conj reconstructionEvidence
              (ay_vrbp_conj exitCodeContract auditTrail)))))
      contract auditTrail
      (fun _fingerprintProof tail =>
        tail auditTrail
          (fun _digestProof tail2 =>
            tail2 auditTrail
              (fun _replayProof tail3 =>
                tail3 auditTrail
                  (fun _reconstructionProof tail4 =>
                    tail4 auditTrail
                      (fun _exitProof auditProof => auditProof)))))

theorem ay_vrbp_sat_bundle_intro
    (portabilityContract modelEvidence originalModel : Prop) :
    portabilityContract -> modelEvidence -> originalModel ->
    ay_vrbp_sat_bundle portabilityContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vrbp_conj_intro portabilityContract
      (ay_vrbp_conj modelEvidence originalModel)
      contractProof
      (ay_vrbp_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vrbp_sat_bundle_contract
    (portabilityContract modelEvidence originalModel : Prop) :
    ay_vrbp_sat_bundle portabilityContract modelEvidence originalModel ->
    portabilityContract :=
  fun bundle =>
    ay_vrbp_conj_left portabilityContract
      (ay_vrbp_conj modelEvidence originalModel) bundle

theorem ay_vrbp_sat_bundle_original_model
    (portabilityContract modelEvidence originalModel : Prop) :
    ay_vrbp_sat_bundle portabilityContract modelEvidence originalModel ->
    originalModel :=
  fun bundle =>
    ay_vrbp_conj_right portabilityContract
      (ay_vrbp_conj modelEvidence originalModel)
      bundle originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vrbp_unsat_bundle_intro
    (portabilityContract proofEvidence originalEmptyClause : Prop) :
    portabilityContract -> proofEvidence -> originalEmptyClause ->
    ay_vrbp_unsat_bundle portabilityContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vrbp_conj_intro portabilityContract
      (ay_vrbp_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vrbp_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vrbp_unsat_bundle_contract
    (portabilityContract proofEvidence originalEmptyClause : Prop) :
    ay_vrbp_unsat_bundle portabilityContract proofEvidence
      originalEmptyClause ->
    portabilityContract :=
  fun bundle =>
    ay_vrbp_conj_left portabilityContract
      (ay_vrbp_conj proofEvidence originalEmptyClause) bundle

theorem ay_vrbp_unsat_bundle_original_empty_clause
    (portabilityContract proofEvidence originalEmptyClause : Prop) :
    ay_vrbp_unsat_bundle portabilityContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun bundle =>
    ay_vrbp_conj_right portabilityContract
      (ay_vrbp_conj proofEvidence originalEmptyClause)
      bundle originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vrbp_no_claim_bundle_intro
    (portabilityContract diagnostic noSemanticClaim : Prop) :
    portabilityContract -> diagnostic -> noSemanticClaim ->
    ay_vrbp_no_claim_bundle portabilityContract diagnostic
      noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_vrbp_conj_intro portabilityContract
      (ay_vrbp_conj diagnostic noSemanticClaim)
      contractProof
      (ay_vrbp_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vrbp_no_claim_bundle_no_semantic_claim
    (portabilityContract diagnostic noSemanticClaim : Prop) :
    ay_vrbp_no_claim_bundle portabilityContract diagnostic
      noSemanticClaim ->
    noSemanticClaim :=
  fun bundle =>
    ay_vrbp_conj_right portabilityContract
      (ay_vrbp_conj diagnostic noSemanticClaim)
      bundle noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vrbp_ported_validation_intro
    (portabilityContract checkerReplay publicEvidence : Prop) :
    portabilityContract -> checkerReplay -> publicEvidence ->
    ay_vrbp_ported_validation portabilityContract checkerReplay
      publicEvidence :=
  fun contractProof replayProof publicProof =>
    ay_vrbp_conj_intro portabilityContract
      (ay_vrbp_conj checkerReplay publicEvidence)
      contractProof
      (ay_vrbp_conj_intro checkerReplay publicEvidence replayProof
        publicProof)

theorem ay_vrbp_ported_validation_public_evidence
    (portabilityContract checkerReplay publicEvidence : Prop) :
    ay_vrbp_ported_validation portabilityContract checkerReplay
      publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vrbp_conj_right portabilityContract
      (ay_vrbp_conj checkerReplay publicEvidence)
      validation publicEvidence
      (fun _replayProof publicProof => publicProof)

theorem ay_vrbp_accepted_sat_bundle_validates_same_result
    (portabilityContract modelEvidence originalModel unsatFact noClaimFact :
      Prop) :
    ay_vrbp_sat_bundle portabilityContract modelEvidence originalModel ->
    ay_vrbp_public_result originalModel unsatFact noClaimFact :=
  fun bundle =>
    ay_vrbp_disj_left originalModel
      (ay_vrbp_disj unsatFact noClaimFact)
      (ay_vrbp_sat_bundle_original_model portabilityContract modelEvidence
        originalModel bundle)

theorem ay_vrbp_accepted_unsat_bundle_validates_same_result
    (satFact portabilityContract proofEvidence originalEmptyClause
      noClaimFact : Prop) :
    ay_vrbp_unsat_bundle portabilityContract proofEvidence
      originalEmptyClause ->
    ay_vrbp_public_result satFact originalEmptyClause noClaimFact :=
  fun bundle =>
    ay_vrbp_disj_right satFact
      (ay_vrbp_disj originalEmptyClause noClaimFact)
      (ay_vrbp_disj_left originalEmptyClause noClaimFact
        (ay_vrbp_unsat_bundle_original_empty_clause portabilityContract
          proofEvidence originalEmptyClause bundle))

theorem ay_vrbp_accepted_no_claim_bundle_validates_same_result
    (satFact unsatFact portabilityContract diagnostic noSemanticClaim : Prop) :
    ay_vrbp_no_claim_bundle portabilityContract diagnostic noSemanticClaim ->
    ay_vrbp_public_result satFact unsatFact noSemanticClaim :=
  fun bundle =>
    ay_vrbp_disj_right satFact
      (ay_vrbp_disj unsatFact noSemanticClaim)
      (ay_vrbp_disj_right unsatFact noSemanticClaim
        (ay_vrbp_no_claim_bundle_no_semantic_claim portabilityContract
          diagnostic noSemanticClaim bundle))

theorem ay_vrbp_sat_bundle_supports_ported_validation
    (portabilityContract modelEvidence originalModel checkerReplay : Prop) :
    ay_vrbp_sat_bundle portabilityContract modelEvidence originalModel ->
    checkerReplay ->
    ay_vrbp_ported_validation portabilityContract checkerReplay
      originalModel :=
  fun bundle replayProof =>
    ay_vrbp_ported_validation_intro portabilityContract checkerReplay
      originalModel
      (ay_vrbp_sat_bundle_contract portabilityContract modelEvidence
        originalModel bundle)
      replayProof
      (ay_vrbp_sat_bundle_original_model portabilityContract modelEvidence
        originalModel bundle)

theorem ay_vrbp_unsat_bundle_supports_ported_validation
    (portabilityContract proofEvidence originalEmptyClause checkerReplay :
      Prop) :
    ay_vrbp_unsat_bundle portabilityContract proofEvidence
      originalEmptyClause ->
    checkerReplay ->
    ay_vrbp_ported_validation portabilityContract checkerReplay
      originalEmptyClause :=
  fun bundle replayProof =>
    ay_vrbp_ported_validation_intro portabilityContract checkerReplay
      originalEmptyClause
      (ay_vrbp_unsat_bundle_contract portabilityContract proofEvidence
        originalEmptyClause bundle)
      replayProof
      (ay_vrbp_unsat_bundle_original_empty_clause portabilityContract
        proofEvidence originalEmptyClause bundle)

theorem ay_vrbp_blocked_validation_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vrbp_blocked_validation satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vrbp_conj_intro reason
      (ay_vrbp_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vrbp_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vrbp_blocked_validation_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vrbp_blocked_validation satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vrbp_conj_right reason
      (ay_vrbp_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vrbp_blocked_validation_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vrbp_blocked_validation satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vrbp_conj_right reason
      (ay_vrbp_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vrbp_recompute_intro
    (reason auditTrail fallbackPath : Prop) :
    reason -> auditTrail -> fallbackPath ->
    ay_vrbp_recompute reason auditTrail fallbackPath :=
  fun reasonProof auditProof fallbackProof =>
    ay_vrbp_conj_intro reason
      (ay_vrbp_conj auditTrail fallbackPath)
      reasonProof
      (ay_vrbp_conj_intro auditTrail fallbackPath auditProof fallbackProof)

theorem ay_vrbp_portability_failure_intro
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrbp_blocked_validation satFact unsatFact reason ->
    ay_vrbp_recompute reason auditTrail fallbackPath ->
    ay_vrbp_portability_failure satFact unsatFact reason auditTrail
      fallbackPath :=
  fun blocked recompute =>
    ay_vrbp_conj_intro
      (ay_vrbp_blocked_validation satFact unsatFact reason)
      (ay_vrbp_recompute reason auditTrail fallbackPath)
      blocked recompute

theorem ay_vrbp_portability_failure_blocks_sat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrbp_portability_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vrbp_blocked_validation_no_sat satFact unsatFact reason
      (ay_vrbp_conj_left
        (ay_vrbp_blocked_validation satFact unsatFact reason)
        (ay_vrbp_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vrbp_portability_failure_blocks_unsat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrbp_portability_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vrbp_blocked_validation_no_unsat satFact unsatFact reason
      (ay_vrbp_conj_left
        (ay_vrbp_blocked_validation satFact unsatFact reason)
        (ay_vrbp_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vrbp_portability_failure_recompute
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrbp_portability_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    ay_vrbp_recompute reason auditTrail fallbackPath :=
  fun failure =>
    ay_vrbp_conj_right
      (ay_vrbp_blocked_validation satFact unsatFact reason)
      (ay_vrbp_recompute reason auditTrail fallbackPath)
      failure

theorem ay_vrbp_build_drift_forces_no_claim
    (satFact unsatFact buildDrift auditTrail fallbackPath : Prop) :
    buildDrift -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrbp_portability_failure satFact unsatFact buildDrift auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrbp_portability_failure_intro satFact unsatFact buildDrift
      auditTrail fallbackPath
      (ay_vrbp_blocked_validation_intro satFact unsatFact buildDrift
        reasonProof blockSat blockUnsat)
      (ay_vrbp_recompute_intro buildDrift auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrbp_fingerprint_drift_forces_no_claim
    (satFact unsatFact fingerprintDrift auditTrail fallbackPath : Prop) :
    fingerprintDrift -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrbp_portability_failure satFact unsatFact fingerprintDrift
      auditTrail fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrbp_portability_failure_intro satFact unsatFact fingerprintDrift
      auditTrail fallbackPath
      (ay_vrbp_blocked_validation_intro satFact unsatFact fingerprintDrift
        reasonProof blockSat blockUnsat)
      (ay_vrbp_recompute_intro fingerprintDrift auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrbp_missing_replay_evidence_forces_no_claim
    (satFact unsatFact missingReplay auditTrail fallbackPath : Prop) :
    missingReplay -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrbp_portability_failure satFact unsatFact missingReplay auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrbp_portability_failure_intro satFact unsatFact missingReplay
      auditTrail fallbackPath
      (ay_vrbp_blocked_validation_intro satFact unsatFact missingReplay
        reasonProof blockSat blockUnsat)
      (ay_vrbp_recompute_intro missingReplay auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrbp_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch auditTrail fallbackPath : Prop) :
    digestMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrbp_portability_failure satFact unsatFact digestMismatch auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrbp_portability_failure_intro satFact unsatFact digestMismatch
      auditTrail fallbackPath
      (ay_vrbp_blocked_validation_intro satFact unsatFact digestMismatch
        reasonProof blockSat blockUnsat)
      (ay_vrbp_recompute_intro digestMismatch auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrbp_audit_contradiction_forces_no_claim
    (satFact unsatFact auditContradiction auditTrail fallbackPath : Prop) :
    auditContradiction -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrbp_portability_failure satFact unsatFact auditContradiction
      auditTrail fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrbp_portability_failure_intro satFact unsatFact auditContradiction
      auditTrail fallbackPath
      (ay_vrbp_blocked_validation_intro satFact unsatFact
        auditContradiction reasonProof blockSat blockUnsat)
      (ay_vrbp_recompute_intro auditContradiction auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrbp_failure_cannot_validate_sat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrbp_portability_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    satFact -> False :=
  ay_vrbp_portability_failure_blocks_sat satFact unsatFact reason auditTrail
    fallbackPath

theorem ay_vrbp_failure_cannot_validate_unsat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrbp_portability_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    unsatFact -> False :=
  ay_vrbp_portability_failure_blocks_unsat satFact unsatFact reason
    auditTrail fallbackPath
