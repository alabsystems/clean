-- SAT-COMP validator checker-version pinning core.
--
-- Public validation may use a checker only when checker version, replay
-- kernel, solver build identity, artifact digest, original input fingerprint,
-- transcript schema, exit-code mapping, and audit fallback agree.

def ay_vcvp_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vcvp_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vcvp_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vcvp_disj satFact (ay_vcvp_disj unsatFact noClaimFact)

def ay_vcvp_pin_contract
    (checkerVersion replayKernel solverBuildIdentity artifactDigest
      originalFingerprint transcriptSchema exitCodeMapping auditFallback :
      Prop) : Prop :=
  ay_vcvp_conj checkerVersion
    (ay_vcvp_conj replayKernel
      (ay_vcvp_conj solverBuildIdentity
        (ay_vcvp_conj artifactDigest
          (ay_vcvp_conj originalFingerprint
            (ay_vcvp_conj transcriptSchema
              (ay_vcvp_conj exitCodeMapping auditFallback))))))

def ay_vcvp_sat_validation
    (pinContract modelEvidence originalModel : Prop) : Prop :=
  ay_vcvp_conj pinContract
    (ay_vcvp_conj modelEvidence originalModel)

def ay_vcvp_unsat_validation
    (pinContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vcvp_conj pinContract
    (ay_vcvp_conj proofEvidence originalEmptyClause)

def ay_vcvp_no_claim_validation
    (pinContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vcvp_conj pinContract
    (ay_vcvp_conj diagnostic noSemanticClaim)

def ay_vcvp_checker_validation
    (pinContract checkerAccepted publicEvidence : Prop) : Prop :=
  ay_vcvp_conj pinContract
    (ay_vcvp_conj checkerAccepted publicEvidence)

def ay_vcvp_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vcvp_conj reason
    (ay_vcvp_conj (satFact -> False) (unsatFact -> False))

def ay_vcvp_recompute
    (reason auditFallback fallbackPath : Prop) : Prop :=
  ay_vcvp_conj reason (ay_vcvp_conj auditFallback fallbackPath)

def ay_vcvp_pin_failure
    (satFact unsatFact reason auditFallback fallbackPath : Prop) : Prop :=
  ay_vcvp_conj
    (ay_vcvp_blocked_publication satFact unsatFact reason)
    (ay_vcvp_recompute reason auditFallback fallbackPath)

theorem ay_vcvp_conj_intro (left right : Prop) :
    left -> right -> ay_vcvp_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcvp_conj_left (left right : Prop) :
    ay_vcvp_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcvp_conj_right (left right : Prop) :
    ay_vcvp_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcvp_disj_left (left right : Prop) :
    left -> ay_vcvp_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vcvp_disj_right (left right : Prop) :
    right -> ay_vcvp_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcvp_pin_contract_intro
    (checkerVersion replayKernel solverBuildIdentity artifactDigest
      originalFingerprint transcriptSchema exitCodeMapping auditFallback :
      Prop) :
    checkerVersion -> replayKernel -> solverBuildIdentity ->
    artifactDigest -> originalFingerprint -> transcriptSchema ->
    exitCodeMapping -> auditFallback ->
    ay_vcvp_pin_contract checkerVersion replayKernel solverBuildIdentity
      artifactDigest originalFingerprint transcriptSchema exitCodeMapping
      auditFallback :=
  fun versionProof kernelProof buildProof digestProof fingerprintProof
      schemaProof mappingProof fallbackProof =>
    ay_vcvp_conj_intro checkerVersion
      (ay_vcvp_conj replayKernel
        (ay_vcvp_conj solverBuildIdentity
          (ay_vcvp_conj artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback))))))
      versionProof
      (ay_vcvp_conj_intro replayKernel
        (ay_vcvp_conj solverBuildIdentity
          (ay_vcvp_conj artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback)))))
        kernelProof
        (ay_vcvp_conj_intro solverBuildIdentity
          (ay_vcvp_conj artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback))))
          buildProof
          (ay_vcvp_conj_intro artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback)))
            digestProof
            (ay_vcvp_conj_intro originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback))
              fingerprintProof
              (ay_vcvp_conj_intro transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback)
                schemaProof
                (ay_vcvp_conj_intro exitCodeMapping auditFallback
                  mappingProof fallbackProof))))))

theorem ay_vcvp_pin_contract_version
    (checkerVersion replayKernel solverBuildIdentity artifactDigest
      originalFingerprint transcriptSchema exitCodeMapping auditFallback :
      Prop) :
    ay_vcvp_pin_contract checkerVersion replayKernel solverBuildIdentity
      artifactDigest originalFingerprint transcriptSchema exitCodeMapping
      auditFallback ->
    checkerVersion :=
  fun contract =>
    ay_vcvp_conj_left checkerVersion
      (ay_vcvp_conj replayKernel
        (ay_vcvp_conj solverBuildIdentity
          (ay_vcvp_conj artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback))))))
      contract

theorem ay_vcvp_pin_contract_kernel
    (checkerVersion replayKernel solverBuildIdentity artifactDigest
      originalFingerprint transcriptSchema exitCodeMapping auditFallback :
      Prop) :
    ay_vcvp_pin_contract checkerVersion replayKernel solverBuildIdentity
      artifactDigest originalFingerprint transcriptSchema exitCodeMapping
      auditFallback ->
    replayKernel :=
  fun contract =>
    ay_vcvp_conj_right checkerVersion
      (ay_vcvp_conj replayKernel
        (ay_vcvp_conj solverBuildIdentity
          (ay_vcvp_conj artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback))))))
      contract replayKernel
      (fun kernelProof _tail => kernelProof)

theorem ay_vcvp_pin_contract_build
    (checkerVersion replayKernel solverBuildIdentity artifactDigest
      originalFingerprint transcriptSchema exitCodeMapping auditFallback :
      Prop) :
    ay_vcvp_pin_contract checkerVersion replayKernel solverBuildIdentity
      artifactDigest originalFingerprint transcriptSchema exitCodeMapping
      auditFallback ->
    solverBuildIdentity :=
  fun contract =>
    ay_vcvp_conj_right checkerVersion
      (ay_vcvp_conj replayKernel
        (ay_vcvp_conj solverBuildIdentity
          (ay_vcvp_conj artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback))))))
      contract solverBuildIdentity
      (fun _kernelProof tail =>
        tail solverBuildIdentity (fun buildProof _tail2 => buildProof))

theorem ay_vcvp_pin_contract_digest
    (checkerVersion replayKernel solverBuildIdentity artifactDigest
      originalFingerprint transcriptSchema exitCodeMapping auditFallback :
      Prop) :
    ay_vcvp_pin_contract checkerVersion replayKernel solverBuildIdentity
      artifactDigest originalFingerprint transcriptSchema exitCodeMapping
      auditFallback ->
    artifactDigest :=
  fun contract =>
    ay_vcvp_conj_right checkerVersion
      (ay_vcvp_conj replayKernel
        (ay_vcvp_conj solverBuildIdentity
          (ay_vcvp_conj artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback))))))
      contract artifactDigest
      (fun _kernelProof tail =>
        tail artifactDigest
          (fun _buildProof tail2 =>
            tail2 artifactDigest (fun digestProof _tail3 => digestProof)))

theorem ay_vcvp_pin_contract_fingerprint
    (checkerVersion replayKernel solverBuildIdentity artifactDigest
      originalFingerprint transcriptSchema exitCodeMapping auditFallback :
      Prop) :
    ay_vcvp_pin_contract checkerVersion replayKernel solverBuildIdentity
      artifactDigest originalFingerprint transcriptSchema exitCodeMapping
      auditFallback ->
    originalFingerprint :=
  fun contract =>
    ay_vcvp_conj_right checkerVersion
      (ay_vcvp_conj replayKernel
        (ay_vcvp_conj solverBuildIdentity
          (ay_vcvp_conj artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback))))))
      contract originalFingerprint
      (fun _kernelProof tail =>
        tail originalFingerprint
          (fun _buildProof tail2 =>
            tail2 originalFingerprint
              (fun _digestProof tail3 =>
                tail3 originalFingerprint
                  (fun fingerprintProof _tail4 => fingerprintProof))))

theorem ay_vcvp_pin_contract_schema
    (checkerVersion replayKernel solverBuildIdentity artifactDigest
      originalFingerprint transcriptSchema exitCodeMapping auditFallback :
      Prop) :
    ay_vcvp_pin_contract checkerVersion replayKernel solverBuildIdentity
      artifactDigest originalFingerprint transcriptSchema exitCodeMapping
      auditFallback ->
    transcriptSchema :=
  fun contract =>
    ay_vcvp_conj_right checkerVersion
      (ay_vcvp_conj replayKernel
        (ay_vcvp_conj solverBuildIdentity
          (ay_vcvp_conj artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback))))))
      contract transcriptSchema
      (fun _kernelProof tail =>
        tail transcriptSchema
          (fun _buildProof tail2 =>
            tail2 transcriptSchema
              (fun _digestProof tail3 =>
                tail3 transcriptSchema
                  (fun _fingerprintProof tail4 =>
                    tail4 transcriptSchema
                      (fun schemaProof _tail5 => schemaProof)))))

theorem ay_vcvp_pin_contract_mapping
    (checkerVersion replayKernel solverBuildIdentity artifactDigest
      originalFingerprint transcriptSchema exitCodeMapping auditFallback :
      Prop) :
    ay_vcvp_pin_contract checkerVersion replayKernel solverBuildIdentity
      artifactDigest originalFingerprint transcriptSchema exitCodeMapping
      auditFallback ->
    exitCodeMapping :=
  fun contract =>
    ay_vcvp_conj_right checkerVersion
      (ay_vcvp_conj replayKernel
        (ay_vcvp_conj solverBuildIdentity
          (ay_vcvp_conj artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback))))))
      contract exitCodeMapping
      (fun _kernelProof tail =>
        tail exitCodeMapping
          (fun _buildProof tail2 =>
            tail2 exitCodeMapping
              (fun _digestProof tail3 =>
                tail3 exitCodeMapping
                  (fun _fingerprintProof tail4 =>
                    tail4 exitCodeMapping
                      (fun _schemaProof tail5 =>
                        tail5 exitCodeMapping
                          (fun mappingProof _fallbackProof =>
                            mappingProof))))))

theorem ay_vcvp_pin_contract_fallback
    (checkerVersion replayKernel solverBuildIdentity artifactDigest
      originalFingerprint transcriptSchema exitCodeMapping auditFallback :
      Prop) :
    ay_vcvp_pin_contract checkerVersion replayKernel solverBuildIdentity
      artifactDigest originalFingerprint transcriptSchema exitCodeMapping
      auditFallback ->
    auditFallback :=
  fun contract =>
    ay_vcvp_conj_right checkerVersion
      (ay_vcvp_conj replayKernel
        (ay_vcvp_conj solverBuildIdentity
          (ay_vcvp_conj artifactDigest
            (ay_vcvp_conj originalFingerprint
              (ay_vcvp_conj transcriptSchema
                (ay_vcvp_conj exitCodeMapping auditFallback))))))
      contract auditFallback
      (fun _kernelProof tail =>
        tail auditFallback
          (fun _buildProof tail2 =>
            tail2 auditFallback
              (fun _digestProof tail3 =>
                tail3 auditFallback
                  (fun _fingerprintProof tail4 =>
                    tail4 auditFallback
                      (fun _schemaProof tail5 =>
                        tail5 auditFallback
                          (fun _mappingProof fallbackProof =>
                            fallbackProof))))))

theorem ay_vcvp_sat_validation_intro
    (pinContract modelEvidence originalModel : Prop) :
    pinContract -> modelEvidence -> originalModel ->
    ay_vcvp_sat_validation pinContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vcvp_conj_intro pinContract
      (ay_vcvp_conj modelEvidence originalModel)
      contractProof
      (ay_vcvp_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vcvp_sat_validation_contract
    (pinContract modelEvidence originalModel : Prop) :
    ay_vcvp_sat_validation pinContract modelEvidence originalModel ->
    pinContract :=
  fun validation =>
    ay_vcvp_conj_left pinContract
      (ay_vcvp_conj modelEvidence originalModel) validation

theorem ay_vcvp_sat_validation_original_model
    (pinContract modelEvidence originalModel : Prop) :
    ay_vcvp_sat_validation pinContract modelEvidence originalModel ->
    originalModel :=
  fun validation =>
    ay_vcvp_conj_right pinContract
      (ay_vcvp_conj modelEvidence originalModel)
      validation originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vcvp_unsat_validation_intro
    (pinContract proofEvidence originalEmptyClause : Prop) :
    pinContract -> proofEvidence -> originalEmptyClause ->
    ay_vcvp_unsat_validation pinContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vcvp_conj_intro pinContract
      (ay_vcvp_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vcvp_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vcvp_unsat_validation_contract
    (pinContract proofEvidence originalEmptyClause : Prop) :
    ay_vcvp_unsat_validation pinContract proofEvidence
      originalEmptyClause ->
    pinContract :=
  fun validation =>
    ay_vcvp_conj_left pinContract
      (ay_vcvp_conj proofEvidence originalEmptyClause) validation

theorem ay_vcvp_unsat_validation_original_empty_clause
    (pinContract proofEvidence originalEmptyClause : Prop) :
    ay_vcvp_unsat_validation pinContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun validation =>
    ay_vcvp_conj_right pinContract
      (ay_vcvp_conj proofEvidence originalEmptyClause)
      validation originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vcvp_no_claim_validation_intro
    (pinContract diagnostic noSemanticClaim : Prop) :
    pinContract -> diagnostic -> noSemanticClaim ->
    ay_vcvp_no_claim_validation pinContract diagnostic noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_vcvp_conj_intro pinContract
      (ay_vcvp_conj diagnostic noSemanticClaim)
      contractProof
      (ay_vcvp_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vcvp_no_claim_validation_no_semantic_claim
    (pinContract diagnostic noSemanticClaim : Prop) :
    ay_vcvp_no_claim_validation pinContract diagnostic noSemanticClaim ->
    noSemanticClaim :=
  fun validation =>
    ay_vcvp_conj_right pinContract
      (ay_vcvp_conj diagnostic noSemanticClaim)
      validation noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vcvp_checker_validation_intro
    (pinContract checkerAccepted publicEvidence : Prop) :
    pinContract -> checkerAccepted -> publicEvidence ->
    ay_vcvp_checker_validation pinContract checkerAccepted publicEvidence :=
  fun contractProof checkerProof publicProof =>
    ay_vcvp_conj_intro pinContract
      (ay_vcvp_conj checkerAccepted publicEvidence)
      contractProof
      (ay_vcvp_conj_intro checkerAccepted publicEvidence checkerProof
        publicProof)

theorem ay_vcvp_checker_validation_public_evidence
    (pinContract checkerAccepted publicEvidence : Prop) :
    ay_vcvp_checker_validation pinContract checkerAccepted publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vcvp_conj_right pinContract
      (ay_vcvp_conj checkerAccepted publicEvidence)
      validation publicEvidence
      (fun _checkerProof publicProof => publicProof)

theorem ay_vcvp_accepted_sat_preserves_result
    (pinContract modelEvidence originalModel unsatFact noClaimFact : Prop) :
    ay_vcvp_sat_validation pinContract modelEvidence originalModel ->
    ay_vcvp_public_result originalModel unsatFact noClaimFact :=
  fun validation =>
    ay_vcvp_disj_left originalModel
      (ay_vcvp_disj unsatFact noClaimFact)
      (ay_vcvp_sat_validation_original_model pinContract modelEvidence
        originalModel validation)

theorem ay_vcvp_accepted_unsat_preserves_result
    (satFact pinContract proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_vcvp_unsat_validation pinContract proofEvidence
      originalEmptyClause ->
    ay_vcvp_public_result satFact originalEmptyClause noClaimFact :=
  fun validation =>
    ay_vcvp_disj_right satFact
      (ay_vcvp_disj originalEmptyClause noClaimFact)
      (ay_vcvp_disj_left originalEmptyClause noClaimFact
        (ay_vcvp_unsat_validation_original_empty_clause pinContract
          proofEvidence originalEmptyClause validation))

theorem ay_vcvp_accepted_no_claim_preserves_result
    (satFact unsatFact pinContract diagnostic noSemanticClaim : Prop) :
    ay_vcvp_no_claim_validation pinContract diagnostic noSemanticClaim ->
    ay_vcvp_public_result satFact unsatFact noSemanticClaim :=
  fun validation =>
    ay_vcvp_disj_right satFact
      (ay_vcvp_disj unsatFact noSemanticClaim)
      (ay_vcvp_disj_right unsatFact noSemanticClaim
        (ay_vcvp_no_claim_validation_no_semantic_claim pinContract
          diagnostic noSemanticClaim validation))

theorem ay_vcvp_sat_supports_checker_validation
    (pinContract modelEvidence originalModel checkerAccepted : Prop) :
    ay_vcvp_sat_validation pinContract modelEvidence originalModel ->
    checkerAccepted ->
    ay_vcvp_checker_validation pinContract checkerAccepted originalModel :=
  fun validation checkerProof =>
    ay_vcvp_checker_validation_intro pinContract checkerAccepted
      originalModel
      (ay_vcvp_sat_validation_contract pinContract modelEvidence
        originalModel validation)
      checkerProof
      (ay_vcvp_sat_validation_original_model pinContract modelEvidence
        originalModel validation)

theorem ay_vcvp_unsat_supports_checker_validation
    (pinContract proofEvidence originalEmptyClause checkerAccepted : Prop) :
    ay_vcvp_unsat_validation pinContract proofEvidence originalEmptyClause ->
    checkerAccepted ->
    ay_vcvp_checker_validation pinContract checkerAccepted
      originalEmptyClause :=
  fun validation checkerProof =>
    ay_vcvp_checker_validation_intro pinContract checkerAccepted
      originalEmptyClause
      (ay_vcvp_unsat_validation_contract pinContract proofEvidence
        originalEmptyClause validation)
      checkerProof
      (ay_vcvp_unsat_validation_original_empty_clause pinContract
        proofEvidence originalEmptyClause validation)

theorem ay_vcvp_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vcvp_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vcvp_conj_intro reason
      (ay_vcvp_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vcvp_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vcvp_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vcvp_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vcvp_conj_right reason
      (ay_vcvp_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vcvp_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vcvp_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vcvp_conj_right reason
      (ay_vcvp_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vcvp_recompute_intro
    (reason auditFallback fallbackPath : Prop) :
    reason -> auditFallback -> fallbackPath ->
    ay_vcvp_recompute reason auditFallback fallbackPath :=
  fun reasonProof auditProof pathProof =>
    ay_vcvp_conj_intro reason
      (ay_vcvp_conj auditFallback fallbackPath)
      reasonProof
      (ay_vcvp_conj_intro auditFallback fallbackPath auditProof pathProof)

theorem ay_vcvp_pin_failure_intro
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vcvp_blocked_publication satFact unsatFact reason ->
    ay_vcvp_recompute reason auditFallback fallbackPath ->
    ay_vcvp_pin_failure satFact unsatFact reason auditFallback
      fallbackPath :=
  fun blocked recompute =>
    ay_vcvp_conj_intro
      (ay_vcvp_blocked_publication satFact unsatFact reason)
      (ay_vcvp_recompute reason auditFallback fallbackPath)
      blocked recompute

theorem ay_vcvp_pin_failure_blocks_sat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vcvp_pin_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vcvp_blocked_publication_no_sat satFact unsatFact reason
      (ay_vcvp_conj_left
        (ay_vcvp_blocked_publication satFact unsatFact reason)
        (ay_vcvp_recompute reason auditFallback fallbackPath)
        failure)

theorem ay_vcvp_pin_failure_blocks_unsat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vcvp_pin_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vcvp_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vcvp_conj_left
        (ay_vcvp_blocked_publication satFact unsatFact reason)
        (ay_vcvp_recompute reason auditFallback fallbackPath)
        failure)

theorem ay_vcvp_pin_failure_recompute
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vcvp_pin_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    ay_vcvp_recompute reason auditFallback fallbackPath :=
  fun failure =>
    ay_vcvp_conj_right
      (ay_vcvp_blocked_publication satFact unsatFact reason)
      (ay_vcvp_recompute reason auditFallback fallbackPath)
      failure

theorem ay_vcvp_version_drift_forces_no_claim
    (satFact unsatFact versionDrift auditFallback fallbackPath : Prop) :
    versionDrift -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vcvp_pin_failure satFact unsatFact versionDrift auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vcvp_pin_failure_intro satFact unsatFact versionDrift auditFallback
      fallbackPath
      (ay_vcvp_blocked_publication_intro satFact unsatFact versionDrift
        reasonProof blockSat blockUnsat)
      (ay_vcvp_recompute_intro versionDrift auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vcvp_kernel_drift_forces_no_claim
    (satFact unsatFact kernelDrift auditFallback fallbackPath : Prop) :
    kernelDrift -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vcvp_pin_failure satFact unsatFact kernelDrift auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vcvp_pin_failure_intro satFact unsatFact kernelDrift auditFallback
      fallbackPath
      (ay_vcvp_blocked_publication_intro satFact unsatFact kernelDrift
        reasonProof blockSat blockUnsat)
      (ay_vcvp_recompute_intro kernelDrift auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vcvp_schema_mismatch_forces_no_claim
    (satFact unsatFact schemaMismatch auditFallback fallbackPath : Prop) :
    schemaMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vcvp_pin_failure satFact unsatFact schemaMismatch auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vcvp_pin_failure_intro satFact unsatFact schemaMismatch
      auditFallback fallbackPath
      (ay_vcvp_blocked_publication_intro satFact unsatFact schemaMismatch
        reasonProof blockSat blockUnsat)
      (ay_vcvp_recompute_intro schemaMismatch auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vcvp_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch auditFallback fallbackPath : Prop) :
    digestMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vcvp_pin_failure satFact unsatFact digestMismatch auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vcvp_pin_failure_intro satFact unsatFact digestMismatch auditFallback
      fallbackPath
      (ay_vcvp_blocked_publication_intro satFact unsatFact digestMismatch
        reasonProof blockSat blockUnsat)
      (ay_vcvp_recompute_intro digestMismatch auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vcvp_missing_mapping_forces_no_claim
    (satFact unsatFact missingMapping auditFallback fallbackPath : Prop) :
    missingMapping -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vcvp_pin_failure satFact unsatFact missingMapping auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vcvp_pin_failure_intro satFact unsatFact missingMapping auditFallback
      fallbackPath
      (ay_vcvp_blocked_publication_intro satFact unsatFact missingMapping
        reasonProof blockSat blockUnsat)
      (ay_vcvp_recompute_intro missingMapping auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vcvp_stale_build_forces_no_claim
    (satFact unsatFact staleBuild auditFallback fallbackPath : Prop) :
    staleBuild -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vcvp_pin_failure satFact unsatFact staleBuild auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vcvp_pin_failure_intro satFact unsatFact staleBuild auditFallback
      fallbackPath
      (ay_vcvp_blocked_publication_intro satFact unsatFact staleBuild
        reasonProof blockSat blockUnsat)
      (ay_vcvp_recompute_intro staleBuild auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vcvp_missing_fallback_forces_no_claim
    (satFact unsatFact missingFallback auditFallback fallbackPath : Prop) :
    missingFallback -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vcvp_pin_failure satFact unsatFact missingFallback auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vcvp_pin_failure_intro satFact unsatFact missingFallback
      auditFallback fallbackPath
      (ay_vcvp_blocked_publication_intro satFact unsatFact missingFallback
        reasonProof blockSat blockUnsat)
      (ay_vcvp_recompute_intro missingFallback auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vcvp_audit_contradiction_forces_no_claim
    (satFact unsatFact auditContradiction auditFallback fallbackPath : Prop) :
    auditContradiction -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vcvp_pin_failure satFact unsatFact auditContradiction auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vcvp_pin_failure_intro satFact unsatFact auditContradiction
      auditFallback fallbackPath
      (ay_vcvp_blocked_publication_intro satFact unsatFact
        auditContradiction reasonProof blockSat blockUnsat)
      (ay_vcvp_recompute_intro auditContradiction auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vcvp_failure_cannot_publish_sat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vcvp_pin_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    satFact -> False :=
  ay_vcvp_pin_failure_blocks_sat satFact unsatFact reason auditFallback
    fallbackPath

theorem ay_vcvp_failure_cannot_publish_unsat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vcvp_pin_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    unsatFact -> False :=
  ay_vcvp_pin_failure_blocks_unsat satFact unsatFact reason auditFallback
    fallbackPath
