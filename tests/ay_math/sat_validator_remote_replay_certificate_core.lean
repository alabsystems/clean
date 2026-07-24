-- SAT-COMP validator remote replay certificate core.
--
-- A remote replay artifact is trusted only when binary/build identity or a
-- documented replay-kernel identity, original input fingerprint, certificate
-- digest chain, transcript coverage, final checker decision, and retained
-- public evidence all agree.  Corruption or drift downgrades to no-claim and
-- recompute instead of publishing stale SAT/UNSAT results.

def ay_vrrc_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrrc_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vrrc_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vrrc_disj satFact (ay_vrrc_disj unsatFact noClaimFact)

def ay_vrrc_identity
    (exactBinaryBuild replayKernelIdentity : Prop) : Prop :=
  ay_vrrc_disj exactBinaryBuild replayKernelIdentity

def ay_vrrc_remote_contract
    (identity originalFingerprint certificateDigestChain transcriptCoverage
      finalCheckerDecision retainedPublicEvidence : Prop) : Prop :=
  ay_vrrc_conj identity
    (ay_vrrc_conj originalFingerprint
      (ay_vrrc_conj certificateDigestChain
        (ay_vrrc_conj transcriptCoverage
          (ay_vrrc_conj finalCheckerDecision retainedPublicEvidence))))

def ay_vrrc_sat_certificate
    (remoteContract modelEvidence originalModel : Prop) : Prop :=
  ay_vrrc_conj remoteContract
    (ay_vrrc_conj modelEvidence originalModel)

def ay_vrrc_unsat_certificate
    (remoteContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vrrc_conj remoteContract
    (ay_vrrc_conj proofEvidence originalEmptyClause)

def ay_vrrc_retained_validation
    (remoteContract replayedDecision publicEvidence : Prop) : Prop :=
  ay_vrrc_conj remoteContract
    (ay_vrrc_conj replayedDecision publicEvidence)

def ay_vrrc_no_claim
    (reason auditTrail diagnostic : Prop) : Prop :=
  ay_vrrc_conj reason (ay_vrrc_conj auditTrail diagnostic)

def ay_vrrc_recompute
    (reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vrrc_conj reason (ay_vrrc_conj auditTrail fallbackPath)

def ay_vrrc_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vrrc_conj reason
    (ay_vrrc_conj (satFact -> False) (unsatFact -> False))

def ay_vrrc_remote_failure
    (satFact unsatFact reason auditTrail fallbackPath : Prop) : Prop :=
  ay_vrrc_conj
    (ay_vrrc_blocked_publication satFact unsatFact reason)
    (ay_vrrc_recompute reason auditTrail fallbackPath)

theorem ay_vrrc_conj_intro (left right : Prop) :
    left -> right -> ay_vrrc_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrrc_conj_left (left right : Prop) :
    ay_vrrc_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrrc_conj_right (left right : Prop) :
    ay_vrrc_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrrc_disj_left (left right : Prop) :
    left -> ay_vrrc_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vrrc_disj_right (left right : Prop) :
    right -> ay_vrrc_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrrc_identity_exact_binary
    (exactBinaryBuild replayKernelIdentity : Prop) :
    exactBinaryBuild ->
    ay_vrrc_identity exactBinaryBuild replayKernelIdentity :=
  ay_vrrc_disj_left exactBinaryBuild replayKernelIdentity

theorem ay_vrrc_identity_replay_kernel
    (exactBinaryBuild replayKernelIdentity : Prop) :
    replayKernelIdentity ->
    ay_vrrc_identity exactBinaryBuild replayKernelIdentity :=
  ay_vrrc_disj_right exactBinaryBuild replayKernelIdentity

theorem ay_vrrc_remote_contract_intro
    (identity originalFingerprint certificateDigestChain transcriptCoverage
      finalCheckerDecision retainedPublicEvidence : Prop) :
    identity -> originalFingerprint -> certificateDigestChain ->
    transcriptCoverage -> finalCheckerDecision -> retainedPublicEvidence ->
    ay_vrrc_remote_contract identity originalFingerprint
      certificateDigestChain transcriptCoverage finalCheckerDecision
      retainedPublicEvidence :=
  fun identityProof fingerprintProof digestProof coverageProof decisionProof
      retainedProof =>
    ay_vrrc_conj_intro identity
      (ay_vrrc_conj originalFingerprint
        (ay_vrrc_conj certificateDigestChain
          (ay_vrrc_conj transcriptCoverage
            (ay_vrrc_conj finalCheckerDecision retainedPublicEvidence))))
      identityProof
      (ay_vrrc_conj_intro originalFingerprint
        (ay_vrrc_conj certificateDigestChain
          (ay_vrrc_conj transcriptCoverage
            (ay_vrrc_conj finalCheckerDecision retainedPublicEvidence)))
        fingerprintProof
        (ay_vrrc_conj_intro certificateDigestChain
          (ay_vrrc_conj transcriptCoverage
            (ay_vrrc_conj finalCheckerDecision retainedPublicEvidence))
          digestProof
          (ay_vrrc_conj_intro transcriptCoverage
            (ay_vrrc_conj finalCheckerDecision retainedPublicEvidence)
            coverageProof
            (ay_vrrc_conj_intro finalCheckerDecision retainedPublicEvidence
              decisionProof retainedProof))))

theorem ay_vrrc_remote_contract_identity
    (identity originalFingerprint certificateDigestChain transcriptCoverage
      finalCheckerDecision retainedPublicEvidence : Prop) :
    ay_vrrc_remote_contract identity originalFingerprint
      certificateDigestChain transcriptCoverage finalCheckerDecision
      retainedPublicEvidence ->
    identity :=
  fun contract =>
    ay_vrrc_conj_left identity
      (ay_vrrc_conj originalFingerprint
        (ay_vrrc_conj certificateDigestChain
          (ay_vrrc_conj transcriptCoverage
            (ay_vrrc_conj finalCheckerDecision retainedPublicEvidence))))
      contract

theorem ay_vrrc_remote_contract_fingerprint
    (identity originalFingerprint certificateDigestChain transcriptCoverage
      finalCheckerDecision retainedPublicEvidence : Prop) :
    ay_vrrc_remote_contract identity originalFingerprint
      certificateDigestChain transcriptCoverage finalCheckerDecision
      retainedPublicEvidence ->
    originalFingerprint :=
  fun contract =>
    ay_vrrc_conj_right identity
      (ay_vrrc_conj originalFingerprint
        (ay_vrrc_conj certificateDigestChain
          (ay_vrrc_conj transcriptCoverage
            (ay_vrrc_conj finalCheckerDecision retainedPublicEvidence))))
      contract originalFingerprint
      (fun fingerprintProof _tail => fingerprintProof)

theorem ay_vrrc_remote_contract_digest
    (identity originalFingerprint certificateDigestChain transcriptCoverage
      finalCheckerDecision retainedPublicEvidence : Prop) :
    ay_vrrc_remote_contract identity originalFingerprint
      certificateDigestChain transcriptCoverage finalCheckerDecision
      retainedPublicEvidence ->
    certificateDigestChain :=
  fun contract =>
    ay_vrrc_conj_right identity
      (ay_vrrc_conj originalFingerprint
        (ay_vrrc_conj certificateDigestChain
          (ay_vrrc_conj transcriptCoverage
            (ay_vrrc_conj finalCheckerDecision retainedPublicEvidence))))
      contract certificateDigestChain
      (fun _fingerprintProof tail =>
        tail certificateDigestChain
          (fun digestProof _tail2 => digestProof))

theorem ay_vrrc_remote_contract_transcript
    (identity originalFingerprint certificateDigestChain transcriptCoverage
      finalCheckerDecision retainedPublicEvidence : Prop) :
    ay_vrrc_remote_contract identity originalFingerprint
      certificateDigestChain transcriptCoverage finalCheckerDecision
      retainedPublicEvidence ->
    transcriptCoverage :=
  fun contract =>
    ay_vrrc_conj_right identity
      (ay_vrrc_conj originalFingerprint
        (ay_vrrc_conj certificateDigestChain
          (ay_vrrc_conj transcriptCoverage
            (ay_vrrc_conj finalCheckerDecision retainedPublicEvidence))))
      contract transcriptCoverage
      (fun _fingerprintProof tail =>
        tail transcriptCoverage
          (fun _digestProof tail2 =>
            tail2 transcriptCoverage
              (fun coverageProof _tail3 => coverageProof)))

theorem ay_vrrc_remote_contract_decision
    (identity originalFingerprint certificateDigestChain transcriptCoverage
      finalCheckerDecision retainedPublicEvidence : Prop) :
    ay_vrrc_remote_contract identity originalFingerprint
      certificateDigestChain transcriptCoverage finalCheckerDecision
      retainedPublicEvidence ->
    finalCheckerDecision :=
  fun contract =>
    ay_vrrc_conj_right identity
      (ay_vrrc_conj originalFingerprint
        (ay_vrrc_conj certificateDigestChain
          (ay_vrrc_conj transcriptCoverage
            (ay_vrrc_conj finalCheckerDecision retainedPublicEvidence))))
      contract finalCheckerDecision
      (fun _fingerprintProof tail =>
        tail finalCheckerDecision
          (fun _digestProof tail2 =>
            tail2 finalCheckerDecision
              (fun _coverageProof tail3 =>
                tail3 finalCheckerDecision
                  (fun decisionProof _retainedProof => decisionProof))))

theorem ay_vrrc_remote_contract_retained
    (identity originalFingerprint certificateDigestChain transcriptCoverage
      finalCheckerDecision retainedPublicEvidence : Prop) :
    ay_vrrc_remote_contract identity originalFingerprint
      certificateDigestChain transcriptCoverage finalCheckerDecision
      retainedPublicEvidence ->
    retainedPublicEvidence :=
  fun contract =>
    ay_vrrc_conj_right identity
      (ay_vrrc_conj originalFingerprint
        (ay_vrrc_conj certificateDigestChain
          (ay_vrrc_conj transcriptCoverage
            (ay_vrrc_conj finalCheckerDecision retainedPublicEvidence))))
      contract retainedPublicEvidence
      (fun _fingerprintProof tail =>
        tail retainedPublicEvidence
          (fun _digestProof tail2 =>
            tail2 retainedPublicEvidence
              (fun _coverageProof tail3 =>
                tail3 retainedPublicEvidence
                  (fun _decisionProof retainedProof => retainedProof))))

theorem ay_vrrc_sat_certificate_intro
    (remoteContract modelEvidence originalModel : Prop) :
    remoteContract -> modelEvidence -> originalModel ->
    ay_vrrc_sat_certificate remoteContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vrrc_conj_intro remoteContract
      (ay_vrrc_conj modelEvidence originalModel)
      contractProof
      (ay_vrrc_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vrrc_sat_certificate_contract
    (remoteContract modelEvidence originalModel : Prop) :
    ay_vrrc_sat_certificate remoteContract modelEvidence originalModel ->
    remoteContract :=
  fun certificate =>
    ay_vrrc_conj_left remoteContract
      (ay_vrrc_conj modelEvidence originalModel) certificate

theorem ay_vrrc_sat_certificate_original_model
    (remoteContract modelEvidence originalModel : Prop) :
    ay_vrrc_sat_certificate remoteContract modelEvidence originalModel ->
    originalModel :=
  fun certificate =>
    ay_vrrc_conj_right remoteContract
      (ay_vrrc_conj modelEvidence originalModel)
      certificate originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vrrc_unsat_certificate_intro
    (remoteContract proofEvidence originalEmptyClause : Prop) :
    remoteContract -> proofEvidence -> originalEmptyClause ->
    ay_vrrc_unsat_certificate remoteContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vrrc_conj_intro remoteContract
      (ay_vrrc_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vrrc_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vrrc_unsat_certificate_contract
    (remoteContract proofEvidence originalEmptyClause : Prop) :
    ay_vrrc_unsat_certificate remoteContract proofEvidence
      originalEmptyClause ->
    remoteContract :=
  fun certificate =>
    ay_vrrc_conj_left remoteContract
      (ay_vrrc_conj proofEvidence originalEmptyClause) certificate

theorem ay_vrrc_unsat_certificate_original_empty_clause
    (remoteContract proofEvidence originalEmptyClause : Prop) :
    ay_vrrc_unsat_certificate remoteContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun certificate =>
    ay_vrrc_conj_right remoteContract
      (ay_vrrc_conj proofEvidence originalEmptyClause)
      certificate originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vrrc_retained_validation_intro
    (remoteContract replayedDecision publicEvidence : Prop) :
    remoteContract -> replayedDecision -> publicEvidence ->
    ay_vrrc_retained_validation remoteContract replayedDecision
      publicEvidence :=
  fun contractProof decisionProof publicProof =>
    ay_vrrc_conj_intro remoteContract
      (ay_vrrc_conj replayedDecision publicEvidence)
      contractProof
      (ay_vrrc_conj_intro replayedDecision publicEvidence decisionProof
        publicProof)

theorem ay_vrrc_retained_validation_public_evidence
    (remoteContract replayedDecision publicEvidence : Prop) :
    ay_vrrc_retained_validation remoteContract replayedDecision
      publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vrrc_conj_right remoteContract
      (ay_vrrc_conj replayedDecision publicEvidence)
      validation publicEvidence
      (fun _decisionProof publicProof => publicProof)

theorem ay_vrrc_sat_certificate_validation_bridge
    (remoteContract modelEvidence originalModel unsatFact noClaimFact :
      Prop) :
    ay_vrrc_sat_certificate remoteContract modelEvidence originalModel ->
    ay_vrrc_public_result originalModel unsatFact noClaimFact :=
  fun certificate =>
    ay_vrrc_disj_left originalModel
      (ay_vrrc_disj unsatFact noClaimFact)
      (ay_vrrc_sat_certificate_original_model remoteContract modelEvidence
        originalModel certificate)

theorem ay_vrrc_unsat_certificate_validation_bridge
    (satFact remoteContract proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_vrrc_unsat_certificate remoteContract proofEvidence
      originalEmptyClause ->
    ay_vrrc_public_result satFact originalEmptyClause noClaimFact :=
  fun certificate =>
    ay_vrrc_disj_right satFact
      (ay_vrrc_disj originalEmptyClause noClaimFact)
      (ay_vrrc_disj_left originalEmptyClause noClaimFact
        (ay_vrrc_unsat_certificate_original_empty_clause remoteContract
          proofEvidence originalEmptyClause certificate))

theorem ay_vrrc_sat_certificate_supports_retained_validation
    (remoteContract modelEvidence originalModel replayedDecision : Prop) :
    ay_vrrc_sat_certificate remoteContract modelEvidence originalModel ->
    replayedDecision ->
    ay_vrrc_retained_validation remoteContract replayedDecision
      originalModel :=
  fun certificate decisionProof =>
    ay_vrrc_retained_validation_intro remoteContract replayedDecision
      originalModel
      (ay_vrrc_sat_certificate_contract remoteContract modelEvidence
        originalModel certificate)
      decisionProof
      (ay_vrrc_sat_certificate_original_model remoteContract modelEvidence
        originalModel certificate)

theorem ay_vrrc_unsat_certificate_supports_retained_validation
    (remoteContract proofEvidence originalEmptyClause replayedDecision :
      Prop) :
    ay_vrrc_unsat_certificate remoteContract proofEvidence
      originalEmptyClause ->
    replayedDecision ->
    ay_vrrc_retained_validation remoteContract replayedDecision
      originalEmptyClause :=
  fun certificate decisionProof =>
    ay_vrrc_retained_validation_intro remoteContract replayedDecision
      originalEmptyClause
      (ay_vrrc_unsat_certificate_contract remoteContract proofEvidence
        originalEmptyClause certificate)
      decisionProof
      (ay_vrrc_unsat_certificate_original_empty_clause remoteContract
        proofEvidence originalEmptyClause certificate)

theorem ay_vrrc_no_claim_intro
    (reason auditTrail diagnostic : Prop) :
    reason -> auditTrail -> diagnostic ->
    ay_vrrc_no_claim reason auditTrail diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vrrc_conj_intro reason
      (ay_vrrc_conj auditTrail diagnostic)
      reasonProof
      (ay_vrrc_conj_intro auditTrail diagnostic auditProof diagnosticProof)

theorem ay_vrrc_recompute_intro
    (reason auditTrail fallbackPath : Prop) :
    reason -> auditTrail -> fallbackPath ->
    ay_vrrc_recompute reason auditTrail fallbackPath :=
  fun reasonProof auditProof fallbackProof =>
    ay_vrrc_conj_intro reason
      (ay_vrrc_conj auditTrail fallbackPath)
      reasonProof
      (ay_vrrc_conj_intro auditTrail fallbackPath auditProof fallbackProof)

theorem ay_vrrc_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vrrc_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vrrc_conj_intro reason
      (ay_vrrc_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vrrc_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vrrc_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vrrc_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vrrc_conj_right reason
      (ay_vrrc_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vrrc_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vrrc_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vrrc_conj_right reason
      (ay_vrrc_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vrrc_remote_failure_intro
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrrc_blocked_publication satFact unsatFact reason ->
    ay_vrrc_recompute reason auditTrail fallbackPath ->
    ay_vrrc_remote_failure satFact unsatFact reason auditTrail
      fallbackPath :=
  fun blocked recompute =>
    ay_vrrc_conj_intro
      (ay_vrrc_blocked_publication satFact unsatFact reason)
      (ay_vrrc_recompute reason auditTrail fallbackPath)
      blocked recompute

theorem ay_vrrc_remote_failure_blocks_sat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrrc_remote_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vrrc_blocked_publication_no_sat satFact unsatFact reason
      (ay_vrrc_conj_left
        (ay_vrrc_blocked_publication satFact unsatFact reason)
        (ay_vrrc_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vrrc_remote_failure_blocks_unsat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrrc_remote_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vrrc_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vrrc_conj_left
        (ay_vrrc_blocked_publication satFact unsatFact reason)
        (ay_vrrc_recompute reason auditTrail fallbackPath)
        failure)

theorem ay_vrrc_remote_failure_recompute
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrrc_remote_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    ay_vrrc_recompute reason auditTrail fallbackPath :=
  fun failure =>
    ay_vrrc_conj_right
      (ay_vrrc_blocked_publication satFact unsatFact reason)
      (ay_vrrc_recompute reason auditTrail fallbackPath)
      failure

theorem ay_vrrc_transport_corruption_blocks_publication
    (satFact unsatFact transportCorruption auditTrail fallbackPath : Prop) :
    transportCorruption -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrrc_remote_failure satFact unsatFact transportCorruption
      auditTrail fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrrc_remote_failure_intro satFact unsatFact transportCorruption
      auditTrail fallbackPath
      (ay_vrrc_blocked_publication_intro satFact unsatFact
        transportCorruption reasonProof blockSat blockUnsat)
      (ay_vrrc_recompute_intro transportCorruption auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrrc_digest_mismatch_blocks_publication
    (satFact unsatFact digestMismatch auditTrail fallbackPath : Prop) :
    digestMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrrc_remote_failure satFact unsatFact digestMismatch auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrrc_remote_failure_intro satFact unsatFact digestMismatch
      auditTrail fallbackPath
      (ay_vrrc_blocked_publication_intro satFact unsatFact digestMismatch
        reasonProof blockSat blockUnsat)
      (ay_vrrc_recompute_intro digestMismatch auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrrc_kernel_drift_blocks_publication
    (satFact unsatFact kernelDrift auditTrail fallbackPath : Prop) :
    kernelDrift -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrrc_remote_failure satFact unsatFact kernelDrift auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrrc_remote_failure_intro satFact unsatFact kernelDrift auditTrail
      fallbackPath
      (ay_vrrc_blocked_publication_intro satFact unsatFact kernelDrift
        reasonProof blockSat blockUnsat)
      (ay_vrrc_recompute_intro kernelDrift auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrrc_missing_retained_evidence_blocks_publication
    (satFact unsatFact missingRetained auditTrail fallbackPath : Prop) :
    missingRetained -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrrc_remote_failure satFact unsatFact missingRetained auditTrail
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrrc_remote_failure_intro satFact unsatFact missingRetained
      auditTrail fallbackPath
      (ay_vrrc_blocked_publication_intro satFact unsatFact missingRetained
        reasonProof blockSat blockUnsat)
      (ay_vrrc_recompute_intro missingRetained auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrrc_audit_contradiction_blocks_publication
    (satFact unsatFact auditContradiction auditTrail fallbackPath : Prop) :
    auditContradiction -> (satFact -> False) -> (unsatFact -> False) ->
    auditTrail -> fallbackPath ->
    ay_vrrc_remote_failure satFact unsatFact auditContradiction
      auditTrail fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof fallbackProof =>
    ay_vrrc_remote_failure_intro satFact unsatFact auditContradiction
      auditTrail fallbackPath
      (ay_vrrc_blocked_publication_intro satFact unsatFact
        auditContradiction reasonProof blockSat blockUnsat)
      (ay_vrrc_recompute_intro auditContradiction auditTrail fallbackPath
        reasonProof auditProof fallbackProof)

theorem ay_vrrc_failure_cannot_publish_sat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrrc_remote_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    satFact -> False :=
  ay_vrrc_remote_failure_blocks_sat satFact unsatFact reason auditTrail
    fallbackPath

theorem ay_vrrc_failure_cannot_publish_unsat
    (satFact unsatFact reason auditTrail fallbackPath : Prop) :
    ay_vrrc_remote_failure satFact unsatFact reason auditTrail
      fallbackPath ->
    unsatFact -> False :=
  ay_vrrc_remote_failure_blocks_unsat satFact unsatFact reason auditTrail
    fallbackPath
