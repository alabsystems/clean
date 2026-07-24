-- SAT-COMP validator public result-kind exclusivity core.
--
-- A public artifact bundle may claim exactly one of SAT, UNSAT, or no-claim
-- only when result kind, fingerprint, build identity, digest, replay
-- transcript, reconstruction handle, exit-code mapping, and fallback audit
-- evidence agree.  Contradictory kind evidence downgrades to no-claim.

def ay_vrke_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrke_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vrke_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vrke_disj satFact (ay_vrke_disj unsatFact noClaimFact)

def ay_vrke_bundle_contract
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) : Prop :=
  ay_vrke_conj resultKind
    (ay_vrke_conj originalFingerprint
      (ay_vrke_conj solverBuildIdentity
        (ay_vrke_conj artifactDigest
          (ay_vrke_conj checkerReplayTranscript
            (ay_vrke_conj reconstructionHandle
              (ay_vrke_conj exitCodeMapping fallbackAudit))))))

def ay_vrke_sat_branch
    (bundleContract satEvidence originalModel unsatFact : Prop) : Prop :=
  ay_vrke_conj bundleContract
    (ay_vrke_conj satEvidence
      (ay_vrke_conj originalModel (unsatFact -> False)))

def ay_vrke_unsat_branch
    (bundleContract proofEvidence originalEmptyClause satFact : Prop) : Prop :=
  ay_vrke_conj bundleContract
    (ay_vrke_conj proofEvidence
      (ay_vrke_conj originalEmptyClause (satFact -> False)))

def ay_vrke_no_claim_branch
    (bundleContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vrke_conj bundleContract
    (ay_vrke_conj diagnostic noSemanticClaim)

def ay_vrke_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vrke_conj reason
    (ay_vrke_conj (satFact -> False) (unsatFact -> False))

def ay_vrke_recompute
    (reason fallbackAudit fallbackPath : Prop) : Prop :=
  ay_vrke_conj reason (ay_vrke_conj fallbackAudit fallbackPath)

def ay_vrke_kind_failure
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) : Prop :=
  ay_vrke_conj
    (ay_vrke_blocked_publication satFact unsatFact reason)
    (ay_vrke_recompute reason fallbackAudit fallbackPath)

theorem ay_vrke_conj_intro (left right : Prop) :
    left -> right -> ay_vrke_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrke_conj_left (left right : Prop) :
    ay_vrke_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrke_conj_right (left right : Prop) :
    ay_vrke_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrke_disj_left (left right : Prop) :
    left -> ay_vrke_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vrke_disj_right (left right : Prop) :
    right -> ay_vrke_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrke_bundle_contract_intro
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    resultKind -> originalFingerprint -> solverBuildIdentity ->
    artifactDigest -> checkerReplayTranscript -> reconstructionHandle ->
    exitCodeMapping -> fallbackAudit ->
    ay_vrke_bundle_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit :=
  fun kindProof fingerprintProof buildProof digestProof replayProof
      reconstructionProof mappingProof auditProof =>
    ay_vrke_conj_intro resultKind
      (ay_vrke_conj originalFingerprint
        (ay_vrke_conj solverBuildIdentity
          (ay_vrke_conj artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit))))))
      kindProof
      (ay_vrke_conj_intro originalFingerprint
        (ay_vrke_conj solverBuildIdentity
          (ay_vrke_conj artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit)))))
        fingerprintProof
        (ay_vrke_conj_intro solverBuildIdentity
          (ay_vrke_conj artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit))))
          buildProof
          (ay_vrke_conj_intro artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit)))
            digestProof
            (ay_vrke_conj_intro checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit))
              replayProof
              (ay_vrke_conj_intro reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit)
                reconstructionProof
                (ay_vrke_conj_intro exitCodeMapping fallbackAudit
                  mappingProof auditProof))))))

theorem ay_vrke_bundle_contract_kind
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vrke_bundle_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    resultKind :=
  fun contract =>
    ay_vrke_conj_left resultKind
      (ay_vrke_conj originalFingerprint
        (ay_vrke_conj solverBuildIdentity
          (ay_vrke_conj artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit))))))
      contract

theorem ay_vrke_bundle_contract_fingerprint
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vrke_bundle_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    originalFingerprint :=
  fun contract =>
    ay_vrke_conj_right resultKind
      (ay_vrke_conj originalFingerprint
        (ay_vrke_conj solverBuildIdentity
          (ay_vrke_conj artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit))))))
      contract originalFingerprint
      (fun fingerprintProof _tail => fingerprintProof)

theorem ay_vrke_bundle_contract_build
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vrke_bundle_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    solverBuildIdentity :=
  fun contract =>
    ay_vrke_conj_right resultKind
      (ay_vrke_conj originalFingerprint
        (ay_vrke_conj solverBuildIdentity
          (ay_vrke_conj artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit))))))
      contract solverBuildIdentity
      (fun _fingerprintProof tail =>
        tail solverBuildIdentity (fun buildProof _tail2 => buildProof))

theorem ay_vrke_bundle_contract_digest
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vrke_bundle_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    artifactDigest :=
  fun contract =>
    ay_vrke_conj_right resultKind
      (ay_vrke_conj originalFingerprint
        (ay_vrke_conj solverBuildIdentity
          (ay_vrke_conj artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit))))))
      contract artifactDigest
      (fun _fingerprintProof tail =>
        tail artifactDigest
          (fun _buildProof tail2 =>
            tail2 artifactDigest (fun digestProof _tail3 => digestProof)))

theorem ay_vrke_bundle_contract_replay
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vrke_bundle_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    checkerReplayTranscript :=
  fun contract =>
    ay_vrke_conj_right resultKind
      (ay_vrke_conj originalFingerprint
        (ay_vrke_conj solverBuildIdentity
          (ay_vrke_conj artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit))))))
      contract checkerReplayTranscript
      (fun _fingerprintProof tail =>
        tail checkerReplayTranscript
          (fun _buildProof tail2 =>
            tail2 checkerReplayTranscript
              (fun _digestProof tail3 =>
                tail3 checkerReplayTranscript
                  (fun replayProof _tail4 => replayProof))))

theorem ay_vrke_bundle_contract_reconstruction
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vrke_bundle_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    reconstructionHandle :=
  fun contract =>
    ay_vrke_conj_right resultKind
      (ay_vrke_conj originalFingerprint
        (ay_vrke_conj solverBuildIdentity
          (ay_vrke_conj artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit))))))
      contract reconstructionHandle
      (fun _fingerprintProof tail =>
        tail reconstructionHandle
          (fun _buildProof tail2 =>
            tail2 reconstructionHandle
              (fun _digestProof tail3 =>
                tail3 reconstructionHandle
                  (fun _replayProof tail4 =>
                    tail4 reconstructionHandle
                      (fun reconstructionProof _tail5 =>
                        reconstructionProof)))))

theorem ay_vrke_bundle_contract_mapping
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vrke_bundle_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    exitCodeMapping :=
  fun contract =>
    ay_vrke_conj_right resultKind
      (ay_vrke_conj originalFingerprint
        (ay_vrke_conj solverBuildIdentity
          (ay_vrke_conj artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit))))))
      contract exitCodeMapping
      (fun _fingerprintProof tail =>
        tail exitCodeMapping
          (fun _buildProof tail2 =>
            tail2 exitCodeMapping
              (fun _digestProof tail3 =>
                tail3 exitCodeMapping
                  (fun _replayProof tail4 =>
                    tail4 exitCodeMapping
                      (fun _reconstructionProof tail5 =>
                        tail5 exitCodeMapping
                          (fun mappingProof _auditProof =>
                            mappingProof))))))

theorem ay_vrke_bundle_contract_fallback
    (resultKind originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      fallbackAudit : Prop) :
    ay_vrke_bundle_contract resultKind originalFingerprint
      solverBuildIdentity artifactDigest checkerReplayTranscript
      reconstructionHandle exitCodeMapping fallbackAudit ->
    fallbackAudit :=
  fun contract =>
    ay_vrke_conj_right resultKind
      (ay_vrke_conj originalFingerprint
        (ay_vrke_conj solverBuildIdentity
          (ay_vrke_conj artifactDigest
            (ay_vrke_conj checkerReplayTranscript
              (ay_vrke_conj reconstructionHandle
                (ay_vrke_conj exitCodeMapping fallbackAudit))))))
      contract fallbackAudit
      (fun _fingerprintProof tail =>
        tail fallbackAudit
          (fun _buildProof tail2 =>
            tail2 fallbackAudit
              (fun _digestProof tail3 =>
                tail3 fallbackAudit
                  (fun _replayProof tail4 =>
                    tail4 fallbackAudit
                      (fun _reconstructionProof tail5 =>
                        tail5 fallbackAudit
                          (fun _mappingProof auditProof =>
                            auditProof))))))

theorem ay_vrke_sat_branch_intro
    (bundleContract satEvidence originalModel unsatFact : Prop) :
    bundleContract -> satEvidence -> originalModel ->
    (unsatFact -> False) ->
    ay_vrke_sat_branch bundleContract satEvidence originalModel
      unsatFact :=
  fun contractProof satProof modelProof excludesUnsat =>
    ay_vrke_conj_intro bundleContract
      (ay_vrke_conj satEvidence
        (ay_vrke_conj originalModel (unsatFact -> False)))
      contractProof
      (ay_vrke_conj_intro satEvidence
        (ay_vrke_conj originalModel (unsatFact -> False))
        satProof
        (ay_vrke_conj_intro originalModel (unsatFact -> False) modelProof
          excludesUnsat))

theorem ay_vrke_sat_branch_contract
    (bundleContract satEvidence originalModel unsatFact : Prop) :
    ay_vrke_sat_branch bundleContract satEvidence originalModel unsatFact ->
    bundleContract :=
  fun branch =>
    ay_vrke_conj_left bundleContract
      (ay_vrke_conj satEvidence
        (ay_vrke_conj originalModel (unsatFact -> False)))
      branch

theorem ay_vrke_sat_branch_model
    (bundleContract satEvidence originalModel unsatFact : Prop) :
    ay_vrke_sat_branch bundleContract satEvidence originalModel unsatFact ->
    originalModel :=
  fun branch =>
    ay_vrke_conj_right bundleContract
      (ay_vrke_conj satEvidence
        (ay_vrke_conj originalModel (unsatFact -> False)))
      branch originalModel
      (fun _satProof tail =>
        tail originalModel (fun modelProof _excludesUnsat => modelProof))

theorem ay_vrke_sat_excludes_unsat
    (bundleContract satEvidence originalModel unsatFact : Prop) :
    ay_vrke_sat_branch bundleContract satEvidence originalModel unsatFact ->
    unsatFact -> False :=
  fun branch =>
    ay_vrke_conj_right bundleContract
      (ay_vrke_conj satEvidence
        (ay_vrke_conj originalModel (unsatFact -> False)))
      branch (unsatFact -> False)
      (fun _satProof tail =>
        tail (unsatFact -> False)
          (fun _modelProof excludesUnsat => excludesUnsat))

theorem ay_vrke_unsat_branch_intro
    (bundleContract proofEvidence originalEmptyClause satFact : Prop) :
    bundleContract -> proofEvidence -> originalEmptyClause ->
    (satFact -> False) ->
    ay_vrke_unsat_branch bundleContract proofEvidence originalEmptyClause
      satFact :=
  fun contractProof proofProof emptyProof excludesSat =>
    ay_vrke_conj_intro bundleContract
      (ay_vrke_conj proofEvidence
        (ay_vrke_conj originalEmptyClause (satFact -> False)))
      contractProof
      (ay_vrke_conj_intro proofEvidence
        (ay_vrke_conj originalEmptyClause (satFact -> False))
        proofProof
        (ay_vrke_conj_intro originalEmptyClause (satFact -> False)
          emptyProof excludesSat))

theorem ay_vrke_unsat_branch_contract
    (bundleContract proofEvidence originalEmptyClause satFact : Prop) :
    ay_vrke_unsat_branch bundleContract proofEvidence originalEmptyClause
      satFact ->
    bundleContract :=
  fun branch =>
    ay_vrke_conj_left bundleContract
      (ay_vrke_conj proofEvidence
        (ay_vrke_conj originalEmptyClause (satFact -> False)))
      branch

theorem ay_vrke_unsat_branch_empty_clause
    (bundleContract proofEvidence originalEmptyClause satFact : Prop) :
    ay_vrke_unsat_branch bundleContract proofEvidence originalEmptyClause
      satFact ->
    originalEmptyClause :=
  fun branch =>
    ay_vrke_conj_right bundleContract
      (ay_vrke_conj proofEvidence
        (ay_vrke_conj originalEmptyClause (satFact -> False)))
      branch originalEmptyClause
      (fun _proofEvidence tail =>
        tail originalEmptyClause
          (fun emptyProof _excludesSat => emptyProof))

theorem ay_vrke_unsat_excludes_sat
    (bundleContract proofEvidence originalEmptyClause satFact : Prop) :
    ay_vrke_unsat_branch bundleContract proofEvidence originalEmptyClause
      satFact ->
    satFact -> False :=
  fun branch =>
    ay_vrke_conj_right bundleContract
      (ay_vrke_conj proofEvidence
        (ay_vrke_conj originalEmptyClause (satFact -> False)))
      branch (satFact -> False)
      (fun _proofEvidence tail =>
        tail (satFact -> False)
          (fun _emptyProof excludesSat => excludesSat))

theorem ay_vrke_no_claim_branch_intro
    (bundleContract diagnostic noSemanticClaim : Prop) :
    bundleContract -> diagnostic -> noSemanticClaim ->
    ay_vrke_no_claim_branch bundleContract diagnostic noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_vrke_conj_intro bundleContract
      (ay_vrke_conj diagnostic noSemanticClaim)
      contractProof
      (ay_vrke_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vrke_no_claim_makes_no_semantic_claim
    (bundleContract diagnostic noSemanticClaim : Prop) :
    ay_vrke_no_claim_branch bundleContract diagnostic noSemanticClaim ->
    noSemanticClaim :=
  fun branch =>
    ay_vrke_conj_right bundleContract
      (ay_vrke_conj diagnostic noSemanticClaim)
      branch noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vrke_accepted_sat_public_result
    (bundleContract satEvidence originalModel unsatFact noClaimFact : Prop) :
    ay_vrke_sat_branch bundleContract satEvidence originalModel unsatFact ->
    ay_vrke_public_result originalModel unsatFact noClaimFact :=
  fun branch =>
    ay_vrke_disj_left originalModel
      (ay_vrke_disj unsatFact noClaimFact)
      (ay_vrke_sat_branch_model bundleContract satEvidence originalModel
        unsatFact branch)

theorem ay_vrke_accepted_unsat_public_result
    (satFact bundleContract proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_vrke_unsat_branch bundleContract proofEvidence originalEmptyClause
      satFact ->
    ay_vrke_public_result satFact originalEmptyClause noClaimFact :=
  fun branch =>
    ay_vrke_disj_right satFact
      (ay_vrke_disj originalEmptyClause noClaimFact)
      (ay_vrke_disj_left originalEmptyClause noClaimFact
        (ay_vrke_unsat_branch_empty_clause bundleContract proofEvidence
          originalEmptyClause satFact branch))

theorem ay_vrke_accepted_no_claim_public_result
    (satFact unsatFact bundleContract diagnostic noSemanticClaim : Prop) :
    ay_vrke_no_claim_branch bundleContract diagnostic noSemanticClaim ->
    ay_vrke_public_result satFact unsatFact noSemanticClaim :=
  fun branch =>
    ay_vrke_disj_right satFact
      (ay_vrke_disj unsatFact noSemanticClaim)
      (ay_vrke_disj_right unsatFact noSemanticClaim
        (ay_vrke_no_claim_makes_no_semantic_claim bundleContract
          diagnostic noSemanticClaim branch))

theorem ay_vrke_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vrke_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vrke_conj_intro reason
      (ay_vrke_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vrke_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vrke_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vrke_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vrke_conj_right reason
      (ay_vrke_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vrke_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vrke_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vrke_conj_right reason
      (ay_vrke_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vrke_recompute_intro
    (reason fallbackAudit fallbackPath : Prop) :
    reason -> fallbackAudit -> fallbackPath ->
    ay_vrke_recompute reason fallbackAudit fallbackPath :=
  fun reasonProof auditProof pathProof =>
    ay_vrke_conj_intro reason
      (ay_vrke_conj fallbackAudit fallbackPath)
      reasonProof
      (ay_vrke_conj_intro fallbackAudit fallbackPath auditProof pathProof)

theorem ay_vrke_kind_failure_intro
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrke_blocked_publication satFact unsatFact reason ->
    ay_vrke_recompute reason fallbackAudit fallbackPath ->
    ay_vrke_kind_failure satFact unsatFact reason fallbackAudit
      fallbackPath :=
  fun blocked recompute =>
    ay_vrke_conj_intro
      (ay_vrke_blocked_publication satFact unsatFact reason)
      (ay_vrke_recompute reason fallbackAudit fallbackPath)
      blocked recompute

theorem ay_vrke_kind_failure_blocks_sat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrke_kind_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vrke_blocked_publication_no_sat satFact unsatFact reason
      (ay_vrke_conj_left
        (ay_vrke_blocked_publication satFact unsatFact reason)
        (ay_vrke_recompute reason fallbackAudit fallbackPath)
        failure)

theorem ay_vrke_kind_failure_blocks_unsat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrke_kind_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vrke_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vrke_conj_left
        (ay_vrke_blocked_publication satFact unsatFact reason)
        (ay_vrke_recompute reason fallbackAudit fallbackPath)
        failure)

theorem ay_vrke_kind_failure_recompute
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrke_kind_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    ay_vrke_recompute reason fallbackAudit fallbackPath :=
  fun failure =>
    ay_vrke_conj_right
      (ay_vrke_blocked_publication satFact unsatFact reason)
      (ay_vrke_recompute reason fallbackAudit fallbackPath)
      failure

theorem ay_vrke_contradictory_kind_forces_no_claim
    (satFact unsatFact contradictoryKind fallbackAudit fallbackPath : Prop) :
    contradictoryKind -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackAudit -> fallbackPath ->
    ay_vrke_kind_failure satFact unsatFact contradictoryKind fallbackAudit
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vrke_kind_failure_intro satFact unsatFact contradictoryKind
      fallbackAudit fallbackPath
      (ay_vrke_blocked_publication_intro satFact unsatFact
        contradictoryKind reasonProof blockSat blockUnsat)
      (ay_vrke_recompute_intro contradictoryKind fallbackAudit fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vrke_failure_cannot_publish_sat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrke_kind_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    satFact -> False :=
  ay_vrke_kind_failure_blocks_sat satFact unsatFact reason fallbackAudit
    fallbackPath

theorem ay_vrke_failure_cannot_publish_unsat
    (satFact unsatFact reason fallbackAudit fallbackPath : Prop) :
    ay_vrke_kind_failure satFact unsatFact reason fallbackAudit
      fallbackPath ->
    unsatFact -> False :=
  ay_vrke_kind_failure_blocks_unsat satFact unsatFact reason fallbackAudit
    fallbackPath
