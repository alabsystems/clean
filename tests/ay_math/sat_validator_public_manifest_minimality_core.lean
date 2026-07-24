-- SAT-COMP validator public manifest minimality core.
--
-- A published SAT/UNSAT artifact manifest is sufficient and minimal only when
-- it retains the original input fingerprint, solver build identity, result
-- artifact digest, checker replay transcript, reconstruction handle,
-- exit-code mapping, and audit fallback/no-claim evidence.

def ay_vpmm_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vpmm_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vpmm_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vpmm_disj satFact (ay_vpmm_disj unsatFact noClaimFact)

def ay_vpmm_required_components
    (originalFingerprint solverBuildIdentity resultArtifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) : Prop :=
  ay_vpmm_conj originalFingerprint
    (ay_vpmm_conj solverBuildIdentity
      (ay_vpmm_conj resultArtifactDigest
        (ay_vpmm_conj checkerReplayTranscript
          (ay_vpmm_conj reconstructionHandle
            (ay_vpmm_conj exitCodeMapping auditFallback)))))

def ay_vpmm_minimal_manifest
    (requiredComponents noContradictoryComponents : Prop) : Prop :=
  ay_vpmm_conj requiredComponents noContradictoryComponents

def ay_vpmm_sat_manifest
    (minimalManifest modelEvidence originalModel : Prop) : Prop :=
  ay_vpmm_conj minimalManifest
    (ay_vpmm_conj modelEvidence originalModel)

def ay_vpmm_unsat_manifest
    (minimalManifest proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vpmm_conj minimalManifest
    (ay_vpmm_conj proofEvidence originalEmptyClause)

def ay_vpmm_no_claim_manifest
    (minimalManifest diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vpmm_conj minimalManifest
    (ay_vpmm_conj diagnostic noSemanticClaim)

def ay_vpmm_manifest_validation
    (minimalManifest checkerAccepted publicEvidence : Prop) : Prop :=
  ay_vpmm_conj minimalManifest
    (ay_vpmm_conj checkerAccepted publicEvidence)

def ay_vpmm_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vpmm_conj reason
    (ay_vpmm_conj (satFact -> False) (unsatFact -> False))

def ay_vpmm_recompute
    (reason auditFallback fallbackPath : Prop) : Prop :=
  ay_vpmm_conj reason (ay_vpmm_conj auditFallback fallbackPath)

def ay_vpmm_manifest_failure
    (satFact unsatFact reason auditFallback fallbackPath : Prop) : Prop :=
  ay_vpmm_conj
    (ay_vpmm_blocked_publication satFact unsatFact reason)
    (ay_vpmm_recompute reason auditFallback fallbackPath)

theorem ay_vpmm_conj_intro (left right : Prop) :
    left -> right -> ay_vpmm_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vpmm_conj_left (left right : Prop) :
    ay_vpmm_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vpmm_conj_right (left right : Prop) :
    ay_vpmm_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vpmm_disj_left (left right : Prop) :
    left -> ay_vpmm_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vpmm_disj_right (left right : Prop) :
    right -> ay_vpmm_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vpmm_required_components_intro
    (originalFingerprint solverBuildIdentity resultArtifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    originalFingerprint -> solverBuildIdentity -> resultArtifactDigest ->
    checkerReplayTranscript -> reconstructionHandle -> exitCodeMapping ->
    auditFallback ->
    ay_vpmm_required_components originalFingerprint solverBuildIdentity
      resultArtifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback :=
  fun fingerprintProof buildProof digestProof transcriptProof
      reconstructionProof mappingProof fallbackProof =>
    ay_vpmm_conj_intro originalFingerprint
      (ay_vpmm_conj solverBuildIdentity
        (ay_vpmm_conj resultArtifactDigest
          (ay_vpmm_conj checkerReplayTranscript
            (ay_vpmm_conj reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback)))))
      fingerprintProof
      (ay_vpmm_conj_intro solverBuildIdentity
        (ay_vpmm_conj resultArtifactDigest
          (ay_vpmm_conj checkerReplayTranscript
            (ay_vpmm_conj reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback))))
        buildProof
        (ay_vpmm_conj_intro resultArtifactDigest
          (ay_vpmm_conj checkerReplayTranscript
            (ay_vpmm_conj reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback)))
          digestProof
          (ay_vpmm_conj_intro checkerReplayTranscript
            (ay_vpmm_conj reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback))
            transcriptProof
            (ay_vpmm_conj_intro reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback)
              reconstructionProof
              (ay_vpmm_conj_intro exitCodeMapping auditFallback
                mappingProof fallbackProof)))))

theorem ay_vpmm_required_components_fingerprint
    (originalFingerprint solverBuildIdentity resultArtifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vpmm_required_components originalFingerprint solverBuildIdentity
      resultArtifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    originalFingerprint :=
  fun components =>
    ay_vpmm_conj_left originalFingerprint
      (ay_vpmm_conj solverBuildIdentity
        (ay_vpmm_conj resultArtifactDigest
          (ay_vpmm_conj checkerReplayTranscript
            (ay_vpmm_conj reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback)))))
      components

theorem ay_vpmm_required_components_build
    (originalFingerprint solverBuildIdentity resultArtifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vpmm_required_components originalFingerprint solverBuildIdentity
      resultArtifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    solverBuildIdentity :=
  fun components =>
    ay_vpmm_conj_right originalFingerprint
      (ay_vpmm_conj solverBuildIdentity
        (ay_vpmm_conj resultArtifactDigest
          (ay_vpmm_conj checkerReplayTranscript
            (ay_vpmm_conj reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback)))))
      components solverBuildIdentity
      (fun buildProof _tail => buildProof)

theorem ay_vpmm_required_components_digest
    (originalFingerprint solverBuildIdentity resultArtifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vpmm_required_components originalFingerprint solverBuildIdentity
      resultArtifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    resultArtifactDigest :=
  fun components =>
    ay_vpmm_conj_right originalFingerprint
      (ay_vpmm_conj solverBuildIdentity
        (ay_vpmm_conj resultArtifactDigest
          (ay_vpmm_conj checkerReplayTranscript
            (ay_vpmm_conj reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback)))))
      components resultArtifactDigest
      (fun _buildProof tail =>
        tail resultArtifactDigest (fun digestProof _tail2 => digestProof))

theorem ay_vpmm_required_components_transcript
    (originalFingerprint solverBuildIdentity resultArtifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vpmm_required_components originalFingerprint solverBuildIdentity
      resultArtifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    checkerReplayTranscript :=
  fun components =>
    ay_vpmm_conj_right originalFingerprint
      (ay_vpmm_conj solverBuildIdentity
        (ay_vpmm_conj resultArtifactDigest
          (ay_vpmm_conj checkerReplayTranscript
            (ay_vpmm_conj reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback)))))
      components checkerReplayTranscript
      (fun _buildProof tail =>
        tail checkerReplayTranscript
          (fun _digestProof tail2 =>
            tail2 checkerReplayTranscript
              (fun transcriptProof _tail3 => transcriptProof)))

theorem ay_vpmm_required_components_reconstruction
    (originalFingerprint solverBuildIdentity resultArtifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vpmm_required_components originalFingerprint solverBuildIdentity
      resultArtifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    reconstructionHandle :=
  fun components =>
    ay_vpmm_conj_right originalFingerprint
      (ay_vpmm_conj solverBuildIdentity
        (ay_vpmm_conj resultArtifactDigest
          (ay_vpmm_conj checkerReplayTranscript
            (ay_vpmm_conj reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback)))))
      components reconstructionHandle
      (fun _buildProof tail =>
        tail reconstructionHandle
          (fun _digestProof tail2 =>
            tail2 reconstructionHandle
              (fun _transcriptProof tail3 =>
                tail3 reconstructionHandle
                  (fun reconstructionProof _tail4 =>
                    reconstructionProof))))

theorem ay_vpmm_required_components_mapping
    (originalFingerprint solverBuildIdentity resultArtifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vpmm_required_components originalFingerprint solverBuildIdentity
      resultArtifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    exitCodeMapping :=
  fun components =>
    ay_vpmm_conj_right originalFingerprint
      (ay_vpmm_conj solverBuildIdentity
        (ay_vpmm_conj resultArtifactDigest
          (ay_vpmm_conj checkerReplayTranscript
            (ay_vpmm_conj reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback)))))
      components exitCodeMapping
      (fun _buildProof tail =>
        tail exitCodeMapping
          (fun _digestProof tail2 =>
            tail2 exitCodeMapping
              (fun _transcriptProof tail3 =>
                tail3 exitCodeMapping
                  (fun _reconstructionProof tail4 =>
                    tail4 exitCodeMapping
                      (fun mappingProof _fallbackProof => mappingProof)))))

theorem ay_vpmm_required_components_fallback
    (originalFingerprint solverBuildIdentity resultArtifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vpmm_required_components originalFingerprint solverBuildIdentity
      resultArtifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    auditFallback :=
  fun components =>
    ay_vpmm_conj_right originalFingerprint
      (ay_vpmm_conj solverBuildIdentity
        (ay_vpmm_conj resultArtifactDigest
          (ay_vpmm_conj checkerReplayTranscript
            (ay_vpmm_conj reconstructionHandle
              (ay_vpmm_conj exitCodeMapping auditFallback)))))
      components auditFallback
      (fun _buildProof tail =>
        tail auditFallback
          (fun _digestProof tail2 =>
            tail2 auditFallback
              (fun _transcriptProof tail3 =>
                tail3 auditFallback
                  (fun _reconstructionProof tail4 =>
                    tail4 auditFallback
                      (fun _mappingProof fallbackProof => fallbackProof)))))

theorem ay_vpmm_minimal_manifest_intro
    (requiredComponents noContradictoryComponents : Prop) :
    requiredComponents -> noContradictoryComponents ->
    ay_vpmm_minimal_manifest requiredComponents
      noContradictoryComponents :=
  fun componentsProof cleanProof =>
    ay_vpmm_conj_intro requiredComponents noContradictoryComponents
      componentsProof cleanProof

theorem ay_vpmm_minimal_manifest_components
    (requiredComponents noContradictoryComponents : Prop) :
    ay_vpmm_minimal_manifest requiredComponents
      noContradictoryComponents ->
    requiredComponents :=
  fun manifest =>
    ay_vpmm_conj_left requiredComponents noContradictoryComponents manifest

theorem ay_vpmm_minimal_manifest_no_contradictions
    (requiredComponents noContradictoryComponents : Prop) :
    ay_vpmm_minimal_manifest requiredComponents
      noContradictoryComponents ->
    noContradictoryComponents :=
  fun manifest =>
    ay_vpmm_conj_right requiredComponents noContradictoryComponents manifest

theorem ay_vpmm_sat_manifest_intro
    (minimalManifest modelEvidence originalModel : Prop) :
    minimalManifest -> modelEvidence -> originalModel ->
    ay_vpmm_sat_manifest minimalManifest modelEvidence originalModel :=
  fun manifestProof modelProof originalProof =>
    ay_vpmm_conj_intro minimalManifest
      (ay_vpmm_conj modelEvidence originalModel)
      manifestProof
      (ay_vpmm_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vpmm_sat_manifest_minimal
    (minimalManifest modelEvidence originalModel : Prop) :
    ay_vpmm_sat_manifest minimalManifest modelEvidence originalModel ->
    minimalManifest :=
  fun manifest =>
    ay_vpmm_conj_left minimalManifest
      (ay_vpmm_conj modelEvidence originalModel) manifest

theorem ay_vpmm_sat_manifest_original_model
    (minimalManifest modelEvidence originalModel : Prop) :
    ay_vpmm_sat_manifest minimalManifest modelEvidence originalModel ->
    originalModel :=
  fun manifest =>
    ay_vpmm_conj_right minimalManifest
      (ay_vpmm_conj modelEvidence originalModel)
      manifest originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vpmm_unsat_manifest_intro
    (minimalManifest proofEvidence originalEmptyClause : Prop) :
    minimalManifest -> proofEvidence -> originalEmptyClause ->
    ay_vpmm_unsat_manifest minimalManifest proofEvidence
      originalEmptyClause :=
  fun manifestProof proofProof emptyProof =>
    ay_vpmm_conj_intro minimalManifest
      (ay_vpmm_conj proofEvidence originalEmptyClause)
      manifestProof
      (ay_vpmm_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vpmm_unsat_manifest_minimal
    (minimalManifest proofEvidence originalEmptyClause : Prop) :
    ay_vpmm_unsat_manifest minimalManifest proofEvidence
      originalEmptyClause ->
    minimalManifest :=
  fun manifest =>
    ay_vpmm_conj_left minimalManifest
      (ay_vpmm_conj proofEvidence originalEmptyClause) manifest

theorem ay_vpmm_unsat_manifest_original_empty_clause
    (minimalManifest proofEvidence originalEmptyClause : Prop) :
    ay_vpmm_unsat_manifest minimalManifest proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun manifest =>
    ay_vpmm_conj_right minimalManifest
      (ay_vpmm_conj proofEvidence originalEmptyClause)
      manifest originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vpmm_no_claim_manifest_intro
    (minimalManifest diagnostic noSemanticClaim : Prop) :
    minimalManifest -> diagnostic -> noSemanticClaim ->
    ay_vpmm_no_claim_manifest minimalManifest diagnostic noSemanticClaim :=
  fun manifestProof diagnosticProof noClaimProof =>
    ay_vpmm_conj_intro minimalManifest
      (ay_vpmm_conj diagnostic noSemanticClaim)
      manifestProof
      (ay_vpmm_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vpmm_no_claim_manifest_no_semantic_claim
    (minimalManifest diagnostic noSemanticClaim : Prop) :
    ay_vpmm_no_claim_manifest minimalManifest diagnostic noSemanticClaim ->
    noSemanticClaim :=
  fun manifest =>
    ay_vpmm_conj_right minimalManifest
      (ay_vpmm_conj diagnostic noSemanticClaim)
      manifest noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vpmm_manifest_validation_intro
    (minimalManifest checkerAccepted publicEvidence : Prop) :
    minimalManifest -> checkerAccepted -> publicEvidence ->
    ay_vpmm_manifest_validation minimalManifest checkerAccepted
      publicEvidence :=
  fun manifestProof checkerProof publicProof =>
    ay_vpmm_conj_intro minimalManifest
      (ay_vpmm_conj checkerAccepted publicEvidence)
      manifestProof
      (ay_vpmm_conj_intro checkerAccepted publicEvidence checkerProof
        publicProof)

theorem ay_vpmm_manifest_validation_public_evidence
    (minimalManifest checkerAccepted publicEvidence : Prop) :
    ay_vpmm_manifest_validation minimalManifest checkerAccepted
      publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vpmm_conj_right minimalManifest
      (ay_vpmm_conj checkerAccepted publicEvidence)
      validation publicEvidence
      (fun _checkerProof publicProof => publicProof)

theorem ay_vpmm_minimal_sat_manifest_validates_same_result
    (minimalManifest modelEvidence originalModel unsatFact noClaimFact :
      Prop) :
    ay_vpmm_sat_manifest minimalManifest modelEvidence originalModel ->
    ay_vpmm_public_result originalModel unsatFact noClaimFact :=
  fun manifest =>
    ay_vpmm_disj_left originalModel
      (ay_vpmm_disj unsatFact noClaimFact)
      (ay_vpmm_sat_manifest_original_model minimalManifest modelEvidence
        originalModel manifest)

theorem ay_vpmm_minimal_unsat_manifest_validates_same_result
    (satFact minimalManifest proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_vpmm_unsat_manifest minimalManifest proofEvidence
      originalEmptyClause ->
    ay_vpmm_public_result satFact originalEmptyClause noClaimFact :=
  fun manifest =>
    ay_vpmm_disj_right satFact
      (ay_vpmm_disj originalEmptyClause noClaimFact)
      (ay_vpmm_disj_left originalEmptyClause noClaimFact
        (ay_vpmm_unsat_manifest_original_empty_clause minimalManifest
          proofEvidence originalEmptyClause manifest))

theorem ay_vpmm_minimal_no_claim_manifest_validates_same_result
    (satFact unsatFact minimalManifest diagnostic noSemanticClaim : Prop) :
    ay_vpmm_no_claim_manifest minimalManifest diagnostic noSemanticClaim ->
    ay_vpmm_public_result satFact unsatFact noSemanticClaim :=
  fun manifest =>
    ay_vpmm_disj_right satFact
      (ay_vpmm_disj unsatFact noSemanticClaim)
      (ay_vpmm_disj_right unsatFact noSemanticClaim
        (ay_vpmm_no_claim_manifest_no_semantic_claim minimalManifest
          diagnostic noSemanticClaim manifest))

theorem ay_vpmm_sat_manifest_supports_validation
    (minimalManifest modelEvidence originalModel checkerAccepted : Prop) :
    ay_vpmm_sat_manifest minimalManifest modelEvidence originalModel ->
    checkerAccepted ->
    ay_vpmm_manifest_validation minimalManifest checkerAccepted
      originalModel :=
  fun manifest checkerProof =>
    ay_vpmm_manifest_validation_intro minimalManifest checkerAccepted
      originalModel
      (ay_vpmm_sat_manifest_minimal minimalManifest modelEvidence
        originalModel manifest)
      checkerProof
      (ay_vpmm_sat_manifest_original_model minimalManifest modelEvidence
        originalModel manifest)

theorem ay_vpmm_unsat_manifest_supports_validation
    (minimalManifest proofEvidence originalEmptyClause checkerAccepted :
      Prop) :
    ay_vpmm_unsat_manifest minimalManifest proofEvidence
      originalEmptyClause ->
    checkerAccepted ->
    ay_vpmm_manifest_validation minimalManifest checkerAccepted
      originalEmptyClause :=
  fun manifest checkerProof =>
    ay_vpmm_manifest_validation_intro minimalManifest checkerAccepted
      originalEmptyClause
      (ay_vpmm_unsat_manifest_minimal minimalManifest proofEvidence
        originalEmptyClause manifest)
      checkerProof
      (ay_vpmm_unsat_manifest_original_empty_clause minimalManifest
        proofEvidence originalEmptyClause manifest)

theorem ay_vpmm_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vpmm_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vpmm_conj_intro reason
      (ay_vpmm_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vpmm_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vpmm_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vpmm_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vpmm_conj_right reason
      (ay_vpmm_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vpmm_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vpmm_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vpmm_conj_right reason
      (ay_vpmm_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vpmm_recompute_intro
    (reason auditFallback fallbackPath : Prop) :
    reason -> auditFallback -> fallbackPath ->
    ay_vpmm_recompute reason auditFallback fallbackPath :=
  fun reasonProof fallbackProof pathProof =>
    ay_vpmm_conj_intro reason
      (ay_vpmm_conj auditFallback fallbackPath)
      reasonProof
      (ay_vpmm_conj_intro auditFallback fallbackPath fallbackProof
        pathProof)

theorem ay_vpmm_manifest_failure_intro
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vpmm_blocked_publication satFact unsatFact reason ->
    ay_vpmm_recompute reason auditFallback fallbackPath ->
    ay_vpmm_manifest_failure satFact unsatFact reason auditFallback
      fallbackPath :=
  fun blocked recompute =>
    ay_vpmm_conj_intro
      (ay_vpmm_blocked_publication satFact unsatFact reason)
      (ay_vpmm_recompute reason auditFallback fallbackPath)
      blocked recompute

theorem ay_vpmm_manifest_failure_blocks_sat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vpmm_manifest_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vpmm_blocked_publication_no_sat satFact unsatFact reason
      (ay_vpmm_conj_left
        (ay_vpmm_blocked_publication satFact unsatFact reason)
        (ay_vpmm_recompute reason auditFallback fallbackPath)
        failure)

theorem ay_vpmm_manifest_failure_blocks_unsat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vpmm_manifest_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vpmm_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vpmm_conj_left
        (ay_vpmm_blocked_publication satFact unsatFact reason)
        (ay_vpmm_recompute reason auditFallback fallbackPath)
        failure)

theorem ay_vpmm_manifest_failure_recompute
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vpmm_manifest_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    ay_vpmm_recompute reason auditFallback fallbackPath :=
  fun failure =>
    ay_vpmm_conj_right
      (ay_vpmm_blocked_publication satFact unsatFact reason)
      (ay_vpmm_recompute reason auditFallback fallbackPath)
      failure

theorem ay_vpmm_removed_fingerprint_forces_no_claim
    (satFact unsatFact removedFingerprint auditFallback fallbackPath : Prop) :
    removedFingerprint -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vpmm_manifest_failure satFact unsatFact removedFingerprint
      auditFallback fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vpmm_manifest_failure_intro satFact unsatFact removedFingerprint
      auditFallback fallbackPath
      (ay_vpmm_blocked_publication_intro satFact unsatFact
        removedFingerprint reasonProof blockSat blockUnsat)
      (ay_vpmm_recompute_intro removedFingerprint auditFallback fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vpmm_removed_build_identity_forces_no_claim
    (satFact unsatFact removedBuild auditFallback fallbackPath : Prop) :
    removedBuild -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vpmm_manifest_failure satFact unsatFact removedBuild auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vpmm_manifest_failure_intro satFact unsatFact removedBuild
      auditFallback fallbackPath
      (ay_vpmm_blocked_publication_intro satFact unsatFact removedBuild
        reasonProof blockSat blockUnsat)
      (ay_vpmm_recompute_intro removedBuild auditFallback fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vpmm_removed_digest_forces_no_claim
    (satFact unsatFact removedDigest auditFallback fallbackPath : Prop) :
    removedDigest -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vpmm_manifest_failure satFact unsatFact removedDigest auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vpmm_manifest_failure_intro satFact unsatFact removedDigest
      auditFallback fallbackPath
      (ay_vpmm_blocked_publication_intro satFact unsatFact removedDigest
        reasonProof blockSat blockUnsat)
      (ay_vpmm_recompute_intro removedDigest auditFallback fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vpmm_removed_replay_transcript_forces_no_claim
    (satFact unsatFact removedTranscript auditFallback fallbackPath : Prop) :
    removedTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vpmm_manifest_failure satFact unsatFact removedTranscript
      auditFallback fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vpmm_manifest_failure_intro satFact unsatFact removedTranscript
      auditFallback fallbackPath
      (ay_vpmm_blocked_publication_intro satFact unsatFact
        removedTranscript reasonProof blockSat blockUnsat)
      (ay_vpmm_recompute_intro removedTranscript auditFallback fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vpmm_removed_reconstruction_forces_no_claim
    (satFact unsatFact removedReconstruction auditFallback fallbackPath :
      Prop) :
    removedReconstruction -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vpmm_manifest_failure satFact unsatFact removedReconstruction
      auditFallback fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vpmm_manifest_failure_intro satFact unsatFact removedReconstruction
      auditFallback fallbackPath
      (ay_vpmm_blocked_publication_intro satFact unsatFact
        removedReconstruction reasonProof blockSat blockUnsat)
      (ay_vpmm_recompute_intro removedReconstruction auditFallback
        fallbackPath reasonProof fallbackProof pathProof)

theorem ay_vpmm_removed_exit_mapping_forces_no_claim
    (satFact unsatFact removedMapping auditFallback fallbackPath : Prop) :
    removedMapping -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vpmm_manifest_failure satFact unsatFact removedMapping
      auditFallback fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vpmm_manifest_failure_intro satFact unsatFact removedMapping
      auditFallback fallbackPath
      (ay_vpmm_blocked_publication_intro satFact unsatFact removedMapping
        reasonProof blockSat blockUnsat)
      (ay_vpmm_recompute_intro removedMapping auditFallback fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vpmm_removed_audit_fallback_forces_no_claim
    (satFact unsatFact removedFallback auditFallback fallbackPath : Prop) :
    removedFallback -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vpmm_manifest_failure satFact unsatFact removedFallback
      auditFallback fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vpmm_manifest_failure_intro satFact unsatFact removedFallback
      auditFallback fallbackPath
      (ay_vpmm_blocked_publication_intro satFact unsatFact
        removedFallback reasonProof blockSat blockUnsat)
      (ay_vpmm_recompute_intro removedFallback auditFallback fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vpmm_contradictory_component_forces_no_claim
    (satFact unsatFact contradiction auditFallback fallbackPath : Prop) :
    contradiction -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vpmm_manifest_failure satFact unsatFact contradiction auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vpmm_manifest_failure_intro satFact unsatFact contradiction
      auditFallback fallbackPath
      (ay_vpmm_blocked_publication_intro satFact unsatFact contradiction
        reasonProof blockSat blockUnsat)
      (ay_vpmm_recompute_intro contradiction auditFallback fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vpmm_failure_cannot_publish_sat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vpmm_manifest_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    satFact -> False :=
  ay_vpmm_manifest_failure_blocks_sat satFact unsatFact reason auditFallback
    fallbackPath

theorem ay_vpmm_failure_cannot_publish_unsat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vpmm_manifest_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    unsatFact -> False :=
  ay_vpmm_manifest_failure_blocks_unsat satFact unsatFact reason
    auditFallback fallbackPath
