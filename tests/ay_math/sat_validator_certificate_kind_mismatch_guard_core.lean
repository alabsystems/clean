-- SAT-COMP validator certificate-kind mismatch guard core.
--
-- Public SAT/UNSAT claims are allowed only when result artifact,
-- certificate kind, certificate/model artifact, checker transcript,
-- benchmark fingerprint, archive manifest, solver build evidence, and
-- no-claim fallback agree.

def ay_ckmg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ckmg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ckmg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_ckmg_disj satFact (ay_ckmg_disj unsatFact noClaimFact)

def ay_ckmg_kind_contract
    (resultArtifact certificateKind certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) : Prop :=
  forall result : Prop,
    (resultArtifact -> certificateKind -> certificateModelArtifact ->
      checkerTranscript -> benchmarkFingerprint -> archiveManifest ->
      solverBuildEvidence -> noClaimFallbackPath -> result) ->
    result

def ay_ckmg_sat_publication
    (kindContract modelKind modelEvidence originalModel : Prop) : Prop :=
  ay_ckmg_conj kindContract
    (ay_ckmg_conj modelKind (ay_ckmg_conj modelEvidence originalModel))

def ay_ckmg_unsat_publication
    (kindContract proofKind proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_ckmg_conj kindContract
    (ay_ckmg_conj proofKind (ay_ckmg_conj proofEvidence originalEmptyClause))

def ay_ckmg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_ckmg_conj reason (ay_ckmg_conj fallbackPath auditTrail)

def ay_ckmg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_ckmg_conj reason
    (ay_ckmg_conj (satFact -> False) (unsatFact -> False))

def ay_ckmg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_ckmg_conj reason
    (ay_ckmg_conj fallbackPath recomputeObligation)

def ay_ckmg_kind_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_ckmg_conj
    (ay_ckmg_blocked_publication satFact unsatFact reason)
    (ay_ckmg_recompute reason fallbackPath recomputeObligation)

theorem ay_ckmg_conj_intro (left right : Prop) :
    left -> right -> ay_ckmg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ckmg_conj_left (left right : Prop) :
    ay_ckmg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ckmg_conj_right (left right : Prop) :
    ay_ckmg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ckmg_disj_left (left right : Prop) :
    left -> ay_ckmg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ckmg_disj_right (left right : Prop) :
    right -> ay_ckmg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ckmg_kind_contract_intro
    (resultArtifact certificateKind certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    resultArtifact -> certificateKind -> certificateModelArtifact ->
    checkerTranscript -> benchmarkFingerprint -> archiveManifest ->
    solverBuildEvidence -> noClaimFallbackPath ->
    ay_ckmg_kind_contract resultArtifact certificateKind
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath :=
  fun artifactProof kindProof certificateProof checkerProof fingerprintProof
      archiveProof buildProof fallbackProof result build =>
    build artifactProof kindProof certificateProof checkerProof
      fingerprintProof archiveProof buildProof fallbackProof

theorem ay_ckmg_kind_contract_artifact
    (resultArtifact certificateKind certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ckmg_kind_contract resultArtifact certificateKind
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    resultArtifact :=
  fun contract =>
    contract resultArtifact
      (fun artifactProof _kindProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        artifactProof)

theorem ay_ckmg_kind_contract_kind
    (resultArtifact certificateKind certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ckmg_kind_contract resultArtifact certificateKind
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    certificateKind :=
  fun contract =>
    contract certificateKind
      (fun _artifactProof kindProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        kindProof)

theorem ay_ckmg_kind_contract_certificate
    (resultArtifact certificateKind certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ckmg_kind_contract resultArtifact certificateKind
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    certificateModelArtifact :=
  fun contract =>
    contract certificateModelArtifact
      (fun _artifactProof _kindProof certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        certificateProof)

theorem ay_ckmg_kind_contract_checker
    (resultArtifact certificateKind certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ckmg_kind_contract resultArtifact certificateKind
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _artifactProof _kindProof _certificateProof checkerProof
          _fingerprintProof _archiveProof _buildProof _fallbackProof =>
        checkerProof)

theorem ay_ckmg_kind_contract_fingerprint
    (resultArtifact certificateKind certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ckmg_kind_contract resultArtifact certificateKind
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _artifactProof _kindProof _certificateProof _checkerProof
          fingerprintProof _archiveProof _buildProof _fallbackProof =>
        fingerprintProof)

theorem ay_ckmg_kind_contract_archive
    (resultArtifact certificateKind certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ckmg_kind_contract resultArtifact certificateKind
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _artifactProof _kindProof _certificateProof _checkerProof
          _fingerprintProof archiveProof _buildProof _fallbackProof =>
        archiveProof)

theorem ay_ckmg_kind_contract_build
    (resultArtifact certificateKind certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ckmg_kind_contract resultArtifact certificateKind
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _artifactProof _kindProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof buildProof _fallbackProof =>
        buildProof)

theorem ay_ckmg_kind_contract_fallback
    (resultArtifact certificateKind certificateModelArtifact checkerTranscript
      benchmarkFingerprint archiveManifest solverBuildEvidence
      noClaimFallbackPath : Prop) :
    ay_ckmg_kind_contract resultArtifact certificateKind
      certificateModelArtifact checkerTranscript benchmarkFingerprint
      archiveManifest solverBuildEvidence noClaimFallbackPath ->
    noClaimFallbackPath :=
  fun contract =>
    contract noClaimFallbackPath
      (fun _artifactProof _kindProof _certificateProof _checkerProof
          _fingerprintProof _archiveProof _buildProof fallbackProof =>
        fallbackProof)

theorem ay_ckmg_sat_publication_intro
    (kindContract modelKind modelEvidence originalModel : Prop) :
    kindContract -> modelKind -> modelEvidence -> originalModel ->
    ay_ckmg_sat_publication kindContract modelKind modelEvidence
      originalModel :=
  fun contractProof kindProof modelProof originalProof =>
    ay_ckmg_conj_intro kindContract
      (ay_ckmg_conj modelKind
        (ay_ckmg_conj modelEvidence originalModel)) contractProof
      (ay_ckmg_conj_intro modelKind
        (ay_ckmg_conj modelEvidence originalModel) kindProof
        (ay_ckmg_conj_intro modelEvidence originalModel modelProof
          originalProof))

theorem ay_ckmg_sat_publication_original_model
    (kindContract modelKind modelEvidence originalModel : Prop) :
    ay_ckmg_sat_publication kindContract modelKind modelEvidence
      originalModel ->
    originalModel :=
  fun publication =>
    ay_ckmg_conj_right modelEvidence originalModel
      (ay_ckmg_conj_right modelKind
        (ay_ckmg_conj modelEvidence originalModel)
        (ay_ckmg_conj_right kindContract
          (ay_ckmg_conj modelKind
            (ay_ckmg_conj modelEvidence originalModel)) publication))

theorem ay_ckmg_sat_publication_model_kind
    (kindContract modelKind modelEvidence originalModel : Prop) :
    ay_ckmg_sat_publication kindContract modelKind modelEvidence
      originalModel ->
    modelKind :=
  fun publication =>
    ay_ckmg_conj_left modelKind
      (ay_ckmg_conj modelEvidence originalModel)
      (ay_ckmg_conj_right kindContract
        (ay_ckmg_conj modelKind
          (ay_ckmg_conj modelEvidence originalModel)) publication)

theorem ay_ckmg_unsat_publication_intro
    (kindContract proofKind proofEvidence originalEmptyClause : Prop) :
    kindContract -> proofKind -> proofEvidence -> originalEmptyClause ->
    ay_ckmg_unsat_publication kindContract proofKind proofEvidence
      originalEmptyClause :=
  fun contractProof kindProof proofProof emptyProof =>
    ay_ckmg_conj_intro kindContract
      (ay_ckmg_conj proofKind
        (ay_ckmg_conj proofEvidence originalEmptyClause)) contractProof
      (ay_ckmg_conj_intro proofKind
        (ay_ckmg_conj proofEvidence originalEmptyClause) kindProof
        (ay_ckmg_conj_intro proofEvidence originalEmptyClause proofProof
          emptyProof))

theorem ay_ckmg_unsat_publication_original_empty_clause
    (kindContract proofKind proofEvidence originalEmptyClause : Prop) :
    ay_ckmg_unsat_publication kindContract proofKind proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_ckmg_conj_right proofEvidence originalEmptyClause
      (ay_ckmg_conj_right proofKind
        (ay_ckmg_conj proofEvidence originalEmptyClause)
        (ay_ckmg_conj_right kindContract
          (ay_ckmg_conj proofKind
            (ay_ckmg_conj proofEvidence originalEmptyClause)) publication))

theorem ay_ckmg_unsat_publication_proof_kind
    (kindContract proofKind proofEvidence originalEmptyClause : Prop) :
    ay_ckmg_unsat_publication kindContract proofKind proofEvidence
      originalEmptyClause ->
    proofKind :=
  fun publication =>
    ay_ckmg_conj_left proofKind
      (ay_ckmg_conj proofEvidence originalEmptyClause)
      (ay_ckmg_conj_right kindContract
        (ay_ckmg_conj proofKind
          (ay_ckmg_conj proofEvidence originalEmptyClause)) publication)

theorem ay_ckmg_accepted_sat_kind_sound
    (kindContract modelKind modelEvidence originalModel : Prop) :
    ay_ckmg_sat_publication kindContract modelKind modelEvidence
      originalModel ->
    originalModel :=
  ay_ckmg_sat_publication_original_model kindContract modelKind modelEvidence
    originalModel

theorem ay_ckmg_accepted_unsat_kind_sound
    (kindContract proofKind proofEvidence originalEmptyClause : Prop) :
    ay_ckmg_unsat_publication kindContract proofKind proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  ay_ckmg_unsat_publication_original_empty_clause kindContract proofKind
    proofEvidence originalEmptyClause

theorem ay_ckmg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_ckmg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_ckmg_conj_intro reason (ay_ckmg_conj fallbackPath auditTrail)
      reasonProof
      (ay_ckmg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_ckmg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ckmg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_ckmg_conj_intro reason
      (ay_ckmg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_ckmg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_ckmg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_ckmg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_ckmg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_ckmg_conj_right reason
        (ay_ckmg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_ckmg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_ckmg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_ckmg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_ckmg_conj_right reason
        (ay_ckmg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_ckmg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_ckmg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_ckmg_conj_intro reason
      (ay_ckmg_conj fallbackPath recomputeObligation) reasonProof
      (ay_ckmg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_ckmg_kind_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ckmg_kind_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_ckmg_conj_intro
      (ay_ckmg_blocked_publication satFact unsatFact reason)
      (ay_ckmg_recompute reason fallbackPath recomputeObligation)
      (ay_ckmg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_ckmg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_ckmg_kind_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ckmg_kind_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_ckmg_blocked_publication_no_sat satFact unsatFact reason
      (ay_ckmg_conj_left
        (ay_ckmg_blocked_publication satFact unsatFact reason)
        (ay_ckmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ckmg_kind_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ckmg_kind_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_ckmg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_ckmg_conj_left
        (ay_ckmg_blocked_publication satFact unsatFact reason)
        (ay_ckmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ckmg_kind_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ckmg_kind_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_ckmg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_ckmg_conj_right
      (ay_ckmg_blocked_publication satFact unsatFact reason)
      (ay_ckmg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_ckmg_sat_with_proof_artifact_forces_no_claim
    (satFact unsatFact satWithProofArtifact fallbackPath auditTrail
      recomputeObligation : Prop) :
    satWithProofArtifact -> fallbackPath -> auditTrail ->
    recomputeObligation -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ckmg_no_claim satWithProofArtifact fallbackPath auditTrail :=
  fun mismatchProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ckmg_no_claim_intro satWithProofArtifact fallbackPath auditTrail
      mismatchProof fallbackProof auditProof

theorem ay_ckmg_unsat_with_model_artifact_forces_no_claim
    (satFact unsatFact unsatWithModelArtifact fallbackPath auditTrail
      recomputeObligation : Prop) :
    unsatWithModelArtifact -> fallbackPath -> auditTrail ->
    recomputeObligation -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ckmg_no_claim unsatWithModelArtifact fallbackPath auditTrail :=
  fun mismatchProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ckmg_no_claim_intro unsatWithModelArtifact fallbackPath auditTrail
      mismatchProof fallbackProof auditProof

theorem ay_ckmg_missing_kind_forces_no_claim
    (satFact unsatFact missingKind fallbackPath auditTrail
      recomputeObligation : Prop) :
    missingKind -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ckmg_no_claim missingKind fallbackPath auditTrail :=
  fun missingProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_ckmg_no_claim_intro missingKind fallbackPath auditTrail missingProof
      fallbackProof auditProof

theorem ay_ckmg_mismatched_kind_forces_no_claim
    (satFact unsatFact mismatchedKind fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchedKind -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ckmg_no_claim mismatchedKind fallbackPath auditTrail :=
  fun mismatchProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ckmg_no_claim_intro mismatchedKind fallbackPath auditTrail
      mismatchProof fallbackProof auditProof

theorem ay_ckmg_checker_disagreement_forces_no_claim
    (satFact unsatFact checkerDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerDisagreement -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ckmg_no_claim checkerDisagreement fallbackPath auditTrail :=
  fun disagreementProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ckmg_no_claim_intro checkerDisagreement fallbackPath auditTrail
      disagreementProof fallbackProof auditProof

theorem ay_ckmg_benchmark_mismatch_forces_no_claim
    (satFact unsatFact benchmarkMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    benchmarkMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ckmg_no_claim benchmarkMismatch fallbackPath auditTrail :=
  fun mismatchProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ckmg_no_claim_intro benchmarkMismatch fallbackPath auditTrail
      mismatchProof fallbackProof auditProof

theorem ay_ckmg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ckmg_no_claim buildMismatch fallbackPath auditTrail :=
  fun mismatchProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ckmg_no_claim_intro buildMismatch fallbackPath auditTrail
      mismatchProof fallbackProof auditProof

theorem ay_ckmg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ckmg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun mismatchProof fallbackProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ckmg_no_claim_intro archiveMismatch fallbackPath auditTrail
      mismatchProof fallbackProof auditProof

theorem ay_ckmg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivated fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_ckmg_no_claim fallbackActivated fallbackPath auditTrail :=
  fun fallbackProof fallbackPathProof auditProof _recomputeProof _noSat
      _noUnsat =>
    ay_ckmg_no_claim_intro fallbackActivated fallbackPath auditTrail
      fallbackProof fallbackPathProof auditProof

theorem ay_ckmg_failed_kind_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ckmg_kind_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_ckmg_kind_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_ckmg_failed_kind_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ckmg_kind_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_ckmg_kind_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_ckmg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_ckmg_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_ckmg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_ckmg_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
