-- SAT-COMP validator benchmark-pack manifest guard core.
--
-- Public SAT/UNSAT claims require benchmark pack identity, per-instance
-- fingerprinting, DIMACS normalization evidence, track/category evidence,
-- solver command evidence, checker transcript, model/proof artifact digest,
-- solver build evidence, archive manifest, fallback, and audit transcript.

def ay_bpmg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bpmg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bpmg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_bpmg_disj satFact (ay_bpmg_disj unsatFact noClaimFact)

def ay_bpmg_pack_contract
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkPackDigest -> perInstanceFingerprint ->
      dimacsNormalizationWitness -> trackCategoryManifest ->
      solverCommandManifest -> checkerTranscript -> modelProofArtifactDigest ->
      solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_bpmg_sat_publication
    (packContract intendedOriginalInstance checkedModel originalModel :
      Prop) : Prop :=
  ay_bpmg_conj packContract
    (ay_bpmg_conj intendedOriginalInstance
      (ay_bpmg_conj checkedModel originalModel))

def ay_bpmg_unsat_publication
    (packContract intendedOriginalInstance checkedProof originalEmptyClause :
      Prop) : Prop :=
  ay_bpmg_conj packContract
    (ay_bpmg_conj intendedOriginalInstance
      (ay_bpmg_conj checkedProof originalEmptyClause))

def ay_bpmg_normalization_preserved
    (originalBenchmarkFormula normalizedBenchmarkFormula : Prop) : Prop :=
  originalBenchmarkFormula -> normalizedBenchmarkFormula

def ay_bpmg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_bpmg_conj reason (ay_bpmg_conj fallbackPath auditTrail)

def ay_bpmg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_bpmg_conj reason
    (ay_bpmg_conj (satFact -> False) (unsatFact -> False))

def ay_bpmg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_bpmg_conj reason
    (ay_bpmg_conj fallbackPath recomputeObligation)

def ay_bpmg_pack_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_bpmg_conj
    (ay_bpmg_blocked_publication satFact unsatFact reason)
    (ay_bpmg_recompute reason fallbackPath recomputeObligation)

theorem ay_bpmg_conj_intro (left right : Prop) :
    left -> right -> ay_bpmg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_bpmg_conj_left (left right : Prop) :
    ay_bpmg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_bpmg_conj_right (left right : Prop) :
    ay_bpmg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_bpmg_disj_left (left right : Prop) :
    left -> ay_bpmg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_bpmg_disj_right (left right : Prop) :
    right -> ay_bpmg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_bpmg_pack_contract_intro
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    benchmarkPackDigest -> perInstanceFingerprint ->
    dimacsNormalizationWitness -> trackCategoryManifest ->
    solverCommandManifest -> checkerTranscript -> modelProofArtifactDigest ->
    solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript :=
  fun packProof fingerprintProof normalizationProof trackProof commandProof
      checkerProof artifactProof buildProof archiveProof fallbackProof
      auditProof result build =>
    build packProof fingerprintProof normalizationProof trackProof commandProof
      checkerProof artifactProof buildProof archiveProof fallbackProof
      auditProof

theorem ay_bpmg_contract_pack
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    benchmarkPackDigest :=
  fun contract =>
    contract benchmarkPackDigest
      (fun packProof _fingerprintProof _normalizationProof _trackProof
          _commandProof _checkerProof _artifactProof _buildProof
          _archiveProof _fallbackProof _auditProof => packProof)

theorem ay_bpmg_contract_fingerprint
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    perInstanceFingerprint :=
  fun contract =>
    contract perInstanceFingerprint
      (fun _packProof fingerprintProof _normalizationProof _trackProof
          _commandProof _checkerProof _artifactProof _buildProof
          _archiveProof _fallbackProof _auditProof => fingerprintProof)

theorem ay_bpmg_contract_normalization
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    dimacsNormalizationWitness :=
  fun contract =>
    contract dimacsNormalizationWitness
      (fun _packProof _fingerprintProof normalizationProof _trackProof
          _commandProof _checkerProof _artifactProof _buildProof
          _archiveProof _fallbackProof _auditProof => normalizationProof)

theorem ay_bpmg_contract_track
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    trackCategoryManifest :=
  fun contract =>
    contract trackCategoryManifest
      (fun _packProof _fingerprintProof _normalizationProof trackProof
          _commandProof _checkerProof _artifactProof _buildProof
          _archiveProof _fallbackProof _auditProof => trackProof)

theorem ay_bpmg_contract_command
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverCommandManifest :=
  fun contract =>
    contract solverCommandManifest
      (fun _packProof _fingerprintProof _normalizationProof _trackProof
          commandProof _checkerProof _artifactProof _buildProof _archiveProof
          _fallbackProof _auditProof => commandProof)

theorem ay_bpmg_contract_checker
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _packProof _fingerprintProof _normalizationProof _trackProof
          _commandProof checkerProof _artifactProof _buildProof _archiveProof
          _fallbackProof _auditProof => checkerProof)

theorem ay_bpmg_contract_artifact
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _packProof _fingerprintProof _normalizationProof _trackProof
          _commandProof _checkerProof artifactProof _buildProof _archiveProof
          _fallbackProof _auditProof => artifactProof)

theorem ay_bpmg_contract_build
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _packProof _fingerprintProof _normalizationProof _trackProof
          _commandProof _checkerProof _artifactProof buildProof _archiveProof
          _fallbackProof _auditProof => buildProof)

theorem ay_bpmg_contract_archive
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _packProof _fingerprintProof _normalizationProof _trackProof
          _commandProof _checkerProof _artifactProof _buildProof archiveProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_bpmg_contract_fallback
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _packProof _fingerprintProof _normalizationProof _trackProof
          _commandProof _checkerProof _artifactProof _buildProof _archiveProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_bpmg_contract_audit
    (benchmarkPackDigest perInstanceFingerprint dimacsNormalizationWitness
      trackCategoryManifest solverCommandManifest checkerTranscript
      modelProofArtifactDigest solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_bpmg_pack_contract benchmarkPackDigest perInstanceFingerprint
      dimacsNormalizationWitness trackCategoryManifest solverCommandManifest
      checkerTranscript modelProofArtifactDigest solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _packProof _fingerprintProof _normalizationProof _trackProof
          _commandProof _checkerProof _artifactProof _buildProof _archiveProof
          _fallbackProof auditProof => auditProof)

theorem ay_bpmg_sat_publication_intro
    (packContract intendedOriginalInstance checkedModel originalModel :
      Prop) :
    packContract -> intendedOriginalInstance -> checkedModel -> originalModel ->
    ay_bpmg_sat_publication packContract intendedOriginalInstance checkedModel
      originalModel :=
  fun contractProof instanceProof modelProof originalProof =>
    ay_bpmg_conj_intro packContract
      (ay_bpmg_conj intendedOriginalInstance
        (ay_bpmg_conj checkedModel originalModel))
      contractProof
      (ay_bpmg_conj_intro intendedOriginalInstance
        (ay_bpmg_conj checkedModel originalModel)
        instanceProof
        (ay_bpmg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_bpmg_unsat_publication_intro
    (packContract intendedOriginalInstance checkedProof originalEmptyClause :
      Prop) :
    packContract -> intendedOriginalInstance -> checkedProof ->
    originalEmptyClause ->
    ay_bpmg_unsat_publication packContract intendedOriginalInstance
      checkedProof originalEmptyClause :=
  fun contractProof instanceProof proofProof originalProof =>
    ay_bpmg_conj_intro packContract
      (ay_bpmg_conj intendedOriginalInstance
        (ay_bpmg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_bpmg_conj_intro intendedOriginalInstance
        (ay_bpmg_conj checkedProof originalEmptyClause)
        instanceProof
        (ay_bpmg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_bpmg_sat_publication_original_model
    (packContract intendedOriginalInstance checkedModel originalModel :
      Prop) :
    ay_bpmg_sat_publication packContract intendedOriginalInstance checkedModel
      originalModel ->
    originalModel :=
  fun publication =>
    ay_bpmg_conj_right checkedModel originalModel
      (ay_bpmg_conj_right intendedOriginalInstance
        (ay_bpmg_conj checkedModel originalModel)
        (ay_bpmg_conj_right packContract
          (ay_bpmg_conj intendedOriginalInstance
            (ay_bpmg_conj checkedModel originalModel))
          publication))

theorem ay_bpmg_unsat_publication_original_empty_clause
    (packContract intendedOriginalInstance checkedProof originalEmptyClause :
      Prop) :
    ay_bpmg_unsat_publication packContract intendedOriginalInstance
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_bpmg_conj_right checkedProof originalEmptyClause
      (ay_bpmg_conj_right intendedOriginalInstance
        (ay_bpmg_conj checkedProof originalEmptyClause)
        (ay_bpmg_conj_right packContract
          (ay_bpmg_conj intendedOriginalInstance
            (ay_bpmg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_bpmg_accepted_pack_sat_tied_to_original_instance
    (packContract intendedOriginalInstance checkedModel originalModel :
      Prop) :
    ay_bpmg_sat_publication packContract intendedOriginalInstance checkedModel
      originalModel ->
    ay_bpmg_public_result originalModel False False :=
  fun publication =>
    ay_bpmg_disj_left originalModel (ay_bpmg_disj False False)
      (ay_bpmg_sat_publication_original_model packContract
        intendedOriginalInstance checkedModel originalModel publication)

theorem ay_bpmg_accepted_pack_unsat_tied_to_original_instance
    (packContract intendedOriginalInstance checkedProof originalEmptyClause :
      Prop) :
    ay_bpmg_unsat_publication packContract intendedOriginalInstance
      checkedProof originalEmptyClause ->
    ay_bpmg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_bpmg_disj_right False (ay_bpmg_disj originalEmptyClause False)
      (ay_bpmg_disj_left originalEmptyClause False
        (ay_bpmg_unsat_publication_original_empty_clause packContract
          intendedOriginalInstance checkedProof originalEmptyClause
          publication))

theorem ay_bpmg_normalization_does_not_change_original_semantics
    (originalBenchmarkFormula normalizedBenchmarkFormula : Prop) :
    ay_bpmg_normalization_preserved originalBenchmarkFormula
      normalizedBenchmarkFormula ->
    originalBenchmarkFormula -> normalizedBenchmarkFormula :=
  fun preserved => preserved

theorem ay_bpmg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_bpmg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_bpmg_conj_intro reason (ay_bpmg_conj fallbackPath auditTrail)
      reasonProof
      (ay_bpmg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_bpmg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_bpmg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_bpmg_conj_intro reason
      (ay_bpmg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_bpmg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_bpmg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_bpmg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_bpmg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_bpmg_conj_right reason
        (ay_bpmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_bpmg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_bpmg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_bpmg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_bpmg_conj_right reason
        (ay_bpmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_bpmg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_bpmg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_bpmg_conj_intro reason
      (ay_bpmg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_bpmg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_bpmg_pack_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_bpmg_blocked_publication satFact unsatFact reason ->
    ay_bpmg_recompute reason fallbackPath recomputeObligation ->
    ay_bpmg_pack_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_bpmg_conj_intro
      (ay_bpmg_blocked_publication satFact unsatFact reason)
      (ay_bpmg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_bpmg_pack_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_bpmg_pack_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_bpmg_blocked_publication_no_sat satFact unsatFact reason
      (ay_bpmg_conj_left
        (ay_bpmg_blocked_publication satFact unsatFact reason)
        (ay_bpmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_bpmg_pack_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_bpmg_pack_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_bpmg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_bpmg_conj_left
        (ay_bpmg_blocked_publication satFact unsatFact reason)
        (ay_bpmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_bpmg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_bpmg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_bpmg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_bpmg_pack_mismatch_forces_no_claim
    (satFact unsatFact packMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    packMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_bpmg_no_claim packMismatch fallbackPath auditTrail :=
  ay_bpmg_mismatch_forces_no_claim satFact unsatFact packMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_bpmg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_bpmg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_bpmg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_bpmg_normalization_mismatch_forces_no_claim
    (satFact unsatFact normalizationMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    normalizationMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_bpmg_no_claim normalizationMismatch fallbackPath auditTrail :=
  ay_bpmg_mismatch_forces_no_claim satFact unsatFact normalizationMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_bpmg_track_mismatch_forces_no_claim
    (satFact unsatFact trackMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    trackMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_bpmg_no_claim trackMismatch fallbackPath auditTrail :=
  ay_bpmg_mismatch_forces_no_claim satFact unsatFact trackMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_bpmg_command_mismatch_forces_no_claim
    (satFact unsatFact commandMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    commandMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_bpmg_no_claim commandMismatch fallbackPath auditTrail :=
  ay_bpmg_mismatch_forces_no_claim satFact unsatFact commandMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_bpmg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_bpmg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_bpmg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_bpmg_artifact_mismatch_forces_no_claim
    (satFact unsatFact artifactMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_bpmg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_bpmg_mismatch_forces_no_claim satFact unsatFact artifactMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_bpmg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_bpmg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_bpmg_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_bpmg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_bpmg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_bpmg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_bpmg_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_bpmg_no_claim auditMismatch fallbackPath auditTrail :=
  ay_bpmg_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_bpmg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_bpmg_pack_failure satFact unsatFact fallbackActivation fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_bpmg_pack_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_bpmg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_bpmg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_bpmg_failed_pack_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_bpmg_pack_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_bpmg_pack_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_bpmg_failed_pack_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_bpmg_pack_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_bpmg_pack_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_bpmg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_bpmg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_bpmg_conj_left reason (ay_bpmg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_bpmg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_bpmg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_bpmg_conj_left reason (ay_bpmg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
