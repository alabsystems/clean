-- SAT-COMP validator benchmark identity guard core.
--
-- Public SAT/UNSAT claims must be tied to exact benchmark bytes, parser
-- interpretation, competition track metadata, solver input, result artifacts,
-- checker transcript, build/environment/archive evidence, fallback, and audit.

def ay_big_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_big_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_big_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_big_disj satFact (ay_big_disj unsatFact noClaimFact)

def ay_big_identity_contract
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkPathManifest -> rawFileDigest -> decompressedCnfDigest ->
      parserTranscript -> clauseVariableCountWitness -> trackCategoryManifest ->
      solverInputDigest -> resultArtifactDigest -> checkerTranscript ->
      solverBuildEvidence -> environmentManifest -> archiveManifest ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_big_sat_publication
    (identityContract parserIdentityEvidence checkerBackedResult checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_big_conj identityContract
    (ay_big_conj parserIdentityEvidence
      (ay_big_conj checkerBackedResult
        (ay_big_conj checkedModel originalBenchmarkSat)))

def ay_big_unsat_publication
    (identityContract parserIdentityEvidence checkerBackedResult checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_big_conj identityContract
    (ay_big_conj parserIdentityEvidence
      (ay_big_conj checkerBackedResult
        (ay_big_conj checkedProof originalBenchmarkUnsat)))

def ay_big_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_big_conj reason (ay_big_conj fallbackPath auditTrail)

def ay_big_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_big_conj reason
    (ay_big_conj (satFact -> False) (unsatFact -> False))

def ay_big_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_big_conj reason
    (ay_big_conj fallbackPath recomputeObligation)

def ay_big_identity_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_big_conj
    (ay_big_blocked_publication satFact unsatFact reason)
    (ay_big_recompute reason fallbackPath recomputeObligation)

theorem ay_big_conj_intro (left right : Prop) :
    left -> right -> ay_big_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_big_conj_left (left right : Prop) :
    ay_big_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_big_conj_right (left right : Prop) :
    ay_big_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_big_disj_left (left right : Prop) :
    left -> ay_big_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_big_disj_right (left right : Prop) :
    right -> ay_big_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_big_identity_contract_intro
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    benchmarkPathManifest -> rawFileDigest -> decompressedCnfDigest ->
    parserTranscript -> clauseVariableCountWitness -> trackCategoryManifest ->
    solverInputDigest -> resultArtifactDigest -> checkerTranscript ->
    solverBuildEvidence -> environmentManifest -> archiveManifest ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript :=
  fun pathProof rawProof decompressedProof parserProof countProof trackProof
      inputProof artifactProof checkerProof buildProof environmentProof
      archiveProof fallbackProof auditProof result build =>
    build pathProof rawProof decompressedProof parserProof countProof trackProof
      inputProof artifactProof checkerProof buildProof environmentProof
      archiveProof fallbackProof auditProof

theorem ay_big_contract_path
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkPathManifest :=
  fun contract =>
    contract benchmarkPathManifest
      (fun pathProof _rawProof _decompressedProof _parserProof _countProof
          _trackProof _inputProof _artifactProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        pathProof)

theorem ay_big_contract_raw
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    rawFileDigest :=
  fun contract =>
    contract rawFileDigest
      (fun _pathProof rawProof _decompressedProof _parserProof _countProof
          _trackProof _inputProof _artifactProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        rawProof)

theorem ay_big_contract_decompressed
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    decompressedCnfDigest :=
  fun contract =>
    contract decompressedCnfDigest
      (fun _pathProof _rawProof decompressedProof _parserProof _countProof
          _trackProof _inputProof _artifactProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        decompressedProof)

theorem ay_big_contract_parser
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    parserTranscript :=
  fun contract =>
    contract parserTranscript
      (fun _pathProof _rawProof _decompressedProof parserProof _countProof
          _trackProof _inputProof _artifactProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        parserProof)

theorem ay_big_contract_count
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    clauseVariableCountWitness :=
  fun contract =>
    contract clauseVariableCountWitness
      (fun _pathProof _rawProof _decompressedProof _parserProof countProof
          _trackProof _inputProof _artifactProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        countProof)

theorem ay_big_contract_track
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    trackCategoryManifest :=
  fun contract =>
    contract trackCategoryManifest
      (fun _pathProof _rawProof _decompressedProof _parserProof _countProof
          trackProof _inputProof _artifactProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        trackProof)

theorem ay_big_contract_input
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverInputDigest :=
  fun contract =>
    contract solverInputDigest
      (fun _pathProof _rawProof _decompressedProof _parserProof _countProof
          _trackProof inputProof _artifactProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        inputProof)

theorem ay_big_contract_artifact
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    resultArtifactDigest :=
  fun contract =>
    contract resultArtifactDigest
      (fun _pathProof _rawProof _decompressedProof _parserProof _countProof
          _trackProof _inputProof artifactProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        artifactProof)

theorem ay_big_contract_checker
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _pathProof _rawProof _decompressedProof _parserProof _countProof
          _trackProof _inputProof _artifactProof checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        checkerProof)

theorem ay_big_contract_build
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _pathProof _rawProof _decompressedProof _parserProof _countProof
          _trackProof _inputProof _artifactProof _checkerProof buildProof
          _environmentProof _archiveProof _fallbackProof _auditProof =>
        buildProof)

theorem ay_big_contract_environment
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    environmentManifest :=
  fun contract =>
    contract environmentManifest
      (fun _pathProof _rawProof _decompressedProof _parserProof _countProof
          _trackProof _inputProof _artifactProof _checkerProof _buildProof
          environmentProof _archiveProof _fallbackProof _auditProof =>
        environmentProof)

theorem ay_big_contract_archive
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _pathProof _rawProof _decompressedProof _parserProof _countProof
          _trackProof _inputProof _artifactProof _checkerProof _buildProof
          _environmentProof archiveProof _fallbackProof _auditProof =>
        archiveProof)

theorem ay_big_contract_fallback
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _pathProof _rawProof _decompressedProof _parserProof _countProof
          _trackProof _inputProof _artifactProof _checkerProof _buildProof
          _environmentProof _archiveProof fallbackProof _auditProof =>
        fallbackProof)

theorem ay_big_contract_audit
    (benchmarkPathManifest rawFileDigest decompressedCnfDigest
      parserTranscript clauseVariableCountWitness trackCategoryManifest
      solverInputDigest resultArtifactDigest checkerTranscript
      solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_big_identity_contract benchmarkPathManifest rawFileDigest
      decompressedCnfDigest parserTranscript clauseVariableCountWitness
      trackCategoryManifest solverInputDigest resultArtifactDigest
      checkerTranscript solverBuildEvidence environmentManifest archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _pathProof _rawProof _decompressedProof _parserProof _countProof
          _trackProof _inputProof _artifactProof _checkerProof _buildProof
          _environmentProof _archiveProof _fallbackProof auditProof =>
        auditProof)

theorem ay_big_sat_publication_intro
    (identityContract parserIdentityEvidence checkerBackedResult checkedModel
      originalBenchmarkSat : Prop) :
    identityContract -> parserIdentityEvidence -> checkerBackedResult ->
    checkedModel -> originalBenchmarkSat ->
    ay_big_sat_publication identityContract parserIdentityEvidence
      checkerBackedResult checkedModel originalBenchmarkSat :=
  fun hcontract hidentity hchecker hchecked horiginal =>
    ay_big_conj_intro identityContract
      (ay_big_conj parserIdentityEvidence
        (ay_big_conj checkerBackedResult
          (ay_big_conj checkedModel originalBenchmarkSat)))
      hcontract
      (ay_big_conj_intro parserIdentityEvidence
        (ay_big_conj checkerBackedResult
          (ay_big_conj checkedModel originalBenchmarkSat))
        hidentity
        (ay_big_conj_intro checkerBackedResult
          (ay_big_conj checkedModel originalBenchmarkSat)
          hchecker
          (ay_big_conj_intro checkedModel originalBenchmarkSat hchecked
            horiginal)))

theorem ay_big_unsat_publication_intro
    (identityContract parserIdentityEvidence checkerBackedResult checkedProof
      originalBenchmarkUnsat : Prop) :
    identityContract -> parserIdentityEvidence -> checkerBackedResult ->
    checkedProof -> originalBenchmarkUnsat ->
    ay_big_unsat_publication identityContract parserIdentityEvidence
      checkerBackedResult checkedProof originalBenchmarkUnsat :=
  fun hcontract hidentity hchecker hchecked horiginal =>
    ay_big_conj_intro identityContract
      (ay_big_conj parserIdentityEvidence
        (ay_big_conj checkerBackedResult
          (ay_big_conj checkedProof originalBenchmarkUnsat)))
      hcontract
      (ay_big_conj_intro parserIdentityEvidence
        (ay_big_conj checkerBackedResult
          (ay_big_conj checkedProof originalBenchmarkUnsat))
        hidentity
        (ay_big_conj_intro checkerBackedResult
          (ay_big_conj checkedProof originalBenchmarkUnsat)
          hchecker
          (ay_big_conj_intro checkedProof originalBenchmarkUnsat hchecked
            horiginal)))

theorem ay_big_sat_requires_checker_backed_result
    (identityContract parserIdentityEvidence checkerBackedResult checkedModel
      originalBenchmarkSat : Prop) :
    ay_big_sat_publication identityContract parserIdentityEvidence
      checkerBackedResult checkedModel originalBenchmarkSat ->
    checkerBackedResult :=
  fun publication =>
    ay_big_conj_left checkerBackedResult
      (ay_big_conj checkedModel originalBenchmarkSat)
      (ay_big_conj_right parserIdentityEvidence
        (ay_big_conj checkerBackedResult
          (ay_big_conj checkedModel originalBenchmarkSat))
        (ay_big_conj_right identityContract
          (ay_big_conj parserIdentityEvidence
            (ay_big_conj checkerBackedResult
              (ay_big_conj checkedModel originalBenchmarkSat)))
          publication))

theorem ay_big_unsat_requires_checker_backed_result
    (identityContract parserIdentityEvidence checkerBackedResult checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_big_unsat_publication identityContract parserIdentityEvidence
      checkerBackedResult checkedProof originalBenchmarkUnsat ->
    checkerBackedResult :=
  fun publication =>
    ay_big_conj_left checkerBackedResult
      (ay_big_conj checkedProof originalBenchmarkUnsat)
      (ay_big_conj_right parserIdentityEvidence
        (ay_big_conj checkerBackedResult
          (ay_big_conj checkedProof originalBenchmarkUnsat))
        (ay_big_conj_right identityContract
          (ay_big_conj parserIdentityEvidence
            (ay_big_conj checkerBackedResult
              (ay_big_conj checkedProof originalBenchmarkUnsat)))
          publication))

theorem ay_big_sat_publication_original_claim
    (identityContract parserIdentityEvidence checkerBackedResult checkedModel
      originalBenchmarkSat : Prop) :
    ay_big_sat_publication identityContract parserIdentityEvidence
      checkerBackedResult checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_big_conj_right checkedModel originalBenchmarkSat
      (ay_big_conj_right checkerBackedResult
        (ay_big_conj checkedModel originalBenchmarkSat)
        (ay_big_conj_right parserIdentityEvidence
          (ay_big_conj checkerBackedResult
            (ay_big_conj checkedModel originalBenchmarkSat))
          (ay_big_conj_right identityContract
            (ay_big_conj parserIdentityEvidence
              (ay_big_conj checkerBackedResult
                (ay_big_conj checkedModel originalBenchmarkSat)))
            publication)))

theorem ay_big_unsat_publication_original_claim
    (identityContract parserIdentityEvidence checkerBackedResult checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_big_unsat_publication identityContract parserIdentityEvidence
      checkerBackedResult checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_big_conj_right checkedProof originalBenchmarkUnsat
      (ay_big_conj_right checkerBackedResult
        (ay_big_conj checkedProof originalBenchmarkUnsat)
        (ay_big_conj_right parserIdentityEvidence
          (ay_big_conj checkerBackedResult
            (ay_big_conj checkedProof originalBenchmarkUnsat))
          (ay_big_conj_right identityContract
            (ay_big_conj parserIdentityEvidence
              (ay_big_conj checkerBackedResult
                (ay_big_conj checkedProof originalBenchmarkUnsat)))
            publication)))

theorem ay_big_accepted_identity_preserves_sat_soundness
    (identityContract parserIdentityEvidence checkerBackedResult checkedModel
      originalBenchmarkSat : Prop) :
    ay_big_sat_publication identityContract parserIdentityEvidence
      checkerBackedResult checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_big_sat_publication_original_claim identityContract parserIdentityEvidence
    checkerBackedResult checkedModel originalBenchmarkSat

theorem ay_big_accepted_identity_preserves_unsat_soundness
    (identityContract parserIdentityEvidence checkerBackedResult checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_big_unsat_publication identityContract parserIdentityEvidence
      checkerBackedResult checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_big_unsat_publication_original_claim identityContract
    parserIdentityEvidence checkerBackedResult checkedProof
    originalBenchmarkUnsat

theorem ay_big_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_big_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_big_conj_intro reason (ay_big_conj fallbackPath auditTrail)
      hreason
      (ay_big_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_big_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_big_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_big_conj_intro reason
      (ay_big_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_big_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_big_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_big_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_big_conj_left (satFact -> False) (unsatFact -> False)
      (ay_big_conj_right reason
        (ay_big_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_big_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_big_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_big_conj_right (satFact -> False) (unsatFact -> False)
      (ay_big_conj_right reason
        (ay_big_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_big_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_big_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_big_conj_intro reason
      (ay_big_conj fallbackPath recomputeObligation)
      hreason
      (ay_big_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_big_identity_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_big_blocked_publication satFact unsatFact reason ->
    ay_big_recompute reason fallbackPath recomputeObligation ->
    ay_big_identity_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_big_conj_intro
      (ay_big_blocked_publication satFact unsatFact reason)
      (ay_big_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_big_identity_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_big_identity_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_big_blocked_publication_no_sat satFact unsatFact reason
      (ay_big_conj_left
        (ay_big_blocked_publication satFact unsatFact reason)
        (ay_big_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_big_identity_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_big_identity_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_big_blocked_publication_no_unsat satFact unsatFact reason
      (ay_big_conj_left
        (ay_big_blocked_publication satFact unsatFact reason)
        (ay_big_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_big_identity_only_cannot_bless_sat
    (satFact unsatFact identityEvidenceOnly : Prop) :
    ay_big_blocked_publication satFact unsatFact identityEvidenceOnly ->
    satFact -> False :=
  ay_big_blocked_publication_no_sat satFact unsatFact identityEvidenceOnly

theorem ay_big_identity_only_cannot_bless_unsat
    (satFact unsatFact identityEvidenceOnly : Prop) :
    ay_big_blocked_publication satFact unsatFact identityEvidenceOnly ->
    unsatFact -> False :=
  ay_big_blocked_publication_no_unsat satFact unsatFact identityEvidenceOnly

theorem ay_big_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_big_no_claim reason fallbackPath auditTrail :=
  ay_big_no_claim_intro reason fallbackPath auditTrail

theorem ay_big_path_mismatch_forces_no_claim
    (pathMismatch fallbackPath auditTrail : Prop) :
    pathMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim pathMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim pathMismatch fallbackPath auditTrail

theorem ay_big_raw_mismatch_forces_no_claim
    (rawMismatch fallbackPath auditTrail : Prop) :
    rawMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim rawMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim rawMismatch fallbackPath auditTrail

theorem ay_big_decompressed_mismatch_forces_no_claim
    (decompressedMismatch fallbackPath auditTrail : Prop) :
    decompressedMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim decompressedMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim decompressedMismatch fallbackPath auditTrail

theorem ay_big_parser_mismatch_forces_no_claim
    (parserMismatch fallbackPath auditTrail : Prop) :
    parserMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim parserMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim parserMismatch fallbackPath auditTrail

theorem ay_big_count_mismatch_forces_no_claim
    (countMismatch fallbackPath auditTrail : Prop) :
    countMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim countMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim countMismatch fallbackPath auditTrail

theorem ay_big_track_mismatch_forces_no_claim
    (trackMismatch fallbackPath auditTrail : Prop) :
    trackMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim trackMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim trackMismatch fallbackPath auditTrail

theorem ay_big_input_mismatch_forces_no_claim
    (inputMismatch fallbackPath auditTrail : Prop) :
    inputMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim inputMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim inputMismatch fallbackPath auditTrail

theorem ay_big_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_big_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_big_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim buildMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_big_environment_mismatch_forces_no_claim
    (environmentMismatch fallbackPath auditTrail : Prop) :
    environmentMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim environmentMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim environmentMismatch fallbackPath auditTrail

theorem ay_big_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_big_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_big_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_big_audit_mismatch_forces_recompute
    (auditMismatch fallbackPath recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> recomputeObligation ->
    ay_big_recompute auditMismatch fallbackPath recomputeObligation :=
  ay_big_recompute_intro auditMismatch fallbackPath recomputeObligation

theorem ay_big_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_big_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_big_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_big_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_big_identity_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_big_identity_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_big_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_big_identity_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_big_identity_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
