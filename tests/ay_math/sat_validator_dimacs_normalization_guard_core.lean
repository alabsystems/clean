-- SAT-COMP validator DIMACS normalization guard core.
--
-- Public SAT/UNSAT claims may use a normalized CNF only when raw input,
-- parser, renaming, clause permutation, checker, build, archive, fallback, and
-- audit evidence all agree with the original benchmark.

def ay_dng_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_dng_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_dng_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_dng_disj satFact (ay_dng_disj unsatFact noClaimFact)

def ay_dng_normalization_contract
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (rawInputDigest -> normalizedCnfDigest -> parserTranscript ->
      variableRenamingLedger -> clausePermutationWitness ->
      benchmarkFingerprint -> checkerTranscript -> solverBuildEvidence ->
      archiveManifest -> fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_dng_sat_publication
    (normalizationContract satNormalizationPreserves checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_dng_conj normalizationContract
    (ay_dng_conj satNormalizationPreserves
      (ay_dng_conj checkedModel originalBenchmarkSat))

def ay_dng_unsat_publication
    (normalizationContract unsatNormalizationPreserves checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_dng_conj normalizationContract
    (ay_dng_conj unsatNormalizationPreserves
      (ay_dng_conj checkedProof originalBenchmarkUnsat))

def ay_dng_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_dng_conj reason (ay_dng_conj fallbackPath auditTrail)

def ay_dng_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_dng_conj reason
    (ay_dng_conj (satFact -> False) (unsatFact -> False))

def ay_dng_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_dng_conj reason
    (ay_dng_conj fallbackPath recomputeObligation)

def ay_dng_normalization_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_dng_conj
    (ay_dng_blocked_publication satFact unsatFact reason)
    (ay_dng_recompute reason fallbackPath recomputeObligation)

theorem ay_dng_conj_intro (left right : Prop) :
    left -> right -> ay_dng_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_dng_conj_left (left right : Prop) :
    ay_dng_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_dng_conj_right (left right : Prop) :
    ay_dng_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_dng_disj_left (left right : Prop) :
    left -> ay_dng_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_dng_disj_right (left right : Prop) :
    right -> ay_dng_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_dng_normalization_contract_intro
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    rawInputDigest -> normalizedCnfDigest -> parserTranscript ->
    variableRenamingLedger -> clausePermutationWitness ->
    benchmarkFingerprint -> checkerTranscript -> solverBuildEvidence ->
    archiveManifest -> fallbackNoClaimPath -> auditTranscript ->
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript :=
  fun rawProof normalizedProof parserProof renamingProof permutationProof
      fingerprintProof checkerProof buildProof archiveProof fallbackProof
      auditProof result build =>
    build rawProof normalizedProof parserProof renamingProof permutationProof
      fingerprintProof checkerProof buildProof archiveProof fallbackProof
      auditProof

theorem ay_dng_contract_raw_input
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    rawInputDigest :=
  fun contract =>
    contract rawInputDigest
      (fun rawProof _normalizedProof _parserProof _renamingProof
          _permutationProof _fingerprintProof _checkerProof _buildProof
          _archiveProof _fallbackProof _auditProof => rawProof)

theorem ay_dng_contract_normalized_cnf
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    normalizedCnfDigest :=
  fun contract =>
    contract normalizedCnfDigest
      (fun _rawProof normalizedProof _parserProof _renamingProof
          _permutationProof _fingerprintProof _checkerProof _buildProof
          _archiveProof _fallbackProof _auditProof => normalizedProof)

theorem ay_dng_contract_parser
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    parserTranscript :=
  fun contract =>
    contract parserTranscript
      (fun _rawProof _normalizedProof parserProof _renamingProof
          _permutationProof _fingerprintProof _checkerProof _buildProof
          _archiveProof _fallbackProof _auditProof => parserProof)

theorem ay_dng_contract_renaming
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    variableRenamingLedger :=
  fun contract =>
    contract variableRenamingLedger
      (fun _rawProof _normalizedProof _parserProof renamingProof
          _permutationProof _fingerprintProof _checkerProof _buildProof
          _archiveProof _fallbackProof _auditProof => renamingProof)

theorem ay_dng_contract_permutation
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    clausePermutationWitness :=
  fun contract =>
    contract clausePermutationWitness
      (fun _rawProof _normalizedProof _parserProof _renamingProof
          permutationProof _fingerprintProof _checkerProof _buildProof
          _archiveProof _fallbackProof _auditProof => permutationProof)

theorem ay_dng_contract_fingerprint
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _rawProof _normalizedProof _parserProof _renamingProof
          _permutationProof fingerprintProof _checkerProof _buildProof
          _archiveProof _fallbackProof _auditProof => fingerprintProof)

theorem ay_dng_contract_checker
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _rawProof _normalizedProof _parserProof _renamingProof
          _permutationProof _fingerprintProof checkerProof _buildProof
          _archiveProof _fallbackProof _auditProof => checkerProof)

theorem ay_dng_contract_build
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _rawProof _normalizedProof _parserProof _renamingProof
          _permutationProof _fingerprintProof _checkerProof buildProof
          _archiveProof _fallbackProof _auditProof => buildProof)

theorem ay_dng_contract_archive
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _rawProof _normalizedProof _parserProof _renamingProof
          _permutationProof _fingerprintProof _checkerProof _buildProof
          archiveProof _fallbackProof _auditProof => archiveProof)

theorem ay_dng_contract_fallback
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _rawProof _normalizedProof _parserProof _renamingProof
          _permutationProof _fingerprintProof _checkerProof _buildProof
          _archiveProof fallbackProof _auditProof => fallbackProof)

theorem ay_dng_contract_audit
    (rawInputDigest normalizedCnfDigest parserTranscript
      variableRenamingLedger clausePermutationWitness benchmarkFingerprint
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_dng_normalization_contract rawInputDigest normalizedCnfDigest
      parserTranscript variableRenamingLedger clausePermutationWitness
      benchmarkFingerprint checkerTranscript solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _rawProof _normalizedProof _parserProof _renamingProof
          _permutationProof _fingerprintProof _checkerProof _buildProof
          _archiveProof _fallbackProof auditProof => auditProof)

theorem ay_dng_sat_publication_intro
    (normalizationContract satNormalizationPreserves checkedModel
      originalBenchmarkSat : Prop) :
    normalizationContract -> satNormalizationPreserves -> checkedModel ->
    originalBenchmarkSat ->
    ay_dng_sat_publication normalizationContract satNormalizationPreserves
      checkedModel originalBenchmarkSat :=
  fun hcontract hpreserves hchecked horiginal =>
    ay_dng_conj_intro normalizationContract
      (ay_dng_conj satNormalizationPreserves
        (ay_dng_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_dng_conj_intro satNormalizationPreserves
        (ay_dng_conj checkedModel originalBenchmarkSat)
        hpreserves
        (ay_dng_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_dng_unsat_publication_intro
    (normalizationContract unsatNormalizationPreserves checkedProof
      originalBenchmarkUnsat : Prop) :
    normalizationContract -> unsatNormalizationPreserves -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_dng_unsat_publication normalizationContract unsatNormalizationPreserves
      checkedProof originalBenchmarkUnsat :=
  fun hcontract hpreserves hchecked horiginal =>
    ay_dng_conj_intro normalizationContract
      (ay_dng_conj unsatNormalizationPreserves
        (ay_dng_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_dng_conj_intro unsatNormalizationPreserves
        (ay_dng_conj checkedProof originalBenchmarkUnsat)
        hpreserves
        (ay_dng_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_dng_sat_publication_original_truth
    (normalizationContract satNormalizationPreserves checkedModel
      originalBenchmarkSat : Prop) :
    ay_dng_sat_publication normalizationContract satNormalizationPreserves
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_dng_conj_right checkedModel originalBenchmarkSat
      (ay_dng_conj_right satNormalizationPreserves
        (ay_dng_conj checkedModel originalBenchmarkSat)
        (ay_dng_conj_right normalizationContract
          (ay_dng_conj satNormalizationPreserves
            (ay_dng_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_dng_unsat_publication_original_truth
    (normalizationContract unsatNormalizationPreserves checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_dng_unsat_publication normalizationContract unsatNormalizationPreserves
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_dng_conj_right checkedProof originalBenchmarkUnsat
      (ay_dng_conj_right unsatNormalizationPreserves
        (ay_dng_conj checkedProof originalBenchmarkUnsat)
        (ay_dng_conj_right normalizationContract
          (ay_dng_conj unsatNormalizationPreserves
            (ay_dng_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_dng_accepted_normalization_preserves_sat_truth
    (normalizationContract satNormalizationPreserves checkedModel
      originalBenchmarkSat : Prop) :
    ay_dng_sat_publication normalizationContract satNormalizationPreserves
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_dng_sat_publication_original_truth normalizationContract
    satNormalizationPreserves checkedModel originalBenchmarkSat

theorem ay_dng_accepted_normalization_preserves_unsat_truth
    (normalizationContract unsatNormalizationPreserves checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_dng_unsat_publication normalizationContract unsatNormalizationPreserves
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_dng_unsat_publication_original_truth normalizationContract
    unsatNormalizationPreserves checkedProof originalBenchmarkUnsat

theorem ay_dng_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_dng_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_dng_conj_intro reason (ay_dng_conj fallbackPath auditTrail)
      hreason
      (ay_dng_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_dng_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_dng_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_dng_conj_intro reason
      (ay_dng_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_dng_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_dng_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_dng_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_dng_conj_left (satFact -> False) (unsatFact -> False)
      (ay_dng_conj_right reason
        (ay_dng_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_dng_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_dng_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_dng_conj_right (satFact -> False) (unsatFact -> False)
      (ay_dng_conj_right reason
        (ay_dng_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_dng_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_dng_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_dng_conj_intro reason
      (ay_dng_conj fallbackPath recomputeObligation)
      hreason
      (ay_dng_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_dng_normalization_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_dng_blocked_publication satFact unsatFact reason ->
    ay_dng_recompute reason fallbackPath recomputeObligation ->
    ay_dng_normalization_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_dng_conj_intro
      (ay_dng_blocked_publication satFact unsatFact reason)
      (ay_dng_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_dng_normalization_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_dng_normalization_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_dng_blocked_publication_no_sat satFact unsatFact reason
      (ay_dng_conj_left
        (ay_dng_blocked_publication satFact unsatFact reason)
        (ay_dng_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_dng_normalization_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_dng_normalization_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_dng_blocked_publication_no_unsat satFact unsatFact reason
      (ay_dng_conj_left
        (ay_dng_blocked_publication satFact unsatFact reason)
        (ay_dng_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_dng_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_dng_no_claim reason fallbackPath auditTrail :=
  ay_dng_no_claim_intro reason fallbackPath auditTrail

theorem ay_dng_parser_mismatch_forces_no_claim
    (parserMismatch fallbackPath auditTrail : Prop) :
    parserMismatch -> fallbackPath -> auditTrail ->
    ay_dng_no_claim parserMismatch fallbackPath auditTrail :=
  ay_dng_mismatch_forces_no_claim parserMismatch fallbackPath auditTrail

theorem ay_dng_digest_mismatch_forces_no_claim
    (digestMismatch fallbackPath auditTrail : Prop) :
    digestMismatch -> fallbackPath -> auditTrail ->
    ay_dng_no_claim digestMismatch fallbackPath auditTrail :=
  ay_dng_mismatch_forces_no_claim digestMismatch fallbackPath auditTrail

theorem ay_dng_renaming_mismatch_forces_no_claim
    (renamingMismatch fallbackPath auditTrail : Prop) :
    renamingMismatch -> fallbackPath -> auditTrail ->
    ay_dng_no_claim renamingMismatch fallbackPath auditTrail :=
  ay_dng_mismatch_forces_no_claim renamingMismatch fallbackPath auditTrail

theorem ay_dng_permutation_mismatch_forces_no_claim
    (permutationMismatch fallbackPath auditTrail : Prop) :
    permutationMismatch -> fallbackPath -> auditTrail ->
    ay_dng_no_claim permutationMismatch fallbackPath auditTrail :=
  ay_dng_mismatch_forces_no_claim permutationMismatch fallbackPath auditTrail

theorem ay_dng_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_dng_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_dng_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_dng_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch fallbackPath auditTrail : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    ay_dng_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_dng_mismatch_forces_no_claim fingerprintMismatch fallbackPath auditTrail

theorem ay_dng_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_dng_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_dng_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_dng_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_dng_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_dng_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_dng_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_dng_normalization_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_dng_normalization_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_dng_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_dng_normalization_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_dng_normalization_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation
