-- SAT-COMP validator CPU-feature manifest guard core.
--
-- Public SAT/UNSAT claims require CPU feature evidence, architecture/ISA
-- ledger, deterministic-mode evidence, floating/rounding irrelevance,
-- command manifest, checker transcript, benchmark fingerprint, build evidence,
-- archive evidence, fallback, and audit transcript to agree.

def ay_cfmg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cfmg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cfmg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_cfmg_disj satFact (ay_cfmg_disj unsatFact noClaimFact)

def ay_cfmg_cpu_contract
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (cpuFeatureManifestDigest -> architectureIsaLedger ->
      deterministicModeWitness -> floatingRoundingIrrelevanceWitness ->
      solverCommandManifest -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_cfmg_sat_publication
    (cpuContract acceptedCpuFeatures checkedModel originalModel : Prop) :
    Prop :=
  ay_cfmg_conj cpuContract
    (ay_cfmg_conj acceptedCpuFeatures
      (ay_cfmg_conj checkedModel originalModel))

def ay_cfmg_unsat_publication
    (cpuContract acceptedCpuFeatures checkedProof originalEmptyClause :
      Prop) : Prop :=
  ay_cfmg_conj cpuContract
    (ay_cfmg_conj acceptedCpuFeatures
      (ay_cfmg_conj checkedProof originalEmptyClause))

def ay_cfmg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_cfmg_conj reason (ay_cfmg_conj fallbackPath auditTrail)

def ay_cfmg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_cfmg_conj reason
    (ay_cfmg_conj (satFact -> False) (unsatFact -> False))

def ay_cfmg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_cfmg_conj reason
    (ay_cfmg_conj fallbackPath recomputeObligation)

def ay_cfmg_cpu_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_cfmg_conj
    (ay_cfmg_blocked_publication satFact unsatFact reason)
    (ay_cfmg_recompute reason fallbackPath recomputeObligation)

theorem ay_cfmg_conj_intro (left right : Prop) :
    left -> right -> ay_cfmg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_cfmg_conj_left (left right : Prop) :
    ay_cfmg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_cfmg_conj_right (left right : Prop) :
    ay_cfmg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_cfmg_disj_left (left right : Prop) :
    left -> ay_cfmg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_cfmg_disj_right (left right : Prop) :
    right -> ay_cfmg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_cfmg_cpu_contract_intro
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    cpuFeatureManifestDigest -> architectureIsaLedger ->
    deterministicModeWitness -> floatingRoundingIrrelevanceWitness ->
    solverCommandManifest -> checkerTranscript -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript :=
  fun featureProof architectureProof deterministicProof roundingProof
      commandProof checkerProof fingerprintProof buildProof archiveProof
      fallbackProof auditProof result build =>
    build featureProof architectureProof deterministicProof roundingProof
      commandProof checkerProof fingerprintProof buildProof archiveProof
      fallbackProof auditProof

theorem ay_cfmg_contract_feature
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    cpuFeatureManifestDigest :=
  fun contract =>
    contract cpuFeatureManifestDigest
      (fun featureProof _architectureProof _deterministicProof
          _roundingProof _commandProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof =>
        featureProof)

theorem ay_cfmg_contract_architecture
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    architectureIsaLedger :=
  fun contract =>
    contract architectureIsaLedger
      (fun _featureProof architectureProof _deterministicProof
          _roundingProof _commandProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof =>
        architectureProof)

theorem ay_cfmg_contract_determinism
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    deterministicModeWitness :=
  fun contract =>
    contract deterministicModeWitness
      (fun _featureProof _architectureProof deterministicProof
          _roundingProof _commandProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof =>
        deterministicProof)

theorem ay_cfmg_contract_rounding
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    floatingRoundingIrrelevanceWitness :=
  fun contract =>
    contract floatingRoundingIrrelevanceWitness
      (fun _featureProof _architectureProof _deterministicProof
          roundingProof _commandProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof =>
        roundingProof)

theorem ay_cfmg_contract_command
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    solverCommandManifest :=
  fun contract =>
    contract solverCommandManifest
      (fun _featureProof _architectureProof _deterministicProof
          _roundingProof commandProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof =>
        commandProof)

theorem ay_cfmg_contract_checker
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _featureProof _architectureProof _deterministicProof
          _roundingProof _commandProof checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof =>
        checkerProof)

theorem ay_cfmg_contract_fingerprint
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _featureProof _architectureProof _deterministicProof
          _roundingProof _commandProof _checkerProof fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof =>
        fingerprintProof)

theorem ay_cfmg_contract_build
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _featureProof _architectureProof _deterministicProof
          _roundingProof _commandProof _checkerProof _fingerprintProof
          buildProof _archiveProof _fallbackProof _auditProof => buildProof)

theorem ay_cfmg_contract_archive
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _featureProof _architectureProof _deterministicProof
          _roundingProof _commandProof _checkerProof _fingerprintProof
          _buildProof archiveProof _fallbackProof _auditProof => archiveProof)

theorem ay_cfmg_contract_fallback
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _featureProof _architectureProof _deterministicProof
          _roundingProof _commandProof _checkerProof _fingerprintProof
          _buildProof _archiveProof fallbackProof _auditProof => fallbackProof)

theorem ay_cfmg_contract_audit
    (cpuFeatureManifestDigest architectureIsaLedger deterministicModeWitness
      floatingRoundingIrrelevanceWitness solverCommandManifest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cfmg_cpu_contract cpuFeatureManifestDigest architectureIsaLedger
      deterministicModeWitness floatingRoundingIrrelevanceWitness
      solverCommandManifest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackNoClaimPath
      auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _featureProof _architectureProof _deterministicProof
          _roundingProof _commandProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof auditProof => auditProof)

theorem ay_cfmg_sat_publication_intro
    (cpuContract acceptedCpuFeatures checkedModel originalModel : Prop) :
    cpuContract -> acceptedCpuFeatures -> checkedModel -> originalModel ->
    ay_cfmg_sat_publication cpuContract acceptedCpuFeatures checkedModel
      originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_cfmg_conj_intro cpuContract
      (ay_cfmg_conj acceptedCpuFeatures
        (ay_cfmg_conj checkedModel originalModel))
      contractProof
      (ay_cfmg_conj_intro acceptedCpuFeatures
        (ay_cfmg_conj checkedModel originalModel)
        acceptedProof
        (ay_cfmg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_cfmg_unsat_publication_intro
    (cpuContract acceptedCpuFeatures checkedProof originalEmptyClause :
      Prop) :
    cpuContract -> acceptedCpuFeatures -> checkedProof ->
    originalEmptyClause ->
    ay_cfmg_unsat_publication cpuContract acceptedCpuFeatures checkedProof
      originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_cfmg_conj_intro cpuContract
      (ay_cfmg_conj acceptedCpuFeatures
        (ay_cfmg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_cfmg_conj_intro acceptedCpuFeatures
        (ay_cfmg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_cfmg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_cfmg_sat_publication_original_model
    (cpuContract acceptedCpuFeatures checkedModel originalModel : Prop) :
    ay_cfmg_sat_publication cpuContract acceptedCpuFeatures checkedModel
      originalModel ->
    originalModel :=
  fun publication =>
    ay_cfmg_conj_right checkedModel originalModel
      (ay_cfmg_conj_right acceptedCpuFeatures
        (ay_cfmg_conj checkedModel originalModel)
        (ay_cfmg_conj_right cpuContract
          (ay_cfmg_conj acceptedCpuFeatures
            (ay_cfmg_conj checkedModel originalModel))
          publication))

theorem ay_cfmg_unsat_publication_original_empty_clause
    (cpuContract acceptedCpuFeatures checkedProof originalEmptyClause :
      Prop) :
    ay_cfmg_unsat_publication cpuContract acceptedCpuFeatures checkedProof
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_cfmg_conj_right checkedProof originalEmptyClause
      (ay_cfmg_conj_right acceptedCpuFeatures
        (ay_cfmg_conj checkedProof originalEmptyClause)
        (ay_cfmg_conj_right cpuContract
          (ay_cfmg_conj acceptedCpuFeatures
            (ay_cfmg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_cfmg_accepted_cpu_preserves_sat_publication
    (cpuContract acceptedCpuFeatures checkedModel originalModel : Prop) :
    ay_cfmg_sat_publication cpuContract acceptedCpuFeatures checkedModel
      originalModel ->
    ay_cfmg_public_result originalModel False False :=
  fun publication =>
    ay_cfmg_disj_left originalModel (ay_cfmg_disj False False)
      (ay_cfmg_sat_publication_original_model cpuContract
        acceptedCpuFeatures checkedModel originalModel publication)

theorem ay_cfmg_accepted_cpu_preserves_unsat_publication
    (cpuContract acceptedCpuFeatures checkedProof originalEmptyClause :
      Prop) :
    ay_cfmg_unsat_publication cpuContract acceptedCpuFeatures checkedProof
      originalEmptyClause ->
    ay_cfmg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_cfmg_disj_right False (ay_cfmg_disj originalEmptyClause False)
      (ay_cfmg_disj_left originalEmptyClause False
        (ay_cfmg_unsat_publication_original_empty_clause cpuContract
          acceptedCpuFeatures checkedProof originalEmptyClause publication))

theorem ay_cfmg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_cfmg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_cfmg_conj_intro reason (ay_cfmg_conj fallbackPath auditTrail)
      reasonProof
      (ay_cfmg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_cfmg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_cfmg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_cfmg_conj_intro reason
      (ay_cfmg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_cfmg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_cfmg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_cfmg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_cfmg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_cfmg_conj_right reason
        (ay_cfmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_cfmg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_cfmg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_cfmg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_cfmg_conj_right reason
        (ay_cfmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_cfmg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_cfmg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_cfmg_conj_intro reason
      (ay_cfmg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_cfmg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_cfmg_cpu_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cfmg_blocked_publication satFact unsatFact reason ->
    ay_cfmg_recompute reason fallbackPath recomputeObligation ->
    ay_cfmg_cpu_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_cfmg_conj_intro
      (ay_cfmg_blocked_publication satFact unsatFact reason)
      (ay_cfmg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_cfmg_cpu_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cfmg_cpu_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_cfmg_blocked_publication_no_sat satFact unsatFact reason
      (ay_cfmg_conj_left
        (ay_cfmg_blocked_publication satFact unsatFact reason)
        (ay_cfmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_cfmg_cpu_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cfmg_cpu_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_cfmg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_cfmg_conj_left
        (ay_cfmg_blocked_publication satFact unsatFact reason)
        (ay_cfmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_cfmg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cfmg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_cfmg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_cfmg_feature_mismatch_forces_no_claim
    (satFact unsatFact featureMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    featureMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cfmg_no_claim featureMismatch fallbackPath auditTrail :=
  ay_cfmg_mismatch_forces_no_claim satFact unsatFact featureMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cfmg_architecture_mismatch_forces_no_claim
    (satFact unsatFact architectureMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    architectureMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cfmg_no_claim architectureMismatch fallbackPath auditTrail :=
  ay_cfmg_mismatch_forces_no_claim satFact unsatFact architectureMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cfmg_determinism_mismatch_forces_no_claim
    (satFact unsatFact determinismMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    determinismMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cfmg_no_claim determinismMismatch fallbackPath auditTrail :=
  ay_cfmg_mismatch_forces_no_claim satFact unsatFact determinismMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cfmg_rounding_mismatch_forces_no_claim
    (satFact unsatFact roundingMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    roundingMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cfmg_no_claim roundingMismatch fallbackPath auditTrail :=
  ay_cfmg_mismatch_forces_no_claim satFact unsatFact roundingMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cfmg_command_mismatch_forces_no_claim
    (satFact unsatFact commandMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    commandMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cfmg_no_claim commandMismatch fallbackPath auditTrail :=
  ay_cfmg_mismatch_forces_no_claim satFact unsatFact commandMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cfmg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cfmg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_cfmg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cfmg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cfmg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_cfmg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cfmg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cfmg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_cfmg_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cfmg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cfmg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_cfmg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cfmg_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_cfmg_no_claim auditMismatch fallbackPath auditTrail :=
  ay_cfmg_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_cfmg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_cfmg_cpu_failure satFact unsatFact fallbackActivation fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_cfmg_cpu_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_cfmg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_cfmg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_cfmg_failed_cpu_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cfmg_cpu_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_cfmg_cpu_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_cfmg_failed_cpu_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_cfmg_cpu_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_cfmg_cpu_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_cfmg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_cfmg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_cfmg_conj_left reason (ay_cfmg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_cfmg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_cfmg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_cfmg_conj_left reason (ay_cfmg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
