-- SAT-COMP validator checker reproducibility guard core.
--
-- Public SAT/UNSAT claims require two independent checker transcripts or replay
-- hashes, deterministic checker version manifest, benchmark fingerprint,
-- certificate/model digest, solver build evidence, archive manifest, fallback
-- baseline, and audit transcript to agree.

def ay_crpg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_crpg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_crpg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_crpg_disj satFact (ay_crpg_disj unsatFact noClaimFact)

def ay_crpg_repro_contract
    (firstCheckerReplay secondCheckerReplay deterministicCheckerVersion
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (firstCheckerReplay -> secondCheckerReplay ->
      deterministicCheckerVersion -> benchmarkFingerprint ->
      certificateModelArtifactDigest -> solverBuildEvidence ->
      archiveManifest -> fallbackBaseline -> auditTranscript -> result) ->
    result

def ay_crpg_sat_publication
    (reproContract reproducibleAcceptance modelEvidence originalModel :
      Prop) : Prop :=
  ay_crpg_conj reproContract
    (ay_crpg_conj reproducibleAcceptance
      (ay_crpg_conj modelEvidence originalModel))

def ay_crpg_unsat_publication
    (reproContract reproducibleAcceptance proofEvidence originalEmptyClause :
      Prop) : Prop :=
  ay_crpg_conj reproContract
    (ay_crpg_conj reproducibleAcceptance
      (ay_crpg_conj proofEvidence originalEmptyClause))

def ay_crpg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_crpg_conj reason (ay_crpg_conj fallbackPath auditTrail)

def ay_crpg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_crpg_conj reason
    (ay_crpg_conj (satFact -> False) (unsatFact -> False))

def ay_crpg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_crpg_conj reason
    (ay_crpg_conj fallbackPath recomputeObligation)

def ay_crpg_repro_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_crpg_conj
    (ay_crpg_blocked_publication satFact unsatFact reason)
    (ay_crpg_recompute reason fallbackPath recomputeObligation)

theorem ay_crpg_conj_intro (left right : Prop) :
    left -> right -> ay_crpg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_crpg_conj_left (left right : Prop) :
    ay_crpg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_crpg_conj_right (left right : Prop) :
    ay_crpg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_crpg_disj_left (left right : Prop) :
    left -> ay_crpg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_crpg_disj_right (left right : Prop) :
    right -> ay_crpg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_crpg_repro_contract_intro
    (firstCheckerReplay secondCheckerReplay deterministicCheckerVersion
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    firstCheckerReplay -> secondCheckerReplay ->
    deterministicCheckerVersion -> benchmarkFingerprint ->
    certificateModelArtifactDigest -> solverBuildEvidence ->
    archiveManifest -> fallbackBaseline -> auditTranscript ->
    ay_crpg_repro_contract firstCheckerReplay secondCheckerReplay
      deterministicCheckerVersion benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline auditTranscript :=
  fun firstProof secondProof versionProof fingerprintProof certificateProof
      buildProof archiveProof fallbackProof auditProof result build =>
    build firstProof secondProof versionProof fingerprintProof
      certificateProof buildProof archiveProof fallbackProof auditProof

theorem ay_crpg_repro_contract_first_replay
    (firstCheckerReplay secondCheckerReplay deterministicCheckerVersion
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_crpg_repro_contract firstCheckerReplay secondCheckerReplay
      deterministicCheckerVersion benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline auditTranscript ->
    firstCheckerReplay :=
  fun contract =>
    contract firstCheckerReplay
      (fun firstProof _secondProof _versionProof _fingerprintProof
          _certificateProof _buildProof _archiveProof _fallbackProof
          _auditProof => firstProof)

theorem ay_crpg_repro_contract_second_replay
    (firstCheckerReplay secondCheckerReplay deterministicCheckerVersion
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_crpg_repro_contract firstCheckerReplay secondCheckerReplay
      deterministicCheckerVersion benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline auditTranscript ->
    secondCheckerReplay :=
  fun contract =>
    contract secondCheckerReplay
      (fun _firstProof secondProof _versionProof _fingerprintProof
          _certificateProof _buildProof _archiveProof _fallbackProof
          _auditProof => secondProof)

theorem ay_crpg_repro_contract_version
    (firstCheckerReplay secondCheckerReplay deterministicCheckerVersion
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_crpg_repro_contract firstCheckerReplay secondCheckerReplay
      deterministicCheckerVersion benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline auditTranscript ->
    deterministicCheckerVersion :=
  fun contract =>
    contract deterministicCheckerVersion
      (fun _firstProof _secondProof versionProof _fingerprintProof
          _certificateProof _buildProof _archiveProof _fallbackProof
          _auditProof => versionProof)

theorem ay_crpg_repro_contract_fingerprint
    (firstCheckerReplay secondCheckerReplay deterministicCheckerVersion
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_crpg_repro_contract firstCheckerReplay secondCheckerReplay
      deterministicCheckerVersion benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _firstProof _secondProof _versionProof fingerprintProof
          _certificateProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_crpg_repro_contract_certificate
    (firstCheckerReplay secondCheckerReplay deterministicCheckerVersion
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_crpg_repro_contract firstCheckerReplay secondCheckerReplay
      deterministicCheckerVersion benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline auditTranscript ->
    certificateModelArtifactDigest :=
  fun contract =>
    contract certificateModelArtifactDigest
      (fun _firstProof _secondProof _versionProof _fingerprintProof
          certificateProof _buildProof _archiveProof _fallbackProof
          _auditProof => certificateProof)

theorem ay_crpg_repro_contract_build
    (firstCheckerReplay secondCheckerReplay deterministicCheckerVersion
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_crpg_repro_contract firstCheckerReplay secondCheckerReplay
      deterministicCheckerVersion benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _firstProof _secondProof _versionProof _fingerprintProof
          _certificateProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_crpg_repro_contract_archive
    (firstCheckerReplay secondCheckerReplay deterministicCheckerVersion
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_crpg_repro_contract firstCheckerReplay secondCheckerReplay
      deterministicCheckerVersion benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _firstProof _secondProof _versionProof _fingerprintProof
          _certificateProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_crpg_repro_contract_fallback
    (firstCheckerReplay secondCheckerReplay deterministicCheckerVersion
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_crpg_repro_contract firstCheckerReplay secondCheckerReplay
      deterministicCheckerVersion benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline auditTranscript ->
    fallbackBaseline :=
  fun contract =>
    contract fallbackBaseline
      (fun _firstProof _secondProof _versionProof _fingerprintProof
          _certificateProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_crpg_repro_contract_audit
    (firstCheckerReplay secondCheckerReplay deterministicCheckerVersion
      benchmarkFingerprint certificateModelArtifactDigest solverBuildEvidence
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_crpg_repro_contract firstCheckerReplay secondCheckerReplay
      deterministicCheckerVersion benchmarkFingerprint
      certificateModelArtifactDigest solverBuildEvidence archiveManifest
      fallbackBaseline auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _firstProof _secondProof _versionProof _fingerprintProof
          _certificateProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_crpg_sat_publication_intro
    (reproContract reproducibleAcceptance modelEvidence originalModel :
      Prop) :
    reproContract -> reproducibleAcceptance -> modelEvidence ->
    originalModel ->
    ay_crpg_sat_publication reproContract reproducibleAcceptance
      modelEvidence originalModel :=
  fun contractProof acceptanceProof modelProof originalProof =>
    ay_crpg_conj_intro reproContract
      (ay_crpg_conj reproducibleAcceptance
        (ay_crpg_conj modelEvidence originalModel)) contractProof
      (ay_crpg_conj_intro reproducibleAcceptance
        (ay_crpg_conj modelEvidence originalModel) acceptanceProof
        (ay_crpg_conj_intro modelEvidence originalModel modelProof
          originalProof))

theorem ay_crpg_sat_publication_reproducible
    (reproContract reproducibleAcceptance modelEvidence originalModel :
      Prop) :
    ay_crpg_sat_publication reproContract reproducibleAcceptance modelEvidence
      originalModel ->
    reproducibleAcceptance :=
  fun publication =>
    ay_crpg_conj_left reproducibleAcceptance
      (ay_crpg_conj modelEvidence originalModel)
      (ay_crpg_conj_right reproContract
        (ay_crpg_conj reproducibleAcceptance
          (ay_crpg_conj modelEvidence originalModel)) publication)

theorem ay_crpg_sat_publication_original_model
    (reproContract reproducibleAcceptance modelEvidence originalModel :
      Prop) :
    ay_crpg_sat_publication reproContract reproducibleAcceptance modelEvidence
      originalModel ->
    originalModel :=
  fun publication =>
    ay_crpg_conj_right modelEvidence originalModel
      (ay_crpg_conj_right reproducibleAcceptance
        (ay_crpg_conj modelEvidence originalModel)
        (ay_crpg_conj_right reproContract
          (ay_crpg_conj reproducibleAcceptance
            (ay_crpg_conj modelEvidence originalModel)) publication))

theorem ay_crpg_unsat_publication_intro
    (reproContract reproducibleAcceptance proofEvidence originalEmptyClause :
      Prop) :
    reproContract -> reproducibleAcceptance -> proofEvidence ->
    originalEmptyClause ->
    ay_crpg_unsat_publication reproContract reproducibleAcceptance
      proofEvidence originalEmptyClause :=
  fun contractProof acceptanceProof proofProof emptyProof =>
    ay_crpg_conj_intro reproContract
      (ay_crpg_conj reproducibleAcceptance
        (ay_crpg_conj proofEvidence originalEmptyClause)) contractProof
      (ay_crpg_conj_intro reproducibleAcceptance
        (ay_crpg_conj proofEvidence originalEmptyClause) acceptanceProof
        (ay_crpg_conj_intro proofEvidence originalEmptyClause proofProof
          emptyProof))

theorem ay_crpg_unsat_publication_reproducible
    (reproContract reproducibleAcceptance proofEvidence originalEmptyClause :
      Prop) :
    ay_crpg_unsat_publication reproContract reproducibleAcceptance
      proofEvidence originalEmptyClause ->
    reproducibleAcceptance :=
  fun publication =>
    ay_crpg_conj_left reproducibleAcceptance
      (ay_crpg_conj proofEvidence originalEmptyClause)
      (ay_crpg_conj_right reproContract
        (ay_crpg_conj reproducibleAcceptance
          (ay_crpg_conj proofEvidence originalEmptyClause)) publication)

theorem ay_crpg_unsat_publication_original_empty_clause
    (reproContract reproducibleAcceptance proofEvidence originalEmptyClause :
      Prop) :
    ay_crpg_unsat_publication reproContract reproducibleAcceptance
      proofEvidence originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_crpg_conj_right proofEvidence originalEmptyClause
      (ay_crpg_conj_right reproducibleAcceptance
        (ay_crpg_conj proofEvidence originalEmptyClause)
        (ay_crpg_conj_right reproContract
          (ay_crpg_conj reproducibleAcceptance
            (ay_crpg_conj proofEvidence originalEmptyClause)) publication))

theorem ay_crpg_accepted_reproducible_sat_is_public_path
    (reproContract reproducibleAcceptance modelEvidence originalModel :
      Prop) :
    ay_crpg_sat_publication reproContract reproducibleAcceptance modelEvidence
      originalModel ->
    ay_crpg_conj reproducibleAcceptance originalModel :=
  fun publication =>
    ay_crpg_conj_intro reproducibleAcceptance originalModel
      (ay_crpg_sat_publication_reproducible reproContract
        reproducibleAcceptance modelEvidence originalModel publication)
      (ay_crpg_sat_publication_original_model reproContract
        reproducibleAcceptance modelEvidence originalModel publication)

theorem ay_crpg_accepted_reproducible_unsat_is_public_path
    (reproContract reproducibleAcceptance proofEvidence originalEmptyClause :
      Prop) :
    ay_crpg_unsat_publication reproContract reproducibleAcceptance
      proofEvidence originalEmptyClause ->
    ay_crpg_conj reproducibleAcceptance originalEmptyClause :=
  fun publication =>
    ay_crpg_conj_intro reproducibleAcceptance originalEmptyClause
      (ay_crpg_unsat_publication_reproducible reproContract
        reproducibleAcceptance proofEvidence originalEmptyClause publication)
      (ay_crpg_unsat_publication_original_empty_clause reproContract
        reproducibleAcceptance proofEvidence originalEmptyClause publication)

theorem ay_crpg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_crpg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_crpg_conj_intro reason (ay_crpg_conj fallbackPath auditTrail)
      reasonProof
      (ay_crpg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_crpg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_crpg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_crpg_conj_intro reason
      (ay_crpg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_crpg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_crpg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_crpg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_crpg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_crpg_conj_right reason
        (ay_crpg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_crpg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_crpg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_crpg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_crpg_conj_right reason
        (ay_crpg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_crpg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_crpg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_crpg_conj_intro reason
      (ay_crpg_conj fallbackPath recomputeObligation) reasonProof
      (ay_crpg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_crpg_repro_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_crpg_repro_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_crpg_conj_intro
      (ay_crpg_blocked_publication satFact unsatFact reason)
      (ay_crpg_recompute reason fallbackPath recomputeObligation)
      (ay_crpg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_crpg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_crpg_repro_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_crpg_repro_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_crpg_blocked_publication_no_sat satFact unsatFact reason
      (ay_crpg_conj_left
        (ay_crpg_blocked_publication satFact unsatFact reason)
        (ay_crpg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_crpg_repro_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_crpg_repro_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_crpg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_crpg_conj_left
        (ay_crpg_blocked_publication satFact unsatFact reason)
        (ay_crpg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_crpg_repro_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_crpg_repro_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_crpg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_crpg_conj_right
      (ay_crpg_blocked_publication satFact unsatFact reason)
      (ay_crpg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_crpg_transient_disagreement_forces_no_claim
    (satFact unsatFact transientDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    transientDisagreement -> fallbackPath -> auditTrail ->
    recomputeObligation -> (satFact -> False) -> (unsatFact -> False) ->
    ay_crpg_no_claim transientDisagreement fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_crpg_no_claim_intro transientDisagreement fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_crpg_nondeterministic_disagreement_forces_no_claim
    (satFact unsatFact nondeterministicDisagreement fallbackPath auditTrail
      recomputeObligation : Prop) :
    nondeterministicDisagreement -> fallbackPath -> auditTrail ->
    recomputeObligation -> (satFact -> False) -> (unsatFact -> False) ->
    ay_crpg_no_claim nondeterministicDisagreement fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_crpg_no_claim_intro nondeterministicDisagreement fallbackPath
      auditTrail reasonProof fallbackProof auditProof

theorem ay_crpg_stale_checker_version_forces_no_claim
    (satFact unsatFact staleCheckerVersion fallbackPath auditTrail
      recomputeObligation : Prop) :
    staleCheckerVersion -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_crpg_no_claim staleCheckerVersion fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_crpg_no_claim_intro staleCheckerVersion fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_crpg_benchmark_mismatch_forces_no_claim
    (satFact unsatFact benchmarkMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    benchmarkMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_crpg_no_claim benchmarkMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_crpg_no_claim_intro benchmarkMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_crpg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_crpg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_crpg_no_claim_intro buildMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_crpg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_crpg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_crpg_no_claim_intro archiveMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_crpg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivated fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_crpg_no_claim fallbackActivated fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_crpg_no_claim_intro fallbackActivated fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_crpg_failed_repro_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_crpg_repro_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_crpg_repro_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_crpg_failed_repro_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_crpg_repro_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_crpg_repro_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_crpg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_crpg_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_crpg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_crpg_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
