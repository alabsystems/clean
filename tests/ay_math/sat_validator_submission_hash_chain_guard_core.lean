-- SAT-COMP validator submission hash-chain guard core.
--
-- Public SAT/UNSAT claims require benchmark fingerprint, solver build digest,
-- result artifact digest, certificate/model digest, checker transcript digest,
-- archive manifest digest, parent hash-chain link, no-claim fallback, and audit
-- transcript to agree.

def ay_shcg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_shcg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_shcg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_shcg_disj satFact (ay_shcg_disj unsatFact noClaimFact)

def ay_shcg_chain_contract
    (benchmarkFingerprint solverBuildDigest resultArtifactDigest
      certificateModelDigest checkerTranscriptDigest archiveManifestDigest
      parentHashChainLink noClaimFallback auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint -> solverBuildDigest -> resultArtifactDigest ->
      certificateModelDigest -> checkerTranscriptDigest ->
      archiveManifestDigest -> parentHashChainLink -> noClaimFallback ->
      auditTranscript -> result) ->
    result

def ay_shcg_sat_publication
    (chainContract acceptedHashChain modelEvidence originalModel : Prop) :
    Prop :=
  ay_shcg_conj chainContract
    (ay_shcg_conj acceptedHashChain
      (ay_shcg_conj modelEvidence originalModel))

def ay_shcg_unsat_publication
    (chainContract acceptedHashChain proofEvidence originalEmptyClause :
      Prop) : Prop :=
  ay_shcg_conj chainContract
    (ay_shcg_conj acceptedHashChain
      (ay_shcg_conj proofEvidence originalEmptyClause))

def ay_shcg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_shcg_conj reason (ay_shcg_conj fallbackPath auditTrail)

def ay_shcg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_shcg_conj reason
    (ay_shcg_conj (satFact -> False) (unsatFact -> False))

def ay_shcg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_shcg_conj reason
    (ay_shcg_conj fallbackPath recomputeObligation)

def ay_shcg_chain_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_shcg_conj
    (ay_shcg_blocked_publication satFact unsatFact reason)
    (ay_shcg_recompute reason fallbackPath recomputeObligation)

theorem ay_shcg_conj_intro (left right : Prop) :
    left -> right -> ay_shcg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_shcg_conj_left (left right : Prop) :
    ay_shcg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_shcg_conj_right (left right : Prop) :
    ay_shcg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_shcg_disj_left (left right : Prop) :
    left -> ay_shcg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_shcg_disj_right (left right : Prop) :
    right -> ay_shcg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_shcg_chain_contract_intro
    (benchmarkFingerprint solverBuildDigest resultArtifactDigest
      certificateModelDigest checkerTranscriptDigest archiveManifestDigest
      parentHashChainLink noClaimFallback auditTranscript : Prop) :
    benchmarkFingerprint -> solverBuildDigest -> resultArtifactDigest ->
    certificateModelDigest -> checkerTranscriptDigest ->
    archiveManifestDigest -> parentHashChainLink -> noClaimFallback ->
    auditTranscript ->
    ay_shcg_chain_contract benchmarkFingerprint solverBuildDigest
      resultArtifactDigest certificateModelDigest checkerTranscriptDigest
      archiveManifestDigest parentHashChainLink noClaimFallback
      auditTranscript :=
  fun fingerprintProof buildProof resultProof certificateProof checkerProof
      archiveProof parentProof fallbackProof auditProof result build =>
    build fingerprintProof buildProof resultProof certificateProof
      checkerProof archiveProof parentProof fallbackProof auditProof

theorem ay_shcg_chain_contract_fingerprint
    (benchmarkFingerprint solverBuildDigest resultArtifactDigest
      certificateModelDigest checkerTranscriptDigest archiveManifestDigest
      parentHashChainLink noClaimFallback auditTranscript : Prop) :
    ay_shcg_chain_contract benchmarkFingerprint solverBuildDigest
      resultArtifactDigest certificateModelDigest checkerTranscriptDigest
      archiveManifestDigest parentHashChainLink noClaimFallback
      auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun fingerprintProof _buildProof _resultProof _certificateProof
          _checkerProof _archiveProof _parentProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_shcg_chain_contract_build
    (benchmarkFingerprint solverBuildDigest resultArtifactDigest
      certificateModelDigest checkerTranscriptDigest archiveManifestDigest
      parentHashChainLink noClaimFallback auditTranscript : Prop) :
    ay_shcg_chain_contract benchmarkFingerprint solverBuildDigest
      resultArtifactDigest certificateModelDigest checkerTranscriptDigest
      archiveManifestDigest parentHashChainLink noClaimFallback
      auditTranscript ->
    solverBuildDigest :=
  fun contract =>
    contract solverBuildDigest
      (fun _fingerprintProof buildProof _resultProof _certificateProof
          _checkerProof _archiveProof _parentProof _fallbackProof
          _auditProof => buildProof)

theorem ay_shcg_chain_contract_result_digest
    (benchmarkFingerprint solverBuildDigest resultArtifactDigest
      certificateModelDigest checkerTranscriptDigest archiveManifestDigest
      parentHashChainLink noClaimFallback auditTranscript : Prop) :
    ay_shcg_chain_contract benchmarkFingerprint solverBuildDigest
      resultArtifactDigest certificateModelDigest checkerTranscriptDigest
      archiveManifestDigest parentHashChainLink noClaimFallback
      auditTranscript ->
    resultArtifactDigest :=
  fun contract =>
    contract resultArtifactDigest
      (fun _fingerprintProof _buildProof resultProof _certificateProof
          _checkerProof _archiveProof _parentProof _fallbackProof
          _auditProof => resultProof)

theorem ay_shcg_chain_contract_certificate_digest
    (benchmarkFingerprint solverBuildDigest resultArtifactDigest
      certificateModelDigest checkerTranscriptDigest archiveManifestDigest
      parentHashChainLink noClaimFallback auditTranscript : Prop) :
    ay_shcg_chain_contract benchmarkFingerprint solverBuildDigest
      resultArtifactDigest certificateModelDigest checkerTranscriptDigest
      archiveManifestDigest parentHashChainLink noClaimFallback
      auditTranscript ->
    certificateModelDigest :=
  fun contract =>
    contract certificateModelDigest
      (fun _fingerprintProof _buildProof _resultProof certificateProof
          _checkerProof _archiveProof _parentProof _fallbackProof
          _auditProof => certificateProof)

theorem ay_shcg_chain_contract_checker_digest
    (benchmarkFingerprint solverBuildDigest resultArtifactDigest
      certificateModelDigest checkerTranscriptDigest archiveManifestDigest
      parentHashChainLink noClaimFallback auditTranscript : Prop) :
    ay_shcg_chain_contract benchmarkFingerprint solverBuildDigest
      resultArtifactDigest certificateModelDigest checkerTranscriptDigest
      archiveManifestDigest parentHashChainLink noClaimFallback
      auditTranscript ->
    checkerTranscriptDigest :=
  fun contract =>
    contract checkerTranscriptDigest
      (fun _fingerprintProof _buildProof _resultProof _certificateProof
          checkerProof _archiveProof _parentProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_shcg_chain_contract_archive_digest
    (benchmarkFingerprint solverBuildDigest resultArtifactDigest
      certificateModelDigest checkerTranscriptDigest archiveManifestDigest
      parentHashChainLink noClaimFallback auditTranscript : Prop) :
    ay_shcg_chain_contract benchmarkFingerprint solverBuildDigest
      resultArtifactDigest certificateModelDigest checkerTranscriptDigest
      archiveManifestDigest parentHashChainLink noClaimFallback
      auditTranscript ->
    archiveManifestDigest :=
  fun contract =>
    contract archiveManifestDigest
      (fun _fingerprintProof _buildProof _resultProof _certificateProof
          _checkerProof archiveProof _parentProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_shcg_chain_contract_parent_link
    (benchmarkFingerprint solverBuildDigest resultArtifactDigest
      certificateModelDigest checkerTranscriptDigest archiveManifestDigest
      parentHashChainLink noClaimFallback auditTranscript : Prop) :
    ay_shcg_chain_contract benchmarkFingerprint solverBuildDigest
      resultArtifactDigest certificateModelDigest checkerTranscriptDigest
      archiveManifestDigest parentHashChainLink noClaimFallback
      auditTranscript ->
    parentHashChainLink :=
  fun contract =>
    contract parentHashChainLink
      (fun _fingerprintProof _buildProof _resultProof _certificateProof
          _checkerProof _archiveProof parentProof _fallbackProof
          _auditProof => parentProof)

theorem ay_shcg_chain_contract_fallback
    (benchmarkFingerprint solverBuildDigest resultArtifactDigest
      certificateModelDigest checkerTranscriptDigest archiveManifestDigest
      parentHashChainLink noClaimFallback auditTranscript : Prop) :
    ay_shcg_chain_contract benchmarkFingerprint solverBuildDigest
      resultArtifactDigest certificateModelDigest checkerTranscriptDigest
      archiveManifestDigest parentHashChainLink noClaimFallback
      auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _fingerprintProof _buildProof _resultProof _certificateProof
          _checkerProof _archiveProof _parentProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_shcg_chain_contract_audit
    (benchmarkFingerprint solverBuildDigest resultArtifactDigest
      certificateModelDigest checkerTranscriptDigest archiveManifestDigest
      parentHashChainLink noClaimFallback auditTranscript : Prop) :
    ay_shcg_chain_contract benchmarkFingerprint solverBuildDigest
      resultArtifactDigest certificateModelDigest checkerTranscriptDigest
      archiveManifestDigest parentHashChainLink noClaimFallback
      auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _fingerprintProof _buildProof _resultProof _certificateProof
          _checkerProof _archiveProof _parentProof _fallbackProof
          auditProof => auditProof)

theorem ay_shcg_sat_publication_intro
    (chainContract acceptedHashChain modelEvidence originalModel : Prop) :
    chainContract -> acceptedHashChain -> modelEvidence -> originalModel ->
    ay_shcg_sat_publication chainContract acceptedHashChain modelEvidence
      originalModel :=
  fun contractProof chainProof modelProof originalProof =>
    ay_shcg_conj_intro chainContract
      (ay_shcg_conj acceptedHashChain
        (ay_shcg_conj modelEvidence originalModel)) contractProof
      (ay_shcg_conj_intro acceptedHashChain
        (ay_shcg_conj modelEvidence originalModel) chainProof
        (ay_shcg_conj_intro modelEvidence originalModel modelProof
          originalProof))

theorem ay_shcg_sat_publication_chain
    (chainContract acceptedHashChain modelEvidence originalModel : Prop) :
    ay_shcg_sat_publication chainContract acceptedHashChain modelEvidence
      originalModel ->
    acceptedHashChain :=
  fun publication =>
    ay_shcg_conj_left acceptedHashChain
      (ay_shcg_conj modelEvidence originalModel)
      (ay_shcg_conj_right chainContract
        (ay_shcg_conj acceptedHashChain
          (ay_shcg_conj modelEvidence originalModel)) publication)

theorem ay_shcg_sat_publication_original_model
    (chainContract acceptedHashChain modelEvidence originalModel : Prop) :
    ay_shcg_sat_publication chainContract acceptedHashChain modelEvidence
      originalModel ->
    originalModel :=
  fun publication =>
    ay_shcg_conj_right modelEvidence originalModel
      (ay_shcg_conj_right acceptedHashChain
        (ay_shcg_conj modelEvidence originalModel)
        (ay_shcg_conj_right chainContract
          (ay_shcg_conj acceptedHashChain
            (ay_shcg_conj modelEvidence originalModel)) publication))

theorem ay_shcg_unsat_publication_intro
    (chainContract acceptedHashChain proofEvidence originalEmptyClause :
      Prop) :
    chainContract -> acceptedHashChain -> proofEvidence ->
    originalEmptyClause ->
    ay_shcg_unsat_publication chainContract acceptedHashChain proofEvidence
      originalEmptyClause :=
  fun contractProof chainProof proofProof emptyProof =>
    ay_shcg_conj_intro chainContract
      (ay_shcg_conj acceptedHashChain
        (ay_shcg_conj proofEvidence originalEmptyClause)) contractProof
      (ay_shcg_conj_intro acceptedHashChain
        (ay_shcg_conj proofEvidence originalEmptyClause) chainProof
        (ay_shcg_conj_intro proofEvidence originalEmptyClause proofProof
          emptyProof))

theorem ay_shcg_unsat_publication_chain
    (chainContract acceptedHashChain proofEvidence originalEmptyClause :
      Prop) :
    ay_shcg_unsat_publication chainContract acceptedHashChain proofEvidence
      originalEmptyClause ->
    acceptedHashChain :=
  fun publication =>
    ay_shcg_conj_left acceptedHashChain
      (ay_shcg_conj proofEvidence originalEmptyClause)
      (ay_shcg_conj_right chainContract
        (ay_shcg_conj acceptedHashChain
          (ay_shcg_conj proofEvidence originalEmptyClause)) publication)

theorem ay_shcg_unsat_publication_original_empty_clause
    (chainContract acceptedHashChain proofEvidence originalEmptyClause :
      Prop) :
    ay_shcg_unsat_publication chainContract acceptedHashChain proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_shcg_conj_right proofEvidence originalEmptyClause
      (ay_shcg_conj_right acceptedHashChain
        (ay_shcg_conj proofEvidence originalEmptyClause)
        (ay_shcg_conj_right chainContract
          (ay_shcg_conj acceptedHashChain
            (ay_shcg_conj proofEvidence originalEmptyClause)) publication))

theorem ay_shcg_accepted_chain_sat_passes_publication
    (chainContract acceptedHashChain modelEvidence originalModel : Prop) :
    ay_shcg_sat_publication chainContract acceptedHashChain modelEvidence
      originalModel ->
    ay_shcg_conj acceptedHashChain originalModel :=
  fun publication =>
    ay_shcg_conj_intro acceptedHashChain originalModel
      (ay_shcg_sat_publication_chain chainContract acceptedHashChain
        modelEvidence originalModel publication)
      (ay_shcg_sat_publication_original_model chainContract acceptedHashChain
        modelEvidence originalModel publication)

theorem ay_shcg_accepted_chain_unsat_passes_publication
    (chainContract acceptedHashChain proofEvidence originalEmptyClause :
      Prop) :
    ay_shcg_unsat_publication chainContract acceptedHashChain proofEvidence
      originalEmptyClause ->
    ay_shcg_conj acceptedHashChain originalEmptyClause :=
  fun publication =>
    ay_shcg_conj_intro acceptedHashChain originalEmptyClause
      (ay_shcg_unsat_publication_chain chainContract acceptedHashChain
        proofEvidence originalEmptyClause publication)
      (ay_shcg_unsat_publication_original_empty_clause chainContract
        acceptedHashChain proofEvidence originalEmptyClause publication)

theorem ay_shcg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_shcg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_shcg_conj_intro reason (ay_shcg_conj fallbackPath auditTrail)
      reasonProof
      (ay_shcg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_shcg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_shcg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_shcg_conj_intro reason
      (ay_shcg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_shcg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_shcg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_shcg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_shcg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_shcg_conj_right reason
        (ay_shcg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_shcg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_shcg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_shcg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_shcg_conj_right reason
        (ay_shcg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_shcg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_shcg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_shcg_conj_intro reason
      (ay_shcg_conj fallbackPath recomputeObligation) reasonProof
      (ay_shcg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_shcg_chain_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_shcg_chain_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_shcg_conj_intro
      (ay_shcg_blocked_publication satFact unsatFact reason)
      (ay_shcg_recompute reason fallbackPath recomputeObligation)
      (ay_shcg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_shcg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_shcg_chain_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_shcg_chain_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_shcg_blocked_publication_no_sat satFact unsatFact reason
      (ay_shcg_conj_left
        (ay_shcg_blocked_publication satFact unsatFact reason)
        (ay_shcg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_shcg_chain_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_shcg_chain_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_shcg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_shcg_conj_left
        (ay_shcg_blocked_publication satFact unsatFact reason)
        (ay_shcg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_shcg_chain_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_shcg_chain_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_shcg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_shcg_conj_right
      (ay_shcg_blocked_publication satFact unsatFact reason)
      (ay_shcg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_shcg_broken_link_forces_no_claim
    (satFact unsatFact brokenLink fallbackPath auditTrail
      recomputeObligation : Prop) :
    brokenLink -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_shcg_no_claim brokenLink fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_shcg_no_claim_intro brokenLink fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_shcg_stale_link_forces_no_claim
    (satFact unsatFact staleLink fallbackPath auditTrail
      recomputeObligation : Prop) :
    staleLink -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_shcg_no_claim staleLink fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_shcg_no_claim_intro staleLink fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_shcg_reordered_link_forces_no_claim
    (satFact unsatFact reorderedLink fallbackPath auditTrail
      recomputeObligation : Prop) :
    reorderedLink -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_shcg_no_claim reorderedLink fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_shcg_no_claim_intro reorderedLink fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_shcg_artifact_mismatch_forces_no_claim
    (satFact unsatFact artifactMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_shcg_no_claim artifactMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_shcg_no_claim_intro artifactMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_shcg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_shcg_no_claim checkerMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_shcg_no_claim_intro checkerMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_shcg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_shcg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_shcg_no_claim_intro buildMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_shcg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_shcg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_shcg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_shcg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_shcg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_shcg_no_claim_intro archiveMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_shcg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivated fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_shcg_no_claim fallbackActivated fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_shcg_no_claim_intro fallbackActivated fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_shcg_failed_chain_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_shcg_chain_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_shcg_chain_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_shcg_failed_chain_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_shcg_chain_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_shcg_chain_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_shcg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_shcg_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_shcg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_shcg_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
