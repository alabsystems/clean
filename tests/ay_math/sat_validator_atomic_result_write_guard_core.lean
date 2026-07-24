-- SAT-COMP validator atomic result-write guard core.
--
-- Public SAT/UNSAT claims require temp result artifact, fsync/rename commit
-- witness, final artifact digest, checker transcript, benchmark fingerprint,
-- solver build evidence, archive manifest, fallback baseline, no-claim
-- fallback, and audit transcript to agree.

def ay_arwg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_arwg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_arwg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_arwg_disj satFact (ay_arwg_disj unsatFact noClaimFact)

def ay_arwg_atomic_contract
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) : Prop :=
  forall result : Prop,
    (tempResultArtifact -> fsyncRenameCommitWitness -> finalArtifactDigest ->
      checkerTranscript -> benchmarkFingerprint -> solverBuildEvidence ->
      archiveManifest -> fallbackBaseline -> noClaimFallback ->
      auditTranscript -> result) ->
    result

def ay_arwg_sat_publication
    (atomicContract atomicCommitChecked modelEvidence originalModel : Prop) :
    Prop :=
  ay_arwg_conj atomicContract
    (ay_arwg_conj atomicCommitChecked
      (ay_arwg_conj modelEvidence originalModel))

def ay_arwg_unsat_publication
    (atomicContract atomicCommitChecked proofEvidence originalEmptyClause :
      Prop) : Prop :=
  ay_arwg_conj atomicContract
    (ay_arwg_conj atomicCommitChecked
      (ay_arwg_conj proofEvidence originalEmptyClause))

def ay_arwg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_arwg_conj reason (ay_arwg_conj fallbackPath auditTrail)

def ay_arwg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_arwg_conj reason
    (ay_arwg_conj (satFact -> False) (unsatFact -> False))

def ay_arwg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_arwg_conj reason
    (ay_arwg_conj fallbackPath recomputeObligation)

def ay_arwg_write_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_arwg_conj
    (ay_arwg_blocked_publication satFact unsatFact reason)
    (ay_arwg_recompute reason fallbackPath recomputeObligation)

theorem ay_arwg_conj_intro (left right : Prop) :
    left -> right -> ay_arwg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_arwg_conj_left (left right : Prop) :
    ay_arwg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_arwg_conj_right (left right : Prop) :
    ay_arwg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_arwg_disj_left (left right : Prop) :
    left -> ay_arwg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_arwg_disj_right (left right : Prop) :
    right -> ay_arwg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_arwg_atomic_contract_intro
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) :
    tempResultArtifact -> fsyncRenameCommitWitness -> finalArtifactDigest ->
    checkerTranscript -> benchmarkFingerprint -> solverBuildEvidence ->
    archiveManifest -> fallbackBaseline -> noClaimFallback ->
    auditTranscript ->
    ay_arwg_atomic_contract tempResultArtifact fsyncRenameCommitWitness
      finalArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackBaseline noClaimFallback
      auditTranscript :=
  fun tempProof commitProof digestProof checkerProof fingerprintProof
      buildProof archiveProof baselineProof fallbackProof auditProof result
      build =>
    build tempProof commitProof digestProof checkerProof fingerprintProof
      buildProof archiveProof baselineProof fallbackProof auditProof

theorem ay_arwg_atomic_contract_temp
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) :
    ay_arwg_atomic_contract tempResultArtifact fsyncRenameCommitWitness
      finalArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackBaseline noClaimFallback
      auditTranscript ->
    tempResultArtifact :=
  fun contract =>
    contract tempResultArtifact
      (fun tempProof _commitProof _digestProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _baselineProof _fallbackProof
          _auditProof => tempProof)

theorem ay_arwg_atomic_contract_commit
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) :
    ay_arwg_atomic_contract tempResultArtifact fsyncRenameCommitWitness
      finalArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackBaseline noClaimFallback
      auditTranscript ->
    fsyncRenameCommitWitness :=
  fun contract =>
    contract fsyncRenameCommitWitness
      (fun _tempProof commitProof _digestProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _baselineProof _fallbackProof
          _auditProof => commitProof)

theorem ay_arwg_atomic_contract_final_digest
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) :
    ay_arwg_atomic_contract tempResultArtifact fsyncRenameCommitWitness
      finalArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackBaseline noClaimFallback
      auditTranscript ->
    finalArtifactDigest :=
  fun contract =>
    contract finalArtifactDigest
      (fun _tempProof _commitProof digestProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _baselineProof _fallbackProof
          _auditProof => digestProof)

theorem ay_arwg_atomic_contract_checker
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) :
    ay_arwg_atomic_contract tempResultArtifact fsyncRenameCommitWitness
      finalArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackBaseline noClaimFallback
      auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _tempProof _commitProof _digestProof checkerProof _fingerprintProof
          _buildProof _archiveProof _baselineProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_arwg_atomic_contract_fingerprint
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) :
    ay_arwg_atomic_contract tempResultArtifact fsyncRenameCommitWitness
      finalArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackBaseline noClaimFallback
      auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _tempProof _commitProof _digestProof _checkerProof fingerprintProof
          _buildProof _archiveProof _baselineProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_arwg_atomic_contract_build
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) :
    ay_arwg_atomic_contract tempResultArtifact fsyncRenameCommitWitness
      finalArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackBaseline noClaimFallback
      auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _tempProof _commitProof _digestProof _checkerProof _fingerprintProof
          buildProof _archiveProof _baselineProof _fallbackProof _auditProof =>
        buildProof)

theorem ay_arwg_atomic_contract_archive
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) :
    ay_arwg_atomic_contract tempResultArtifact fsyncRenameCommitWitness
      finalArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackBaseline noClaimFallback
      auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _tempProof _commitProof _digestProof _checkerProof _fingerprintProof
          _buildProof archiveProof _baselineProof _fallbackProof _auditProof =>
        archiveProof)

theorem ay_arwg_atomic_contract_baseline
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) :
    ay_arwg_atomic_contract tempResultArtifact fsyncRenameCommitWitness
      finalArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackBaseline noClaimFallback
      auditTranscript ->
    fallbackBaseline :=
  fun contract =>
    contract fallbackBaseline
      (fun _tempProof _commitProof _digestProof _checkerProof _fingerprintProof
          _buildProof _archiveProof baselineProof _fallbackProof _auditProof =>
        baselineProof)

theorem ay_arwg_atomic_contract_fallback
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) :
    ay_arwg_atomic_contract tempResultArtifact fsyncRenameCommitWitness
      finalArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackBaseline noClaimFallback
      auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _tempProof _commitProof _digestProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _baselineProof fallbackProof _auditProof =>
        fallbackProof)

theorem ay_arwg_atomic_contract_audit
    (tempResultArtifact fsyncRenameCommitWitness finalArtifactDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackBaseline noClaimFallback auditTranscript :
      Prop) :
    ay_arwg_atomic_contract tempResultArtifact fsyncRenameCommitWitness
      finalArtifactDigest checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest fallbackBaseline noClaimFallback
      auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _tempProof _commitProof _digestProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _baselineProof _fallbackProof auditProof =>
        auditProof)

theorem ay_arwg_sat_publication_intro
    (atomicContract atomicCommitChecked modelEvidence originalModel : Prop) :
    atomicContract -> atomicCommitChecked -> modelEvidence -> originalModel ->
    ay_arwg_sat_publication atomicContract atomicCommitChecked modelEvidence
      originalModel :=
  fun contractProof atomicProof modelProof originalProof =>
    ay_arwg_conj_intro atomicContract
      (ay_arwg_conj atomicCommitChecked
        (ay_arwg_conj modelEvidence originalModel)) contractProof
      (ay_arwg_conj_intro atomicCommitChecked
        (ay_arwg_conj modelEvidence originalModel) atomicProof
        (ay_arwg_conj_intro modelEvidence originalModel modelProof
          originalProof))

theorem ay_arwg_sat_publication_atomic
    (atomicContract atomicCommitChecked modelEvidence originalModel : Prop) :
    ay_arwg_sat_publication atomicContract atomicCommitChecked modelEvidence
      originalModel ->
    atomicCommitChecked :=
  fun publication =>
    ay_arwg_conj_left atomicCommitChecked
      (ay_arwg_conj modelEvidence originalModel)
      (ay_arwg_conj_right atomicContract
        (ay_arwg_conj atomicCommitChecked
          (ay_arwg_conj modelEvidence originalModel)) publication)

theorem ay_arwg_sat_publication_original_model
    (atomicContract atomicCommitChecked modelEvidence originalModel : Prop) :
    ay_arwg_sat_publication atomicContract atomicCommitChecked modelEvidence
      originalModel ->
    originalModel :=
  fun publication =>
    ay_arwg_conj_right modelEvidence originalModel
      (ay_arwg_conj_right atomicCommitChecked
        (ay_arwg_conj modelEvidence originalModel)
        (ay_arwg_conj_right atomicContract
          (ay_arwg_conj atomicCommitChecked
            (ay_arwg_conj modelEvidence originalModel)) publication))

theorem ay_arwg_unsat_publication_intro
    (atomicContract atomicCommitChecked proofEvidence originalEmptyClause :
      Prop) :
    atomicContract -> atomicCommitChecked -> proofEvidence ->
    originalEmptyClause ->
    ay_arwg_unsat_publication atomicContract atomicCommitChecked proofEvidence
      originalEmptyClause :=
  fun contractProof atomicProof proofProof emptyProof =>
    ay_arwg_conj_intro atomicContract
      (ay_arwg_conj atomicCommitChecked
        (ay_arwg_conj proofEvidence originalEmptyClause)) contractProof
      (ay_arwg_conj_intro atomicCommitChecked
        (ay_arwg_conj proofEvidence originalEmptyClause) atomicProof
        (ay_arwg_conj_intro proofEvidence originalEmptyClause proofProof
          emptyProof))

theorem ay_arwg_unsat_publication_atomic
    (atomicContract atomicCommitChecked proofEvidence originalEmptyClause :
      Prop) :
    ay_arwg_unsat_publication atomicContract atomicCommitChecked proofEvidence
      originalEmptyClause ->
    atomicCommitChecked :=
  fun publication =>
    ay_arwg_conj_left atomicCommitChecked
      (ay_arwg_conj proofEvidence originalEmptyClause)
      (ay_arwg_conj_right atomicContract
        (ay_arwg_conj atomicCommitChecked
          (ay_arwg_conj proofEvidence originalEmptyClause)) publication)

theorem ay_arwg_unsat_publication_original_empty_clause
    (atomicContract atomicCommitChecked proofEvidence originalEmptyClause :
      Prop) :
    ay_arwg_unsat_publication atomicContract atomicCommitChecked proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_arwg_conj_right proofEvidence originalEmptyClause
      (ay_arwg_conj_right atomicCommitChecked
        (ay_arwg_conj proofEvidence originalEmptyClause)
        (ay_arwg_conj_right atomicContract
          (ay_arwg_conj atomicCommitChecked
            (ay_arwg_conj proofEvidence originalEmptyClause)) publication))

theorem ay_arwg_atomically_committed_sat_passes_publication
    (atomicContract atomicCommitChecked modelEvidence originalModel : Prop) :
    ay_arwg_sat_publication atomicContract atomicCommitChecked modelEvidence
      originalModel ->
    ay_arwg_conj atomicCommitChecked originalModel :=
  fun publication =>
    ay_arwg_conj_intro atomicCommitChecked originalModel
      (ay_arwg_sat_publication_atomic atomicContract atomicCommitChecked
        modelEvidence originalModel publication)
      (ay_arwg_sat_publication_original_model atomicContract
        atomicCommitChecked modelEvidence originalModel publication)

theorem ay_arwg_atomically_committed_unsat_passes_publication
    (atomicContract atomicCommitChecked proofEvidence originalEmptyClause :
      Prop) :
    ay_arwg_unsat_publication atomicContract atomicCommitChecked proofEvidence
      originalEmptyClause ->
    ay_arwg_conj atomicCommitChecked originalEmptyClause :=
  fun publication =>
    ay_arwg_conj_intro atomicCommitChecked originalEmptyClause
      (ay_arwg_unsat_publication_atomic atomicContract atomicCommitChecked
        proofEvidence originalEmptyClause publication)
      (ay_arwg_unsat_publication_original_empty_clause atomicContract
        atomicCommitChecked proofEvidence originalEmptyClause publication)

theorem ay_arwg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_arwg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_arwg_conj_intro reason (ay_arwg_conj fallbackPath auditTrail)
      reasonProof
      (ay_arwg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_arwg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_arwg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_arwg_conj_intro reason
      (ay_arwg_conj (satFact -> False) (unsatFact -> False)) reasonProof
      (ay_arwg_conj_intro (satFact -> False) (unsatFact -> False) noSat
        noUnsat)

theorem ay_arwg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_arwg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_arwg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_arwg_conj_right reason
        (ay_arwg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_arwg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_arwg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_arwg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_arwg_conj_right reason
        (ay_arwg_conj (satFact -> False) (unsatFact -> False)) blocked)

theorem ay_arwg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_arwg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_arwg_conj_intro reason
      (ay_arwg_conj fallbackPath recomputeObligation) reasonProof
      (ay_arwg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_arwg_write_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_arwg_write_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof noSat noUnsat =>
    ay_arwg_conj_intro
      (ay_arwg_blocked_publication satFact unsatFact reason)
      (ay_arwg_recompute reason fallbackPath recomputeObligation)
      (ay_arwg_blocked_publication_intro satFact unsatFact reason
        reasonProof noSat noUnsat)
      (ay_arwg_recompute_intro reason fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_arwg_write_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_arwg_write_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_arwg_blocked_publication_no_sat satFact unsatFact reason
      (ay_arwg_conj_left
        (ay_arwg_blocked_publication satFact unsatFact reason)
        (ay_arwg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_arwg_write_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_arwg_write_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_arwg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_arwg_conj_left
        (ay_arwg_blocked_publication satFact unsatFact reason)
        (ay_arwg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_arwg_write_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_arwg_write_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_arwg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_arwg_conj_right
      (ay_arwg_blocked_publication satFact unsatFact reason)
      (ay_arwg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_arwg_partial_write_forces_no_claim
    (satFact unsatFact partialWrite fallbackPath auditTrail
      recomputeObligation : Prop) :
    partialWrite -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_arwg_no_claim partialWrite fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_arwg_no_claim_intro partialWrite fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_arwg_torn_rename_forces_no_claim
    (satFact unsatFact tornRename fallbackPath auditTrail
      recomputeObligation : Prop) :
    tornRename -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_arwg_no_claim tornRename fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_arwg_no_claim_intro tornRename fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_arwg_stale_final_digest_forces_no_claim
    (satFact unsatFact staleFinalDigest fallbackPath auditTrail
      recomputeObligation : Prop) :
    staleFinalDigest -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_arwg_no_claim staleFinalDigest fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_arwg_no_claim_intro staleFinalDigest fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_arwg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_arwg_no_claim checkerMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_arwg_no_claim_intro checkerMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_arwg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_arwg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_arwg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_arwg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_arwg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_arwg_no_claim_intro buildMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_arwg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_arwg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_arwg_no_claim_intro archiveMismatch fallbackPath auditTrail reasonProof
      fallbackProof auditProof

theorem ay_arwg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivated fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> auditTrail -> recomputeObligation ->
    (satFact -> False) -> (unsatFact -> False) ->
    ay_arwg_no_claim fallbackActivated fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _recomputeProof _noSat _noUnsat =>
    ay_arwg_no_claim_intro fallbackActivated fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_arwg_failed_write_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_arwg_write_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_arwg_write_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_arwg_failed_write_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_arwg_write_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_arwg_write_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_arwg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_arwg_no_claim reason fallbackPath auditTrail ->
    (satFact -> False) -> satFact -> False :=
  fun _noClaim noSat satProof => noSat satProof

theorem ay_arwg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_arwg_no_claim reason fallbackPath auditTrail ->
    (unsatFact -> False) -> unsatFact -> False :=
  fun _noClaim noUnsat unsatProof => noUnsat unsatProof
