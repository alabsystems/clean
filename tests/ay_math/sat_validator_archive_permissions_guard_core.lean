-- SAT-COMP validator archive permissions/mutability guard core.
--
-- Public SAT/UNSAT claims require archive digest, read-only artifact evidence,
-- permission ledger, mtime/size digest, no-postcheck-mutation witness, checker
-- transcript, benchmark fingerprint, solver build evidence, fallback, and audit
-- transcript to agree.

def ay_apmg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_apmg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_apmg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_apmg_disj satFact (ay_apmg_disj unsatFact noClaimFact)

def ay_apmg_permission_contract
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (archiveManifestDigest -> readOnlyArtifactWitness ->
      filePermissionLedger -> mtimeSizeDigest -> noPostcheckMutationWitness ->
      checkerTranscript -> benchmarkFingerprint -> solverBuildEvidence ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_apmg_sat_publication
    (permissionContract immutableCheckerInputs checkedModel originalModel :
      Prop) : Prop :=
  ay_apmg_conj permissionContract
    (ay_apmg_conj immutableCheckerInputs
      (ay_apmg_conj checkedModel originalModel))

def ay_apmg_unsat_publication
    (permissionContract immutableCheckerInputs checkedProof
      originalEmptyClause : Prop) : Prop :=
  ay_apmg_conj permissionContract
    (ay_apmg_conj immutableCheckerInputs
      (ay_apmg_conj checkedProof originalEmptyClause))

def ay_apmg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_apmg_conj reason (ay_apmg_conj fallbackPath auditTrail)

def ay_apmg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_apmg_conj reason
    (ay_apmg_conj (satFact -> False) (unsatFact -> False))

def ay_apmg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_apmg_conj reason
    (ay_apmg_conj fallbackPath recomputeObligation)

def ay_apmg_permission_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_apmg_conj
    (ay_apmg_blocked_publication satFact unsatFact reason)
    (ay_apmg_recompute reason fallbackPath recomputeObligation)

theorem ay_apmg_conj_intro (left right : Prop) :
    left -> right -> ay_apmg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_apmg_conj_left (left right : Prop) :
    ay_apmg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_apmg_conj_right (left right : Prop) :
    ay_apmg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_apmg_disj_left (left right : Prop) :
    left -> ay_apmg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_apmg_disj_right (left right : Prop) :
    right -> ay_apmg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_apmg_permission_contract_intro
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    archiveManifestDigest -> readOnlyArtifactWitness -> filePermissionLedger ->
    mtimeSizeDigest -> noPostcheckMutationWitness -> checkerTranscript ->
    benchmarkFingerprint -> solverBuildEvidence -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_apmg_permission_contract archiveManifestDigest readOnlyArtifactWitness
      filePermissionLedger mtimeSizeDigest noPostcheckMutationWitness
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      fallbackNoClaimPath auditTranscript :=
  fun archiveProof readonlyProof permissionProof mtimeProof mutationProof
      checkerProof fingerprintProof buildProof fallbackProof auditProof result
      build =>
    build archiveProof readonlyProof permissionProof mtimeProof mutationProof
      checkerProof fingerprintProof buildProof fallbackProof auditProof

theorem ay_apmg_contract_archive
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apmg_permission_contract archiveManifestDigest readOnlyArtifactWitness
      filePermissionLedger mtimeSizeDigest noPostcheckMutationWitness
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      fallbackNoClaimPath auditTranscript ->
    archiveManifestDigest :=
  fun contract =>
    contract archiveManifestDigest
      (fun archiveProof _readonlyProof _permissionProof _mtimeProof
          _mutationProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_apmg_contract_readonly
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apmg_permission_contract archiveManifestDigest readOnlyArtifactWitness
      filePermissionLedger mtimeSizeDigest noPostcheckMutationWitness
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      fallbackNoClaimPath auditTranscript ->
    readOnlyArtifactWitness :=
  fun contract =>
    contract readOnlyArtifactWitness
      (fun _archiveProof readonlyProof _permissionProof _mtimeProof
          _mutationProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => readonlyProof)

theorem ay_apmg_contract_permissions
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apmg_permission_contract archiveManifestDigest readOnlyArtifactWitness
      filePermissionLedger mtimeSizeDigest noPostcheckMutationWitness
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      fallbackNoClaimPath auditTranscript ->
    filePermissionLedger :=
  fun contract =>
    contract filePermissionLedger
      (fun _archiveProof _readonlyProof permissionProof _mtimeProof
          _mutationProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => permissionProof)

theorem ay_apmg_contract_mtime
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apmg_permission_contract archiveManifestDigest readOnlyArtifactWitness
      filePermissionLedger mtimeSizeDigest noPostcheckMutationWitness
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      fallbackNoClaimPath auditTranscript ->
    mtimeSizeDigest :=
  fun contract =>
    contract mtimeSizeDigest
      (fun _archiveProof _readonlyProof _permissionProof mtimeProof
          _mutationProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => mtimeProof)

theorem ay_apmg_contract_no_mutation
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apmg_permission_contract archiveManifestDigest readOnlyArtifactWitness
      filePermissionLedger mtimeSizeDigest noPostcheckMutationWitness
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      fallbackNoClaimPath auditTranscript ->
    noPostcheckMutationWitness :=
  fun contract =>
    contract noPostcheckMutationWitness
      (fun _archiveProof _readonlyProof _permissionProof _mtimeProof
          mutationProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => mutationProof)

theorem ay_apmg_contract_checker
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apmg_permission_contract archiveManifestDigest readOnlyArtifactWitness
      filePermissionLedger mtimeSizeDigest noPostcheckMutationWitness
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _archiveProof _readonlyProof _permissionProof _mtimeProof
          _mutationProof checkerProof _fingerprintProof _buildProof
          _fallbackProof _auditProof => checkerProof)

theorem ay_apmg_contract_fingerprint
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apmg_permission_contract archiveManifestDigest readOnlyArtifactWitness
      filePermissionLedger mtimeSizeDigest noPostcheckMutationWitness
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _archiveProof _readonlyProof _permissionProof _mtimeProof
          _mutationProof _checkerProof fingerprintProof _buildProof
          _fallbackProof _auditProof => fingerprintProof)

theorem ay_apmg_contract_build
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apmg_permission_contract archiveManifestDigest readOnlyArtifactWitness
      filePermissionLedger mtimeSizeDigest noPostcheckMutationWitness
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _archiveProof _readonlyProof _permissionProof _mtimeProof
          _mutationProof _checkerProof _fingerprintProof buildProof
          _fallbackProof _auditProof => buildProof)

theorem ay_apmg_contract_fallback
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apmg_permission_contract archiveManifestDigest readOnlyArtifactWitness
      filePermissionLedger mtimeSizeDigest noPostcheckMutationWitness
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _archiveProof _readonlyProof _permissionProof _mtimeProof
          _mutationProof _checkerProof _fingerprintProof _buildProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_apmg_contract_audit
    (archiveManifestDigest readOnlyArtifactWitness filePermissionLedger
      mtimeSizeDigest noPostcheckMutationWitness checkerTranscript
      benchmarkFingerprint solverBuildEvidence fallbackNoClaimPath
      auditTranscript : Prop) :
    ay_apmg_permission_contract archiveManifestDigest readOnlyArtifactWitness
      filePermissionLedger mtimeSizeDigest noPostcheckMutationWitness
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _archiveProof _readonlyProof _permissionProof _mtimeProof
          _mutationProof _checkerProof _fingerprintProof _buildProof
          _fallbackProof auditProof => auditProof)

theorem ay_apmg_sat_publication_intro
    (permissionContract immutableCheckerInputs checkedModel originalModel :
      Prop) :
    permissionContract -> immutableCheckerInputs -> checkedModel ->
    originalModel ->
    ay_apmg_sat_publication permissionContract immutableCheckerInputs
      checkedModel originalModel :=
  fun contractProof immutableProof modelProof originalProof =>
    ay_apmg_conj_intro permissionContract
      (ay_apmg_conj immutableCheckerInputs
        (ay_apmg_conj checkedModel originalModel))
      contractProof
      (ay_apmg_conj_intro immutableCheckerInputs
        (ay_apmg_conj checkedModel originalModel)
        immutableProof
        (ay_apmg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_apmg_unsat_publication_intro
    (permissionContract immutableCheckerInputs checkedProof
      originalEmptyClause : Prop) :
    permissionContract -> immutableCheckerInputs -> checkedProof ->
    originalEmptyClause ->
    ay_apmg_unsat_publication permissionContract immutableCheckerInputs
      checkedProof originalEmptyClause :=
  fun contractProof immutableProof proofProof originalProof =>
    ay_apmg_conj_intro permissionContract
      (ay_apmg_conj immutableCheckerInputs
        (ay_apmg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_apmg_conj_intro immutableCheckerInputs
        (ay_apmg_conj checkedProof originalEmptyClause)
        immutableProof
        (ay_apmg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_apmg_sat_publication_original_model
    (permissionContract immutableCheckerInputs checkedModel originalModel :
      Prop) :
    ay_apmg_sat_publication permissionContract immutableCheckerInputs
      checkedModel originalModel ->
    originalModel :=
  fun publication =>
    ay_apmg_conj_right checkedModel originalModel
      (ay_apmg_conj_right immutableCheckerInputs
        (ay_apmg_conj checkedModel originalModel)
        (ay_apmg_conj_right permissionContract
          (ay_apmg_conj immutableCheckerInputs
            (ay_apmg_conj checkedModel originalModel))
          publication))

theorem ay_apmg_unsat_publication_original_empty_clause
    (permissionContract immutableCheckerInputs checkedProof
      originalEmptyClause : Prop) :
    ay_apmg_unsat_publication permissionContract immutableCheckerInputs
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_apmg_conj_right checkedProof originalEmptyClause
      (ay_apmg_conj_right immutableCheckerInputs
        (ay_apmg_conj checkedProof originalEmptyClause)
        (ay_apmg_conj_right permissionContract
          (ay_apmg_conj immutableCheckerInputs
            (ay_apmg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_apmg_accepted_permissions_preserve_sat_publication
    (permissionContract immutableCheckerInputs checkedModel originalModel :
      Prop) :
    ay_apmg_sat_publication permissionContract immutableCheckerInputs
      checkedModel originalModel ->
    ay_apmg_public_result originalModel False False :=
  fun publication =>
    ay_apmg_disj_left originalModel (ay_apmg_disj False False)
      (ay_apmg_sat_publication_original_model permissionContract
        immutableCheckerInputs checkedModel originalModel publication)

theorem ay_apmg_accepted_permissions_preserve_unsat_publication
    (permissionContract immutableCheckerInputs checkedProof
      originalEmptyClause : Prop) :
    ay_apmg_unsat_publication permissionContract immutableCheckerInputs
      checkedProof originalEmptyClause ->
    ay_apmg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_apmg_disj_right False (ay_apmg_disj originalEmptyClause False)
      (ay_apmg_disj_left originalEmptyClause False
        (ay_apmg_unsat_publication_original_empty_clause permissionContract
          immutableCheckerInputs checkedProof originalEmptyClause publication))

theorem ay_apmg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_apmg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_apmg_conj_intro reason (ay_apmg_conj fallbackPath auditTrail)
      reasonProof
      (ay_apmg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_apmg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_apmg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_apmg_conj_intro reason
      (ay_apmg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_apmg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_apmg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_apmg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_apmg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_apmg_conj_right reason
        (ay_apmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_apmg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_apmg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_apmg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_apmg_conj_right reason
        (ay_apmg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_apmg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_apmg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_apmg_conj_intro reason
      (ay_apmg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_apmg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_apmg_permission_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_apmg_blocked_publication satFact unsatFact reason ->
    ay_apmg_recompute reason fallbackPath recomputeObligation ->
    ay_apmg_permission_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_apmg_conj_intro
      (ay_apmg_blocked_publication satFact unsatFact reason)
      (ay_apmg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_apmg_permission_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_apmg_permission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_apmg_blocked_publication_no_sat satFact unsatFact reason
      (ay_apmg_conj_left
        (ay_apmg_blocked_publication satFact unsatFact reason)
        (ay_apmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_apmg_permission_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_apmg_permission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_apmg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_apmg_conj_left
        (ay_apmg_blocked_publication satFact unsatFact reason)
        (ay_apmg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_apmg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apmg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_apmg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_apmg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apmg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_apmg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apmg_permission_mismatch_forces_no_claim
    (satFact unsatFact permissionMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    permissionMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apmg_no_claim permissionMismatch fallbackPath auditTrail :=
  ay_apmg_mismatch_forces_no_claim satFact unsatFact permissionMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apmg_mtime_mismatch_forces_no_claim
    (satFact unsatFact mtimeMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    mtimeMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apmg_no_claim mtimeMismatch fallbackPath auditTrail :=
  ay_apmg_mismatch_forces_no_claim satFact unsatFact mtimeMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apmg_mutation_mismatch_forces_no_claim
    (satFact unsatFact mutationMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    mutationMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apmg_no_claim mutationMismatch fallbackPath auditTrail :=
  ay_apmg_mismatch_forces_no_claim satFact unsatFact mutationMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apmg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apmg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_apmg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apmg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apmg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_apmg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apmg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apmg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_apmg_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apmg_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_apmg_no_claim auditMismatch fallbackPath auditTrail :=
  ay_apmg_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_apmg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_apmg_permission_failure satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_apmg_permission_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_apmg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_apmg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_apmg_failed_permission_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_apmg_permission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_apmg_permission_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_apmg_failed_permission_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_apmg_permission_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_apmg_permission_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_apmg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_apmg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_apmg_conj_left reason (ay_apmg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_apmg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_apmg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_apmg_conj_left reason (ay_apmg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
