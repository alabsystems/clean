-- SAT-COMP validator log redaction guard core.
--
-- Public SAT/UNSAT claims may use redacted logs only when raw transcript
-- digest, redaction policy, public transcript digest, checker transcript,
-- artifact digest, benchmark fingerprint, build evidence, archive evidence,
-- fallback, and audit transcript agree.

def ay_lrg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_lrg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_lrg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_lrg_disj satFact (ay_lrg_disj unsatFact noClaimFact)

def ay_lrg_redaction_contract
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (rawTranscriptDigest -> redactionPolicyManifest ->
      publicTranscriptDigest -> checkerTranscript -> artifactDigest ->
      benchmarkFingerprint -> solverBuildEvidence -> archiveManifest ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_lrg_sat_publication
    (redactionContract redactionPreservesEvidence checkedModel
      originalModel : Prop) : Prop :=
  ay_lrg_conj redactionContract
    (ay_lrg_conj redactionPreservesEvidence
      (ay_lrg_conj checkedModel originalModel))

def ay_lrg_unsat_publication
    (redactionContract redactionPreservesEvidence checkedProof
      originalEmptyClause : Prop) : Prop :=
  ay_lrg_conj redactionContract
    (ay_lrg_conj redactionPreservesEvidence
      (ay_lrg_conj checkedProof originalEmptyClause))

def ay_lrg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_lrg_conj reason (ay_lrg_conj fallbackPath auditTrail)

def ay_lrg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_lrg_conj reason
    (ay_lrg_conj (satFact -> False) (unsatFact -> False))

def ay_lrg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_lrg_conj reason
    (ay_lrg_conj fallbackPath recomputeObligation)

def ay_lrg_redaction_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_lrg_conj
    (ay_lrg_blocked_publication satFact unsatFact reason)
    (ay_lrg_recompute reason fallbackPath recomputeObligation)

theorem ay_lrg_conj_intro (left right : Prop) :
    left -> right -> ay_lrg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_lrg_conj_left (left right : Prop) :
    ay_lrg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_lrg_conj_right (left right : Prop) :
    ay_lrg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_lrg_disj_left (left right : Prop) :
    left -> ay_lrg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_lrg_disj_right (left right : Prop) :
    right -> ay_lrg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_lrg_redaction_contract_intro
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    rawTranscriptDigest -> redactionPolicyManifest ->
    publicTranscriptDigest -> checkerTranscript -> artifactDigest ->
    benchmarkFingerprint -> solverBuildEvidence -> archiveManifest ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_lrg_redaction_contract rawTranscriptDigest redactionPolicyManifest
      publicTranscriptDigest checkerTranscript artifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript :=
  fun rawProof policyProof publicProof checkerProof artifactProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof result
      build =>
    build rawProof policyProof publicProof checkerProof artifactProof
      fingerprintProof buildProof archiveProof fallbackProof auditProof

theorem ay_lrg_contract_raw
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_lrg_redaction_contract rawTranscriptDigest redactionPolicyManifest
      publicTranscriptDigest checkerTranscript artifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    rawTranscriptDigest :=
  fun contract =>
    contract rawTranscriptDigest
      (fun rawProof _policyProof _publicProof _checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => rawProof)

theorem ay_lrg_contract_policy
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_lrg_redaction_contract rawTranscriptDigest redactionPolicyManifest
      publicTranscriptDigest checkerTranscript artifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    redactionPolicyManifest :=
  fun contract =>
    contract redactionPolicyManifest
      (fun _rawProof policyProof _publicProof _checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => policyProof)

theorem ay_lrg_contract_public
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_lrg_redaction_contract rawTranscriptDigest redactionPolicyManifest
      publicTranscriptDigest checkerTranscript artifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    publicTranscriptDigest :=
  fun contract =>
    contract publicTranscriptDigest
      (fun _rawProof _policyProof publicProof _checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => publicProof)

theorem ay_lrg_contract_checker
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_lrg_redaction_contract rawTranscriptDigest redactionPolicyManifest
      publicTranscriptDigest checkerTranscript artifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _rawProof _policyProof _publicProof checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_lrg_contract_artifact
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_lrg_redaction_contract rawTranscriptDigest redactionPolicyManifest
      publicTranscriptDigest checkerTranscript artifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    artifactDigest :=
  fun contract =>
    contract artifactDigest
      (fun _rawProof _policyProof _publicProof _checkerProof artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => artifactProof)

theorem ay_lrg_contract_fingerprint
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_lrg_redaction_contract rawTranscriptDigest redactionPolicyManifest
      publicTranscriptDigest checkerTranscript artifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _rawProof _policyProof _publicProof _checkerProof _artifactProof
          fingerprintProof _buildProof _archiveProof _fallbackProof
          _auditProof => fingerprintProof)

theorem ay_lrg_contract_build
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_lrg_redaction_contract rawTranscriptDigest redactionPolicyManifest
      publicTranscriptDigest checkerTranscript artifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _rawProof _policyProof _publicProof _checkerProof _artifactProof
          _fingerprintProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_lrg_contract_archive
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_lrg_redaction_contract rawTranscriptDigest redactionPolicyManifest
      publicTranscriptDigest checkerTranscript artifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _rawProof _policyProof _publicProof _checkerProof _artifactProof
          _fingerprintProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_lrg_contract_fallback
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_lrg_redaction_contract rawTranscriptDigest redactionPolicyManifest
      publicTranscriptDigest checkerTranscript artifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _rawProof _policyProof _publicProof _checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_lrg_contract_audit
    (rawTranscriptDigest redactionPolicyManifest publicTranscriptDigest
      checkerTranscript artifactDigest benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_lrg_redaction_contract rawTranscriptDigest redactionPolicyManifest
      publicTranscriptDigest checkerTranscript artifactDigest
      benchmarkFingerprint solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _rawProof _policyProof _publicProof _checkerProof _artifactProof
          _fingerprintProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_lrg_sat_publication_intro
    (redactionContract redactionPreservesEvidence checkedModel
      originalModel : Prop) :
    redactionContract -> redactionPreservesEvidence -> checkedModel ->
    originalModel ->
    ay_lrg_sat_publication redactionContract redactionPreservesEvidence
      checkedModel originalModel :=
  fun contractProof preservesProof modelProof originalProof =>
    ay_lrg_conj_intro redactionContract
      (ay_lrg_conj redactionPreservesEvidence
        (ay_lrg_conj checkedModel originalModel))
      contractProof
      (ay_lrg_conj_intro redactionPreservesEvidence
        (ay_lrg_conj checkedModel originalModel)
        preservesProof
        (ay_lrg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_lrg_unsat_publication_intro
    (redactionContract redactionPreservesEvidence checkedProof
      originalEmptyClause : Prop) :
    redactionContract -> redactionPreservesEvidence -> checkedProof ->
    originalEmptyClause ->
    ay_lrg_unsat_publication redactionContract redactionPreservesEvidence
      checkedProof originalEmptyClause :=
  fun contractProof preservesProof proofProof originalProof =>
    ay_lrg_conj_intro redactionContract
      (ay_lrg_conj redactionPreservesEvidence
        (ay_lrg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_lrg_conj_intro redactionPreservesEvidence
        (ay_lrg_conj checkedProof originalEmptyClause)
        preservesProof
        (ay_lrg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_lrg_sat_publication_original_model
    (redactionContract redactionPreservesEvidence checkedModel
      originalModel : Prop) :
    ay_lrg_sat_publication redactionContract redactionPreservesEvidence
      checkedModel originalModel ->
    originalModel :=
  fun publication =>
    ay_lrg_conj_right checkedModel originalModel
      (ay_lrg_conj_right redactionPreservesEvidence
        (ay_lrg_conj checkedModel originalModel)
        (ay_lrg_conj_right redactionContract
          (ay_lrg_conj redactionPreservesEvidence
            (ay_lrg_conj checkedModel originalModel))
          publication))

theorem ay_lrg_unsat_publication_original_empty_clause
    (redactionContract redactionPreservesEvidence checkedProof
      originalEmptyClause : Prop) :
    ay_lrg_unsat_publication redactionContract redactionPreservesEvidence
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_lrg_conj_right checkedProof originalEmptyClause
      (ay_lrg_conj_right redactionPreservesEvidence
        (ay_lrg_conj checkedProof originalEmptyClause)
        (ay_lrg_conj_right redactionContract
          (ay_lrg_conj redactionPreservesEvidence
            (ay_lrg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_lrg_accepted_redaction_preserves_sat_soundness
    (redactionContract redactionPreservesEvidence checkedModel
      originalModel : Prop) :
    ay_lrg_sat_publication redactionContract redactionPreservesEvidence
      checkedModel originalModel ->
    ay_lrg_public_result originalModel False False :=
  fun publication =>
    ay_lrg_disj_left originalModel (ay_lrg_disj False False)
      (ay_lrg_sat_publication_original_model redactionContract
        redactionPreservesEvidence checkedModel originalModel publication)

theorem ay_lrg_accepted_redaction_preserves_unsat_soundness
    (redactionContract redactionPreservesEvidence checkedProof
      originalEmptyClause : Prop) :
    ay_lrg_unsat_publication redactionContract redactionPreservesEvidence
      checkedProof originalEmptyClause ->
    ay_lrg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_lrg_disj_right False (ay_lrg_disj originalEmptyClause False)
      (ay_lrg_disj_left originalEmptyClause False
        (ay_lrg_unsat_publication_original_empty_clause redactionContract
          redactionPreservesEvidence checkedProof originalEmptyClause
          publication))

theorem ay_lrg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_lrg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_lrg_conj_intro reason (ay_lrg_conj fallbackPath auditTrail)
      reasonProof
      (ay_lrg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_lrg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_lrg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_lrg_conj_intro reason
      (ay_lrg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_lrg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_lrg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_lrg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_lrg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_lrg_conj_right reason
        (ay_lrg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_lrg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_lrg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_lrg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_lrg_conj_right reason
        (ay_lrg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_lrg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_lrg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_lrg_conj_intro reason
      (ay_lrg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_lrg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_lrg_redaction_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_lrg_blocked_publication satFact unsatFact reason ->
    ay_lrg_recompute reason fallbackPath recomputeObligation ->
    ay_lrg_redaction_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_lrg_conj_intro
      (ay_lrg_blocked_publication satFact unsatFact reason)
      (ay_lrg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_lrg_redaction_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_lrg_redaction_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_lrg_blocked_publication_no_sat satFact unsatFact reason
      (ay_lrg_conj_left
        (ay_lrg_blocked_publication satFact unsatFact reason)
        (ay_lrg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_lrg_redaction_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_lrg_redaction_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_lrg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_lrg_conj_left
        (ay_lrg_blocked_publication satFact unsatFact reason)
        (ay_lrg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_lrg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_lrg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_lrg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_lrg_transcript_mismatch_forces_no_claim
    (satFact unsatFact transcriptMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    transcriptMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_lrg_no_claim transcriptMismatch fallbackPath auditTrail :=
  ay_lrg_mismatch_forces_no_claim satFact unsatFact transcriptMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_lrg_policy_mismatch_forces_no_claim
    (satFact unsatFact policyMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    policyMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_lrg_no_claim policyMismatch fallbackPath auditTrail :=
  ay_lrg_mismatch_forces_no_claim satFact unsatFact policyMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_lrg_digest_mismatch_forces_no_claim
    (satFact unsatFact digestMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    digestMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_lrg_no_claim digestMismatch fallbackPath auditTrail :=
  ay_lrg_mismatch_forces_no_claim satFact unsatFact digestMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_lrg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_lrg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_lrg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_lrg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_lrg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_lrg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_lrg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_lrg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_lrg_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_lrg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_lrg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_lrg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_lrg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_lrg_redaction_failure satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_lrg_redaction_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_lrg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_lrg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_lrg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_lrg_redaction_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_lrg_redaction_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_lrg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_lrg_redaction_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_lrg_redaction_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
