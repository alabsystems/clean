-- SAT-COMP validator symlink/hardlink artifact guard core.
--
-- Public SAT/UNSAT claims require normalized artifact paths, no-link evidence,
-- inode/file digest agreement, checker transcript, benchmark fingerprint,
-- solver build evidence, archive manifest, no-claim fallback, and audit
-- transcript to agree.  Link traversal or aliasing failures become no-claim
-- recompute obligations rather than public semantic answers.

def ay_shlg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_shlg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_shlg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_shlg_disj satFact (ay_shlg_disj unsatFact noClaimFact)

def ay_shlg_link_clean_contract
    (normalizedArtifactPathManifest noSymlinkNoHardlinkWitness
      inodeFileDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) : Prop :=
  forall result : Prop,
    (normalizedArtifactPathManifest -> noSymlinkNoHardlinkWitness ->
      inodeFileDigestAgreement -> checkerTranscript -> benchmarkFingerprint ->
      solverBuildEvidence -> archiveManifest -> noClaimFallback ->
      auditTranscript -> result) ->
    result

def ay_shlg_sat_publication
    (linkContract acceptedLinkcleanArtifact checkedModel originalModel :
      Prop) : Prop :=
  ay_shlg_conj linkContract
    (ay_shlg_conj acceptedLinkcleanArtifact
      (ay_shlg_conj checkedModel originalModel))

def ay_shlg_unsat_publication
    (linkContract acceptedLinkcleanArtifact checkedProof originalEmptyClause :
      Prop) : Prop :=
  ay_shlg_conj linkContract
    (ay_shlg_conj acceptedLinkcleanArtifact
      (ay_shlg_conj checkedProof originalEmptyClause))

def ay_shlg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_shlg_conj reason (ay_shlg_conj fallbackPath auditTrail)

def ay_shlg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_shlg_conj reason
    (ay_shlg_conj (satFact -> False) (unsatFact -> False))

def ay_shlg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_shlg_conj reason
    (ay_shlg_conj fallbackPath recomputeObligation)

def ay_shlg_link_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_shlg_conj
    (ay_shlg_blocked_publication satFact unsatFact reason)
    (ay_shlg_recompute reason fallbackPath recomputeObligation)

theorem ay_shlg_conj_intro (left right : Prop) :
    left -> right -> ay_shlg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_shlg_conj_left (left right : Prop) :
    ay_shlg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_shlg_conj_right (left right : Prop) :
    ay_shlg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_shlg_disj_left (left right : Prop) :
    left -> ay_shlg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_shlg_disj_right (left right : Prop) :
    right -> ay_shlg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_shlg_link_clean_contract_intro
    (normalizedArtifactPathManifest noSymlinkNoHardlinkWitness
      inodeFileDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    normalizedArtifactPathManifest -> noSymlinkNoHardlinkWitness ->
    inodeFileDigestAgreement -> checkerTranscript -> benchmarkFingerprint ->
    solverBuildEvidence -> archiveManifest -> noClaimFallback ->
    auditTranscript ->
    ay_shlg_link_clean_contract normalizedArtifactPathManifest
      noSymlinkNoHardlinkWitness inodeFileDigestAgreement checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript :=
  fun pathProof linkProof digestProof checkerProof fingerprintProof buildProof
      archiveProof fallbackProof auditProof result build =>
    build pathProof linkProof digestProof checkerProof fingerprintProof
      buildProof archiveProof fallbackProof auditProof

theorem ay_shlg_contract_path
    (normalizedArtifactPathManifest noSymlinkNoHardlinkWitness
      inodeFileDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_shlg_link_clean_contract normalizedArtifactPathManifest
      noSymlinkNoHardlinkWitness inodeFileDigestAgreement checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    normalizedArtifactPathManifest :=
  fun contract =>
    contract normalizedArtifactPathManifest
      (fun pathProof _linkProof _digestProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof => pathProof)

theorem ay_shlg_contract_no_links
    (normalizedArtifactPathManifest noSymlinkNoHardlinkWitness
      inodeFileDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_shlg_link_clean_contract normalizedArtifactPathManifest
      noSymlinkNoHardlinkWitness inodeFileDigestAgreement checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    noSymlinkNoHardlinkWitness :=
  fun contract =>
    contract noSymlinkNoHardlinkWitness
      (fun _pathProof linkProof _digestProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof => linkProof)

theorem ay_shlg_contract_digest
    (normalizedArtifactPathManifest noSymlinkNoHardlinkWitness
      inodeFileDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_shlg_link_clean_contract normalizedArtifactPathManifest
      noSymlinkNoHardlinkWitness inodeFileDigestAgreement checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    inodeFileDigestAgreement :=
  fun contract =>
    contract inodeFileDigestAgreement
      (fun _pathProof _linkProof digestProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof => digestProof)

theorem ay_shlg_contract_checker
    (normalizedArtifactPathManifest noSymlinkNoHardlinkWitness
      inodeFileDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_shlg_link_clean_contract normalizedArtifactPathManifest
      noSymlinkNoHardlinkWitness inodeFileDigestAgreement checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _pathProof _linkProof _digestProof checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof => checkerProof)

theorem ay_shlg_contract_fingerprint
    (normalizedArtifactPathManifest noSymlinkNoHardlinkWitness
      inodeFileDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_shlg_link_clean_contract normalizedArtifactPathManifest
      noSymlinkNoHardlinkWitness inodeFileDigestAgreement checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _pathProof _linkProof _digestProof _checkerProof fingerprintProof
          _buildProof _archiveProof _fallbackProof _auditProof =>
        fingerprintProof)

theorem ay_shlg_contract_build
    (normalizedArtifactPathManifest noSymlinkNoHardlinkWitness
      inodeFileDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_shlg_link_clean_contract normalizedArtifactPathManifest
      noSymlinkNoHardlinkWitness inodeFileDigestAgreement checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _pathProof _linkProof _digestProof _checkerProof _fingerprintProof
          buildProof _archiveProof _fallbackProof _auditProof => buildProof)

theorem ay_shlg_contract_archive
    (normalizedArtifactPathManifest noSymlinkNoHardlinkWitness
      inodeFileDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_shlg_link_clean_contract normalizedArtifactPathManifest
      noSymlinkNoHardlinkWitness inodeFileDigestAgreement checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _pathProof _linkProof _digestProof _checkerProof _fingerprintProof
          _buildProof archiveProof _fallbackProof _auditProof => archiveProof)

theorem ay_shlg_contract_fallback
    (normalizedArtifactPathManifest noSymlinkNoHardlinkWitness
      inodeFileDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_shlg_link_clean_contract normalizedArtifactPathManifest
      noSymlinkNoHardlinkWitness inodeFileDigestAgreement checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _pathProof _linkProof _digestProof _checkerProof _fingerprintProof
          _buildProof _archiveProof fallbackProof _auditProof => fallbackProof)

theorem ay_shlg_contract_audit
    (normalizedArtifactPathManifest noSymlinkNoHardlinkWitness
      inodeFileDigestAgreement checkerTranscript benchmarkFingerprint
      solverBuildEvidence archiveManifest noClaimFallback auditTranscript :
      Prop) :
    ay_shlg_link_clean_contract normalizedArtifactPathManifest
      noSymlinkNoHardlinkWitness inodeFileDigestAgreement checkerTranscript
      benchmarkFingerprint solverBuildEvidence archiveManifest
      noClaimFallback auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _pathProof _linkProof _digestProof _checkerProof _fingerprintProof
          _buildProof _archiveProof _fallbackProof auditProof => auditProof)

theorem ay_shlg_sat_publication_intro
    (linkContract acceptedLinkcleanArtifact checkedModel originalModel :
      Prop) :
    linkContract -> acceptedLinkcleanArtifact -> checkedModel ->
    originalModel ->
    ay_shlg_sat_publication linkContract acceptedLinkcleanArtifact
      checkedModel originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_shlg_conj_intro linkContract
      (ay_shlg_conj acceptedLinkcleanArtifact
        (ay_shlg_conj checkedModel originalModel))
      contractProof
      (ay_shlg_conj_intro acceptedLinkcleanArtifact
        (ay_shlg_conj checkedModel originalModel)
        acceptedProof
        (ay_shlg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_shlg_sat_publication_link
    (linkContract acceptedLinkcleanArtifact checkedModel originalModel :
      Prop) :
    ay_shlg_sat_publication linkContract acceptedLinkcleanArtifact
      checkedModel originalModel ->
    linkContract :=
  fun publication =>
    ay_shlg_conj_left linkContract
      (ay_shlg_conj acceptedLinkcleanArtifact
        (ay_shlg_conj checkedModel originalModel))
      publication

theorem ay_shlg_sat_publication_original_model
    (linkContract acceptedLinkcleanArtifact checkedModel originalModel :
      Prop) :
    ay_shlg_sat_publication linkContract acceptedLinkcleanArtifact
      checkedModel originalModel ->
    originalModel :=
  fun publication =>
    ay_shlg_conj_right checkedModel originalModel
      (ay_shlg_conj_right acceptedLinkcleanArtifact
        (ay_shlg_conj checkedModel originalModel)
        (ay_shlg_conj_right linkContract
          (ay_shlg_conj acceptedLinkcleanArtifact
            (ay_shlg_conj checkedModel originalModel))
          publication))

theorem ay_shlg_unsat_publication_intro
    (linkContract acceptedLinkcleanArtifact checkedProof originalEmptyClause :
      Prop) :
    linkContract -> acceptedLinkcleanArtifact -> checkedProof ->
    originalEmptyClause ->
    ay_shlg_unsat_publication linkContract acceptedLinkcleanArtifact
      checkedProof originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_shlg_conj_intro linkContract
      (ay_shlg_conj acceptedLinkcleanArtifact
        (ay_shlg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_shlg_conj_intro acceptedLinkcleanArtifact
        (ay_shlg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_shlg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_shlg_unsat_publication_link
    (linkContract acceptedLinkcleanArtifact checkedProof originalEmptyClause :
      Prop) :
    ay_shlg_unsat_publication linkContract acceptedLinkcleanArtifact
      checkedProof originalEmptyClause ->
    linkContract :=
  fun publication =>
    ay_shlg_conj_left linkContract
      (ay_shlg_conj acceptedLinkcleanArtifact
        (ay_shlg_conj checkedProof originalEmptyClause))
      publication

theorem ay_shlg_unsat_publication_original_empty_clause
    (linkContract acceptedLinkcleanArtifact checkedProof originalEmptyClause :
      Prop) :
    ay_shlg_unsat_publication linkContract acceptedLinkcleanArtifact
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_shlg_conj_right checkedProof originalEmptyClause
      (ay_shlg_conj_right acceptedLinkcleanArtifact
        (ay_shlg_conj checkedProof originalEmptyClause)
        (ay_shlg_conj_right linkContract
          (ay_shlg_conj acceptedLinkcleanArtifact
            (ay_shlg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_shlg_accepted_link_clean_sat_passes_publication
    (linkContract acceptedLinkcleanArtifact checkedModel originalModel :
      Prop) :
    ay_shlg_sat_publication linkContract acceptedLinkcleanArtifact
      checkedModel originalModel ->
    ay_shlg_public_result originalModel False False :=
  fun publication =>
    ay_shlg_disj_left originalModel (ay_shlg_disj False False)
      (ay_shlg_sat_publication_original_model linkContract
        acceptedLinkcleanArtifact checkedModel originalModel publication)

theorem ay_shlg_accepted_link_clean_unsat_passes_publication
    (linkContract acceptedLinkcleanArtifact checkedProof originalEmptyClause :
      Prop) :
    ay_shlg_unsat_publication linkContract acceptedLinkcleanArtifact
      checkedProof originalEmptyClause ->
    ay_shlg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_shlg_disj_right False (ay_shlg_disj originalEmptyClause False)
      (ay_shlg_disj_left originalEmptyClause False
        (ay_shlg_unsat_publication_original_empty_clause linkContract
          acceptedLinkcleanArtifact checkedProof originalEmptyClause
          publication))

theorem ay_shlg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_shlg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_shlg_conj_intro reason (ay_shlg_conj fallbackPath auditTrail)
      reasonProof
      (ay_shlg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_shlg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_shlg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_shlg_conj_intro reason
      (ay_shlg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_shlg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_shlg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_shlg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_shlg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_shlg_conj_right reason
        (ay_shlg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_shlg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_shlg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_shlg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_shlg_conj_right reason
        (ay_shlg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_shlg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_shlg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_shlg_conj_intro reason
      (ay_shlg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_shlg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_shlg_link_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_shlg_blocked_publication satFact unsatFact reason ->
    ay_shlg_recompute reason fallbackPath recomputeObligation ->
    ay_shlg_link_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_shlg_conj_intro
      (ay_shlg_blocked_publication satFact unsatFact reason)
      (ay_shlg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_shlg_link_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_shlg_link_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_shlg_blocked_publication_no_sat satFact unsatFact reason
      (ay_shlg_conj_left
        (ay_shlg_blocked_publication satFact unsatFact reason)
        (ay_shlg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_shlg_link_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_shlg_link_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_shlg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_shlg_conj_left
        (ay_shlg_blocked_publication satFact unsatFact reason)
        (ay_shlg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_shlg_link_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_shlg_link_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_shlg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_shlg_conj_right
      (ay_shlg_blocked_publication satFact unsatFact reason)
      (ay_shlg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_shlg_symlink_traversal_forces_no_claim
    (satFact unsatFact symlinkTraversal fallbackPath auditTrail
      recomputeObligation : Prop) :
    symlinkTraversal -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_shlg_no_claim symlinkTraversal fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_shlg_no_claim_intro symlinkTraversal fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_shlg_hardlink_aliasing_forces_recompute
    (satFact unsatFact hardlinkAliasing fallbackPath recomputeObligation :
      Prop) :
    hardlinkAliasing -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_shlg_link_failure satFact unsatFact hardlinkAliasing fallbackPath
      recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_shlg_link_failure_intro satFact unsatFact hardlinkAliasing
      fallbackPath recomputeObligation
      (ay_shlg_blocked_publication_intro satFact unsatFact hardlinkAliasing
        reasonProof noSat noUnsat)
      (ay_shlg_recompute_intro hardlinkAliasing fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_shlg_inode_digest_mismatch_forces_no_claim
    (satFact unsatFact inodeDigestMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    inodeDigestMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_shlg_no_claim inodeDigestMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_shlg_no_claim_intro inodeDigestMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_shlg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_shlg_no_claim checkerMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_shlg_no_claim_intro checkerMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_shlg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_shlg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_shlg_no_claim_intro fingerprintMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_shlg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_shlg_no_claim buildMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_shlg_no_claim_intro buildMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_shlg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_shlg_no_claim archiveMismatch fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_shlg_no_claim_intro archiveMismatch fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_shlg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivation fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivation -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_shlg_no_claim fallbackActivation fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_shlg_no_claim_intro fallbackActivation fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_shlg_failed_link_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_shlg_link_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_shlg_link_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_shlg_failed_link_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_shlg_link_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_shlg_link_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_shlg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_shlg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_shlg_conj_left reason (ay_shlg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_shlg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_shlg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_shlg_conj_left reason (ay_shlg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
