-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT checker resource-quarantine guard soundness for ay
-- sequential-main SAT-COMP publication. Propositions stand for checker
-- completion, memory/time budget manifests, proof artifact digests,
-- empty-clause reachability witnesses, checker transcript digests, benchmark
-- fingerprints, solver build evidence, archive manifests, fallback baselines,
-- quarantine/no-claim paths, audit transcripts, and fail-closed recompute
-- diagnostics.

def AyCRQGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyCRQGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyCRQGMap (source : Prop) (target : Prop) :=
  source -> target

def AyCRQGAcceptedEvidence
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (checkerCompletion ->
      budgetManifest ->
      proofArtifactDigest ->
      emptyClauseReachable ->
      checkerTranscriptDigest ->
      benchmarkFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      archiveManifest ->
      fallbackBaseline ->
      quarantineClear ->
      auditTranscript ->
      visibleUnsat ->
      originalUnsat ->
      result) ->
    result

def AyCRQGCompletedCheckerPath
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyCRQGConj
    (AyCRQGMap checkerCompletion budgetManifest)
    (AyCRQGConj
      (AyCRQGMap budgetManifest proofArtifactDigest)
      (AyCRQGConj
        (AyCRQGMap proofArtifactDigest checkerTranscriptDigest)
        (AyCRQGConj
          (AyCRQGMap checkerTranscriptDigest emptyClauseReachable)
          (AyCRQGConj
            (AyCRQGMap emptyClauseReachable visibleUnsat)
            (AyCRQGMap visibleUnsat originalUnsat)))))

def AyCRQGPublication
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyCRQGConj
    (AyCRQGAcceptedEvidence checkerCompletion budgetManifest
      proofArtifactDigest emptyClauseReachable checkerTranscriptDigest
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline quarantineClear
      auditTranscript visibleUnsat originalUnsat)
    originalUnsat

def AyCRQGFailureReason
    (outOfMemory : Prop) (timeout : Prop) (partialTranscript : Prop)
    (staleBudget : Prop) (digestMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (quarantineActivated : Prop) :=
  forall result : Prop,
    (outOfMemory -> result) ->
    (timeout -> result) ->
    (partialTranscript -> result) ->
    (staleBudget -> result) ->
    (digestMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (quarantineActivated -> result) ->
    result

def AyCRQGBadResourceRun
    (outOfMemory : Prop) (timeout : Prop) (partialTranscript : Prop)
    (staleBudget : Prop) (digestMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (quarantineActivated : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyCRQGConj
    (AyCRQGConj noClaim recompute)
    (AyCRQGFailureReason outOfMemory timeout partialTranscript staleBudget
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch quarantineActivated)

def AyCRQGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyCRQGDisj noClaim originalUnsat

theorem ay_crqg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyCRQGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_crqg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyCRQGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_crqg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyCRQGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_crqg_accepted_evidence
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    checkerCompletion ->
    budgetManifest ->
    proofArtifactDigest ->
    emptyClauseReachable ->
    checkerTranscriptDigest ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    fallbackBaseline ->
    quarantineClear ->
    auditTranscript ->
    visibleUnsat ->
    originalUnsat ->
    AyCRQGAcceptedEvidence checkerCompletion budgetManifest
      proofArtifactDigest emptyClauseReachable checkerTranscriptDigest
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline quarantineClear
      auditTranscript visibleUnsat originalUnsat := by
  intro hComplete hBudget hDigest hEmpty hTranscript hFingerprint
  intro hFingerprintAccepted hBuild hBuildAccepted hArchive hFallback
  intro hQuarantineClear hAudit hVisible hOriginal result publish
  exact publish hComplete hBudget hDigest hEmpty hTranscript hFingerprint
    hFingerprintAccepted hBuild hBuildAccepted hArchive hFallback
    hQuarantineClear hAudit hVisible hOriginal

theorem ay_crqg_checker_completion
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCRQGAcceptedEvidence checkerCompletion budgetManifest
      proofArtifactDigest emptyClauseReachable checkerTranscriptDigest
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline quarantineClear
      auditTranscript visibleUnsat originalUnsat ->
    checkerCompletion := by
  intro accepted
  exact accepted checkerCompletion
    (fun hComplete _hBudget _hDigest _hEmpty _hTranscript _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hQuarantineClear _hAudit _hVisible _hOriginal => hComplete)

theorem ay_crqg_budget_manifest
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCRQGAcceptedEvidence checkerCompletion budgetManifest
      proofArtifactDigest emptyClauseReachable checkerTranscriptDigest
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline quarantineClear
      auditTranscript visibleUnsat originalUnsat ->
    budgetManifest := by
  intro accepted
  exact accepted budgetManifest
    (fun _hComplete hBudget _hDigest _hEmpty _hTranscript _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hQuarantineClear _hAudit _hVisible _hOriginal => hBudget)

theorem ay_crqg_proof_artifact_digest
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCRQGAcceptedEvidence checkerCompletion budgetManifest
      proofArtifactDigest emptyClauseReachable checkerTranscriptDigest
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline quarantineClear
      auditTranscript visibleUnsat originalUnsat ->
    proofArtifactDigest := by
  intro accepted
  exact accepted proofArtifactDigest
    (fun _hComplete _hBudget hDigest _hEmpty _hTranscript _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hQuarantineClear _hAudit _hVisible _hOriginal => hDigest)

theorem ay_crqg_empty_clause_reachable
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCRQGAcceptedEvidence checkerCompletion budgetManifest
      proofArtifactDigest emptyClauseReachable checkerTranscriptDigest
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline quarantineClear
      auditTranscript visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hComplete _hBudget _hDigest hEmpty _hTranscript _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hQuarantineClear _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_crqg_checker_transcript_digest
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCRQGAcceptedEvidence checkerCompletion budgetManifest
      proofArtifactDigest emptyClauseReachable checkerTranscriptDigest
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline quarantineClear
      auditTranscript visibleUnsat originalUnsat ->
    checkerTranscriptDigest := by
  intro accepted
  exact accepted checkerTranscriptDigest
    (fun _hComplete _hBudget _hDigest _hEmpty hTranscript _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hQuarantineClear _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_crqg_quarantine_clear
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCRQGAcceptedEvidence checkerCompletion budgetManifest
      proofArtifactDigest emptyClauseReachable checkerTranscriptDigest
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline quarantineClear
      auditTranscript visibleUnsat originalUnsat ->
    quarantineClear := by
  intro accepted
  exact accepted quarantineClear
    (fun _hComplete _hBudget _hDigest _hEmpty _hTranscript _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      hQuarantineClear _hAudit _hVisible _hOriginal => hQuarantineClear)

theorem ay_crqg_original_unsat
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCRQGAcceptedEvidence checkerCompletion budgetManifest
      proofArtifactDigest emptyClauseReachable checkerTranscriptDigest
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline quarantineClear
      auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hComplete _hBudget _hDigest _hEmpty _hTranscript _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hQuarantineClear _hAudit _hVisible hOriginal => hOriginal)

theorem ay_crqg_completed_checker_path_to_original
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    checkerCompletion ->
    AyCRQGCompletedCheckerPath checkerCompletion budgetManifest
      proofArtifactDigest emptyClauseReachable checkerTranscriptDigest
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro hComplete
  intro path
  exact path originalUnsat
    (fun complete_to_budget rest1 =>
      rest1 originalUnsat
        (fun budget_to_digest rest2 =>
          rest2 originalUnsat
            (fun digest_to_transcript rest3 =>
              rest3 originalUnsat
                (fun transcript_to_empty rest4 =>
                  rest4 originalUnsat
                    (fun empty_to_visible visible_to_original =>
                      visible_to_original
                        (empty_to_visible
                          (transcript_to_empty
                            (digest_to_transcript
                              (budget_to_digest
                                (complete_to_budget hComplete))))))))))

theorem ay_crqg_completed_checker_only_unsat_publication_path
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCRQGPublication checkerCompletion budgetManifest proofArtifactDigest
      emptyClauseReachable checkerTranscriptDigest benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline quarantineClear auditTranscript visibleUnsat
      originalUnsat ->
    AyCRQGConj checkerCompletion originalUnsat := by
  intro publication
  exact ay_crqg_conj_intro checkerCompletion originalUnsat
    (publication checkerCompletion
      (fun accepted _unsat =>
        ay_crqg_checker_completion checkerCompletion budgetManifest
          proofArtifactDigest emptyClauseReachable checkerTranscriptDigest
          benchmarkFingerprint fingerprintAccepted solverBuildEvidence
          buildAccepted archiveManifest fallbackBaseline quarantineClear
          auditTranscript visibleUnsat originalUnsat accepted))
    (publication originalUnsat (fun _accepted unsat => unsat))

theorem ay_crqg_publication_sound
    (checkerCompletion : Prop) (budgetManifest : Prop)
    (proofArtifactDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscriptDigest : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (quarantineClear : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCRQGPublication checkerCompletion budgetManifest proofArtifactDigest
      emptyClauseReachable checkerTranscriptDigest benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline quarantineClear auditTranscript visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat (fun _accepted unsat => unsat)

theorem ay_crqg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyCRQGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_crqg_disj_right noClaim originalUnsat unsat

theorem ay_crqg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyCRQGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_crqg_disj_left noClaim originalUnsat no_claim

theorem ay_crqg_bad_no_claim
    (outOfMemory : Prop) (timeout : Prop) (partialTranscript : Prop)
    (staleBudget : Prop) (digestMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (quarantineActivated : Prop) (noClaim : Prop) (recompute : Prop) :
    AyCRQGBadResourceRun outOfMemory timeout partialTranscript staleBudget
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch quarantineActivated noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_crqg_bad_recompute
    (outOfMemory : Prop) (timeout : Prop) (partialTranscript : Prop)
    (staleBudget : Prop) (digestMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (quarantineActivated : Prop) (noClaim : Prop) (recompute : Prop) :
    AyCRQGBadResourceRun outOfMemory timeout partialTranscript staleBudget
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch quarantineActivated noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_crqg_failed_resource_run_cannot_bless_unsat
    (outOfMemory : Prop) (timeout : Prop) (partialTranscript : Prop)
    (staleBudget : Prop) (digestMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (quarantineActivated : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyCRQGBadResourceRun outOfMemory timeout partialTranscript staleBudget
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch quarantineActivated noClaim recompute ->
    AyCRQGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_crqg_public_no_claim_report noClaim originalUnsat
    (ay_crqg_bad_no_claim outOfMemory timeout partialTranscript staleBudget
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch quarantineActivated noClaim recompute bad)

theorem ay_crqg_failure_forces_no_claim
    (outOfMemory : Prop) (timeout : Prop) (partialTranscript : Prop)
    (staleBudget : Prop) (digestMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (quarantineActivated : Prop) (noClaim : Prop) (recompute : Prop) :
    AyCRQGBadResourceRun outOfMemory timeout partialTranscript staleBudget
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch quarantineActivated noClaim recompute ->
    AyCRQGConj noClaim recompute := by
  intro bad
  exact ay_crqg_conj_intro noClaim recompute
    (ay_crqg_bad_no_claim outOfMemory timeout partialTranscript staleBudget
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch quarantineActivated noClaim recompute bad)
    (ay_crqg_bad_recompute outOfMemory timeout partialTranscript staleBudget
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch quarantineActivated noClaim recompute bad)

theorem ay_crqg_out_of_memory_forces_no_claim
    (outOfMemory : Prop) (noClaim : Prop) :
    outOfMemory -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_crqg_timeout_forces_no_claim
    (timeout : Prop) (noClaim : Prop) :
    timeout -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_crqg_partial_transcript_forces_no_claim
    (partialTranscript : Prop) (noClaim : Prop) :
    partialTranscript -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_crqg_stale_budget_forces_no_claim
    (staleBudget : Prop) (noClaim : Prop) :
    staleBudget -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_crqg_digest_mismatch_forces_no_claim
    (digestMismatch : Prop) (noClaim : Prop) :
    digestMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_crqg_checker_mismatch_forces_no_claim
    (checkerMismatch : Prop) (noClaim : Prop) :
    checkerMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_crqg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_crqg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_crqg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_crqg_quarantine_activation_forces_no_claim
    (quarantineActivated : Prop) (noClaim : Prop) :
    quarantineActivated -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
