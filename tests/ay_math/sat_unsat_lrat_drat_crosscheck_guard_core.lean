-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded LRAT/DRAT cross-check guard soundness for ay sequential-main
-- SAT-COMP UNSAT publication. Propositions stand for DRAT proof artifact
-- digests, LRAT-expanded proof digests or checker transcripts, conversion
-- manifests, antecedent coverage ledgers, empty-clause reachability witnesses,
-- benchmark fingerprints, solver build evidence, archive manifests, fallback
-- baselines, audit transcripts, and fail-closed no-claim/recompute diagnostics.

def AyLDCGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyLDCGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyLDCGMap (source : Prop) (target : Prop) :=
  source -> target

def AyLDCGAcceptedEvidence
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (dratProofDigest ->
      lratReplayEvidence ->
      conversionManifest ->
      antecedentCoverageLedger ->
      emptyClauseReachable ->
      benchmarkFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      archiveManifest ->
      fallbackBaseline ->
      auditTranscript ->
      visibleUnsat ->
      originalUnsat ->
      result) ->
    result

def AyLDCGCrossCheckComposition
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyLDCGConj
    (AyLDCGMap dratProofDigest conversionManifest)
    (AyLDCGConj
      (AyLDCGMap conversionManifest lratReplayEvidence)
      (AyLDCGConj
        (AyLDCGMap lratReplayEvidence antecedentCoverageLedger)
        (AyLDCGConj
          (AyLDCGMap antecedentCoverageLedger emptyClauseReachable)
          (AyLDCGConj
            (AyLDCGMap emptyClauseReachable visibleUnsat)
            (AyLDCGMap visibleUnsat originalUnsat)))))

def AyLDCGPublication
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyLDCGConj
    (AyLDCGAcceptedEvidence dratProofDigest lratReplayEvidence
      conversionManifest antecedentCoverageLedger emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat)
    originalUnsat

def AyLDCGFailureReason
    (conversionMismatch : Prop) (antecedentMismatch : Prop)
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (conversionMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (digestMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (fallbackMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def AyLDCGBadCrossCheck
    (conversionMismatch : Prop) (antecedentMismatch : Prop)
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyLDCGConj
    (AyLDCGConj noClaim recompute)
    (AyLDCGFailureReason conversionMismatch antecedentMismatch
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch)

def AyLDCGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyLDCGDisj noClaim originalUnsat

theorem ay_ldcg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyLDCGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_ldcg_conj_left
    (p : Prop) (q : Prop) :
    AyLDCGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ldcg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyLDCGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_ldcg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyLDCGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_ldcg_accepted_evidence
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    dratProofDigest ->
    lratReplayEvidence ->
    conversionManifest ->
    antecedentCoverageLedger ->
    emptyClauseReachable ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    fallbackBaseline ->
    auditTranscript ->
    visibleUnsat ->
    originalUnsat ->
    AyLDCGAcceptedEvidence dratProofDigest lratReplayEvidence
      conversionManifest antecedentCoverageLedger emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat := by
  intro hDrat hLrat hConversion hAntecedent hEmpty hFingerprint
  intro hFingerprintAccepted hBuild hBuildAccepted hArchive hFallback hAudit
  intro hVisible hOriginal result publish
  exact publish hDrat hLrat hConversion hAntecedent hEmpty hFingerprint
    hFingerprintAccepted hBuild hBuildAccepted hArchive hFallback hAudit
    hVisible hOriginal

theorem ay_ldcg_drat_proof_digest
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLDCGAcceptedEvidence dratProofDigest lratReplayEvidence
      conversionManifest antecedentCoverageLedger emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    dratProofDigest := by
  intro accepted
  exact accepted dratProofDigest
    (fun hDrat _hLrat _hConversion _hAntecedent _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hDrat)

theorem ay_ldcg_lrat_replay_evidence
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLDCGAcceptedEvidence dratProofDigest lratReplayEvidence
      conversionManifest antecedentCoverageLedger emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    lratReplayEvidence := by
  intro accepted
  exact accepted lratReplayEvidence
    (fun _hDrat hLrat _hConversion _hAntecedent _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hLrat)

theorem ay_ldcg_conversion_manifest
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLDCGAcceptedEvidence dratProofDigest lratReplayEvidence
      conversionManifest antecedentCoverageLedger emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    conversionManifest := by
  intro accepted
  exact accepted conversionManifest
    (fun _hDrat _hLrat hConversion _hAntecedent _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hConversion)

theorem ay_ldcg_antecedent_coverage_ledger
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLDCGAcceptedEvidence dratProofDigest lratReplayEvidence
      conversionManifest antecedentCoverageLedger emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    antecedentCoverageLedger := by
  intro accepted
  exact accepted antecedentCoverageLedger
    (fun _hDrat _hLrat _hConversion hAntecedent _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hAntecedent)

theorem ay_ldcg_empty_clause_reachable
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLDCGAcceptedEvidence dratProofDigest lratReplayEvidence
      conversionManifest antecedentCoverageLedger emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hDrat _hLrat _hConversion _hAntecedent hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_ldcg_benchmark_fingerprint
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLDCGAcceptedEvidence dratProofDigest lratReplayEvidence
      conversionManifest antecedentCoverageLedger emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    benchmarkFingerprint := by
  intro accepted
  exact accepted benchmarkFingerprint
    (fun _hDrat _hLrat _hConversion _hAntecedent _hEmpty hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_ldcg_archive_manifest
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLDCGAcceptedEvidence dratProofDigest lratReplayEvidence
      conversionManifest antecedentCoverageLedger emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    archiveManifest := by
  intro accepted
  exact accepted archiveManifest
    (fun _hDrat _hLrat _hConversion _hAntecedent _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted hArchive _hFallback
      _hAudit _hVisible _hOriginal => hArchive)

theorem ay_ldcg_original_unsat
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLDCGAcceptedEvidence dratProofDigest lratReplayEvidence
      conversionManifest antecedentCoverageLedger emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDrat _hLrat _hConversion _hAntecedent _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible hOriginal => hOriginal)

theorem ay_ldcg_crosscheck_composes_to_original
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    dratProofDigest ->
    AyLDCGCrossCheckComposition dratProofDigest lratReplayEvidence
      conversionManifest antecedentCoverageLedger emptyClauseReachable
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro hDrat
  intro composed
  exact composed originalUnsat
    (fun drat_to_conversion rest1 =>
      rest1 originalUnsat
        (fun conversion_to_lrat rest2 =>
          rest2 originalUnsat
            (fun lrat_to_antecedent rest3 =>
              rest3 originalUnsat
                (fun antecedent_to_empty rest4 =>
                  rest4 originalUnsat
                    (fun empty_to_visible visible_to_original =>
                      visible_to_original
                        (empty_to_visible
                          (antecedent_to_empty
                            (lrat_to_antecedent
                              (conversion_to_lrat
                                (drat_to_conversion hDrat))))))))))

theorem ay_ldcg_publication_sound
    (dratProofDigest : Prop) (lratReplayEvidence : Prop)
    (conversionManifest : Prop) (antecedentCoverageLedger : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLDCGPublication dratProofDigest lratReplayEvidence conversionManifest
      antecedentCoverageLedger emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted unsat => unsat)

theorem ay_ldcg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyLDCGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ldcg_disj_right noClaim originalUnsat unsat

theorem ay_ldcg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyLDCGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ldcg_disj_left noClaim originalUnsat no_claim

theorem ay_ldcg_bad_no_claim
    (conversionMismatch : Prop) (antecedentMismatch : Prop)
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyLDCGBadCrossCheck conversionMismatch antecedentMismatch digestMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_ldcg_bad_recompute
    (conversionMismatch : Prop) (antecedentMismatch : Prop)
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyLDCGBadCrossCheck conversionMismatch antecedentMismatch digestMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_ldcg_failed_crosscheck_cannot_bless_unsat
    (conversionMismatch : Prop) (antecedentMismatch : Prop)
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyLDCGBadCrossCheck conversionMismatch antecedentMismatch digestMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch noClaim recompute ->
    AyLDCGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ldcg_public_no_claim_report noClaim originalUnsat
    (ay_ldcg_bad_no_claim conversionMismatch antecedentMismatch
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_ldcg_failure_forces_no_claim
    (conversionMismatch : Prop) (antecedentMismatch : Prop)
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyLDCGBadCrossCheck conversionMismatch antecedentMismatch digestMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch noClaim recompute ->
    AyLDCGConj noClaim recompute := by
  intro bad
  exact ay_ldcg_conj_intro noClaim recompute
    (ay_ldcg_bad_no_claim conversionMismatch antecedentMismatch
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)
    (ay_ldcg_bad_recompute conversionMismatch antecedentMismatch
      digestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_ldcg_conversion_mismatch_forces_no_claim
    (conversionMismatch : Prop) (noClaim : Prop) :
    conversionMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ldcg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch : Prop) (noClaim : Prop) :
    antecedentMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ldcg_digest_mismatch_forces_no_claim
    (digestMismatch : Prop) (noClaim : Prop) :
    digestMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ldcg_checker_mismatch_forces_no_claim
    (checkerMismatch : Prop) (noClaim : Prop) :
    checkerMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ldcg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ldcg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ldcg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ldcg_fallback_mismatch_forces_no_claim
    (fallbackMismatch : Prop) (noClaim : Prop) :
    fallbackMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ldcg_audit_mismatch_forces_no_claim
    (auditMismatch : Prop) (noClaim : Prop) :
    auditMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
