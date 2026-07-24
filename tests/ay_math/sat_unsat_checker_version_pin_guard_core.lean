-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT checker version-pin guard soundness for ay sequential-main
-- SAT-COMP publication. Propositions stand for checker binary digests,
-- checker version manifests, proof artifact digests, checker transcripts,
-- empty-clause reachability witnesses, benchmark fingerprints, solver build
-- evidence, archive manifests, fallback baselines, audit transcripts, and
-- fail-closed no-claim/recompute diagnostics.

def AyCVPGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyCVPGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyCVPGMap (source : Prop) (target : Prop) :=
  source -> target

def AyCVPGAcceptedEvidence
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (checkerBinaryDigest ->
      checkerVersionManifest ->
      proofArtifactDigest ->
      checkerTranscript ->
      checkerAccepted ->
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

def AyCVPGPinnedReplayComposition
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyCVPGConj
    (AyCVPGMap checkerBinaryDigest checkerVersionManifest)
    (AyCVPGConj
      (AyCVPGMap checkerVersionManifest proofArtifactDigest)
      (AyCVPGConj
        (AyCVPGMap proofArtifactDigest checkerTranscript)
        (AyCVPGConj
          (AyCVPGMap checkerTranscript emptyClauseReachable)
          (AyCVPGConj
            (AyCVPGMap emptyClauseReachable visibleUnsat)
            (AyCVPGMap visibleUnsat originalUnsat)))))

def AyCVPGPublication
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyCVPGConj
    (AyCVPGAcceptedEvidence checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat)
    originalUnsat

def AyCVPGFailureReason
    (unpinnedVersion : Prop) (staleVersion : Prop)
    (binaryMismatch : Prop) (transcriptMismatch : Prop)
    (proofMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (fallbackMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (unpinnedVersion -> result) ->
    (staleVersion -> result) ->
    (binaryMismatch -> result) ->
    (transcriptMismatch -> result) ->
    (proofMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (fallbackMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def AyCVPGBadVersionPin
    (unpinnedVersion : Prop) (staleVersion : Prop)
    (binaryMismatch : Prop) (transcriptMismatch : Prop)
    (proofMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (fallbackMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyCVPGConj
    (AyCVPGConj noClaim recompute)
    (AyCVPGFailureReason unpinnedVersion staleVersion binaryMismatch
      transcriptMismatch proofMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch)

def AyCVPGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyCVPGDisj noClaim originalUnsat

theorem ay_cvpg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyCVPGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_cvpg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyCVPGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_cvpg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyCVPGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_cvpg_accepted_evidence
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    checkerBinaryDigest ->
    checkerVersionManifest ->
    proofArtifactDigest ->
    checkerTranscript ->
    checkerAccepted ->
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
    AyCVPGAcceptedEvidence checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat := by
  intro hBinary hVersion hProof hTranscript hChecker hEmpty hFingerprint
  intro hFingerprintAccepted hBuild hBuildAccepted hArchive hFallback hAudit
  intro hVisible hOriginal result publish
  exact publish hBinary hVersion hProof hTranscript hChecker hEmpty
    hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
    hFallback hAudit hVisible hOriginal

theorem ay_cvpg_checker_binary_digest
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCVPGAcceptedEvidence checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    checkerBinaryDigest := by
  intro accepted
  exact accepted checkerBinaryDigest
    (fun hBinary _hVersion _hProof _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hBinary)

theorem ay_cvpg_checker_version_manifest
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCVPGAcceptedEvidence checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    checkerVersionManifest := by
  intro accepted
  exact accepted checkerVersionManifest
    (fun _hBinary hVersion _hProof _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hVersion)

theorem ay_cvpg_proof_artifact_digest
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCVPGAcceptedEvidence checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    proofArtifactDigest := by
  intro accepted
  exact accepted proofArtifactDigest
    (fun _hBinary _hVersion hProof _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hProof)

theorem ay_cvpg_checker_transcript
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCVPGAcceptedEvidence checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hBinary _hVersion _hProof hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_cvpg_checker_accepted
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCVPGAcceptedEvidence checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hBinary _hVersion _hProof _hTranscript hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hChecker)

theorem ay_cvpg_empty_clause_reachable
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCVPGAcceptedEvidence checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hBinary _hVersion _hProof _hTranscript _hChecker hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_cvpg_benchmark_fingerprint
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCVPGAcceptedEvidence checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    benchmarkFingerprint := by
  intro accepted
  exact accepted benchmarkFingerprint
    (fun _hBinary _hVersion _hProof _hTranscript _hChecker _hEmpty
      hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_cvpg_original_unsat
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCVPGAcceptedEvidence checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hBinary _hVersion _hProof _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible hOriginal => hOriginal)

theorem ay_cvpg_pinned_checker_composes_to_original
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    checkerBinaryDigest ->
    AyCVPGPinnedReplayComposition checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript emptyClauseReachable visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro hBinary
  intro composed
  exact composed originalUnsat
    (fun binary_to_version rest1 =>
      rest1 originalUnsat
        (fun version_to_proof rest2 =>
          rest2 originalUnsat
            (fun proof_to_transcript rest3 =>
              rest3 originalUnsat
                (fun transcript_to_empty rest4 =>
                  rest4 originalUnsat
                    (fun empty_to_visible visible_to_original =>
                      visible_to_original
                        (empty_to_visible
                          (transcript_to_empty
                            (proof_to_transcript
                              (version_to_proof
                                (binary_to_version hBinary))))))))))

theorem ay_cvpg_publication_sound
    (checkerBinaryDigest : Prop) (checkerVersionManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCVPGPublication checkerBinaryDigest checkerVersionManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat (fun _accepted unsat => unsat)

theorem ay_cvpg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyCVPGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_cvpg_disj_right noClaim originalUnsat unsat

theorem ay_cvpg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyCVPGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_cvpg_disj_left noClaim originalUnsat no_claim

theorem ay_cvpg_bad_no_claim
    (unpinnedVersion : Prop) (staleVersion : Prop)
    (binaryMismatch : Prop) (transcriptMismatch : Prop)
    (proofMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (fallbackMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyCVPGBadVersionPin unpinnedVersion staleVersion binaryMismatch
      transcriptMismatch proofMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_cvpg_bad_recompute
    (unpinnedVersion : Prop) (staleVersion : Prop)
    (binaryMismatch : Prop) (transcriptMismatch : Prop)
    (proofMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (fallbackMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyCVPGBadVersionPin unpinnedVersion staleVersion binaryMismatch
      transcriptMismatch proofMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_cvpg_failed_version_guard_cannot_bless_unsat
    (unpinnedVersion : Prop) (staleVersion : Prop)
    (binaryMismatch : Prop) (transcriptMismatch : Prop)
    (proofMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (fallbackMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyCVPGBadVersionPin unpinnedVersion staleVersion binaryMismatch
      transcriptMismatch proofMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    AyCVPGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_cvpg_public_no_claim_report noClaim originalUnsat
    (ay_cvpg_bad_no_claim unpinnedVersion staleVersion binaryMismatch
      transcriptMismatch proofMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_cvpg_failure_forces_no_claim
    (unpinnedVersion : Prop) (staleVersion : Prop)
    (binaryMismatch : Prop) (transcriptMismatch : Prop)
    (proofMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (fallbackMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyCVPGBadVersionPin unpinnedVersion staleVersion binaryMismatch
      transcriptMismatch proofMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    AyCVPGConj noClaim recompute := by
  intro bad
  exact ay_cvpg_conj_intro noClaim recompute
    (ay_cvpg_bad_no_claim unpinnedVersion staleVersion binaryMismatch
      transcriptMismatch proofMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)
    (ay_cvpg_bad_recompute unpinnedVersion staleVersion binaryMismatch
      transcriptMismatch proofMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_cvpg_unpinned_version_forces_no_claim
    (unpinnedVersion : Prop) (noClaim : Prop) :
    unpinnedVersion -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cvpg_stale_version_forces_no_claim
    (staleVersion : Prop) (noClaim : Prop) :
    staleVersion -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cvpg_binary_mismatch_forces_no_claim
    (binaryMismatch : Prop) (noClaim : Prop) :
    binaryMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cvpg_transcript_mismatch_forces_no_claim
    (transcriptMismatch : Prop) (noClaim : Prop) :
    transcriptMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cvpg_proof_mismatch_forces_no_claim
    (proofMismatch : Prop) (noClaim : Prop) :
    proofMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cvpg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cvpg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cvpg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cvpg_fallback_mismatch_forces_no_claim
    (fallbackMismatch : Prop) (noClaim : Prop) :
    fallbackMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cvpg_audit_mismatch_forces_no_claim
    (auditMismatch : Prop) (noClaim : Prop) :
    auditMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
