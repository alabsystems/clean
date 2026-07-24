-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof archive hash guard soundness for ay sequential-main
-- SAT-COMP publication. Propositions stand for proof archive digests, chunk
-- digest lists, manifest-to-file mappings, checker transcript digests,
-- empty-clause reachability witnesses, benchmark fingerprints, solver build
-- evidence, submission archive manifests, fallback baselines, audit
-- transcripts, and fail-closed no-claim/recompute diagnostics.

def AyPAHGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyPAHGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyPAHGMap (source : Prop) (target : Prop) :=
  source -> target

def AyPAHGAcceptedEvidence
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofArchiveDigest ->
      chunkDigestList ->
      manifestFileMap ->
      checkerTranscriptDigest ->
      emptyClauseReachable ->
      benchmarkFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      submissionArchiveManifest ->
      fallbackBaseline ->
      auditTranscript ->
      visibleUnsat ->
      originalUnsat ->
      result) ->
    result

def AyPAHGArchiveHashComposition
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyPAHGConj
    (AyPAHGMap proofArchiveDigest chunkDigestList)
    (AyPAHGConj
      (AyPAHGMap chunkDigestList manifestFileMap)
      (AyPAHGConj
        (AyPAHGMap manifestFileMap checkerTranscriptDigest)
        (AyPAHGConj
          (AyPAHGMap checkerTranscriptDigest emptyClauseReachable)
          (AyPAHGConj
            (AyPAHGMap emptyClauseReachable visibleUnsat)
            (AyPAHGMap visibleUnsat originalUnsat)))))

def AyPAHGPublication
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyPAHGConj
    (AyPAHGAcceptedEvidence proofArchiveDigest chunkDigestList
      manifestFileMap checkerTranscriptDigest emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted submissionArchiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat)
    originalUnsat

def AyPAHGFailureReason
    (missingChunk : Prop) (reorderedChunk : Prop) (corruptChunk : Prop)
    (manifestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (missingChunk -> result) ->
    (reorderedChunk -> result) ->
    (corruptChunk -> result) ->
    (manifestMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (fallbackMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def AyPAHGBadArchiveHash
    (missingChunk : Prop) (reorderedChunk : Prop) (corruptChunk : Prop)
    (manifestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyPAHGConj
    (AyPAHGConj noClaim recompute)
    (AyPAHGFailureReason missingChunk reorderedChunk corruptChunk
      manifestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch)

def AyPAHGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyPAHGDisj noClaim originalUnsat

theorem ay_pahg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyPAHGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_pahg_conj_left
    (p : Prop) (q : Prop) :
    AyPAHGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_pahg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyPAHGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_pahg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyPAHGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_pahg_accepted_evidence
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    proofArchiveDigest ->
    chunkDigestList ->
    manifestFileMap ->
    checkerTranscriptDigest ->
    emptyClauseReachable ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    submissionArchiveManifest ->
    fallbackBaseline ->
    auditTranscript ->
    visibleUnsat ->
    originalUnsat ->
    AyPAHGAcceptedEvidence proofArchiveDigest chunkDigestList manifestFileMap
      checkerTranscriptDigest emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted
      submissionArchiveManifest fallbackBaseline auditTranscript visibleUnsat
      originalUnsat := by
  intro hArchiveDigest hChunks hMap hCheckerDigest hEmpty hFingerprint
  intro hFingerprintAccepted hBuild hBuildAccepted hSubmission hFallback
  intro hAudit hVisible hOriginal result publish
  exact publish hArchiveDigest hChunks hMap hCheckerDigest hEmpty hFingerprint
    hFingerprintAccepted hBuild hBuildAccepted hSubmission hFallback hAudit
    hVisible hOriginal

theorem ay_pahg_proof_archive_digest
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPAHGAcceptedEvidence proofArchiveDigest chunkDigestList manifestFileMap
      checkerTranscriptDigest emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted
      submissionArchiveManifest fallbackBaseline auditTranscript visibleUnsat
      originalUnsat ->
    proofArchiveDigest := by
  intro accepted
  exact accepted proofArchiveDigest
    (fun hArchiveDigest _hChunks _hMap _hCheckerDigest _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hSubmission _hFallback
      _hAudit _hVisible _hOriginal => hArchiveDigest)

theorem ay_pahg_chunk_digest_list
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPAHGAcceptedEvidence proofArchiveDigest chunkDigestList manifestFileMap
      checkerTranscriptDigest emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted
      submissionArchiveManifest fallbackBaseline auditTranscript visibleUnsat
      originalUnsat ->
    chunkDigestList := by
  intro accepted
  exact accepted chunkDigestList
    (fun _hArchiveDigest hChunks _hMap _hCheckerDigest _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hSubmission _hFallback
      _hAudit _hVisible _hOriginal => hChunks)

theorem ay_pahg_manifest_file_map
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPAHGAcceptedEvidence proofArchiveDigest chunkDigestList manifestFileMap
      checkerTranscriptDigest emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted
      submissionArchiveManifest fallbackBaseline auditTranscript visibleUnsat
      originalUnsat ->
    manifestFileMap := by
  intro accepted
  exact accepted manifestFileMap
    (fun _hArchiveDigest _hChunks hMap _hCheckerDigest _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hSubmission _hFallback
      _hAudit _hVisible _hOriginal => hMap)

theorem ay_pahg_checker_transcript_digest
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPAHGAcceptedEvidence proofArchiveDigest chunkDigestList manifestFileMap
      checkerTranscriptDigest emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted
      submissionArchiveManifest fallbackBaseline auditTranscript visibleUnsat
      originalUnsat ->
    checkerTranscriptDigest := by
  intro accepted
  exact accepted checkerTranscriptDigest
    (fun _hArchiveDigest _hChunks _hMap hCheckerDigest _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hSubmission _hFallback
      _hAudit _hVisible _hOriginal => hCheckerDigest)

theorem ay_pahg_empty_clause_reachable
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPAHGAcceptedEvidence proofArchiveDigest chunkDigestList manifestFileMap
      checkerTranscriptDigest emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted
      submissionArchiveManifest fallbackBaseline auditTranscript visibleUnsat
      originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hArchiveDigest _hChunks _hMap _hCheckerDigest hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hSubmission _hFallback
      _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_pahg_benchmark_fingerprint
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPAHGAcceptedEvidence proofArchiveDigest chunkDigestList manifestFileMap
      checkerTranscriptDigest emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted
      submissionArchiveManifest fallbackBaseline auditTranscript visibleUnsat
      originalUnsat ->
    benchmarkFingerprint := by
  intro accepted
  exact accepted benchmarkFingerprint
    (fun _hArchiveDigest _hChunks _hMap _hCheckerDigest _hEmpty hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hSubmission _hFallback
      _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_pahg_submission_archive_manifest
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPAHGAcceptedEvidence proofArchiveDigest chunkDigestList manifestFileMap
      checkerTranscriptDigest emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted
      submissionArchiveManifest fallbackBaseline auditTranscript visibleUnsat
      originalUnsat ->
    submissionArchiveManifest := by
  intro accepted
  exact accepted submissionArchiveManifest
    (fun _hArchiveDigest _hChunks _hMap _hCheckerDigest _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted hSubmission _hFallback
      _hAudit _hVisible _hOriginal => hSubmission)

theorem ay_pahg_original_unsat
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPAHGAcceptedEvidence proofArchiveDigest chunkDigestList manifestFileMap
      checkerTranscriptDigest emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted
      submissionArchiveManifest fallbackBaseline auditTranscript visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hArchiveDigest _hChunks _hMap _hCheckerDigest _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hSubmission _hFallback
      _hAudit _hVisible hOriginal => hOriginal)

theorem ay_pahg_archive_hash_composes_to_original
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    proofArchiveDigest ->
    AyPAHGArchiveHashComposition proofArchiveDigest chunkDigestList
      manifestFileMap checkerTranscriptDigest emptyClauseReachable visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro hArchiveDigest
  intro composed
  exact composed originalUnsat
    (fun archive_to_chunks rest1 =>
      rest1 originalUnsat
        (fun chunks_to_manifest rest2 =>
          rest2 originalUnsat
            (fun manifest_to_checker rest3 =>
              rest3 originalUnsat
                (fun checker_to_empty rest4 =>
                  rest4 originalUnsat
                    (fun empty_to_visible visible_to_original =>
                      visible_to_original
                        (empty_to_visible
                          (checker_to_empty
                            (manifest_to_checker
                              (chunks_to_manifest
                                (archive_to_chunks hArchiveDigest))))))))))

theorem ay_pahg_publication_sound
    (proofArchiveDigest : Prop) (chunkDigestList : Prop)
    (manifestFileMap : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionArchiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPAHGPublication proofArchiveDigest chunkDigestList manifestFileMap
      checkerTranscriptDigest emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted
      submissionArchiveManifest fallbackBaseline auditTranscript visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted unsat => unsat)

theorem ay_pahg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyPAHGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_pahg_disj_right noClaim originalUnsat unsat

theorem ay_pahg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyPAHGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_pahg_disj_left noClaim originalUnsat no_claim

theorem ay_pahg_bad_no_claim
    (missingChunk : Prop) (reorderedChunk : Prop) (corruptChunk : Prop)
    (manifestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPAHGBadArchiveHash missingChunk reorderedChunk corruptChunk
      manifestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_pahg_bad_recompute
    (missingChunk : Prop) (reorderedChunk : Prop) (corruptChunk : Prop)
    (manifestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPAHGBadArchiveHash missingChunk reorderedChunk corruptChunk
      manifestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_pahg_failed_archive_hash_cannot_bless_unsat
    (missingChunk : Prop) (reorderedChunk : Prop) (corruptChunk : Prop)
    (manifestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyPAHGBadArchiveHash missingChunk reorderedChunk corruptChunk
      manifestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    AyPAHGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_pahg_public_no_claim_report noClaim originalUnsat
    (ay_pahg_bad_no_claim missingChunk reorderedChunk corruptChunk
      manifestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_pahg_failure_forces_no_claim
    (missingChunk : Prop) (reorderedChunk : Prop) (corruptChunk : Prop)
    (manifestMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPAHGBadArchiveHash missingChunk reorderedChunk corruptChunk
      manifestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    AyPAHGConj noClaim recompute := by
  intro bad
  exact ay_pahg_conj_intro noClaim recompute
    (ay_pahg_bad_no_claim missingChunk reorderedChunk corruptChunk
      manifestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)
    (ay_pahg_bad_recompute missingChunk reorderedChunk corruptChunk
      manifestMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_pahg_missing_chunk_forces_no_claim
    (missingChunk : Prop) (noClaim : Prop) :
    missingChunk -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pahg_reordered_chunk_forces_no_claim
    (reorderedChunk : Prop) (noClaim : Prop) :
    reorderedChunk -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pahg_corrupt_chunk_forces_no_claim
    (corruptChunk : Prop) (noClaim : Prop) :
    corruptChunk -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pahg_manifest_mismatch_forces_no_claim
    (manifestMismatch : Prop) (noClaim : Prop) :
    manifestMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pahg_checker_mismatch_forces_no_claim
    (checkerMismatch : Prop) (noClaim : Prop) :
    checkerMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pahg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pahg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pahg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pahg_fallback_mismatch_forces_no_claim
    (fallbackMismatch : Prop) (noClaim : Prop) :
    fallbackMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pahg_audit_mismatch_forces_no_claim
    (auditMismatch : Prop) (noClaim : Prop) :
    auditMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
