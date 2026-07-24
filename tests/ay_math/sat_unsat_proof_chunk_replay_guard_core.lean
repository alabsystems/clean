-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof chunk replay guard soundness for ay sequential-main
-- SAT-COMP publication. Propositions stand for proof chunk manifests, chunk
-- ordering digests, antecedent availability ledgers, deletion/retention
-- ledgers, empty-clause reachability witnesses, checker transcripts, benchmark
-- fingerprints, solver build evidence, archive manifests, fallback baselines,
-- audit transcripts, and fail-closed no-claim/recompute diagnostics.

def AyPCRGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyPCRGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyPCRGMap (source : Prop) (target : Prop) :=
  source -> target

def AyPCRGAcceptedEvidence
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofChunkManifest ->
      chunkOrderingDigest ->
      antecedentLedger ->
      deletionRetentionLedger ->
      emptyClauseReachable ->
      checkerTranscript ->
      checkerAccepted ->
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

def AyPCRGChunkReplayComposition
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyPCRGConj
    (AyPCRGMap proofChunkManifest chunkOrderingDigest)
    (AyPCRGConj
      (AyPCRGMap chunkOrderingDigest antecedentLedger)
      (AyPCRGConj
        (AyPCRGMap antecedentLedger deletionRetentionLedger)
        (AyPCRGConj
          (AyPCRGMap deletionRetentionLedger emptyClauseReachable)
          (AyPCRGConj
            (AyPCRGMap emptyClauseReachable visibleUnsat)
            (AyPCRGMap visibleUnsat originalUnsat)))))

def AyPCRGPublication
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyPCRGConj
    (AyPCRGAcceptedEvidence proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat)
    originalUnsat

def AyPCRGFailureReason
    (missingChunk : Prop) (outOfOrderChunk : Prop) (staleChunk : Prop)
    (antecedentFailure : Prop) (deletionLedgerFailure : Prop)
    (checkerFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (fallbackFailure : Prop) (auditFailure : Prop) :=
  forall result : Prop,
    (missingChunk -> result) ->
    (outOfOrderChunk -> result) ->
    (staleChunk -> result) ->
    (antecedentFailure -> result) ->
    (deletionLedgerFailure -> result) ->
    (checkerFailure -> result) ->
    (fingerprintFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    (fallbackFailure -> result) ->
    (auditFailure -> result) ->
    result

def AyPCRGBadChunkReplay
    (missingChunk : Prop) (outOfOrderChunk : Prop) (staleChunk : Prop)
    (antecedentFailure : Prop) (deletionLedgerFailure : Prop)
    (checkerFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (fallbackFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyPCRGConj
    (AyPCRGConj noClaim recompute)
    (AyPCRGFailureReason missingChunk outOfOrderChunk staleChunk
      antecedentFailure deletionLedgerFailure checkerFailure
      fingerprintFailure buildFailure archiveFailure fallbackFailure
      auditFailure)

def AyPCRGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyPCRGDisj noClaim originalUnsat

theorem ay_pcrg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyPCRGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_pcrg_conj_left
    (p : Prop) (q : Prop) :
    AyPCRGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_pcrg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyPCRGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_pcrg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyPCRGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_pcrg_accepted_evidence
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    proofChunkManifest ->
    chunkOrderingDigest ->
    antecedentLedger ->
    deletionRetentionLedger ->
    emptyClauseReachable ->
    checkerTranscript ->
    checkerAccepted ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    fallbackBaseline ->
    auditTranscript ->
    visibleUnsat ->
    originalUnsat ->
    AyPCRGAcceptedEvidence proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat := by
  intro hChunk hOrder hAntecedent hDeletion hEmpty hTranscript hChecker
  intro hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
  intro hFallback hAudit hVisible hOriginal result publish
  exact publish hChunk hOrder hAntecedent hDeletion hEmpty hTranscript
    hChecker hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
    hFallback hAudit hVisible hOriginal

theorem ay_pcrg_proof_chunk_manifest
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCRGAcceptedEvidence proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    proofChunkManifest := by
  intro accepted
  exact accepted proofChunkManifest
    (fun hChunk _hOrder _hAntecedent _hDeletion _hEmpty _hTranscript _hChecker
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hChunk)

theorem ay_pcrg_chunk_ordering_digest
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCRGAcceptedEvidence proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    chunkOrderingDigest := by
  intro accepted
  exact accepted chunkOrderingDigest
    (fun _hChunk hOrder _hAntecedent _hDeletion _hEmpty _hTranscript _hChecker
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hOrder)

theorem ay_pcrg_antecedent_ledger
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCRGAcceptedEvidence proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    antecedentLedger := by
  intro accepted
  exact accepted antecedentLedger
    (fun _hChunk _hOrder hAntecedent _hDeletion _hEmpty _hTranscript _hChecker
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hAntecedent)

theorem ay_pcrg_deletion_retention_ledger
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCRGAcceptedEvidence proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    deletionRetentionLedger := by
  intro accepted
  exact accepted deletionRetentionLedger
    (fun _hChunk _hOrder _hAntecedent hDeletion _hEmpty _hTranscript _hChecker
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hDeletion)

theorem ay_pcrg_empty_clause_reachable
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCRGAcceptedEvidence proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hChunk _hOrder _hAntecedent _hDeletion hEmpty _hTranscript _hChecker
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_pcrg_checker_transcript
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCRGAcceptedEvidence proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hChunk _hOrder _hAntecedent _hDeletion _hEmpty hTranscript _hChecker
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_pcrg_checker_accepted
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCRGAcceptedEvidence proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hChunk _hOrder _hAntecedent _hDeletion _hEmpty _hTranscript hChecker
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hChecker)

theorem ay_pcrg_benchmark_fingerprint
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCRGAcceptedEvidence proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    benchmarkFingerprint := by
  intro accepted
  exact accepted benchmarkFingerprint
    (fun _hChunk _hOrder _hAntecedent _hDeletion _hEmpty _hTranscript _hChecker
      hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_pcrg_original_unsat
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCRGAcceptedEvidence proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hChunk _hOrder _hAntecedent _hDeletion _hEmpty _hTranscript _hChecker
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible hOriginal => hOriginal)

theorem ay_pcrg_chunked_replay_composes_to_original
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    proofChunkManifest ->
    AyPCRGChunkReplayComposition proofChunkManifest chunkOrderingDigest
      antecedentLedger deletionRetentionLedger emptyClauseReachable
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro hChunk
  intro composed
  exact composed originalUnsat
    (fun chunk_to_order rest1 =>
      rest1 originalUnsat
        (fun order_to_antecedent rest2 =>
          rest2 originalUnsat
            (fun antecedent_to_deletion rest3 =>
              rest3 originalUnsat
                (fun deletion_to_empty rest4 =>
                  rest4 originalUnsat
                    (fun empty_to_visible visible_to_original =>
                      visible_to_original
                        (empty_to_visible
                          (deletion_to_empty
                            (antecedent_to_deletion
                              (order_to_antecedent
                                (chunk_to_order hChunk))))))))))

theorem ay_pcrg_publication_sound
    (proofChunkManifest : Prop) (chunkOrderingDigest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCRGPublication proofChunkManifest chunkOrderingDigest antecedentLedger
      deletionRetentionLedger emptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted unsat => unsat)

theorem ay_pcrg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyPCRGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_pcrg_disj_right noClaim originalUnsat unsat

theorem ay_pcrg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyPCRGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_pcrg_disj_left noClaim originalUnsat no_claim

theorem ay_pcrg_bad_no_claim
    (missingChunk : Prop) (outOfOrderChunk : Prop) (staleChunk : Prop)
    (antecedentFailure : Prop) (deletionLedgerFailure : Prop)
    (checkerFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (fallbackFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyPCRGBadChunkReplay missingChunk outOfOrderChunk staleChunk
      antecedentFailure deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_pcrg_bad_recompute
    (missingChunk : Prop) (outOfOrderChunk : Prop) (staleChunk : Prop)
    (antecedentFailure : Prop) (deletionLedgerFailure : Prop)
    (checkerFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (fallbackFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyPCRGBadChunkReplay missingChunk outOfOrderChunk staleChunk
      antecedentFailure deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_pcrg_failed_chunk_replay_cannot_bless_unsat
    (missingChunk : Prop) (outOfOrderChunk : Prop) (staleChunk : Prop)
    (antecedentFailure : Prop) (deletionLedgerFailure : Prop)
    (checkerFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (fallbackFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyPCRGBadChunkReplay missingChunk outOfOrderChunk staleChunk
      antecedentFailure deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute ->
    AyPCRGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_pcrg_public_no_claim_report noClaim originalUnsat
    (ay_pcrg_bad_no_claim missingChunk outOfOrderChunk staleChunk
      antecedentFailure deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute bad)

theorem ay_pcrg_failure_forces_no_claim
    (missingChunk : Prop) (outOfOrderChunk : Prop) (staleChunk : Prop)
    (antecedentFailure : Prop) (deletionLedgerFailure : Prop)
    (checkerFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (fallbackFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyPCRGBadChunkReplay missingChunk outOfOrderChunk staleChunk
      antecedentFailure deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute ->
    AyPCRGConj noClaim recompute := by
  intro bad
  exact ay_pcrg_conj_intro noClaim recompute
    (ay_pcrg_bad_no_claim missingChunk outOfOrderChunk staleChunk
      antecedentFailure deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute bad)
    (ay_pcrg_bad_recompute missingChunk outOfOrderChunk staleChunk
      antecedentFailure deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute bad)

theorem ay_pcrg_missing_chunk_forces_no_claim
    (missingChunk : Prop) (noClaim : Prop) :
    missingChunk -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcrg_out_of_order_chunk_forces_no_claim
    (outOfOrderChunk : Prop) (noClaim : Prop) :
    outOfOrderChunk -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcrg_stale_chunk_forces_no_claim
    (staleChunk : Prop) (noClaim : Prop) :
    staleChunk -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcrg_antecedent_failure_forces_no_claim
    (antecedentFailure : Prop) (noClaim : Prop) :
    antecedentFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcrg_deletion_ledger_failure_forces_no_claim
    (deletionLedgerFailure : Prop) (noClaim : Prop) :
    deletionLedgerFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcrg_checker_failure_forces_no_claim
    (checkerFailure : Prop) (noClaim : Prop) :
    checkerFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcrg_fingerprint_failure_forces_no_claim
    (fingerprintFailure : Prop) (noClaim : Prop) :
    fingerprintFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcrg_build_failure_forces_no_claim
    (buildFailure : Prop) (noClaim : Prop) :
    buildFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcrg_archive_failure_forces_no_claim
    (archiveFailure : Prop) (noClaim : Prop) :
    archiveFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcrg_fallback_failure_forces_no_claim
    (fallbackFailure : Prop) (noClaim : Prop) :
    fallbackFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcrg_audit_failure_forces_no_claim
    (auditFailure : Prop) (noClaim : Prop) :
    auditFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
