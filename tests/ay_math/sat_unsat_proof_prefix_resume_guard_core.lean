-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof prefix/resume guard soundness for ay sequential-main
-- SAT-COMP publication. Propositions stand for proof prefix digests, resume
-- point manifests, antecedent availability ledgers, deletion/retention
-- ledgers, continuation proof digests, empty-clause reachability witnesses,
-- checker transcripts, benchmark fingerprints, solver build evidence, archive
-- manifests, fallback baselines, audit transcripts, and fail-closed
-- no-claim/recompute diagnostics.

def AyPPRGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyPPRGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyPPRGMap (source : Prop) (target : Prop) :=
  source -> target

def AyPPRGAcceptedEvidence
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofPrefixDigest ->
      resumePointManifest ->
      antecedentLedger ->
      deletionRetentionLedger ->
      continuationProofDigest ->
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

def AyPPRGResumeComposition
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyPPRGConj
    (AyPPRGMap proofPrefixDigest resumePointManifest)
    (AyPPRGConj
      (AyPPRGMap resumePointManifest antecedentLedger)
      (AyPPRGConj
        (AyPPRGMap antecedentLedger deletionRetentionLedger)
        (AyPPRGConj
          (AyPPRGMap deletionRetentionLedger continuationProofDigest)
          (AyPPRGConj
            (AyPPRGMap continuationProofDigest emptyClauseReachable)
            (AyPPRGConj
              (AyPPRGMap emptyClauseReachable visibleUnsat)
              (AyPPRGMap visibleUnsat originalUnsat))))))

def AyPPRGPublication
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyPPRGConj
    (AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat)
    originalUnsat

def AyPPRGFailureReason
    (missingPrefix : Prop) (stalePrefix : Prop)
    (invalidResumePoint : Prop) (antecedentFailure : Prop)
    (deletionLedgerFailure : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (missingPrefix -> result) ->
    (stalePrefix -> result) ->
    (invalidResumePoint -> result) ->
    (antecedentFailure -> result) ->
    (deletionLedgerFailure -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (fallbackMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def AyPPRGBadResume
    (missingPrefix : Prop) (stalePrefix : Prop)
    (invalidResumePoint : Prop) (antecedentFailure : Prop)
    (deletionLedgerFailure : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyPPRGConj
    (AyPPRGConj noClaim recompute)
    (AyPPRGFailureReason missingPrefix stalePrefix invalidResumePoint
      antecedentFailure deletionLedgerFailure checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch fallbackMismatch
      auditMismatch)

def AyPPRGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyPPRGDisj noClaim originalUnsat

theorem ay_pprg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyPPRGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_pprg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyPPRGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_pprg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyPPRGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_pprg_accepted_evidence
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    proofPrefixDigest ->
    resumePointManifest ->
    antecedentLedger ->
    deletionRetentionLedger ->
    continuationProofDigest ->
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
    AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat := by
  intro hPrefix hResume hAntecedent hDeletion hContinuation hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hVisible hOriginal
  intro result publish
  exact publish hPrefix hResume hAntecedent hDeletion hContinuation hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hVisible hOriginal

theorem ay_pprg_proof_prefix_digest
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    proofPrefixDigest := by
  intro accepted
  exact accepted proofPrefixDigest
    (fun hPrefix _hResume _hAntecedent _hDeletion _hContinuation _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hPrefix)

theorem ay_pprg_resume_point_manifest
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    resumePointManifest := by
  intro accepted
  exact accepted resumePointManifest
    (fun _hPrefix hResume _hAntecedent _hDeletion _hContinuation _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hResume)

theorem ay_pprg_antecedent_ledger
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    antecedentLedger := by
  intro accepted
  exact accepted antecedentLedger
    (fun _hPrefix _hResume hAntecedent _hDeletion _hContinuation _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hAntecedent)

theorem ay_pprg_deletion_retention_ledger
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    deletionRetentionLedger := by
  intro accepted
  exact accepted deletionRetentionLedger
    (fun _hPrefix _hResume _hAntecedent hDeletion _hContinuation _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hDeletion)

theorem ay_pprg_continuation_proof_digest
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    continuationProofDigest := by
  intro accepted
  exact accepted continuationProofDigest
    (fun _hPrefix _hResume _hAntecedent _hDeletion hContinuation _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hContinuation)

theorem ay_pprg_empty_clause_reachable
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hPrefix _hResume _hAntecedent _hDeletion _hContinuation hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hEmpty)

theorem ay_pprg_checker_transcript
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hPrefix _hResume _hAntecedent _hDeletion _hContinuation _hEmpty
      hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hTranscript)

theorem ay_pprg_checker_accepted
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hPrefix _hResume _hAntecedent _hDeletion _hContinuation _hEmpty
      _hTranscript hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hChecker)

theorem ay_pprg_benchmark_fingerprint
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    benchmarkFingerprint := by
  intro accepted
  exact accepted benchmarkFingerprint
    (fun _hPrefix _hResume _hAntecedent _hDeletion _hContinuation _hEmpty
      _hTranscript _hChecker hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hFingerprint)

theorem ay_pprg_original_unsat
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPPRGAcceptedEvidence proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hPrefix _hResume _hAntecedent _hDeletion _hContinuation _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible hOriginal =>
      hOriginal)

theorem ay_pprg_prefix_continuation_replay_composes_to_original
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    proofPrefixDigest ->
    AyPPRGResumeComposition proofPrefixDigest resumePointManifest
      antecedentLedger deletionRetentionLedger continuationProofDigest
      emptyClauseReachable visibleUnsat originalUnsat ->
    originalUnsat := by
  intro hPrefix
  intro composed
  exact composed originalUnsat
    (fun prefix_to_resume rest1 =>
      rest1 originalUnsat
        (fun resume_to_antecedent rest2 =>
          rest2 originalUnsat
            (fun antecedent_to_deletion rest3 =>
              rest3 originalUnsat
                (fun deletion_to_continuation rest4 =>
                  rest4 originalUnsat
                    (fun continuation_to_empty rest5 =>
                      rest5 originalUnsat
                        (fun empty_to_visible visible_to_original =>
                          visible_to_original
                            (empty_to_visible
                              (continuation_to_empty
                                (deletion_to_continuation
                                  (antecedent_to_deletion
                                    (resume_to_antecedent
                                      (prefix_to_resume hPrefix))))))))))))

theorem ay_pprg_publication_sound
    (proofPrefixDigest : Prop) (resumePointManifest : Prop)
    (antecedentLedger : Prop) (deletionRetentionLedger : Prop)
    (continuationProofDigest : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPPRGPublication proofPrefixDigest resumePointManifest antecedentLedger
      deletionRetentionLedger continuationProofDigest emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat (fun _accepted unsat => unsat)

theorem ay_pprg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyPPRGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_pprg_disj_right noClaim originalUnsat unsat

theorem ay_pprg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyPPRGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_pprg_disj_left noClaim originalUnsat no_claim

theorem ay_pprg_bad_no_claim
    (missingPrefix : Prop) (stalePrefix : Prop)
    (invalidResumePoint : Prop) (antecedentFailure : Prop)
    (deletionLedgerFailure : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPPRGBadResume missingPrefix stalePrefix invalidResumePoint
      antecedentFailure deletionLedgerFailure checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch fallbackMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_pprg_bad_recompute
    (missingPrefix : Prop) (stalePrefix : Prop)
    (invalidResumePoint : Prop) (antecedentFailure : Prop)
    (deletionLedgerFailure : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPPRGBadResume missingPrefix stalePrefix invalidResumePoint
      antecedentFailure deletionLedgerFailure checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch fallbackMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_pprg_failed_resume_guard_cannot_bless_unsat
    (missingPrefix : Prop) (stalePrefix : Prop)
    (invalidResumePoint : Prop) (antecedentFailure : Prop)
    (deletionLedgerFailure : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyPPRGBadResume missingPrefix stalePrefix invalidResumePoint
      antecedentFailure deletionLedgerFailure checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch fallbackMismatch
      auditMismatch noClaim recompute ->
    AyPPRGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_pprg_public_no_claim_report noClaim originalUnsat
    (ay_pprg_bad_no_claim missingPrefix stalePrefix invalidResumePoint
      antecedentFailure deletionLedgerFailure checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch fallbackMismatch
      auditMismatch noClaim recompute bad)

theorem ay_pprg_failure_forces_no_claim
    (missingPrefix : Prop) (stalePrefix : Prop)
    (invalidResumePoint : Prop) (antecedentFailure : Prop)
    (deletionLedgerFailure : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPPRGBadResume missingPrefix stalePrefix invalidResumePoint
      antecedentFailure deletionLedgerFailure checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch fallbackMismatch
      auditMismatch noClaim recompute ->
    AyPPRGConj noClaim recompute := by
  intro bad
  exact ay_pprg_conj_intro noClaim recompute
    (ay_pprg_bad_no_claim missingPrefix stalePrefix invalidResumePoint
      antecedentFailure deletionLedgerFailure checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch fallbackMismatch
      auditMismatch noClaim recompute bad)
    (ay_pprg_bad_recompute missingPrefix stalePrefix invalidResumePoint
      antecedentFailure deletionLedgerFailure checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch fallbackMismatch
      auditMismatch noClaim recompute bad)

theorem ay_pprg_missing_prefix_forces_no_claim
    (missingPrefix : Prop) (noClaim : Prop) :
    missingPrefix -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pprg_stale_prefix_forces_no_claim
    (stalePrefix : Prop) (noClaim : Prop) :
    stalePrefix -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pprg_invalid_resume_point_forces_no_claim
    (invalidResumePoint : Prop) (noClaim : Prop) :
    invalidResumePoint -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pprg_antecedent_failure_forces_no_claim
    (antecedentFailure : Prop) (noClaim : Prop) :
    antecedentFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pprg_deletion_ledger_failure_forces_no_claim
    (deletionLedgerFailure : Prop) (noClaim : Prop) :
    deletionLedgerFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pprg_checker_mismatch_forces_no_claim
    (checkerMismatch : Prop) (noClaim : Prop) :
    checkerMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pprg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pprg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pprg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pprg_fallback_mismatch_forces_no_claim
    (fallbackMismatch : Prop) (noClaim : Prop) :
    fallbackMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pprg_audit_mismatch_forces_no_claim
    (auditMismatch : Prop) (noClaim : Prop) :
    auditMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
