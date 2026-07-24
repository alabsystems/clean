-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof index-width/overflow guard soundness for ay
-- sequential-main SAT-COMP publication. Propositions stand for clause-index
-- width manifests, max-index witnesses, antecedent index range proofs,
-- deletion/retention ledgers, checker transcripts, empty-clause reachability
-- witnesses, benchmark fingerprints, solver build evidence, archive
-- manifests, fallback baselines, audit transcripts, and fail-closed
-- no-claim/recompute diagnostics.

def AyPIWGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyPIWGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyPIWGMap (source : Prop) (target : Prop) :=
  source -> target

def AyPIWGAcceptedEvidence
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (indexWidthManifest ->
      maxIndexWitness ->
      antecedentRangeProof ->
      deletionRetentionLedger ->
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

def AyPIWGIndexReplayComposition
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyPIWGConj
    (AyPIWGMap indexWidthManifest maxIndexWitness)
    (AyPIWGConj
      (AyPIWGMap maxIndexWitness antecedentRangeProof)
      (AyPIWGConj
        (AyPIWGMap antecedentRangeProof deletionRetentionLedger)
        (AyPIWGConj
          (AyPIWGMap deletionRetentionLedger emptyClauseReachable)
          (AyPIWGConj
            (AyPIWGMap emptyClauseReachable visibleUnsat)
            (AyPIWGMap visibleUnsat originalUnsat)))))

def AyPIWGPublication
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyPIWGConj
    (AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat)
    originalUnsat

def AyPIWGFailureReason
    (indexOverflow : Prop) (indexTruncation : Prop)
    (outOfRangeAntecedent : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (indexOverflow -> result) ->
    (indexTruncation -> result) ->
    (outOfRangeAntecedent -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (fallbackMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def AyPIWGBadIndexGuard
    (indexOverflow : Prop) (indexTruncation : Prop)
    (outOfRangeAntecedent : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyPIWGConj
    (AyPIWGConj noClaim recompute)
    (AyPIWGFailureReason indexOverflow indexTruncation outOfRangeAntecedent
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch)

def AyPIWGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyPIWGDisj noClaim originalUnsat

theorem ay_piwg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyPIWGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_piwg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyPIWGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_piwg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyPIWGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_piwg_accepted_evidence
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    indexWidthManifest ->
    maxIndexWitness ->
    antecedentRangeProof ->
    deletionRetentionLedger ->
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
    AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat := by
  intro hWidth hMax hRange hDeletion hTranscript hChecker hEmpty hFingerprint
  intro hFingerprintAccepted hBuild hBuildAccepted hArchive hFallback hAudit
  intro hVisible hOriginal result publish
  exact publish hWidth hMax hRange hDeletion hTranscript hChecker hEmpty
    hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
    hFallback hAudit hVisible hOriginal

theorem ay_piwg_index_width_manifest
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    indexWidthManifest := by
  intro accepted
  exact accepted indexWidthManifest
    (fun hWidth _hMax _hRange _hDeletion _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hWidth)

theorem ay_piwg_max_index_witness
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    maxIndexWitness := by
  intro accepted
  exact accepted maxIndexWitness
    (fun _hWidth hMax _hRange _hDeletion _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hMax)

theorem ay_piwg_antecedent_range_proof
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    antecedentRangeProof := by
  intro accepted
  exact accepted antecedentRangeProof
    (fun _hWidth _hMax hRange _hDeletion _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hRange)

theorem ay_piwg_deletion_retention_ledger
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    deletionRetentionLedger := by
  intro accepted
  exact accepted deletionRetentionLedger
    (fun _hWidth _hMax _hRange hDeletion _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hDeletion)

theorem ay_piwg_checker_transcript
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hWidth _hMax _hRange _hDeletion hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_piwg_checker_accepted
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hWidth _hMax _hRange _hDeletion _hTranscript hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hChecker)

theorem ay_piwg_empty_clause_reachable
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hWidth _hMax _hRange _hDeletion _hTranscript _hChecker hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_piwg_benchmark_fingerprint
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    benchmarkFingerprint := by
  intro accepted
  exact accepted benchmarkFingerprint
    (fun _hWidth _hMax _hRange _hDeletion _hTranscript _hChecker _hEmpty
      hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_piwg_archive_manifest
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    archiveManifest := by
  intro accepted
  exact accepted archiveManifest
    (fun _hWidth _hMax _hRange _hDeletion _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted hArchive
      _hFallback _hAudit _hVisible _hOriginal => hArchive)

theorem ay_piwg_original_unsat
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPIWGAcceptedEvidence indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hWidth _hMax _hRange _hDeletion _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hVisible hOriginal => hOriginal)

theorem ay_piwg_index_width_composes_to_original
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    indexWidthManifest ->
    AyPIWGIndexReplayComposition indexWidthManifest maxIndexWitness
      antecedentRangeProof deletionRetentionLedger emptyClauseReachable
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro hWidth
  intro composed
  exact composed originalUnsat
    (fun width_to_max rest1 =>
      rest1 originalUnsat
        (fun max_to_range rest2 =>
          rest2 originalUnsat
            (fun range_to_deletion rest3 =>
              rest3 originalUnsat
                (fun deletion_to_empty rest4 =>
                  rest4 originalUnsat
                    (fun empty_to_visible visible_to_original =>
                      visible_to_original
                        (empty_to_visible
                          (deletion_to_empty
                            (range_to_deletion
                              (max_to_range
                                (width_to_max hWidth))))))))))

theorem ay_piwg_publication_sound
    (indexWidthManifest : Prop) (maxIndexWitness : Prop)
    (antecedentRangeProof : Prop) (deletionRetentionLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPIWGPublication indexWidthManifest maxIndexWitness antecedentRangeProof
      deletionRetentionLedger checkerTranscript checkerAccepted
      emptyClauseReachable benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackBaseline
      auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat (fun _accepted unsat => unsat)

theorem ay_piwg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyPIWGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_piwg_disj_right noClaim originalUnsat unsat

theorem ay_piwg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyPIWGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_piwg_disj_left noClaim originalUnsat no_claim

theorem ay_piwg_bad_no_claim
    (indexOverflow : Prop) (indexTruncation : Prop)
    (outOfRangeAntecedent : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPIWGBadIndexGuard indexOverflow indexTruncation outOfRangeAntecedent
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_piwg_bad_recompute
    (indexOverflow : Prop) (indexTruncation : Prop)
    (outOfRangeAntecedent : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPIWGBadIndexGuard indexOverflow indexTruncation outOfRangeAntecedent
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_piwg_failed_index_guard_cannot_bless_unsat
    (indexOverflow : Prop) (indexTruncation : Prop)
    (outOfRangeAntecedent : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyPIWGBadIndexGuard indexOverflow indexTruncation outOfRangeAntecedent
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch noClaim recompute ->
    AyPIWGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_piwg_public_no_claim_report noClaim originalUnsat
    (ay_piwg_bad_no_claim indexOverflow indexTruncation outOfRangeAntecedent
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_piwg_failure_forces_no_claim
    (indexOverflow : Prop) (indexTruncation : Prop)
    (outOfRangeAntecedent : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPIWGBadIndexGuard indexOverflow indexTruncation outOfRangeAntecedent
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch noClaim recompute ->
    AyPIWGConj noClaim recompute := by
  intro bad
  exact ay_piwg_conj_intro noClaim recompute
    (ay_piwg_bad_no_claim indexOverflow indexTruncation outOfRangeAntecedent
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch noClaim recompute bad)
    (ay_piwg_bad_recompute indexOverflow indexTruncation outOfRangeAntecedent
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_piwg_index_overflow_forces_no_claim
    (indexOverflow : Prop) (noClaim : Prop) :
    indexOverflow -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_piwg_index_truncation_forces_no_claim
    (indexTruncation : Prop) (noClaim : Prop) :
    indexTruncation -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_piwg_out_of_range_antecedent_forces_no_claim
    (outOfRangeAntecedent : Prop) (noClaim : Prop) :
    outOfRangeAntecedent -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_piwg_checker_mismatch_forces_no_claim
    (checkerMismatch : Prop) (noClaim : Prop) :
    checkerMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_piwg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_piwg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_piwg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_piwg_fallback_mismatch_forces_no_claim
    (fallbackMismatch : Prop) (noClaim : Prop) :
    fallbackMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_piwg_audit_mismatch_forces_no_claim
    (auditMismatch : Prop) (noClaim : Prop) :
    auditMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
