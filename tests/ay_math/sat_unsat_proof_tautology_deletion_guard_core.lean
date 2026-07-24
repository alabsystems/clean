-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof tautology/deletion guard soundness for ay
-- sequential-main SAT-COMP publication. Propositions stand for proof step
-- digests, tautology policy manifests, deletion/retention ledgers, antecedent
-- availability witnesses, checker transcripts, empty-clause reachability
-- witnesses, benchmark fingerprints, solver build evidence, archive
-- manifests, fallback baselines, audit transcripts, and fail-closed
-- no-claim/recompute diagnostics.

def AyPTDGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyPTDGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyPTDGMap (source : Prop) (target : Prop) :=
  source -> target

def AyPTDGAcceptedEvidence
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofStepDigest ->
      tautologyPolicyManifest ->
      deletionRetentionLedger ->
      antecedentAvailability ->
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

def AyPTDGReplayComposition
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyPTDGConj
    (AyPTDGMap proofStepDigest tautologyPolicyManifest)
    (AyPTDGConj
      (AyPTDGMap tautologyPolicyManifest deletionRetentionLedger)
      (AyPTDGConj
        (AyPTDGMap deletionRetentionLedger antecedentAvailability)
        (AyPTDGConj
          (AyPTDGMap antecedentAvailability emptyClauseReachable)
          (AyPTDGConj
            (AyPTDGMap emptyClauseReachable visibleUnsat)
            (AyPTDGMap visibleUnsat originalUnsat)))))

def AyPTDGPublication
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyPTDGConj
    (AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat)
    originalUnsat

def AyPTDGFailureReason
    (badTautologyClassification : Prop) (missingAntecedent : Prop)
    (staleDeletionLedger : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (badTautologyClassification -> result) ->
    (missingAntecedent -> result) ->
    (staleDeletionLedger -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (fallbackMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def AyPTDGBadDeletionGuard
    (badTautologyClassification : Prop) (missingAntecedent : Prop)
    (staleDeletionLedger : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyPTDGConj
    (AyPTDGConj noClaim recompute)
    (AyPTDGFailureReason badTautologyClassification missingAntecedent
      staleDeletionLedger checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch)

def AyPTDGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyPTDGDisj noClaim originalUnsat

theorem ay_ptdg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyPTDGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_ptdg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyPTDGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_ptdg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyPTDGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_ptdg_accepted_evidence
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    proofStepDigest ->
    tautologyPolicyManifest ->
    deletionRetentionLedger ->
    antecedentAvailability ->
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
    AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat := by
  intro hStep hPolicy hDeletion hAntecedent hTranscript hChecker hEmpty
  intro hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
  intro hFallback hAudit hVisible hOriginal result publish
  exact publish hStep hPolicy hDeletion hAntecedent hTranscript hChecker
    hEmpty hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
    hFallback hAudit hVisible hOriginal

theorem ay_ptdg_proof_step_digest
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    proofStepDigest := by
  intro accepted
  exact accepted proofStepDigest
    (fun hStep _hPolicy _hDeletion _hAntecedent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hStep)

theorem ay_ptdg_tautology_policy_manifest
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    tautologyPolicyManifest := by
  intro accepted
  exact accepted tautologyPolicyManifest
    (fun _hStep hPolicy _hDeletion _hAntecedent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hPolicy)

theorem ay_ptdg_deletion_retention_ledger
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    deletionRetentionLedger := by
  intro accepted
  exact accepted deletionRetentionLedger
    (fun _hStep _hPolicy hDeletion _hAntecedent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hDeletion)

theorem ay_ptdg_antecedent_availability
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    antecedentAvailability := by
  intro accepted
  exact accepted antecedentAvailability
    (fun _hStep _hPolicy _hDeletion hAntecedent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hAntecedent)

theorem ay_ptdg_checker_transcript
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hStep _hPolicy _hDeletion _hAntecedent hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_ptdg_checker_accepted
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hStep _hPolicy _hDeletion _hAntecedent _hTranscript hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hChecker)

theorem ay_ptdg_empty_clause_reachable
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hStep _hPolicy _hDeletion _hAntecedent _hTranscript _hChecker
      hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_ptdg_benchmark_fingerprint
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    benchmarkFingerprint := by
  intro accepted
  exact accepted benchmarkFingerprint
    (fun _hStep _hPolicy _hDeletion _hAntecedent _hTranscript _hChecker
      _hEmpty hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_ptdg_archive_manifest
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    archiveManifest := by
  intro accepted
  exact accepted archiveManifest
    (fun _hStep _hPolicy _hDeletion _hAntecedent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      hArchive _hFallback _hAudit _hVisible _hOriginal => hArchive)

theorem ay_ptdg_original_unsat
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTDGAcceptedEvidence proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hStep _hPolicy _hDeletion _hAntecedent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible hOriginal => hOriginal)

theorem ay_ptdg_tautology_deletion_replay_composes_to_original
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    proofStepDigest ->
    AyPTDGReplayComposition proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability emptyClauseReachable
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro hStep
  intro composed
  exact composed originalUnsat
    (fun step_to_policy rest1 =>
      rest1 originalUnsat
        (fun policy_to_deletion rest2 =>
          rest2 originalUnsat
            (fun deletion_to_antecedent rest3 =>
              rest3 originalUnsat
                (fun antecedent_to_empty rest4 =>
                  rest4 originalUnsat
                    (fun empty_to_visible visible_to_original =>
                      visible_to_original
                        (empty_to_visible
                          (antecedent_to_empty
                            (deletion_to_antecedent
                              (policy_to_deletion
                                (step_to_policy hStep))))))))))

theorem ay_ptdg_publication_sound
    (proofStepDigest : Prop) (tautologyPolicyManifest : Prop)
    (deletionRetentionLedger : Prop) (antecedentAvailability : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTDGPublication proofStepDigest tautologyPolicyManifest
      deletionRetentionLedger antecedentAvailability checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat (fun _accepted unsat => unsat)

theorem ay_ptdg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyPTDGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ptdg_disj_right noClaim originalUnsat unsat

theorem ay_ptdg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyPTDGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ptdg_disj_left noClaim originalUnsat no_claim

theorem ay_ptdg_bad_no_claim
    (badTautologyClassification : Prop) (missingAntecedent : Prop)
    (staleDeletionLedger : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPTDGBadDeletionGuard badTautologyClassification missingAntecedent
      staleDeletionLedger checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_ptdg_bad_recompute
    (badTautologyClassification : Prop) (missingAntecedent : Prop)
    (staleDeletionLedger : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPTDGBadDeletionGuard badTautologyClassification missingAntecedent
      staleDeletionLedger checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_ptdg_failed_deletion_guard_cannot_bless_unsat
    (badTautologyClassification : Prop) (missingAntecedent : Prop)
    (staleDeletionLedger : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyPTDGBadDeletionGuard badTautologyClassification missingAntecedent
      staleDeletionLedger checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    AyPTDGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ptdg_public_no_claim_report noClaim originalUnsat
    (ay_ptdg_bad_no_claim badTautologyClassification missingAntecedent
      staleDeletionLedger checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_ptdg_failure_forces_no_claim
    (badTautologyClassification : Prop) (missingAntecedent : Prop)
    (staleDeletionLedger : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPTDGBadDeletionGuard badTautologyClassification missingAntecedent
      staleDeletionLedger checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    AyPTDGConj noClaim recompute := by
  intro bad
  exact ay_ptdg_conj_intro noClaim recompute
    (ay_ptdg_bad_no_claim badTautologyClassification missingAntecedent
      staleDeletionLedger checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)
    (ay_ptdg_bad_recompute badTautologyClassification missingAntecedent
      staleDeletionLedger checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_ptdg_bad_tautology_classification_forces_no_claim
    (badTautologyClassification : Prop) (noClaim : Prop) :
    badTautologyClassification -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ptdg_missing_antecedent_forces_no_claim
    (missingAntecedent : Prop) (noClaim : Prop) :
    missingAntecedent -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ptdg_stale_deletion_ledger_forces_no_claim
    (staleDeletionLedger : Prop) (noClaim : Prop) :
    staleDeletionLedger -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ptdg_checker_mismatch_forces_no_claim
    (checkerMismatch : Prop) (noClaim : Prop) :
    checkerMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ptdg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ptdg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ptdg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ptdg_fallback_mismatch_forces_no_claim
    (fallbackMismatch : Prop) (noClaim : Prop) :
    fallbackMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ptdg_audit_mismatch_forces_no_claim
    (auditMismatch : Prop) (noClaim : Prop) :
    auditMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
