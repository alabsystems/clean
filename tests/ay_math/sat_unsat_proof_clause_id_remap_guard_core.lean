-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof clause-id remap guard soundness for ay sequential-main
-- SAT-COMP publication. Propositions stand for original clause-id manifests,
-- transformed clause-id maps, proof antecedent remap witnesses,
-- deletion/retention ledgers, empty-clause reachability witnesses, checker
-- transcripts, benchmark fingerprints, solver build evidence, archive
-- manifests, fallback baselines, audit transcripts, and fail-closed
-- no-claim/recompute diagnostics.

def AyCIRGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyCIRGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyCIRGMap (source : Prop) (target : Prop) :=
  source -> target

def AyCIRGAcceptedEvidence
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (originalClauseIdManifest ->
      transformedClauseIdMap ->
      antecedentRemapWitness ->
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

def AyCIRGRemapReplayComposition
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyCIRGConj
    (AyCIRGMap originalClauseIdManifest transformedClauseIdMap)
    (AyCIRGConj
      (AyCIRGMap transformedClauseIdMap antecedentRemapWitness)
      (AyCIRGConj
        (AyCIRGMap antecedentRemapWitness deletionRetentionLedger)
        (AyCIRGConj
          (AyCIRGMap deletionRetentionLedger emptyClauseReachable)
          (AyCIRGConj
            (AyCIRGMap emptyClauseReachable visibleUnsat)
            (AyCIRGMap visibleUnsat originalUnsat)))))

def AyCIRGPublication
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyCIRGConj
    (AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat)
    originalUnsat

def AyCIRGFailureReason
    (missingClauseId : Prop) (collidingClauseId : Prop)
    (staleClauseId : Prop) (remapMismatch : Prop)
    (deletionLedgerFailure : Prop) (checkerFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (fallbackFailure : Prop)
    (auditFailure : Prop) :=
  forall result : Prop,
    (missingClauseId -> result) ->
    (collidingClauseId -> result) ->
    (staleClauseId -> result) ->
    (remapMismatch -> result) ->
    (deletionLedgerFailure -> result) ->
    (checkerFailure -> result) ->
    (fingerprintFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    (fallbackFailure -> result) ->
    (auditFailure -> result) ->
    result

def AyCIRGBadRemap
    (missingClauseId : Prop) (collidingClauseId : Prop)
    (staleClauseId : Prop) (remapMismatch : Prop)
    (deletionLedgerFailure : Prop) (checkerFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (fallbackFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyCIRGConj
    (AyCIRGConj noClaim recompute)
    (AyCIRGFailureReason missingClauseId collidingClauseId staleClauseId
      remapMismatch deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure)

def AyCIRGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyCIRGDisj noClaim originalUnsat

theorem ay_cirg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyCIRGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_cirg_conj_left
    (p : Prop) (q : Prop) :
    AyCIRGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_cirg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyCIRGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_cirg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyCIRGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_cirg_accepted_evidence
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    originalClauseIdManifest ->
    transformedClauseIdMap ->
    antecedentRemapWitness ->
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
    AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat := by
  intro hOriginalIds hTransformed hRemap hDeletion hEmpty hTranscript hChecker
  intro hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
  intro hFallback hAudit hVisible hOriginalUnsat result publish
  exact publish hOriginalIds hTransformed hRemap hDeletion hEmpty hTranscript
    hChecker hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
    hFallback hAudit hVisible hOriginalUnsat

theorem ay_cirg_original_clause_id_manifest
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    originalClauseIdManifest := by
  intro accepted
  exact accepted originalClauseIdManifest
    (fun hOriginalIds _hTransformed _hRemap _hDeletion _hEmpty _hTranscript
      _hChecker _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginalUnsat => hOriginalIds)

theorem ay_cirg_transformed_clause_id_map
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    transformedClauseIdMap := by
  intro accepted
  exact accepted transformedClauseIdMap
    (fun _hOriginalIds hTransformed _hRemap _hDeletion _hEmpty _hTranscript
      _hChecker _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginalUnsat => hTransformed)

theorem ay_cirg_antecedent_remap_witness
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    antecedentRemapWitness := by
  intro accepted
  exact accepted antecedentRemapWitness
    (fun _hOriginalIds _hTransformed hRemap _hDeletion _hEmpty _hTranscript
      _hChecker _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginalUnsat => hRemap)

theorem ay_cirg_deletion_retention_ledger
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    deletionRetentionLedger := by
  intro accepted
  exact accepted deletionRetentionLedger
    (fun _hOriginalIds _hTransformed _hRemap hDeletion _hEmpty _hTranscript
      _hChecker _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginalUnsat => hDeletion)

theorem ay_cirg_empty_clause_reachable
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hOriginalIds _hTransformed _hRemap _hDeletion hEmpty _hTranscript
      _hChecker _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginalUnsat => hEmpty)

theorem ay_cirg_checker_transcript
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hOriginalIds _hTransformed _hRemap _hDeletion _hEmpty hTranscript
      _hChecker _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginalUnsat => hTranscript)

theorem ay_cirg_checker_accepted
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hOriginalIds _hTransformed _hRemap _hDeletion _hEmpty _hTranscript
      hChecker _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginalUnsat => hChecker)

theorem ay_cirg_benchmark_fingerprint
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    benchmarkFingerprint := by
  intro accepted
  exact accepted benchmarkFingerprint
    (fun _hOriginalIds _hTransformed _hRemap _hDeletion _hEmpty _hTranscript
      _hChecker hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginalUnsat => hFingerprint)

theorem ay_cirg_archive_manifest
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    archiveManifest := by
  intro accepted
  exact accepted archiveManifest
    (fun _hOriginalIds _hTransformed _hRemap _hDeletion _hEmpty _hTranscript
      _hChecker _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      hArchive _hFallback _hAudit _hVisible _hOriginalUnsat => hArchive)

theorem ay_cirg_original_unsat
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hOriginalIds _hTransformed _hRemap _hDeletion _hEmpty _hTranscript
      _hChecker _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible hOriginalUnsat => hOriginalUnsat)

theorem ay_cirg_remapped_replay_composes_to_original
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    originalClauseIdManifest ->
    AyCIRGRemapReplayComposition originalClauseIdManifest
      transformedClauseIdMap antecedentRemapWitness deletionRetentionLedger
      emptyClauseReachable visibleUnsat originalUnsat ->
    originalUnsat := by
  intro hOriginalIds
  intro composed
  exact composed originalUnsat
    (fun original_to_transformed rest1 =>
      rest1 originalUnsat
        (fun transformed_to_remap rest2 =>
          rest2 originalUnsat
            (fun remap_to_deletion rest3 =>
              rest3 originalUnsat
                (fun deletion_to_empty rest4 =>
                  rest4 originalUnsat
                    (fun empty_to_visible visible_to_original =>
                      visible_to_original
                        (empty_to_visible
                          (deletion_to_empty
                            (remap_to_deletion
                              (transformed_to_remap
                                (original_to_transformed
                                  hOriginalIds))))))))))

theorem ay_cirg_publication_sound
    (originalClauseIdManifest : Prop) (transformedClauseIdMap : Prop)
    (antecedentRemapWitness : Prop) (deletionRetentionLedger : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGPublication originalClauseIdManifest transformedClauseIdMap
      antecedentRemapWitness deletionRetentionLedger emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted unsat => unsat)

theorem ay_cirg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyCIRGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_cirg_disj_right noClaim originalUnsat unsat

theorem ay_cirg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyCIRGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_cirg_disj_left noClaim originalUnsat no_claim

theorem ay_cirg_bad_no_claim
    (missingClauseId : Prop) (collidingClauseId : Prop)
    (staleClauseId : Prop) (remapMismatch : Prop)
    (deletionLedgerFailure : Prop) (checkerFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (fallbackFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyCIRGBadRemap missingClauseId collidingClauseId staleClauseId
      remapMismatch deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_cirg_bad_recompute
    (missingClauseId : Prop) (collidingClauseId : Prop)
    (staleClauseId : Prop) (remapMismatch : Prop)
    (deletionLedgerFailure : Prop) (checkerFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (fallbackFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyCIRGBadRemap missingClauseId collidingClauseId staleClauseId
      remapMismatch deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_cirg_failed_remap_cannot_bless_unsat
    (missingClauseId : Prop) (collidingClauseId : Prop)
    (staleClauseId : Prop) (remapMismatch : Prop)
    (deletionLedgerFailure : Prop) (checkerFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (fallbackFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyCIRGBadRemap missingClauseId collidingClauseId staleClauseId
      remapMismatch deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute ->
    AyCIRGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_cirg_public_no_claim_report noClaim originalUnsat
    (ay_cirg_bad_no_claim missingClauseId collidingClauseId staleClauseId
      remapMismatch deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute bad)

theorem ay_cirg_failure_forces_no_claim
    (missingClauseId : Prop) (collidingClauseId : Prop)
    (staleClauseId : Prop) (remapMismatch : Prop)
    (deletionLedgerFailure : Prop) (checkerFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (fallbackFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyCIRGBadRemap missingClauseId collidingClauseId staleClauseId
      remapMismatch deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute ->
    AyCIRGConj noClaim recompute := by
  intro bad
  exact ay_cirg_conj_intro noClaim recompute
    (ay_cirg_bad_no_claim missingClauseId collidingClauseId staleClauseId
      remapMismatch deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute bad)
    (ay_cirg_bad_recompute missingClauseId collidingClauseId staleClauseId
      remapMismatch deletionLedgerFailure checkerFailure fingerprintFailure
      buildFailure archiveFailure fallbackFailure auditFailure noClaim
      recompute bad)

theorem ay_cirg_missing_clause_id_forces_no_claim
    (missingClauseId : Prop) (noClaim : Prop) :
    missingClauseId -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cirg_colliding_clause_id_forces_no_claim
    (collidingClauseId : Prop) (noClaim : Prop) :
    collidingClauseId -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cirg_stale_clause_id_forces_no_claim
    (staleClauseId : Prop) (noClaim : Prop) :
    staleClauseId -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cirg_remap_mismatch_forces_no_claim
    (remapMismatch : Prop) (noClaim : Prop) :
    remapMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cirg_deletion_ledger_failure_forces_no_claim
    (deletionLedgerFailure : Prop) (noClaim : Prop) :
    deletionLedgerFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cirg_checker_failure_forces_no_claim
    (checkerFailure : Prop) (noClaim : Prop) :
    checkerFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cirg_fingerprint_failure_forces_no_claim
    (fingerprintFailure : Prop) (noClaim : Prop) :
    fingerprintFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cirg_build_failure_forces_no_claim
    (buildFailure : Prop) (noClaim : Prop) :
    buildFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cirg_archive_failure_forces_no_claim
    (archiveFailure : Prop) (noClaim : Prop) :
    archiveFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cirg_fallback_failure_forces_no_claim
    (fallbackFailure : Prop) (noClaim : Prop) :
    fallbackFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_cirg_audit_failure_forces_no_claim
    (auditFailure : Prop) (noClaim : Prop) :
    auditFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
