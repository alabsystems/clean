-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded clause-deletion certificate guard soundness for ay sequential-main
-- SAT-COMP validation. Propositions stand for deletion manifests, active
-- clause-set digests, clause-id maps, parent coverage, checker transcripts,
-- empty-clause reachability, formula fingerprints, solver build evidence,
-- archive manifests, audit transcripts, and fail-closed no-claim/recompute
-- diagnostics.

def AyCDPGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyCDPGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyCDPGMap (source : Prop) (target : Prop) :=
  source -> target

def AyCDPGAcceptedEvidence
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (deletionManifest ->
      activeClauseSetDigest ->
      clauseIdMap ->
      parentCoverage ->
      checkerTranscript ->
      checkerAccepted ->
      emptyClauseReachable ->
      formulaFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      archiveManifest ->
      auditTranscript ->
      visibleUnsat ->
      originalUnsat ->
      result) ->
    result

def AyCDPGDeletionCertificate
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) :=
  AyCDPGConj deletionManifest
    (AyCDPGConj activeClauseSetDigest
      (AyCDPGConj clauseIdMap
        (AyCDPGConj archiveManifest auditTranscript)))

def AyCDPGDeletionAwareReplay
    (activeClauseSetDigest : Prop) (clauseIdMap : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop) :=
  AyCDPGConj
    (AyCDPGMap activeClauseSetDigest clauseIdMap)
    (AyCDPGConj
      (AyCDPGMap clauseIdMap parentCoverage)
      (AyCDPGConj
        (AyCDPGMap parentCoverage emptyClauseReachable)
        (AyCDPGMap checkerTranscript checkerAccepted)))

def AyCDPGPublication
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyCDPGConj
    (AyCDPGAcceptedEvidence deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat)
    originalUnsat

def AyCDPGFailureReason
    (deletionManifestFailure : Prop) (activeDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop) :=
  forall result : Prop,
    (deletionManifestFailure -> result) ->
    (activeDigestFailure -> result) ->
    (clauseIdMapFailure -> result) ->
    (parentCoverageFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (fingerprintFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    (auditFailure -> result) ->
    result

def AyCDPGBadDeletionHandling
    (deletionManifestFailure : Prop) (activeDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyCDPGConj
    (AyCDPGConj noClaim recompute)
    (AyCDPGFailureReason deletionManifestFailure activeDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure)

def AyCDPGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyCDPGDisj noClaim originalUnsat

theorem ay_cdpg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyCDPGConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_cdpg_conj_left
    (p : Prop) (q : Prop) :
    AyCDPGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_cdpg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyCDPGDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_cdpg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyCDPGDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_cdpg_accepted_evidence
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    deletionManifest ->
    activeClauseSetDigest ->
    clauseIdMap ->
    parentCoverage ->
    checkerTranscript ->
    checkerAccepted ->
    emptyClauseReachable ->
    formulaFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    auditTranscript ->
    visibleUnsat ->
    originalUnsat ->
    AyCDPGAcceptedEvidence deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat := by
  intro hDeletion
  intro hActive
  intro hMap
  intro hParent
  intro hTranscript
  intro hChecker
  intro hEmpty
  intro hFingerprint
  intro hFingerprintAccepted
  intro hBuild
  intro hBuildAccepted
  intro hArchive
  intro hAudit
  intro hVisible
  intro hOriginal
  intro result
  intro publish
  exact publish hDeletion hActive hMap hParent hTranscript hChecker hEmpty
    hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive hAudit
    hVisible hOriginal

theorem ay_cdpg_deletion_manifest
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCDPGAcceptedEvidence deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    deletionManifest := by
  intro accepted
  exact accepted deletionManifest
    (fun hDeletion _hActive _hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hDeletion)

theorem ay_cdpg_active_clause_set_digest
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCDPGAcceptedEvidence deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    activeClauseSetDigest := by
  intro accepted
  exact accepted activeClauseSetDigest
    (fun _hDeletion hActive _hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hActive)

theorem ay_cdpg_clause_id_map
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCDPGAcceptedEvidence deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    clauseIdMap := by
  intro accepted
  exact accepted clauseIdMap
    (fun _hDeletion _hActive hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hMap)

theorem ay_cdpg_parent_coverage
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCDPGAcceptedEvidence deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    parentCoverage := by
  intro accepted
  exact accepted parentCoverage
    (fun _hDeletion _hActive _hMap hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hParent)

theorem ay_cdpg_checker_transcript
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCDPGAcceptedEvidence deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hDeletion _hActive _hMap _hParent hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_cdpg_checker_accepted
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCDPGAcceptedEvidence deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hDeletion _hActive _hMap _hParent _hTranscript hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hChecker)

theorem ay_cdpg_empty_clause_reachable
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCDPGAcceptedEvidence deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hDeletion _hActive _hMap _hParent _hTranscript _hChecker hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_cdpg_formula_fingerprint
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCDPGAcceptedEvidence deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    formulaFingerprint := by
  intro accepted
  exact accepted formulaFingerprint
    (fun _hDeletion _hActive _hMap _hParent _hTranscript _hChecker _hEmpty
      hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_cdpg_original_unsat
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCDPGAcceptedEvidence deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDeletion _hActive _hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible hOriginal => hOriginal)

theorem ay_cdpg_publication_sound
    (deletionManifest : Prop) (activeClauseSetDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyCDPGPublication deletionManifest activeClauseSetDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted unsat => unsat)

theorem ay_cdpg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyCDPGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_cdpg_disj_right noClaim originalUnsat unsat

theorem ay_cdpg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyCDPGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_cdpg_disj_left noClaim originalUnsat no_claim

theorem ay_cdpg_bad_no_claim
    (deletionManifestFailure : Prop) (activeDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyCDPGBadDeletionHandling deletionManifestFailure activeDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_cdpg_bad_recompute
    (deletionManifestFailure : Prop) (activeDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyCDPGBadDeletionHandling deletionManifestFailure activeDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_cdpg_failed_deletion_handling_cannot_bless_unsat
    (deletionManifestFailure : Prop) (activeDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyCDPGBadDeletionHandling deletionManifestFailure activeDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute ->
    AyCDPGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_cdpg_public_no_claim_report noClaim originalUnsat
    (ay_cdpg_bad_no_claim deletionManifestFailure activeDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute bad)

theorem ay_cdpg_failure_forces_no_claim
    (deletionManifestFailure : Prop) (activeDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyCDPGBadDeletionHandling deletionManifestFailure activeDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute ->
    AyCDPGConj noClaim recompute := by
  intro bad
  exact ay_cdpg_conj_intro noClaim recompute
    (ay_cdpg_bad_no_claim deletionManifestFailure activeDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute bad)
    (ay_cdpg_bad_recompute deletionManifestFailure activeDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute bad)

theorem ay_cdpg_deletion_manifest_failure_forces_no_claim
    (deletionManifestFailure : Prop) (activeDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) :
    deletionManifestFailure ->
    AyCDPGFailureReason deletionManifestFailure activeDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure ->
    noClaim ->
    noClaim := by
  intro _failure
  intro _reason
  intro no_claim
  exact no_claim

theorem ay_cdpg_active_digest_failure_forces_no_claim
    (activeDigestFailure : Prop) (noClaim : Prop) :
    activeDigestFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cdpg_clause_id_map_failure_forces_no_claim
    (clauseIdMapFailure : Prop) (noClaim : Prop) :
    clauseIdMapFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cdpg_parent_coverage_failure_forces_no_claim
    (parentCoverageFailure : Prop) (noClaim : Prop) :
    parentCoverageFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cdpg_checker_failure_forces_no_claim
    (checkerFailure : Prop) (noClaim : Prop) :
    checkerFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cdpg_empty_clause_failure_forces_no_claim
    (emptyClauseFailure : Prop) (noClaim : Prop) :
    emptyClauseFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cdpg_fingerprint_failure_forces_no_claim
    (fingerprintFailure : Prop) (noClaim : Prop) :
    fingerprintFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cdpg_build_failure_forces_no_claim
    (buildFailure : Prop) (noClaim : Prop) :
    buildFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cdpg_archive_failure_forces_no_claim
    (archiveFailure : Prop) (noClaim : Prop) :
    archiveFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cdpg_audit_failure_forces_no_claim
    (auditFailure : Prop) (noClaim : Prop) :
    auditFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim
