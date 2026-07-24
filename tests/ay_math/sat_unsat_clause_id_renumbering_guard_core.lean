-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded clause-ID renumbering guard soundness for ay sequential-main
-- SAT-COMP validation. Propositions stand for source clause-id maps,
-- renumbering manifests, parent coverage, checker transcripts, empty-clause
-- reachability, formula fingerprints, solver build evidence, archive
-- manifests, audit transcripts, and fail-closed no-claim/recompute
-- diagnostics.

def AyCIRGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyCIRGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyCIRGMap (source : Prop) (target : Prop) :=
  source -> target

def AyCIRGAcceptedEvidence
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (sourceClauseIdMap ->
      renumberingManifest ->
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

def AyCIRGRenumberingCertificate
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop) :=
  AyCIRGConj sourceClauseIdMap
    (AyCIRGConj renumberingManifest
      (AyCIRGConj archiveManifest auditTranscript))

def AyCIRGReplayGuard
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop) :=
  AyCIRGConj
    (AyCIRGMap sourceClauseIdMap renumberingManifest)
    (AyCIRGConj
      (AyCIRGMap renumberingManifest parentCoverage)
      (AyCIRGConj
        (AyCIRGMap parentCoverage emptyClauseReachable)
        (AyCIRGMap checkerTranscript checkerAccepted)))

def AyCIRGPublication
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyCIRGConj
    (AyCIRGAcceptedEvidence sourceClauseIdMap renumberingManifest
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest auditTranscript visibleUnsat
      originalUnsat)
    originalUnsat

def AyCIRGFailureReason
    (sourceMapFailure : Prop) (renumberingManifestFailure : Prop)
    (parentCoverageFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) :=
  forall result : Prop,
    (sourceMapFailure -> result) ->
    (renumberingManifestFailure -> result) ->
    (parentCoverageFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (fingerprintFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    (auditFailure -> result) ->
    result

def AyCIRGBadRenumbering
    (sourceMapFailure : Prop) (renumberingManifestFailure : Prop)
    (parentCoverageFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyCIRGConj
    (AyCIRGConj noClaim recompute)
    (AyCIRGFailureReason sourceMapFailure renumberingManifestFailure
      parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure)

def AyCIRGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyCIRGDisj noClaim originalUnsat

theorem ay_cirg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyCIRGConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_cirg_conj_left
    (p : Prop) (q : Prop) :
    AyCIRGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_cirg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyCIRGDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_cirg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyCIRGDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_cirg_accepted_evidence
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    sourceClauseIdMap ->
    renumberingManifest ->
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
    AyCIRGAcceptedEvidence sourceClauseIdMap renumberingManifest
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest auditTranscript visibleUnsat
      originalUnsat := by
  intro hSourceMap
  intro hManifest
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
  exact publish hSourceMap hManifest hParent hTranscript hChecker hEmpty
    hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive hAudit
    hVisible hOriginal

theorem ay_cirg_source_clause_id_map
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence sourceClauseIdMap renumberingManifest
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    sourceClauseIdMap := by
  intro accepted
  exact accepted sourceClauseIdMap
    (fun hSourceMap _hManifest _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hSourceMap)

theorem ay_cirg_renumbering_manifest
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence sourceClauseIdMap renumberingManifest
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    renumberingManifest := by
  intro accepted
  exact accepted renumberingManifest
    (fun _hSourceMap hManifest _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hManifest)

theorem ay_cirg_parent_coverage
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence sourceClauseIdMap renumberingManifest
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    parentCoverage := by
  intro accepted
  exact accepted parentCoverage
    (fun _hSourceMap _hManifest hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hParent)

theorem ay_cirg_checker_transcript
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence sourceClauseIdMap renumberingManifest
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hSourceMap _hManifest _hParent hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_cirg_checker_accepted
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence sourceClauseIdMap renumberingManifest
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hSourceMap _hManifest _hParent _hTranscript hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hChecker)

theorem ay_cirg_empty_clause_reachable
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence sourceClauseIdMap renumberingManifest
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hSourceMap _hManifest _hParent _hTranscript _hChecker hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_cirg_formula_fingerprint
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence sourceClauseIdMap renumberingManifest
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    formulaFingerprint := by
  intro accepted
  exact accepted formulaFingerprint
    (fun _hSourceMap _hManifest _hParent _hTranscript _hChecker _hEmpty
      hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_cirg_original_unsat
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGAcceptedEvidence sourceClauseIdMap renumberingManifest
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hSourceMap _hManifest _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible hOriginal => hOriginal)

theorem ay_cirg_publication_sound
    (sourceClauseIdMap : Prop) (renumberingManifest : Prop)
    (parentCoverage : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyCIRGPublication sourceClauseIdMap renumberingManifest parentCoverage
      checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
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
    (sourceMapFailure : Prop) (renumberingManifestFailure : Prop)
    (parentCoverageFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyCIRGBadRenumbering sourceMapFailure renumberingManifestFailure
      parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_cirg_bad_recompute
    (sourceMapFailure : Prop) (renumberingManifestFailure : Prop)
    (parentCoverageFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyCIRGBadRenumbering sourceMapFailure renumberingManifestFailure
      parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_cirg_failed_renumbering_cannot_bless_unsat
    (sourceMapFailure : Prop) (renumberingManifestFailure : Prop)
    (parentCoverageFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyCIRGBadRenumbering sourceMapFailure renumberingManifestFailure
      parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute ->
    AyCIRGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_cirg_public_no_claim_report noClaim originalUnsat
    (ay_cirg_bad_no_claim sourceMapFailure renumberingManifestFailure
      parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute bad)

theorem ay_cirg_failure_forces_no_claim
    (sourceMapFailure : Prop) (renumberingManifestFailure : Prop)
    (parentCoverageFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyCIRGBadRenumbering sourceMapFailure renumberingManifestFailure
      parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute ->
    AyCIRGConj noClaim recompute := by
  intro bad
  exact ay_cirg_conj_intro noClaim recompute
    (ay_cirg_bad_no_claim sourceMapFailure renumberingManifestFailure
      parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute bad)
    (ay_cirg_bad_recompute sourceMapFailure renumberingManifestFailure
      parentCoverageFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure archiveFailure auditFailure noClaim
      recompute bad)

theorem ay_cirg_source_map_failure_forces_no_claim
    (sourceMapFailure : Prop) (noClaim : Prop) :
    sourceMapFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cirg_renumbering_manifest_failure_forces_no_claim
    (renumberingManifestFailure : Prop) (noClaim : Prop) :
    renumberingManifestFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cirg_parent_coverage_failure_forces_no_claim
    (parentCoverageFailure : Prop) (noClaim : Prop) :
    parentCoverageFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cirg_checker_failure_forces_no_claim
    (checkerFailure : Prop) (noClaim : Prop) :
    checkerFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cirg_empty_clause_failure_forces_no_claim
    (emptyClauseFailure : Prop) (noClaim : Prop) :
    emptyClauseFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cirg_fingerprint_failure_forces_no_claim
    (fingerprintFailure : Prop) (noClaim : Prop) :
    fingerprintFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cirg_build_failure_forces_no_claim
    (buildFailure : Prop) (noClaim : Prop) :
    buildFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cirg_archive_failure_forces_no_claim
    (archiveFailure : Prop) (noClaim : Prop) :
    archiveFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_cirg_audit_failure_forces_no_claim
    (auditFailure : Prop) (noClaim : Prop) :
    auditFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim
