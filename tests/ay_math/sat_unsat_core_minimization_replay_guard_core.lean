-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT-core minimization replay guard soundness for ay
-- sequential-main SAT-COMP validation. Propositions stand for source core
-- manifests, minimized core manifests, selected-clause maps, parent coverage,
-- checker transcripts, empty-clause reachability, formula fingerprints, solver
-- build evidence, archive manifests, audit transcripts, public core reports,
-- and fail-closed no-claim/recompute diagnostics.

def AyUCMGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCMGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCMGMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCMGAcceptedEvidence
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :=
  forall result : Prop,
    (sourceCoreManifest ->
      minimizedCoreManifest ->
      selectedClauseMap ->
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
      publicCore ->
      coreReportAccepted ->
      result) ->
    result

def AyUCMGMinimizationCertificate
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) :=
  AyUCMGConj sourceCoreManifest
    (AyUCMGConj minimizedCoreManifest
      (AyUCMGConj selectedClauseMap
        (AyUCMGConj archiveManifest auditTranscript)))

def AyUCMGReplayGuard
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) :=
  AyUCMGConj
    (AyUCMGMap sourceCoreManifest minimizedCoreManifest)
    (AyUCMGConj
      (AyUCMGMap minimizedCoreManifest selectedClauseMap)
      (AyUCMGConj
        (AyUCMGMap selectedClauseMap parentCoverage)
        (AyUCMGConj
          (AyUCMGMap parentCoverage emptyClauseReachable)
          (AyUCMGMap checkerTranscript checkerAccepted))))

def AyUCMGPublication
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :=
  AyUCMGConj
    (AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted)
    (AyUCMGConj originalUnsat coreReportAccepted)

def AyUCMGFailureReason
    (sourceManifestFailure : Prop) (minimizedManifestFailure : Prop)
    (selectedMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :=
  forall result : Prop,
    (sourceManifestFailure -> result) ->
    (minimizedManifestFailure -> result) ->
    (selectedMapFailure -> result) ->
    (parentCoverageFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (fingerprintFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    (auditFailure -> result) ->
    (coreReportFailure -> result) ->
    result

def AyUCMGBadMinimization
    (sourceManifestFailure : Prop) (minimizedManifestFailure : Prop)
    (selectedMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUCMGConj
    (AyUCMGConj noClaim recompute)
    (AyUCMGFailureReason sourceManifestFailure minimizedManifestFailure
      selectedMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure coreReportFailure)

def AyUCMGPublicReport
    (noClaim : Prop) (originalUnsat : Prop) (publicCore : Prop) :=
  AyUCMGDisj noClaim (AyUCMGConj originalUnsat publicCore)

theorem ay_ucmg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCMGConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucmg_conj_left
    (p : Prop) (q : Prop) :
    AyUCMGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucmg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCMGDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucmg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCMGDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucmg_accepted_evidence
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    sourceCoreManifest ->
    minimizedCoreManifest ->
    selectedClauseMap ->
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
    publicCore ->
    coreReportAccepted ->
    AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted := by
  intro hSource
  intro hMinimized
  intro hSelected
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
  intro hCore
  intro hCoreAccepted
  intro result
  intro publish
  exact publish hSource hMinimized hSelected hParent hTranscript hChecker
    hEmpty hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
    hAudit hVisible hOriginal hCore hCoreAccepted

theorem ay_ucmg_source_core_manifest
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    sourceCoreManifest := by
  intro accepted
  exact accepted sourceCoreManifest
    (fun hSource _hMinimized _hSelected _hParent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hAudit _hVisible _hOriginal _hCore _hCoreAccepted => hSource)

theorem ay_ucmg_minimized_core_manifest
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    minimizedCoreManifest := by
  intro accepted
  exact accepted minimizedCoreManifest
    (fun _hSource hMinimized _hSelected _hParent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hAudit _hVisible _hOriginal _hCore _hCoreAccepted =>
      hMinimized)

theorem ay_ucmg_selected_clause_map
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    selectedClauseMap := by
  intro accepted
  exact accepted selectedClauseMap
    (fun _hSource _hMinimized hSelected _hParent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hAudit _hVisible _hOriginal _hCore _hCoreAccepted =>
      hSelected)

theorem ay_ucmg_parent_coverage
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    parentCoverage := by
  intro accepted
  exact accepted parentCoverage
    (fun _hSource _hMinimized _hSelected hParent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hAudit _hVisible _hOriginal _hCore _hCoreAccepted => hParent)

theorem ay_ucmg_checker_transcript
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hSource _hMinimized _hSelected _hParent hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hAudit _hVisible _hOriginal _hCore _hCoreAccepted =>
      hTranscript)

theorem ay_ucmg_checker_accepted
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hSource _hMinimized _hSelected _hParent _hTranscript hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hAudit _hVisible _hOriginal _hCore _hCoreAccepted =>
      hChecker)

theorem ay_ucmg_empty_clause_reachable
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hSource _hMinimized _hSelected _hParent _hTranscript _hChecker hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal _hCore _hCoreAccepted => hEmpty)

theorem ay_ucmg_original_unsat
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hSource _hMinimized _hSelected _hParent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hAudit _hVisible hOriginal _hCore _hCoreAccepted =>
      hOriginal)

theorem ay_ucmg_public_core
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    publicCore := by
  intro accepted
  exact accepted publicCore
    (fun _hSource _hMinimized _hSelected _hParent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hAudit _hVisible _hOriginal hCore _hCoreAccepted => hCore)

theorem ay_ucmg_core_report_accepted
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGAcceptedEvidence sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    coreReportAccepted := by
  intro accepted
  exact accepted coreReportAccepted
    (fun _hSource _hMinimized _hSelected _hParent _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hAudit _hVisible _hOriginal _hCore hCoreAccepted =>
      hCoreAccepted)

theorem ay_ucmg_publication_sound
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGPublication sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted published =>
      published originalUnsat (fun unsat _core_ok => unsat))

theorem ay_ucmg_public_core_sound
    (sourceCoreManifest : Prop) (minimizedCoreManifest : Prop)
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCMGPublication sourceCoreManifest minimizedCoreManifest
      selectedClauseMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat publicCore coreReportAccepted ->
    coreReportAccepted := by
  intro publication
  exact publication coreReportAccepted
    (fun _accepted published =>
      published coreReportAccepted (fun _unsat core_ok => core_ok))

theorem ay_ucmg_public_unsat_core_report
    (noClaim : Prop) (originalUnsat : Prop) (publicCore : Prop) :
    originalUnsat ->
    publicCore ->
    AyUCMGPublicReport noClaim originalUnsat publicCore := by
  intro unsat
  intro core
  exact ay_ucmg_disj_right noClaim (AyUCMGConj originalUnsat publicCore)
    (ay_ucmg_conj_intro originalUnsat publicCore unsat core)

theorem ay_ucmg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicCore : Prop) :
    noClaim -> AyUCMGPublicReport noClaim originalUnsat publicCore := by
  intro no_claim
  exact ay_ucmg_disj_left noClaim (AyUCMGConj originalUnsat publicCore)
    no_claim

theorem ay_ucmg_bad_no_claim
    (sourceManifestFailure : Prop) (minimizedManifestFailure : Prop)
    (selectedMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCMGBadMinimization sourceManifestFailure minimizedManifestFailure
      selectedMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure coreReportFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_ucmg_bad_recompute
    (sourceManifestFailure : Prop) (minimizedManifestFailure : Prop)
    (selectedMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCMGBadMinimization sourceManifestFailure minimizedManifestFailure
      selectedMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure coreReportFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_ucmg_failed_minimization_cannot_bless_unsat_or_core
    (sourceManifestFailure : Prop) (minimizedManifestFailure : Prop)
    (selectedMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) (publicCore : Prop) :
    AyUCMGBadMinimization sourceManifestFailure minimizedManifestFailure
      selectedMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure coreReportFailure noClaim recompute ->
    AyUCMGPublicReport noClaim originalUnsat publicCore := by
  intro bad
  exact ay_ucmg_public_no_claim_report noClaim originalUnsat publicCore
    (ay_ucmg_bad_no_claim sourceManifestFailure minimizedManifestFailure
      selectedMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure coreReportFailure noClaim recompute bad)

theorem ay_ucmg_failure_forces_no_claim
    (sourceManifestFailure : Prop) (minimizedManifestFailure : Prop)
    (selectedMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCMGBadMinimization sourceManifestFailure minimizedManifestFailure
      selectedMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure coreReportFailure noClaim recompute ->
    AyUCMGConj noClaim recompute := by
  intro bad
  exact ay_ucmg_conj_intro noClaim recompute
    (ay_ucmg_bad_no_claim sourceManifestFailure minimizedManifestFailure
      selectedMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure coreReportFailure noClaim recompute bad)
    (ay_ucmg_bad_recompute sourceManifestFailure minimizedManifestFailure
      selectedMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure coreReportFailure noClaim recompute bad)

theorem ay_ucmg_source_manifest_failure_forces_no_claim
    (sourceManifestFailure : Prop) (noClaim : Prop) :
    sourceManifestFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucmg_minimized_manifest_failure_forces_no_claim
    (minimizedManifestFailure : Prop) (noClaim : Prop) :
    minimizedManifestFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucmg_selected_map_failure_forces_no_claim
    (selectedMapFailure : Prop) (noClaim : Prop) :
    selectedMapFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucmg_parent_coverage_failure_forces_no_claim
    (parentCoverageFailure : Prop) (noClaim : Prop) :
    parentCoverageFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucmg_checker_failure_forces_no_claim
    (checkerFailure : Prop) (noClaim : Prop) :
    checkerFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucmg_empty_clause_failure_forces_no_claim
    (emptyClauseFailure : Prop) (noClaim : Prop) :
    emptyClauseFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucmg_fingerprint_failure_forces_no_claim
    (fingerprintFailure : Prop) (noClaim : Prop) :
    fingerprintFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucmg_build_failure_forces_no_claim
    (buildFailure : Prop) (noClaim : Prop) :
    buildFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucmg_archive_failure_forces_no_claim
    (archiveFailure : Prop) (noClaim : Prop) :
    archiveFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucmg_audit_failure_forces_no_claim
    (auditFailure : Prop) (noClaim : Prop) :
    auditFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucmg_core_report_failure_forces_no_claim
    (coreReportFailure : Prop) (noClaim : Prop) :
    coreReportFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim
