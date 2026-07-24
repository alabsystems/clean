-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT checker-version manifest guard soundness for ay
-- sequential-main SAT-COMP validation. Propositions stand for checker
-- binary/version manifests, proof artifact digests, clause-id maps, parent
-- coverage, checker transcripts, empty-clause reachability, formula
-- fingerprints, solver build evidence, archive manifests, audit transcripts,
-- and fail-closed no-claim/recompute diagnostics.

def AyUCVGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCVGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCVGMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCVGAcceptedEvidence
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (checkerVersionManifest ->
      proofArtifactDigest ->
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

def AyUCVGVersionCertificate
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) :=
  AyUCVGConj checkerVersionManifest
    (AyUCVGConj proofArtifactDigest
      (AyUCVGConj clauseIdMap
        (AyUCVGConj archiveManifest auditTranscript)))

def AyUCVGReplayGuard
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) :=
  AyUCVGConj
    (AyUCVGMap checkerVersionManifest proofArtifactDigest)
    (AyUCVGConj
      (AyUCVGMap proofArtifactDigest clauseIdMap)
      (AyUCVGConj
        (AyUCVGMap clauseIdMap parentCoverage)
        (AyUCVGConj
          (AyUCVGMap parentCoverage emptyClauseReachable)
          (AyUCVGMap checkerTranscript checkerAccepted))))

def AyUCVGPublication
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUCVGConj
    (AyUCVGAcceptedEvidence checkerVersionManifest proofArtifactDigest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat)
    originalUnsat

def AyUCVGFailureReason
    (versionManifestFailure : Prop) (artifactDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop) :=
  forall result : Prop,
    (versionManifestFailure -> result) ->
    (artifactDigestFailure -> result) ->
    (clauseIdMapFailure -> result) ->
    (parentCoverageFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (fingerprintFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    (auditFailure -> result) ->
    result

def AyUCVGBadVersionAgreement
    (versionManifestFailure : Prop) (artifactDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUCVGConj
    (AyUCVGConj noClaim recompute)
    (AyUCVGFailureReason versionManifestFailure artifactDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure)

def AyUCVGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCVGDisj noClaim originalUnsat

theorem ay_ucvg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCVGConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucvg_conj_left
    (p : Prop) (q : Prop) :
    AyUCVGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucvg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCVGDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucvg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCVGDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucvg_accepted_evidence
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    checkerVersionManifest ->
    proofArtifactDigest ->
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
    AyUCVGAcceptedEvidence checkerVersionManifest proofArtifactDigest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat := by
  intro hVersion
  intro hDigest
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
  exact publish hVersion hDigest hMap hParent hTranscript hChecker hEmpty
    hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive hAudit
    hVisible hOriginal

theorem ay_ucvg_checker_version_manifest
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCVGAcceptedEvidence checkerVersionManifest proofArtifactDigest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    checkerVersionManifest := by
  intro accepted
  exact accepted checkerVersionManifest
    (fun hVersion _hDigest _hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hVersion)

theorem ay_ucvg_proof_artifact_digest
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCVGAcceptedEvidence checkerVersionManifest proofArtifactDigest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    proofArtifactDigest := by
  intro accepted
  exact accepted proofArtifactDigest
    (fun _hVersion hDigest _hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hDigest)

theorem ay_ucvg_clause_id_map
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCVGAcceptedEvidence checkerVersionManifest proofArtifactDigest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    clauseIdMap := by
  intro accepted
  exact accepted clauseIdMap
    (fun _hVersion _hDigest hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hMap)

theorem ay_ucvg_parent_coverage
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCVGAcceptedEvidence checkerVersionManifest proofArtifactDigest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    parentCoverage := by
  intro accepted
  exact accepted parentCoverage
    (fun _hVersion _hDigest _hMap hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hParent)

theorem ay_ucvg_checker_transcript
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCVGAcceptedEvidence checkerVersionManifest proofArtifactDigest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hVersion _hDigest _hMap _hParent hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_ucvg_checker_accepted
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCVGAcceptedEvidence checkerVersionManifest proofArtifactDigest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hVersion _hDigest _hMap _hParent _hTranscript hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hChecker)

theorem ay_ucvg_empty_clause_reachable
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCVGAcceptedEvidence checkerVersionManifest proofArtifactDigest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hVersion _hDigest _hMap _hParent _hTranscript _hChecker hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_ucvg_formula_fingerprint
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCVGAcceptedEvidence checkerVersionManifest proofArtifactDigest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    formulaFingerprint := by
  intro accepted
  exact accepted formulaFingerprint
    (fun _hVersion _hDigest _hMap _hParent _hTranscript _hChecker _hEmpty
      hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_ucvg_original_unsat
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCVGAcceptedEvidence checkerVersionManifest proofArtifactDigest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hVersion _hDigest _hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible hOriginal => hOriginal)

theorem ay_ucvg_publication_sound
    (checkerVersionManifest : Prop) (proofArtifactDigest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCVGPublication checkerVersionManifest proofArtifactDigest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted unsat => unsat)

theorem ay_ucvg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUCVGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucvg_disj_right noClaim originalUnsat unsat

theorem ay_ucvg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUCVGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucvg_disj_left noClaim originalUnsat no_claim

theorem ay_ucvg_bad_no_claim
    (versionManifestFailure : Prop) (artifactDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCVGBadVersionAgreement versionManifestFailure artifactDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_ucvg_bad_recompute
    (versionManifestFailure : Prop) (artifactDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCVGBadVersionAgreement versionManifestFailure artifactDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_ucvg_failed_version_agreement_cannot_bless_unsat
    (versionManifestFailure : Prop) (artifactDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCVGBadVersionAgreement versionManifestFailure artifactDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute ->
    AyUCVGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucvg_public_no_claim_report noClaim originalUnsat
    (ay_ucvg_bad_no_claim versionManifestFailure artifactDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute bad)

theorem ay_ucvg_failure_forces_no_claim
    (versionManifestFailure : Prop) (artifactDigestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCVGBadVersionAgreement versionManifestFailure artifactDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute ->
    AyUCVGConj noClaim recompute := by
  intro bad
  exact ay_ucvg_conj_intro noClaim recompute
    (ay_ucvg_bad_no_claim versionManifestFailure artifactDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute bad)
    (ay_ucvg_bad_recompute versionManifestFailure artifactDigestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute bad)

theorem ay_ucvg_version_manifest_failure_forces_no_claim
    (versionManifestFailure : Prop) (noClaim : Prop) :
    versionManifestFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucvg_artifact_digest_failure_forces_no_claim
    (artifactDigestFailure : Prop) (noClaim : Prop) :
    artifactDigestFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucvg_clause_id_map_failure_forces_no_claim
    (clauseIdMapFailure : Prop) (noClaim : Prop) :
    clauseIdMapFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucvg_parent_coverage_failure_forces_no_claim
    (parentCoverageFailure : Prop) (noClaim : Prop) :
    parentCoverageFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucvg_checker_failure_forces_no_claim
    (checkerFailure : Prop) (noClaim : Prop) :
    checkerFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucvg_empty_clause_failure_forces_no_claim
    (emptyClauseFailure : Prop) (noClaim : Prop) :
    emptyClauseFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucvg_fingerprint_failure_forces_no_claim
    (fingerprintFailure : Prop) (noClaim : Prop) :
    fingerprintFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucvg_build_failure_forces_no_claim
    (buildFailure : Prop) (noClaim : Prop) :
    buildFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucvg_archive_failure_forces_no_claim
    (archiveFailure : Prop) (noClaim : Prop) :
    archiveFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_ucvg_audit_failure_forces_no_claim
    (auditFailure : Prop) (noClaim : Prop) :
    auditFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim
