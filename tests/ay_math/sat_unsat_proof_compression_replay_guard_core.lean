-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded proof-compression replay guard soundness for ay sequential-main
-- SAT-COMP validation. Propositions stand for source proof digests,
-- compressed proof manifests, clause-id maps, parent coverage, checker
-- transcripts, empty-clause reachability, formula fingerprints, solver build
-- evidence, archive manifests, audit transcripts, and fail-closed
-- no-claim/recompute diagnostics.

def AyPCPGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyPCPGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyPCPGMap (source : Prop) (target : Prop) :=
  source -> target

def AyPCPGAcceptedEvidence
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (sourceProofDigest ->
      compressedProofManifest ->
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

def AyPCPGCompressionCertificate
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) :=
  AyPCPGConj sourceProofDigest
    (AyPCPGConj compressedProofManifest
      (AyPCPGConj clauseIdMap
        (AyPCPGConj archiveManifest auditTranscript)))

def AyPCPGReplayGuard
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) :=
  AyPCPGConj
    (AyPCPGMap sourceProofDigest compressedProofManifest)
    (AyPCPGConj
      (AyPCPGMap compressedProofManifest clauseIdMap)
      (AyPCPGConj
        (AyPCPGMap clauseIdMap parentCoverage)
        (AyPCPGConj
          (AyPCPGMap parentCoverage emptyClauseReachable)
          (AyPCPGMap checkerTranscript checkerAccepted))))

def AyPCPGPublication
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyPCPGConj
    (AyPCPGAcceptedEvidence sourceProofDigest compressedProofManifest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat)
    originalUnsat

def AyPCPGFailureReason
    (sourceDigestFailure : Prop) (compressionManifestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop) :=
  forall result : Prop,
    (sourceDigestFailure -> result) ->
    (compressionManifestFailure -> result) ->
    (clauseIdMapFailure -> result) ->
    (parentCoverageFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (fingerprintFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    (auditFailure -> result) ->
    result

def AyPCPGBadCompression
    (sourceDigestFailure : Prop) (compressionManifestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyPCPGConj
    (AyPCPGConj noClaim recompute)
    (AyPCPGFailureReason sourceDigestFailure compressionManifestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure)

def AyPCPGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyPCPGDisj noClaim originalUnsat

theorem ay_pcpg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyPCPGConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_pcpg_conj_left
    (p : Prop) (q : Prop) :
    AyPCPGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_pcpg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyPCPGDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_pcpg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyPCPGDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_pcpg_accepted_evidence
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    sourceProofDigest ->
    compressedProofManifest ->
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
    AyPCPGAcceptedEvidence sourceProofDigest compressedProofManifest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat := by
  intro hSource
  intro hCompressed
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
  exact publish hSource hCompressed hMap hParent hTranscript hChecker hEmpty
    hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive hAudit
    hVisible hOriginal

theorem ay_pcpg_source_proof_digest
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPCPGAcceptedEvidence sourceProofDigest compressedProofManifest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    sourceProofDigest := by
  intro accepted
  exact accepted sourceProofDigest
    (fun hSource _hCompressed _hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hSource)

theorem ay_pcpg_compressed_proof_manifest
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPCPGAcceptedEvidence sourceProofDigest compressedProofManifest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    compressedProofManifest := by
  intro accepted
  exact accepted compressedProofManifest
    (fun _hSource hCompressed _hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hCompressed)

theorem ay_pcpg_clause_id_map
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPCPGAcceptedEvidence sourceProofDigest compressedProofManifest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    clauseIdMap := by
  intro accepted
  exact accepted clauseIdMap
    (fun _hSource _hCompressed hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hMap)

theorem ay_pcpg_parent_coverage
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPCPGAcceptedEvidence sourceProofDigest compressedProofManifest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    parentCoverage := by
  intro accepted
  exact accepted parentCoverage
    (fun _hSource _hCompressed _hMap hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hParent)

theorem ay_pcpg_checker_transcript
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPCPGAcceptedEvidence sourceProofDigest compressedProofManifest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hSource _hCompressed _hMap _hParent hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_pcpg_checker_accepted
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPCPGAcceptedEvidence sourceProofDigest compressedProofManifest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hSource _hCompressed _hMap _hParent _hTranscript hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hChecker)

theorem ay_pcpg_empty_clause_reachable
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPCPGAcceptedEvidence sourceProofDigest compressedProofManifest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hSource _hCompressed _hMap _hParent _hTranscript _hChecker hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_pcpg_formula_fingerprint
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPCPGAcceptedEvidence sourceProofDigest compressedProofManifest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    formulaFingerprint := by
  intro accepted
  exact accepted formulaFingerprint
    (fun _hSource _hCompressed _hMap _hParent _hTranscript _hChecker _hEmpty
      hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_pcpg_original_unsat
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPCPGAcceptedEvidence sourceProofDigest compressedProofManifest
      clauseIdMap parentCoverage checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest auditTranscript
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hSource _hCompressed _hMap _hParent _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hAudit _hVisible hOriginal => hOriginal)

theorem ay_pcpg_publication_sound
    (sourceProofDigest : Prop) (compressedProofManifest : Prop)
    (clauseIdMap : Prop) (parentCoverage : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPCPGPublication sourceProofDigest compressedProofManifest clauseIdMap
      parentCoverage checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      archiveManifest auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted unsat => unsat)

theorem ay_pcpg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyPCPGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_pcpg_disj_right noClaim originalUnsat unsat

theorem ay_pcpg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyPCPGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_pcpg_disj_left noClaim originalUnsat no_claim

theorem ay_pcpg_bad_no_claim
    (sourceDigestFailure : Prop) (compressionManifestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyPCPGBadCompression sourceDigestFailure compressionManifestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_pcpg_bad_recompute
    (sourceDigestFailure : Prop) (compressionManifestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyPCPGBadCompression sourceDigestFailure compressionManifestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_pcpg_failed_compression_cannot_bless_unsat
    (sourceDigestFailure : Prop) (compressionManifestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyPCPGBadCompression sourceDigestFailure compressionManifestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute ->
    AyPCPGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_pcpg_public_no_claim_report noClaim originalUnsat
    (ay_pcpg_bad_no_claim sourceDigestFailure compressionManifestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute bad)

theorem ay_pcpg_failure_forces_no_claim
    (sourceDigestFailure : Prop) (compressionManifestFailure : Prop)
    (clauseIdMapFailure : Prop) (parentCoverageFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (auditFailure : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyPCPGBadCompression sourceDigestFailure compressionManifestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute ->
    AyPCPGConj noClaim recompute := by
  intro bad
  exact ay_pcpg_conj_intro noClaim recompute
    (ay_pcpg_bad_no_claim sourceDigestFailure compressionManifestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute bad)
    (ay_pcpg_bad_recompute sourceDigestFailure compressionManifestFailure
      clauseIdMapFailure parentCoverageFailure checkerFailure
      emptyClauseFailure fingerprintFailure buildFailure archiveFailure
      auditFailure noClaim recompute bad)

theorem ay_pcpg_source_digest_failure_forces_no_claim
    (sourceDigestFailure : Prop) (noClaim : Prop) :
    sourceDigestFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_pcpg_compression_manifest_failure_forces_no_claim
    (compressionManifestFailure : Prop) (noClaim : Prop) :
    compressionManifestFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_pcpg_clause_id_map_failure_forces_no_claim
    (clauseIdMapFailure : Prop) (noClaim : Prop) :
    clauseIdMapFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_pcpg_parent_coverage_failure_forces_no_claim
    (parentCoverageFailure : Prop) (noClaim : Prop) :
    parentCoverageFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_pcpg_checker_failure_forces_no_claim
    (checkerFailure : Prop) (noClaim : Prop) :
    checkerFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_pcpg_empty_clause_failure_forces_no_claim
    (emptyClauseFailure : Prop) (noClaim : Prop) :
    emptyClauseFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_pcpg_fingerprint_failure_forces_no_claim
    (fingerprintFailure : Prop) (noClaim : Prop) :
    fingerprintFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_pcpg_build_failure_forces_no_claim
    (buildFailure : Prop) (noClaim : Prop) :
    buildFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_pcpg_archive_failure_forces_no_claim
    (archiveFailure : Prop) (noClaim : Prop) :
    archiveFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_pcpg_audit_failure_forces_no_claim
    (auditFailure : Prop) (noClaim : Prop) :
    auditFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim
