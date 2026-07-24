-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded DRAT/LRAT hint digest manifest soundness for ay sequential-main
-- SAT-COMP validation. Propositions stand for hint digest manifests, proof
-- artifact digests, clause-ID maps, parent coverage, checker transcripts,
-- formula fingerprints, empty-clause reachability, reconstruction evidence,
-- build evidence, archive manifests, and fail-closed no-claim/recompute
-- diagnostics.

def AyUDHDConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUDHDDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUDHDMap (source : Prop) (target : Prop) :=
  source -> target

def AyUDHDHintManifest
    (hintDigestManifest : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :=
  AyUDHDConj hintDigestManifest
    (AyUDHDConj
      (AyUDHDMap hintDigestManifest artifactDigest)
      (AyUDHDConj
        (AyUDHDMap artifactDigest archiveManifest)
        (AyUDHDMap archiveManifest checkerTranscript)))

def AyUDHDClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyUDHDConj
    (AyUDHDMap checkerTranscript clauseIdMap)
    (AyUDHDMap clauseIdMap mappedTranscript)

def AyUDHDParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyUDHDConj
    (AyUDHDMap mappedTranscript parentCoverage)
    (AyUDHDMap parentCoverage emptyClauseReachable)

def AyUDHDFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUDHDConj
    (AyUDHDMap mappedTranscript formulaFingerprint)
    (AyUDHDMap formulaFingerprint fingerprintAccepted)

def AyUDHDTranscript
    (checkerTranscript : Prop) (transcriptAccepted : Prop) :=
  AyUDHDMap checkerTranscript transcriptAccepted

def AyUDHDBuild
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyUDHDConj
    (AyUDHDMap mappedTranscript buildEvidence)
    (AyUDHDMap buildEvidence buildAccepted)

def AyUDHDReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUDHDConj reconstructionEvidence
    (AyUDHDConj
      (AyUDHDMap emptyClauseReachable visibleUnsat)
      (AyUDHDMap visibleUnsat originalUnsat))

def AyUDHDAcceptedEvidence
    (hintDigestManifest : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUDHDConj
    (AyUDHDHintManifest hintDigestManifest artifactDigest archiveManifest
      checkerTranscript)
    (AyUDHDConj
      (AyUDHDTranscript checkerTranscript transcriptAccepted)
      (AyUDHDConj
        (AyUDHDClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyUDHDConj
          (AyUDHDParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyUDHDConj
            (AyUDHDFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyUDHDConj
              (AyUDHDBuild mappedTranscript buildEvidence buildAccepted)
              (AyUDHDReconstruction emptyClauseReachable
                reconstructionEvidence visibleUnsat originalUnsat))))))

def AyUDHDAcceptedPublication
    (hintDigestManifest : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUDHDConj
    (AyUDHDAcceptedEvidence hintDigestManifest artifactDigest
      archiveManifest checkerTranscript transcriptAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat)
    originalUnsat

def AyUDHDFailureReason
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :=
  AyUDHDDisj hintDigestDrift
    (AyUDHDDisj artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))))

def AyUDHDBadManifest
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUDHDConj
    (AyUDHDConj noClaim recompute)
    (AyUDHDFailureReason hintDigestDrift artifactDigestDrift
      idMapMismatch parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch)

def AyUDHDPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUDHDDisj noClaim originalUnsat

theorem ay_udhd_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUDHDConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_udhd_conj_left
    (p : Prop) (q : Prop) :
    AyUDHDConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_udhd_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUDHDDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_udhd_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUDHDDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_udhd_hint_digest_manifest
    (hintDigestManifest : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUDHDHintManifest hintDigestManifest artifactDigest archiveManifest
      checkerTranscript ->
    hintDigestManifest := by
  intro manifest
  exact ay_udhd_conj_left hintDigestManifest
    (AyUDHDConj
      (AyUDHDMap hintDigestManifest artifactDigest)
      (AyUDHDConj
        (AyUDHDMap artifactDigest archiveManifest)
        (AyUDHDMap archiveManifest checkerTranscript)))
    manifest

theorem ay_udhd_artifact_digest
    (hintDigestManifest : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUDHDHintManifest hintDigestManifest artifactDigest archiveManifest
      checkerTranscript ->
    artifactDigest := by
  intro manifest
  exact manifest artifactDigest
    (fun hint tail =>
      tail artifactDigest
        (fun hint_to_digest _rest => hint_to_digest hint))

theorem ay_udhd_archive_manifest
    (hintDigestManifest : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUDHDHintManifest hintDigestManifest artifactDigest archiveManifest
      checkerTranscript ->
    archiveManifest := by
  intro manifest
  exact manifest archiveManifest
    (fun hint tail =>
      tail archiveManifest
        (fun hint_to_digest rest =>
          rest archiveManifest
            (fun digest_to_archive _archive_to_transcript =>
              digest_to_archive (hint_to_digest hint))))

theorem ay_udhd_checker_transcript
    (hintDigestManifest : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUDHDHintManifest hintDigestManifest artifactDigest archiveManifest
      checkerTranscript ->
    checkerTranscript := by
  intro manifest
  exact manifest checkerTranscript
    (fun hint tail =>
      tail checkerTranscript
        (fun hint_to_digest rest =>
          rest checkerTranscript
            (fun digest_to_archive archive_to_transcript =>
              archive_to_transcript
                (digest_to_archive (hint_to_digest hint)))))

theorem ay_udhd_transcript_accepted
    (checkerTranscript : Prop) (transcriptAccepted : Prop) :
    AyUDHDTranscript checkerTranscript transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro accepted
  exact accepted

theorem ay_udhd_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUDHDClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_id_map _id_map_to_mapped => transcript_to_id_map)

theorem ay_udhd_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUDHDClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_id_map id_map_to_mapped => id_map_to_mapped)

theorem ay_udhd_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUDHDParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_udhd_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUDHDParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_udhd_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUDHDFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_udhd_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUDHDFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_udhd_build_evidence
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUDHDBuild mappedTranscript buildEvidence buildAccepted ->
    mappedTranscript ->
    buildEvidence := by
  intro build
  exact build (mappedTranscript -> buildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_udhd_build_accepted
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUDHDBuild mappedTranscript buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_udhd_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDHDReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_udhd_conj_left reconstructionEvidence
    (AyUDHDConj
      (AyUDHDMap emptyClauseReachable visibleUnsat)
      (AyUDHDMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_udhd_visible_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDHDReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_udhd_original_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDHDReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_udhd_accepted_evidence
    (hintDigestManifest : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDHDAcceptedPublication hintDigestManifest artifactDigest
      archiveManifest checkerTranscript transcriptAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    AyUDHDAcceptedEvidence hintDigestManifest artifactDigest archiveManifest
      checkerTranscript transcriptAccepted clauseIdMap mappedTranscript
      parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat := by
  intro accepted
  exact accepted
    (AyUDHDAcceptedEvidence hintDigestManifest artifactDigest archiveManifest
      checkerTranscript transcriptAccepted clauseIdMap mappedTranscript
      parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_udhd_publication_sound
    (hintDigestManifest : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDHDAcceptedPublication hintDigestManifest artifactDigest
      archiveManifest checkerTranscript transcriptAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_udhd_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUDHDPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_udhd_disj_right noClaim originalUnsat unsat

theorem ay_udhd_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUDHDPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_udhd_disj_left noClaim originalUnsat no_claim

theorem ay_udhd_bad_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUDHDBadManifest hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_udhd_conj_left noClaim recompute fail_closed)

theorem ay_udhd_bad_recompute
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUDHDBadManifest hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_udhd_bad_public_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUDHDBadManifest hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute ->
    AyUDHDPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_udhd_public_no_claim_report noClaim originalUnsat
    (ay_udhd_bad_no_claim hintDigestDrift artifactDigestDrift
      idMapMismatch parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute bad)

theorem ay_udhd_bad_cannot_bless_unsat
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUDHDBadManifest hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_udhd_bad_no_claim hintDigestDrift artifactDigestDrift
    idMapMismatch parentCoverageGap staleFingerprint uncheckedTranscript
    missingEmptyClause reconstructionGap buildDrift archiveMismatch noClaim
    recompute bad

theorem ay_udhd_failure_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch ->
    noClaim ->
    recompute ->
    AyUDHDBadManifest hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_udhd_conj_intro (AyUDHDConj noClaim recompute)
    (AyUDHDFailureReason hintDigestDrift artifactDigestDrift
      idMapMismatch parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch)
    (ay_udhd_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_udhd_hint_digest_drift_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    hintDigestDrift ->
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro drift
  exact ay_udhd_disj_left hintDigestDrift
    (AyUDHDDisj artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))))
    drift

theorem ay_udhd_failure_tail_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    AyUDHDDisj artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))) ->
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro tail
  exact ay_udhd_disj_right hintDigestDrift
    (AyUDHDDisj artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))))
    tail

theorem ay_udhd_artifact_digest_drift_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    artifactDigestDrift ->
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro drift
  exact ay_udhd_failure_tail_forces_no_claim hintDigestDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_udhd_disj_left artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))))
      drift)

theorem ay_udhd_id_map_mismatch_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    idMapMismatch ->
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro mismatch
  exact ay_udhd_failure_tail_forces_no_claim hintDigestDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_udhd_disj_right artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))))
      (ay_udhd_disj_left idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))
        mismatch))

theorem ay_udhd_parent_coverage_gap_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    parentCoverageGap ->
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro gap
  exact ay_udhd_failure_tail_forces_no_claim hintDigestDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_udhd_disj_right artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))))
      (ay_udhd_disj_right idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))
        (ay_udhd_disj_left parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))
          gap)))

theorem ay_udhd_stale_fingerprint_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    staleFingerprint ->
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro stale
  exact ay_udhd_failure_tail_forces_no_claim hintDigestDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_udhd_disj_right artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))))
      (ay_udhd_disj_right idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))
        (ay_udhd_disj_right parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))
          (ay_udhd_disj_left staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))
            stale))))

theorem ay_udhd_unchecked_transcript_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    uncheckedTranscript ->
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro unchecked
  exact ay_udhd_failure_tail_forces_no_claim hintDigestDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_udhd_disj_right artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))))
      (ay_udhd_disj_right idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))
        (ay_udhd_disj_right parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))
          (ay_udhd_disj_right staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))
            (ay_udhd_disj_left uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))
              unchecked)))))

theorem ay_udhd_missing_empty_clause_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    missingEmptyClause ->
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro missing
  exact ay_udhd_failure_tail_forces_no_claim hintDigestDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_udhd_disj_right artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))))
      (ay_udhd_disj_right idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))
        (ay_udhd_disj_right parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))
          (ay_udhd_disj_right staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))
            (ay_udhd_disj_right uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))
              (ay_udhd_disj_left missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))
                missing))))))

theorem ay_udhd_reconstruction_gap_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    reconstructionGap ->
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro gap
  exact ay_udhd_failure_tail_forces_no_claim hintDigestDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_udhd_disj_right artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))))
      (ay_udhd_disj_right idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))
        (ay_udhd_disj_right parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))
          (ay_udhd_disj_right staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))
            (ay_udhd_disj_right uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))
              (ay_udhd_disj_right missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))
                (ay_udhd_disj_left reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)
                  gap)))))))

theorem ay_udhd_build_drift_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    buildDrift ->
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro drift
  exact ay_udhd_failure_tail_forces_no_claim hintDigestDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_udhd_disj_right artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))))
      (ay_udhd_disj_right idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))
        (ay_udhd_disj_right parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))
          (ay_udhd_disj_right staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))
            (ay_udhd_disj_right uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))
              (ay_udhd_disj_right missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))
                (ay_udhd_disj_right reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)
                  (ay_udhd_disj_left buildDrift archiveMismatch
                    drift))))))))

theorem ay_udhd_archive_mismatch_forces_no_claim
    (hintDigestDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    archiveMismatch ->
    AyUDHDFailureReason hintDigestDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro mismatch
  exact ay_udhd_failure_tail_forces_no_claim hintDigestDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_udhd_disj_right artifactDigestDrift
      (AyUDHDDisj idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))))
      (ay_udhd_disj_right idMapMismatch
        (AyUDHDDisj parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))))
        (ay_udhd_disj_right parentCoverageGap
          (AyUDHDDisj staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))))
          (ay_udhd_disj_right staleFingerprint
            (AyUDHDDisj uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))))
            (ay_udhd_disj_right uncheckedTranscript
              (AyUDHDDisj missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)))
              (ay_udhd_disj_right missingEmptyClause
                (AyUDHDDisj reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch))
                (ay_udhd_disj_right reconstructionGap
                  (AyUDHDDisj buildDrift archiveMismatch)
                  (ay_udhd_disj_right buildDrift archiveMismatch
                    mismatch))))))))
