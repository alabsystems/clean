-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT clause-digest archive manifest soundness for ay
-- sequential-main SAT-COMP validation. Propositions stand for clause digest
-- archives, proof artifact digests, clause-ID maps, parent coverage, checker
-- transcripts, formula fingerprints, empty-clause reachability,
-- reconstruction evidence, build evidence, archive manifests, and fail-closed
-- no-claim/recompute diagnostics.

def AyUCDAConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCDADisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCDAMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCDAArchiveManifest
    (clauseDigestArchive : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :=
  AyUCDAConj clauseDigestArchive
    (AyUCDAConj
      (AyUCDAMap clauseDigestArchive artifactDigest)
      (AyUCDAConj
        (AyUCDAMap artifactDigest archiveManifest)
        (AyUCDAMap archiveManifest checkerTranscript)))

def AyUCDAClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyUCDAConj
    (AyUCDAMap checkerTranscript clauseIdMap)
    (AyUCDAMap clauseIdMap mappedTranscript)

def AyUCDAParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyUCDAConj
    (AyUCDAMap mappedTranscript parentCoverage)
    (AyUCDAMap parentCoverage emptyClauseReachable)

def AyUCDAFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUCDAConj
    (AyUCDAMap mappedTranscript formulaFingerprint)
    (AyUCDAMap formulaFingerprint fingerprintAccepted)

def AyUCDATranscript
    (checkerTranscript : Prop) (transcriptAccepted : Prop) :=
  AyUCDAMap checkerTranscript transcriptAccepted

def AyUCDABuild
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyUCDAConj
    (AyUCDAMap mappedTranscript buildEvidence)
    (AyUCDAMap buildEvidence buildAccepted)

def AyUCDAReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCDAConj reconstructionEvidence
    (AyUCDAConj
      (AyUCDAMap emptyClauseReachable visibleUnsat)
      (AyUCDAMap visibleUnsat originalUnsat))

def AyUCDAAcceptedEvidence
    (clauseDigestArchive : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCDAConj
    (AyUCDAArchiveManifest clauseDigestArchive artifactDigest
      archiveManifest checkerTranscript)
    (AyUCDAConj
      (AyUCDATranscript checkerTranscript transcriptAccepted)
      (AyUCDAConj
        (AyUCDAClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyUCDAConj
          (AyUCDAParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyUCDAConj
            (AyUCDAFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyUCDAConj
              (AyUCDABuild mappedTranscript buildEvidence buildAccepted)
              (AyUCDAReconstruction emptyClauseReachable
                reconstructionEvidence visibleUnsat originalUnsat))))))

def AyUCDAAcceptedPublication
    (clauseDigestArchive : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCDAConj
    (AyUCDAAcceptedEvidence clauseDigestArchive artifactDigest
      archiveManifest checkerTranscript transcriptAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    originalUnsat

def AyUCDAFailureReason
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :=
  AyUCDADisj clauseArchiveDrift
    (AyUCDADisj artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))))

def AyUCDABadArchive
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUCDAConj
    (AyUCDAConj noClaim recompute)
    (AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift
      idMapMismatch parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch)

def AyUCDAPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCDADisj noClaim originalUnsat

theorem ay_ucda_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCDAConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucda_conj_left
    (p : Prop) (q : Prop) :
    AyUCDAConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucda_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCDADisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucda_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCDADisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucda_clause_digest_archive
    (clauseDigestArchive : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUCDAArchiveManifest clauseDigestArchive artifactDigest
      archiveManifest checkerTranscript ->
    clauseDigestArchive := by
  intro manifest
  exact ay_ucda_conj_left clauseDigestArchive
    (AyUCDAConj
      (AyUCDAMap clauseDigestArchive artifactDigest)
      (AyUCDAConj
        (AyUCDAMap artifactDigest archiveManifest)
        (AyUCDAMap archiveManifest checkerTranscript)))
    manifest

theorem ay_ucda_artifact_digest
    (clauseDigestArchive : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUCDAArchiveManifest clauseDigestArchive artifactDigest
      archiveManifest checkerTranscript ->
    artifactDigest := by
  intro manifest
  exact manifest artifactDigest
    (fun archive tail =>
      tail artifactDigest
        (fun archive_to_digest _rest => archive_to_digest archive))

theorem ay_ucda_archive_manifest
    (clauseDigestArchive : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUCDAArchiveManifest clauseDigestArchive artifactDigest
      archiveManifest checkerTranscript ->
    archiveManifest := by
  intro manifest
  exact manifest archiveManifest
    (fun archive tail =>
      tail archiveManifest
        (fun archive_to_digest rest =>
          rest archiveManifest
            (fun digest_to_manifest _manifest_to_transcript =>
              digest_to_manifest (archive_to_digest archive))))

theorem ay_ucda_checker_transcript
    (clauseDigestArchive : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUCDAArchiveManifest clauseDigestArchive artifactDigest
      archiveManifest checkerTranscript ->
    checkerTranscript := by
  intro manifest
  exact manifest checkerTranscript
    (fun archive tail =>
      tail checkerTranscript
        (fun archive_to_digest rest =>
          rest checkerTranscript
            (fun digest_to_manifest manifest_to_transcript =>
              manifest_to_transcript
                (digest_to_manifest (archive_to_digest archive)))))

theorem ay_ucda_transcript_accepted
    (checkerTranscript : Prop) (transcriptAccepted : Prop) :
    AyUCDATranscript checkerTranscript transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro accepted
  exact accepted

theorem ay_ucda_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUCDAClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_id_map _id_map_to_mapped => transcript_to_id_map)

theorem ay_ucda_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUCDAClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_id_map id_map_to_mapped => id_map_to_mapped)

theorem ay_ucda_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUCDAParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_ucda_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUCDAParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_ucda_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCDAFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_ucda_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCDAFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_ucda_build_evidence
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUCDABuild mappedTranscript buildEvidence buildAccepted ->
    mappedTranscript ->
    buildEvidence := by
  intro build
  exact build (mappedTranscript -> buildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_ucda_build_accepted
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUCDABuild mappedTranscript buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_ucda_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDAReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_ucda_conj_left reconstructionEvidence
    (AyUCDAConj
      (AyUCDAMap emptyClauseReachable visibleUnsat)
      (AyUCDAMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_ucda_visible_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDAReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_ucda_original_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDAReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_ucda_accepted_evidence
    (clauseDigestArchive : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDAAcceptedPublication clauseDigestArchive artifactDigest
      archiveManifest checkerTranscript transcriptAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    AyUCDAAcceptedEvidence clauseDigestArchive artifactDigest archiveManifest
      checkerTranscript transcriptAccepted clauseIdMap mappedTranscript
      parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat := by
  intro accepted
  exact accepted
    (AyUCDAAcceptedEvidence clauseDigestArchive artifactDigest
      archiveManifest checkerTranscript transcriptAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_ucda_publication_sound
    (clauseDigestArchive : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDAAcceptedPublication clauseDigestArchive artifactDigest
      archiveManifest checkerTranscript transcriptAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_ucda_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUCDAPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucda_disj_right noClaim originalUnsat unsat

theorem ay_ucda_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUCDAPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucda_disj_left noClaim originalUnsat no_claim

theorem ay_ucda_bad_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDABadArchive clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_ucda_conj_left noClaim recompute fail_closed)

theorem ay_ucda_bad_recompute
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDABadArchive clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_ucda_bad_public_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCDABadArchive clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute ->
    AyUCDAPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucda_public_no_claim_report noClaim originalUnsat
    (ay_ucda_bad_no_claim clauseArchiveDrift artifactDigestDrift
      idMapMismatch parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute bad)

theorem ay_ucda_bad_cannot_bless_unsat
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDABadArchive clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_ucda_bad_no_claim clauseArchiveDrift artifactDigestDrift
    idMapMismatch parentCoverageGap staleFingerprint uncheckedTranscript
    missingEmptyClause reconstructionGap buildDrift archiveMismatch noClaim
    recompute bad

theorem ay_ucda_failure_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch ->
    noClaim ->
    recompute ->
    AyUCDABadArchive clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch
      noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_ucda_conj_intro (AyUCDAConj noClaim recompute)
    (AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift
      idMapMismatch parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch)
    (ay_ucda_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_ucda_clause_archive_drift_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    clauseArchiveDrift ->
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro drift
  exact ay_ucda_disj_left clauseArchiveDrift
    (AyUCDADisj artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))))
    drift

theorem ay_ucda_failure_tail_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    AyUCDADisj artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))) ->
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro tail
  exact ay_ucda_disj_right clauseArchiveDrift
    (AyUCDADisj artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))))
    tail

theorem ay_ucda_artifact_digest_drift_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    artifactDigestDrift ->
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro drift
  exact ay_ucda_failure_tail_forces_no_claim clauseArchiveDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_ucda_disj_left artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))))
      drift)

theorem ay_ucda_id_map_mismatch_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    idMapMismatch ->
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro mismatch
  exact ay_ucda_failure_tail_forces_no_claim clauseArchiveDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_ucda_disj_right artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))))
      (ay_ucda_disj_left idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))
        mismatch))

theorem ay_ucda_parent_coverage_gap_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    parentCoverageGap ->
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro gap
  exact ay_ucda_failure_tail_forces_no_claim clauseArchiveDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_ucda_disj_right artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))))
      (ay_ucda_disj_right idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))
        (ay_ucda_disj_left parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))
          gap)))

theorem ay_ucda_stale_fingerprint_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    staleFingerprint ->
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro stale
  exact ay_ucda_failure_tail_forces_no_claim clauseArchiveDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_ucda_disj_right artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))))
      (ay_ucda_disj_right idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))
        (ay_ucda_disj_right parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))
          (ay_ucda_disj_left staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))
            stale))))

theorem ay_ucda_unchecked_transcript_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    uncheckedTranscript ->
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro unchecked
  exact ay_ucda_failure_tail_forces_no_claim clauseArchiveDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_ucda_disj_right artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))))
      (ay_ucda_disj_right idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))
        (ay_ucda_disj_right parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))
          (ay_ucda_disj_right staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))
            (ay_ucda_disj_left uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))
              unchecked)))))

theorem ay_ucda_missing_empty_clause_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    missingEmptyClause ->
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro missing
  exact ay_ucda_failure_tail_forces_no_claim clauseArchiveDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_ucda_disj_right artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))))
      (ay_ucda_disj_right idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))
        (ay_ucda_disj_right parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))
          (ay_ucda_disj_right staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))
            (ay_ucda_disj_right uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))
              (ay_ucda_disj_left missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))
                missing))))))

theorem ay_ucda_reconstruction_gap_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    reconstructionGap ->
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro gap
  exact ay_ucda_failure_tail_forces_no_claim clauseArchiveDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_ucda_disj_right artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))))
      (ay_ucda_disj_right idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))
        (ay_ucda_disj_right parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))
          (ay_ucda_disj_right staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))
            (ay_ucda_disj_right uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))
              (ay_ucda_disj_right missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))
                (ay_ucda_disj_left reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)
                  gap)))))))

theorem ay_ucda_build_drift_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    buildDrift ->
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro drift
  exact ay_ucda_failure_tail_forces_no_claim clauseArchiveDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_ucda_disj_right artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))))
      (ay_ucda_disj_right idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))
        (ay_ucda_disj_right parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))
          (ay_ucda_disj_right staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))
            (ay_ucda_disj_right uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))
              (ay_ucda_disj_right missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))
                (ay_ucda_disj_right reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)
                  (ay_ucda_disj_left buildDrift archiveMismatch
                    drift))))))))

theorem ay_ucda_archive_mismatch_forces_no_claim
    (clauseArchiveDrift : Prop) (artifactDigestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop) :
    archiveMismatch ->
    AyUCDAFailureReason clauseArchiveDrift artifactDigestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift archiveMismatch := by
  intro mismatch
  exact ay_ucda_failure_tail_forces_no_claim clauseArchiveDrift
    artifactDigestDrift idMapMismatch parentCoverageGap staleFingerprint
    uncheckedTranscript missingEmptyClause reconstructionGap buildDrift
    archiveMismatch
    (ay_ucda_disj_right artifactDigestDrift
      (AyUCDADisj idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))))
      (ay_ucda_disj_right idMapMismatch
        (AyUCDADisj parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))))
        (ay_ucda_disj_right parentCoverageGap
          (AyUCDADisj staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))))
          (ay_ucda_disj_right staleFingerprint
            (AyUCDADisj uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))))
            (ay_ucda_disj_right uncheckedTranscript
              (AyUCDADisj missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)))
              (ay_ucda_disj_right missingEmptyClause
                (AyUCDADisj reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch))
                (ay_ucda_disj_right reconstructionGap
                  (AyUCDADisj buildDrift archiveMismatch)
                  (ay_ucda_disj_right buildDrift archiveMismatch
                    mismatch))))))))
