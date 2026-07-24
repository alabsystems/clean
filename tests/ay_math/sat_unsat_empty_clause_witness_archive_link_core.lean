-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded empty-clause witness/archive link soundness for ay sequential-main
-- SAT-COMP validation. Propositions stand for empty-clause witnesses, proof
-- artifact digests, clause-ID maps, parent coverage, checker transcripts,
-- formula fingerprints, build evidence, archive manifests, reconstruction
-- evidence, and fail-closed no-claim/recompute diagnostics.

def AyUEWAConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUEWADisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUEWAMap (source : Prop) (target : Prop) :=
  source -> target

def AyUEWAWitnessArchiveLink
    (emptyWitness : Prop) (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :=
  AyUEWAConj emptyWitness
    (AyUEWAConj
      (AyUEWAMap emptyWitness artifactDigest)
      (AyUEWAConj
        (AyUEWAMap artifactDigest archiveManifest)
        (AyUEWAMap archiveManifest checkerTranscript)))

def AyUEWAClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyUEWAConj
    (AyUEWAMap checkerTranscript clauseIdMap)
    (AyUEWAMap clauseIdMap mappedTranscript)

def AyUEWAParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyReachable : Prop) :=
  AyUEWAConj
    (AyUEWAMap mappedTranscript parentCoverage)
    (AyUEWAMap parentCoverage emptyReachable)

def AyUEWAFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUEWAConj
    (AyUEWAMap mappedTranscript formulaFingerprint)
    (AyUEWAMap formulaFingerprint fingerprintAccepted)

def AyUEWATranscript
    (checkerTranscript : Prop) (transcriptAccepted : Prop) :=
  AyUEWAMap checkerTranscript transcriptAccepted

def AyUEWABuild
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyUEWAConj
    (AyUEWAMap mappedTranscript buildEvidence)
    (AyUEWAMap buildEvidence buildAccepted)

def AyUEWAReconstruction
    (emptyReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUEWAConj reconstructionEvidence
    (AyUEWAConj
      (AyUEWAMap emptyReachable visibleUnsat)
      (AyUEWAMap visibleUnsat originalUnsat))

def AyUEWAAcceptedEvidence
    (emptyWitness : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUEWAConj
    (AyUEWAWitnessArchiveLink emptyWitness artifactDigest archiveManifest
      checkerTranscript)
    (AyUEWAConj
      (AyUEWATranscript checkerTranscript transcriptAccepted)
      (AyUEWAConj
        (AyUEWAClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyUEWAConj
          (AyUEWAParentCoverage mappedTranscript parentCoverage
            emptyReachable)
          (AyUEWAConj
            (AyUEWAFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyUEWAConj
              (AyUEWABuild mappedTranscript buildEvidence buildAccepted)
              (AyUEWAReconstruction emptyReachable reconstructionEvidence
                visibleUnsat originalUnsat))))))

def AyUEWAAcceptedPublication
    (emptyWitness : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUEWAConj
    (AyUEWAAcceptedEvidence emptyWitness artifactDigest archiveManifest
      checkerTranscript transcriptAccepted clauseIdMap mappedTranscript
      parentCoverage emptyReachable formulaFingerprint fingerprintAccepted
      buildEvidence buildAccepted reconstructionEvidence visibleUnsat
      originalUnsat)
    originalUnsat

def AyUEWAFailureReason
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) :=
  AyUEWADisj missingWitness
    (AyUEWADisj digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))))

def AyUEWABadLink
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUEWAConj
    (AyUEWAConj noClaim recompute)
    (AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap)

def AyUEWAPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUEWADisj noClaim originalUnsat

theorem ay_uewa_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUEWAConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uewa_conj_left
    (p : Prop) (q : Prop) :
    AyUEWAConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uewa_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUEWADisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uewa_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUEWADisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uewa_empty_witness
    (emptyWitness : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUEWAWitnessArchiveLink emptyWitness artifactDigest archiveManifest
      checkerTranscript ->
    emptyWitness := by
  intro link
  exact ay_uewa_conj_left emptyWitness
    (AyUEWAConj
      (AyUEWAMap emptyWitness artifactDigest)
      (AyUEWAConj
        (AyUEWAMap artifactDigest archiveManifest)
        (AyUEWAMap archiveManifest checkerTranscript)))
    link

theorem ay_uewa_artifact_digest
    (emptyWitness : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUEWAWitnessArchiveLink emptyWitness artifactDigest archiveManifest
      checkerTranscript ->
    artifactDigest := by
  intro link
  exact link artifactDigest
    (fun witness tail =>
      tail artifactDigest
        (fun witness_to_digest _rest => witness_to_digest witness))

theorem ay_uewa_archive_manifest
    (emptyWitness : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUEWAWitnessArchiveLink emptyWitness artifactDigest archiveManifest
      checkerTranscript ->
    archiveManifest := by
  intro link
  exact link archiveManifest
    (fun witness tail =>
      tail archiveManifest
        (fun witness_to_digest rest =>
          rest archiveManifest
            (fun digest_to_archive _archive_to_transcript =>
              digest_to_archive (witness_to_digest witness))))

theorem ay_uewa_checker_transcript
    (emptyWitness : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUEWAWitnessArchiveLink emptyWitness artifactDigest archiveManifest
      checkerTranscript ->
    checkerTranscript := by
  intro link
  exact link checkerTranscript
    (fun witness tail =>
      tail checkerTranscript
        (fun witness_to_digest rest =>
          rest checkerTranscript
            (fun digest_to_archive archive_to_transcript =>
              archive_to_transcript
                (digest_to_archive (witness_to_digest witness)))))

theorem ay_uewa_transcript_accepted
    (checkerTranscript : Prop) (transcriptAccepted : Prop) :
    AyUEWATranscript checkerTranscript transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro accepted
  exact accepted

theorem ay_uewa_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUEWAClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_id_map _id_map_to_mapped => transcript_to_id_map)

theorem ay_uewa_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUEWAClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_id_map id_map_to_mapped => id_map_to_mapped)

theorem ay_uewa_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyReachable : Prop) :
    AyUEWAParentCoverage mappedTranscript parentCoverage emptyReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_uewa_empty_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyReachable : Prop) :
    AyUEWAParentCoverage mappedTranscript parentCoverage emptyReachable ->
    parentCoverage ->
    emptyReachable := by
  intro parents
  exact parents (parentCoverage -> emptyReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_uewa_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUEWAFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_uewa_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUEWAFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_uewa_build_evidence
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUEWABuild mappedTranscript buildEvidence buildAccepted ->
    mappedTranscript ->
    buildEvidence := by
  intro build
  exact build (mappedTranscript -> buildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_uewa_build_accepted
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUEWABuild mappedTranscript buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_uewa_reconstruction_evidence
    (emptyReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUEWAReconstruction emptyReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_uewa_conj_left reconstructionEvidence
    (AyUEWAConj
      (AyUEWAMap emptyReachable visibleUnsat)
      (AyUEWAMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_uewa_visible_unsat
    (emptyReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUEWAReconstruction emptyReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    emptyReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyReachable -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyReachable -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_uewa_original_unsat
    (emptyReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUEWAReconstruction emptyReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_uewa_accepted_evidence
    (emptyWitness : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUEWAAcceptedPublication emptyWitness artifactDigest archiveManifest
      checkerTranscript transcriptAccepted clauseIdMap mappedTranscript
      parentCoverage emptyReachable formulaFingerprint fingerprintAccepted
      buildEvidence buildAccepted reconstructionEvidence visibleUnsat
      originalUnsat ->
    AyUEWAAcceptedEvidence emptyWitness artifactDigest archiveManifest
      checkerTranscript transcriptAccepted clauseIdMap mappedTranscript
      parentCoverage emptyReachable formulaFingerprint fingerprintAccepted
      buildEvidence buildAccepted reconstructionEvidence visibleUnsat
      originalUnsat := by
  intro accepted
  exact accepted
    (AyUEWAAcceptedEvidence emptyWitness artifactDigest archiveManifest
      checkerTranscript transcriptAccepted clauseIdMap mappedTranscript
      parentCoverage emptyReachable formulaFingerprint fingerprintAccepted
      buildEvidence buildAccepted reconstructionEvidence visibleUnsat
      originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_uewa_publication_sound
    (emptyWitness : Prop) (artifactDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUEWAAcceptedPublication emptyWitness artifactDigest archiveManifest
      checkerTranscript transcriptAccepted clauseIdMap mappedTranscript
      parentCoverage emptyReachable formulaFingerprint fingerprintAccepted
      buildEvidence buildAccepted reconstructionEvidence visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_uewa_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUEWAPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_uewa_disj_right noClaim originalUnsat unsat

theorem ay_uewa_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUEWAPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_uewa_disj_left noClaim originalUnsat no_claim

theorem ay_uewa_bad_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUEWABadLink missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_uewa_conj_left noClaim recompute fail_closed)

theorem ay_uewa_bad_recompute
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUEWABadLink missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_uewa_bad_public_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUEWABadLink missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap noClaim recompute ->
    AyUEWAPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_uewa_public_no_claim_report noClaim originalUnsat
    (ay_uewa_bad_no_claim missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap noClaim recompute bad)

theorem ay_uewa_bad_cannot_bless_unsat
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUEWABadLink missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_uewa_bad_no_claim missingWitness digestDrift idMapMismatch
    parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
    archiveMismatch reconstructionGap noClaim recompute bad

theorem ay_uewa_failure_forces_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap ->
    noClaim ->
    recompute ->
    AyUEWABadLink missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_uewa_conj_intro (AyUEWAConj noClaim recompute)
    (AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap)
    (ay_uewa_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_uewa_missing_witness_forces_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) :
    missingWitness ->
    AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap := by
  intro missing
  exact ay_uewa_disj_left missingWitness
    (AyUEWADisj digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))))
    missing

theorem ay_uewa_digest_drift_forces_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) :
    digestDrift ->
    AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap := by
  intro drift
  exact ay_uewa_disj_right missingWitness
    (AyUEWADisj digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))))
    (ay_uewa_disj_left digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))))
      drift)

theorem ay_uewa_id_map_mismatch_forces_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) :
    idMapMismatch ->
    AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap := by
  intro mismatch
  exact ay_uewa_disj_right missingWitness
    (AyUEWADisj digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))))
    (ay_uewa_disj_right digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))))
      (ay_uewa_disj_left idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))
        mismatch))

theorem ay_uewa_parent_coverage_gap_forces_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) :
    parentCoverageGap ->
    AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap := by
  intro gap
  exact ay_uewa_disj_right missingWitness
    (AyUEWADisj digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))))
    (ay_uewa_disj_right digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))))
      (ay_uewa_disj_right idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))
        (ay_uewa_disj_left parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))
          gap)))

theorem ay_uewa_stale_fingerprint_forces_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) :
    staleFingerprint ->
    AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap := by
  intro stale
  exact ay_uewa_disj_right missingWitness
    (AyUEWADisj digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))))
    (ay_uewa_disj_right digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))))
      (ay_uewa_disj_right idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))
        (ay_uewa_disj_right parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))
          (ay_uewa_disj_left staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))
            stale))))

theorem ay_uewa_unchecked_transcript_forces_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) :
    uncheckedTranscript ->
    AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap := by
  intro unchecked
  exact ay_uewa_disj_right missingWitness
    (AyUEWADisj digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))))
    (ay_uewa_disj_right digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))))
      (ay_uewa_disj_right idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))
        (ay_uewa_disj_right parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))
          (ay_uewa_disj_right staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))
            (ay_uewa_disj_left uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))
              unchecked)))))

theorem ay_uewa_build_drift_forces_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) :
    buildDrift ->
    AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap := by
  intro drift
  exact ay_uewa_disj_right missingWitness
    (AyUEWADisj digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))))
    (ay_uewa_disj_right digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))))
      (ay_uewa_disj_right idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))
        (ay_uewa_disj_right parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))
          (ay_uewa_disj_right staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))
            (ay_uewa_disj_right uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))
              (ay_uewa_disj_left buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)
                drift))))))

theorem ay_uewa_archive_mismatch_forces_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) :
    archiveMismatch ->
    AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap := by
  intro mismatch
  exact ay_uewa_disj_right missingWitness
    (AyUEWADisj digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))))
    (ay_uewa_disj_right digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))))
      (ay_uewa_disj_right idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))
        (ay_uewa_disj_right parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))
          (ay_uewa_disj_right staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))
            (ay_uewa_disj_right uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))
              (ay_uewa_disj_right buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)
                (ay_uewa_disj_left archiveMismatch reconstructionGap
                  mismatch)))))))

theorem ay_uewa_reconstruction_gap_forces_no_claim
    (missingWitness : Prop) (digestDrift : Prop)
    (idMapMismatch : Prop) (parentCoverageGap : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (buildDrift : Prop) (archiveMismatch : Prop)
    (reconstructionGap : Prop) :
    reconstructionGap ->
    AyUEWAFailureReason missingWitness digestDrift idMapMismatch
      parentCoverageGap staleFingerprint uncheckedTranscript buildDrift
      archiveMismatch reconstructionGap := by
  intro gap
  exact ay_uewa_disj_right missingWitness
    (AyUEWADisj digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))))
    (ay_uewa_disj_right digestDrift
      (AyUEWADisj idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))))
      (ay_uewa_disj_right idMapMismatch
        (AyUEWADisj parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))))
        (ay_uewa_disj_right parentCoverageGap
          (AyUEWADisj staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))))
          (ay_uewa_disj_right staleFingerprint
            (AyUEWADisj uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)))
            (ay_uewa_disj_right uncheckedTranscript
              (AyUEWADisj buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap))
              (ay_uewa_disj_right buildDrift
                (AyUEWADisj archiveMismatch reconstructionGap)
                (ay_uewa_disj_right archiveMismatch reconstructionGap
                  gap)))))))
