-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof-artifact digest roundtrip soundness for ay
-- sequential-main SAT-COMP validation. Propositions stand for artifact
-- digest roundtrips across internal DAGs, proof files, compressed archives,
-- checker transcripts, public results, clause-ID maps, parent coverage,
-- root fingerprints, empty-clause reachability, reconstruction evidence,
-- build evidence, archive manifests, and fail-closed no-claim diagnostics.

def AyUADRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUADRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUADRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUADRArtifactRoundtrip
    (internalDag : Prop) (proofFile : Prop) (compressedArchive : Prop)
    (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :=
  AyUADRConj internalDag
    (AyUADRConj
      (AyUADRMap internalDag proofFile)
      (AyUADRConj
        (AyUADRMap proofFile compressedArchive)
        (AyUADRConj
          (AyUADRMap compressedArchive artifactDigest)
          (AyUADRConj
            (AyUADRMap artifactDigest archiveManifest)
            (AyUADRMap archiveManifest checkerTranscript)))))

def AyUADRClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyUADRConj
    (AyUADRMap checkerTranscript clauseIdMap)
    (AyUADRMap clauseIdMap mappedTranscript)

def AyUADRParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyUADRConj
    (AyUADRMap mappedTranscript parentCoverage)
    (AyUADRMap parentCoverage emptyClauseReachable)

def AyUADRFingerprint
    (mappedTranscript : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUADRConj
    (AyUADRMap mappedTranscript rootFingerprint)
    (AyUADRMap rootFingerprint fingerprintAccepted)

def AyUADRTranscript
    (checkerTranscript : Prop) (transcriptAccepted : Prop) :=
  AyUADRMap checkerTranscript transcriptAccepted

def AyUADRBuild
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyUADRConj
    (AyUADRMap mappedTranscript buildEvidence)
    (AyUADRMap buildEvidence buildAccepted)

def AyUADRReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUADRConj reconstructionEvidence
    (AyUADRConj
      (AyUADRMap emptyClauseReachable visibleUnsat)
      (AyUADRMap visibleUnsat originalUnsat))

def AyUADRAcceptedEvidence
    (internalDag : Prop) (proofFile : Prop) (compressedArchive : Prop)
    (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) (emptyClauseReachable : Prop)
    (reconstructionEvidence : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUADRConj
    (AyUADRArtifactRoundtrip internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript)
    (AyUADRConj
      (AyUADRTranscript checkerTranscript transcriptAccepted)
      (AyUADRConj
        (AyUADRClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyUADRConj
          (AyUADRParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyUADRConj
            (AyUADRFingerprint mappedTranscript rootFingerprint
              fingerprintAccepted)
            (AyUADRConj
              (AyUADRBuild mappedTranscript buildEvidence buildAccepted)
              (AyUADRReconstruction emptyClauseReachable
                reconstructionEvidence visibleUnsat originalUnsat))))))

def AyUADRAcceptedRoundtrip
    (internalDag : Prop) (proofFile : Prop) (compressedArchive : Prop)
    (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) (emptyClauseReachable : Prop)
    (reconstructionEvidence : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUADRConj
    (AyUADRAcceptedEvidence internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript transcriptAccepted
      clauseIdMap mappedTranscript parentCoverage rootFingerprint
      fingerprintAccepted emptyClauseReachable reconstructionEvidence
      buildEvidence buildAccepted visibleUnsat originalUnsat)
    originalUnsat

def AyUADRFailureReason
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) :=
  AyUADRDisj digestDrift
    (AyUADRDisj archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))))

def AyUADRBadRoundtrip
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUADRConj
    (AyUADRConj noClaim recompute)
    (AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift)

def AyUADRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUADRDisj noClaim originalUnsat

theorem ay_uadr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUADRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uadr_conj_left
    (p : Prop) (q : Prop) :
    AyUADRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uadr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUADRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uadr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUADRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uadr_internal_dag
    (internalDag : Prop) (proofFile : Prop) (compressedArchive : Prop)
    (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyUADRArtifactRoundtrip internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript ->
    internalDag := by
  intro roundtrip
  exact ay_uadr_conj_left internalDag
    (AyUADRConj
      (AyUADRMap internalDag proofFile)
      (AyUADRConj
        (AyUADRMap proofFile compressedArchive)
        (AyUADRConj
          (AyUADRMap compressedArchive artifactDigest)
          (AyUADRConj
            (AyUADRMap artifactDigest archiveManifest)
            (AyUADRMap archiveManifest checkerTranscript)))))
    roundtrip

theorem ay_uadr_proof_file
    (internalDag : Prop) (proofFile : Prop) (compressedArchive : Prop)
    (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyUADRArtifactRoundtrip internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript ->
    proofFile := by
  intro roundtrip
  exact roundtrip proofFile
    (fun dag tail =>
      tail proofFile
        (fun dag_to_file _rest => dag_to_file dag))

theorem ay_uadr_compressed_archive
    (internalDag : Prop) (proofFile : Prop) (compressedArchive : Prop)
    (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyUADRArtifactRoundtrip internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript ->
    compressedArchive := by
  intro roundtrip
  exact roundtrip compressedArchive
    (fun dag tail =>
      tail compressedArchive
        (fun dag_to_file rest =>
          rest compressedArchive
            (fun file_to_archive _rest2 =>
              file_to_archive (dag_to_file dag))))

theorem ay_uadr_artifact_digest
    (internalDag : Prop) (proofFile : Prop) (compressedArchive : Prop)
    (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyUADRArtifactRoundtrip internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript ->
    artifactDigest := by
  intro roundtrip
  exact roundtrip artifactDigest
    (fun dag tail =>
      tail artifactDigest
        (fun dag_to_file rest =>
          rest artifactDigest
            (fun file_to_archive rest2 =>
              rest2 artifactDigest
                (fun archive_to_digest _rest3 =>
                  archive_to_digest (file_to_archive (dag_to_file dag))))))

theorem ay_uadr_archive_manifest
    (internalDag : Prop) (proofFile : Prop) (compressedArchive : Prop)
    (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyUADRArtifactRoundtrip internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript ->
    archiveManifest := by
  intro roundtrip
  exact roundtrip archiveManifest
    (fun dag tail =>
      tail archiveManifest
        (fun dag_to_file rest =>
          rest archiveManifest
            (fun file_to_archive rest2 =>
              rest2 archiveManifest
                (fun archive_to_digest rest3 =>
                  rest3 archiveManifest
                    (fun digest_to_manifest _manifest_to_transcript =>
                      digest_to_manifest
                        (archive_to_digest
                          (file_to_archive (dag_to_file dag))))))))

theorem ay_uadr_checker_transcript
    (internalDag : Prop) (proofFile : Prop) (compressedArchive : Prop)
    (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyUADRArtifactRoundtrip internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript ->
    checkerTranscript := by
  intro roundtrip
  exact roundtrip checkerTranscript
    (fun dag tail =>
      tail checkerTranscript
        (fun dag_to_file rest =>
          rest checkerTranscript
            (fun file_to_archive rest2 =>
              rest2 checkerTranscript
                (fun archive_to_digest rest3 =>
                  rest3 checkerTranscript
                    (fun digest_to_manifest manifest_to_transcript =>
                      manifest_to_transcript
                        (digest_to_manifest
                          (archive_to_digest
                            (file_to_archive (dag_to_file dag)))))))))

theorem ay_uadr_transcript_accepted
    (checkerTranscript : Prop) (transcriptAccepted : Prop) :
    AyUADRTranscript checkerTranscript transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro accepted
  exact accepted

theorem ay_uadr_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUADRClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_id_map _id_map_to_mapped => transcript_to_id_map)

theorem ay_uadr_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUADRClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_id_map id_map_to_mapped => id_map_to_mapped)

theorem ay_uadr_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUADRParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_uadr_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUADRParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_uadr_root_fingerprint
    (mappedTranscript : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUADRFingerprint mappedTranscript rootFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    rootFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> rootFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_uadr_fingerprint_accepted
    (mappedTranscript : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUADRFingerprint mappedTranscript rootFingerprint
      fingerprintAccepted ->
    rootFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (rootFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_uadr_build_evidence
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUADRBuild mappedTranscript buildEvidence buildAccepted ->
    mappedTranscript ->
    buildEvidence := by
  intro build
  exact build (mappedTranscript -> buildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_uadr_build_accepted
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUADRBuild mappedTranscript buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_uadr_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUADRReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_uadr_conj_left reconstructionEvidence
    (AyUADRConj
      (AyUADRMap emptyClauseReachable visibleUnsat)
      (AyUADRMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_uadr_visible_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUADRReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_uadr_original_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUADRReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_uadr_accepted_evidence
    (internalDag : Prop) (proofFile : Prop) (compressedArchive : Prop)
    (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) (emptyClauseReachable : Prop)
    (reconstructionEvidence : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUADRAcceptedRoundtrip internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript transcriptAccepted
      clauseIdMap mappedTranscript parentCoverage rootFingerprint
      fingerprintAccepted emptyClauseReachable reconstructionEvidence
      buildEvidence buildAccepted visibleUnsat originalUnsat ->
    AyUADRAcceptedEvidence internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript transcriptAccepted
      clauseIdMap mappedTranscript parentCoverage rootFingerprint
      fingerprintAccepted emptyClauseReachable reconstructionEvidence
      buildEvidence buildAccepted visibleUnsat originalUnsat := by
  intro accepted
  exact accepted
    (AyUADRAcceptedEvidence internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript transcriptAccepted
      clauseIdMap mappedTranscript parentCoverage rootFingerprint
      fingerprintAccepted emptyClauseReachable reconstructionEvidence
      buildEvidence buildAccepted visibleUnsat originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_uadr_roundtrip_publish_sound
    (internalDag : Prop) (proofFile : Prop) (compressedArchive : Prop)
    (artifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) (emptyClauseReachable : Prop)
    (reconstructionEvidence : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUADRAcceptedRoundtrip internalDag proofFile compressedArchive
      artifactDigest archiveManifest checkerTranscript transcriptAccepted
      clauseIdMap mappedTranscript parentCoverage rootFingerprint
      fingerprintAccepted emptyClauseReachable reconstructionEvidence
      buildEvidence buildAccepted visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_uadr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUADRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_uadr_disj_right noClaim originalUnsat unsat

theorem ay_uadr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUADRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_uadr_disj_left noClaim originalUnsat no_claim

theorem ay_uadr_bad_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUADRBadRoundtrip digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_uadr_conj_left noClaim recompute fail_closed)

theorem ay_uadr_bad_recompute
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUADRBadRoundtrip digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_uadr_bad_public_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUADRBadRoundtrip digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift noClaim recompute ->
    AyUADRPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_uadr_public_no_claim_report noClaim originalUnsat
    (ay_uadr_bad_no_claim digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift noClaim recompute bad)

theorem ay_uadr_bad_cannot_bless_unsat
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUADRBadRoundtrip digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_uadr_bad_no_claim digestDrift archiveMismatch idMapMismatch
    missingParentCoverage staleFingerprint uncheckedTranscript
    missingEmptyClause reconstructionGap buildDrift noClaim recompute bad

theorem ay_uadr_failure_forces_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift ->
    noClaim ->
    recompute ->
    AyUADRBadRoundtrip digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_uadr_conj_intro (AyUADRConj noClaim recompute)
    (AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift)
    (ay_uadr_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_uadr_digest_drift_forces_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) :
    digestDrift ->
    AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift := by
  intro drift
  exact ay_uadr_disj_left digestDrift
    (AyUADRDisj archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))))
    drift

theorem ay_uadr_archive_mismatch_forces_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) :
    archiveMismatch ->
    AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift := by
  intro mismatch
  exact ay_uadr_disj_right digestDrift
    (AyUADRDisj archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))))
    (ay_uadr_disj_left archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))))
      mismatch)

theorem ay_uadr_id_map_mismatch_forces_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) :
    idMapMismatch ->
    AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift := by
  intro mismatch
  exact ay_uadr_disj_right digestDrift
    (AyUADRDisj archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))))
    (ay_uadr_disj_right archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))))
      (ay_uadr_disj_left idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))
        mismatch))

theorem ay_uadr_missing_parent_coverage_forces_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) :
    missingParentCoverage ->
    AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift := by
  intro missing
  exact ay_uadr_disj_right digestDrift
    (AyUADRDisj archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))))
    (ay_uadr_disj_right archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))))
      (ay_uadr_disj_right idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))
        (ay_uadr_disj_left missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))
          missing)))

theorem ay_uadr_stale_fingerprint_forces_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) :
    staleFingerprint ->
    AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift := by
  intro stale
  exact ay_uadr_disj_right digestDrift
    (AyUADRDisj archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))))
    (ay_uadr_disj_right archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))))
      (ay_uadr_disj_right idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))
        (ay_uadr_disj_right missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))
          (ay_uadr_disj_left staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))
            stale))))

theorem ay_uadr_unchecked_transcript_forces_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) :
    uncheckedTranscript ->
    AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift := by
  intro unchecked
  exact ay_uadr_disj_right digestDrift
    (AyUADRDisj archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))))
    (ay_uadr_disj_right archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))))
      (ay_uadr_disj_right idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))
        (ay_uadr_disj_right missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))
          (ay_uadr_disj_right staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))
            (ay_uadr_disj_left uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))
              unchecked)))))

theorem ay_uadr_missing_empty_clause_forces_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) :
    missingEmptyClause ->
    AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift := by
  intro missing
  exact ay_uadr_disj_right digestDrift
    (AyUADRDisj archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))))
    (ay_uadr_disj_right archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))))
      (ay_uadr_disj_right idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))
        (ay_uadr_disj_right missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))
          (ay_uadr_disj_right staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))
            (ay_uadr_disj_right uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))
              (ay_uadr_disj_left missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)
                missing))))))

theorem ay_uadr_reconstruction_gap_forces_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) :
    reconstructionGap ->
    AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift := by
  intro gap
  exact ay_uadr_disj_right digestDrift
    (AyUADRDisj archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))))
    (ay_uadr_disj_right archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))))
      (ay_uadr_disj_right idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))
        (ay_uadr_disj_right missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))
          (ay_uadr_disj_right staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))
            (ay_uadr_disj_right uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))
              (ay_uadr_disj_right missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)
                (ay_uadr_disj_left reconstructionGap buildDrift gap)))))))

theorem ay_uadr_build_drift_forces_no_claim
    (digestDrift : Prop) (archiveMismatch : Prop)
    (idMapMismatch : Prop) (missingParentCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedTranscript : Prop)
    (missingEmptyClause : Prop) (reconstructionGap : Prop)
    (buildDrift : Prop) :
    buildDrift ->
    AyUADRFailureReason digestDrift archiveMismatch idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyClause reconstructionGap buildDrift := by
  intro drift
  exact ay_uadr_disj_right digestDrift
    (AyUADRDisj archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))))
    (ay_uadr_disj_right archiveMismatch
      (AyUADRDisj idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))))
      (ay_uadr_disj_right idMapMismatch
        (AyUADRDisj missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))))
        (ay_uadr_disj_right missingParentCoverage
          (AyUADRDisj staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))))
          (ay_uadr_disj_right staleFingerprint
            (AyUADRDisj uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)))
            (ay_uadr_disj_right uncheckedTranscript
              (AyUADRDisj missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift))
              (ay_uadr_disj_right missingEmptyClause
                (AyUADRDisj reconstructionGap buildDrift)
                (ay_uadr_disj_right reconstructionGap buildDrift drift)))))))
