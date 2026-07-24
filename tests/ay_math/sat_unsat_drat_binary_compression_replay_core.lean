-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded binary-compressed DRAT/LRAT replay soundness for ay sequential-main
-- SAT-COMP validation. Propositions stand for compression manifests,
-- decompressor build digests, proof artifact digests, clause-ID maps, parent
-- coverage, checker transcripts, empty-clause reachability, formula
-- fingerprints, reconstruction evidence, archive manifests, and fail-closed
-- no-claim/recompute diagnostics.

def AyUDBCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUDBCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUDBCMap (source : Prop) (target : Prop) :=
  source -> target

def AyUDBCCompressionReplay
    (compressionManifest : Prop) (decompressorBuildDigest : Prop)
    (proofArtifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :=
  AyUDBCConj compressionManifest
    (AyUDBCConj
      (AyUDBCMap compressionManifest decompressorBuildDigest)
      (AyUDBCConj
        (AyUDBCMap decompressorBuildDigest proofArtifactDigest)
        (AyUDBCConj
          (AyUDBCMap proofArtifactDigest archiveManifest)
          (AyUDBCMap archiveManifest checkerTranscript))))

def AyUDBCClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyUDBCConj
    (AyUDBCMap checkerTranscript clauseIdMap)
    (AyUDBCMap clauseIdMap mappedTranscript)

def AyUDBCParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyUDBCConj
    (AyUDBCMap mappedTranscript parentCoverage)
    (AyUDBCMap parentCoverage emptyClauseReachable)

def AyUDBCFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUDBCConj
    (AyUDBCMap mappedTranscript formulaFingerprint)
    (AyUDBCMap formulaFingerprint fingerprintAccepted)

def AyUDBCTranscript
    (checkerTranscript : Prop) (transcriptAccepted : Prop) :=
  AyUDBCMap checkerTranscript transcriptAccepted

def AyUDBCReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUDBCConj reconstructionEvidence
    (AyUDBCConj
      (AyUDBCMap emptyClauseReachable visibleUnsat)
      (AyUDBCMap visibleUnsat originalUnsat))

def AyUDBCAcceptedEvidence
    (compressionManifest : Prop) (decompressorBuildDigest : Prop)
    (proofArtifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUDBCConj
    (AyUDBCCompressionReplay compressionManifest decompressorBuildDigest
      proofArtifactDigest archiveManifest checkerTranscript)
    (AyUDBCConj
      (AyUDBCTranscript checkerTranscript transcriptAccepted)
      (AyUDBCConj
        (AyUDBCClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyUDBCConj
          (AyUDBCParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyUDBCConj
            (AyUDBCFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyUDBCReconstruction emptyClauseReachable
              reconstructionEvidence visibleUnsat originalUnsat)))))

def AyUDBCAcceptedPublication
    (compressionManifest : Prop) (decompressorBuildDigest : Prop)
    (proofArtifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUDBCConj
    (AyUDBCAcceptedEvidence compressionManifest decompressorBuildDigest
      proofArtifactDigest archiveManifest checkerTranscript transcriptAccepted
      clauseIdMap mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    originalUnsat

def AyUDBCFailureReason
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :=
  AyUDBCDisj compressionFailure
    (AyUDBCDisj decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))))

def AyUDBCBadReplay
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUDBCConj
    (AyUDBCConj noClaim recompute)
    (AyUDBCFailureReason compressionFailure decompressorFailure
      digestFailure mapFailure parentFailure checkerFailure
      emptyClauseFailure fingerprintFailure reconstructionFailure
      archiveFailure)

def AyUDBCPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUDBCDisj noClaim originalUnsat

theorem ay_udbc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUDBCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_udbc_conj_left
    (p : Prop) (q : Prop) :
    AyUDBCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_udbc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUDBCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_udbc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUDBCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_udbc_compression_manifest
    (compressionManifest : Prop) (decompressorBuildDigest : Prop)
    (proofArtifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyUDBCCompressionReplay compressionManifest decompressorBuildDigest
      proofArtifactDigest archiveManifest checkerTranscript ->
    compressionManifest := by
  intro replay
  exact ay_udbc_conj_left compressionManifest
    (AyUDBCConj
      (AyUDBCMap compressionManifest decompressorBuildDigest)
      (AyUDBCConj
        (AyUDBCMap decompressorBuildDigest proofArtifactDigest)
        (AyUDBCConj
          (AyUDBCMap proofArtifactDigest archiveManifest)
          (AyUDBCMap archiveManifest checkerTranscript))))
    replay

theorem ay_udbc_decompressor_build_digest
    (compressionManifest : Prop) (decompressorBuildDigest : Prop)
    (proofArtifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyUDBCCompressionReplay compressionManifest decompressorBuildDigest
      proofArtifactDigest archiveManifest checkerTranscript ->
    decompressorBuildDigest := by
  intro replay
  exact replay decompressorBuildDigest
    (fun manifest tail =>
      tail decompressorBuildDigest
        (fun manifest_to_build _rest => manifest_to_build manifest))

theorem ay_udbc_proof_artifact_digest
    (compressionManifest : Prop) (decompressorBuildDigest : Prop)
    (proofArtifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyUDBCCompressionReplay compressionManifest decompressorBuildDigest
      proofArtifactDigest archiveManifest checkerTranscript ->
    proofArtifactDigest := by
  intro replay
  exact replay proofArtifactDigest
    (fun manifest tail =>
      tail proofArtifactDigest
        (fun manifest_to_build rest =>
          rest proofArtifactDigest
            (fun build_to_digest _rest2 =>
              build_to_digest (manifest_to_build manifest))))

theorem ay_udbc_archive_manifest
    (compressionManifest : Prop) (decompressorBuildDigest : Prop)
    (proofArtifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyUDBCCompressionReplay compressionManifest decompressorBuildDigest
      proofArtifactDigest archiveManifest checkerTranscript ->
    archiveManifest := by
  intro replay
  exact replay archiveManifest
    (fun manifest tail =>
      tail archiveManifest
        (fun manifest_to_build rest =>
          rest archiveManifest
            (fun build_to_digest rest2 =>
              rest2 archiveManifest
                (fun digest_to_archive _archive_to_transcript =>
                  digest_to_archive
                    (build_to_digest (manifest_to_build manifest))))))

theorem ay_udbc_checker_transcript
    (compressionManifest : Prop) (decompressorBuildDigest : Prop)
    (proofArtifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyUDBCCompressionReplay compressionManifest decompressorBuildDigest
      proofArtifactDigest archiveManifest checkerTranscript ->
    checkerTranscript := by
  intro replay
  exact replay checkerTranscript
    (fun manifest tail =>
      tail checkerTranscript
        (fun manifest_to_build rest =>
          rest checkerTranscript
            (fun build_to_digest rest2 =>
              rest2 checkerTranscript
                (fun digest_to_archive archive_to_transcript =>
                  archive_to_transcript
                    (digest_to_archive
                      (build_to_digest (manifest_to_build manifest)))))))

theorem ay_udbc_transcript_accepted
    (checkerTranscript : Prop) (transcriptAccepted : Prop) :
    AyUDBCTranscript checkerTranscript transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro accepted
  exact accepted

theorem ay_udbc_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUDBCClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_id_map _id_map_to_mapped => transcript_to_id_map)

theorem ay_udbc_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUDBCClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_id_map id_map_to_mapped => id_map_to_mapped)

theorem ay_udbc_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUDBCParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_udbc_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUDBCParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_udbc_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUDBCFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_udbc_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUDBCFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_udbc_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDBCReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_udbc_conj_left reconstructionEvidence
    (AyUDBCConj
      (AyUDBCMap emptyClauseReachable visibleUnsat)
      (AyUDBCMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_udbc_visible_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDBCReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_udbc_original_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDBCReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_udbc_accepted_evidence
    (compressionManifest : Prop) (decompressorBuildDigest : Prop)
    (proofArtifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDBCAcceptedPublication compressionManifest decompressorBuildDigest
      proofArtifactDigest archiveManifest checkerTranscript
      transcriptAccepted clauseIdMap mappedTranscript parentCoverage
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    AyUDBCAcceptedEvidence compressionManifest decompressorBuildDigest
      proofArtifactDigest archiveManifest checkerTranscript transcriptAccepted
      clauseIdMap mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat := by
  intro accepted
  exact accepted
    (AyUDBCAcceptedEvidence compressionManifest decompressorBuildDigest
      proofArtifactDigest archiveManifest checkerTranscript
      transcriptAccepted clauseIdMap mappedTranscript parentCoverage
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      reconstructionEvidence visibleUnsat originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_udbc_publication_sound
    (compressionManifest : Prop) (decompressorBuildDigest : Prop)
    (proofArtifactDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDBCAcceptedPublication compressionManifest decompressorBuildDigest
      proofArtifactDigest archiveManifest checkerTranscript
      transcriptAccepted clauseIdMap mappedTranscript parentCoverage
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_udbc_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUDBCPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_udbc_disj_right noClaim originalUnsat unsat

theorem ay_udbc_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUDBCPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_udbc_disj_left noClaim originalUnsat no_claim

theorem ay_udbc_bad_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUDBCBadReplay compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_udbc_conj_left noClaim recompute fail_closed)

theorem ay_udbc_bad_recompute
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUDBCBadReplay compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_udbc_bad_public_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUDBCBadReplay compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure noClaim
      recompute ->
    AyUDBCPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_udbc_public_no_claim_report noClaim originalUnsat
    (ay_udbc_bad_no_claim compressionFailure decompressorFailure
      digestFailure mapFailure parentFailure checkerFailure
      emptyClauseFailure fingerprintFailure reconstructionFailure
      archiveFailure noClaim recompute bad)

theorem ay_udbc_bad_cannot_bless_unsat
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUDBCBadReplay compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure noClaim
      recompute ->
    noClaim := by
  intro bad
  exact ay_udbc_bad_no_claim compressionFailure decompressorFailure
    digestFailure mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure reconstructionFailure archiveFailure noClaim
    recompute bad

theorem ay_udbc_failure_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure ->
    noClaim ->
    recompute ->
    AyUDBCBadReplay compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure noClaim
      recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_udbc_conj_intro (AyUDBCConj noClaim recompute)
    (AyUDBCFailureReason compressionFailure decompressorFailure
      digestFailure mapFailure parentFailure checkerFailure
      emptyClauseFailure fingerprintFailure reconstructionFailure
      archiveFailure)
    (ay_udbc_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_udbc_compression_failure_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :
    compressionFailure ->
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure := by
  intro failure
  exact ay_udbc_disj_left compressionFailure
    (AyUDBCDisj decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))))
    failure

theorem ay_udbc_failure_tail_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :
    AyUDBCDisj decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))) ->
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure := by
  intro tail
  exact ay_udbc_disj_right compressionFailure
    (AyUDBCDisj decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))))
    tail

theorem ay_udbc_decompressor_failure_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :
    decompressorFailure ->
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure := by
  intro failure
  exact ay_udbc_failure_tail_forces_no_claim compressionFailure
    decompressorFailure digestFailure mapFailure parentFailure checkerFailure
    emptyClauseFailure fingerprintFailure reconstructionFailure archiveFailure
    (ay_udbc_disj_left decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))))
      failure)

theorem ay_udbc_digest_failure_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :
    digestFailure ->
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure := by
  intro failure
  exact ay_udbc_failure_tail_forces_no_claim compressionFailure
    decompressorFailure digestFailure mapFailure parentFailure checkerFailure
    emptyClauseFailure fingerprintFailure reconstructionFailure archiveFailure
    (ay_udbc_disj_right decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))))
      (ay_udbc_disj_left digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))
        failure))

theorem ay_udbc_map_failure_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :
    mapFailure ->
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure := by
  intro failure
  exact ay_udbc_failure_tail_forces_no_claim compressionFailure
    decompressorFailure digestFailure mapFailure parentFailure checkerFailure
    emptyClauseFailure fingerprintFailure reconstructionFailure archiveFailure
    (ay_udbc_disj_right decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))))
      (ay_udbc_disj_right digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))
        (ay_udbc_disj_left mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))
          failure)))

theorem ay_udbc_parent_failure_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :
    parentFailure ->
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure := by
  intro failure
  exact ay_udbc_failure_tail_forces_no_claim compressionFailure
    decompressorFailure digestFailure mapFailure parentFailure checkerFailure
    emptyClauseFailure fingerprintFailure reconstructionFailure archiveFailure
    (ay_udbc_disj_right decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))))
      (ay_udbc_disj_right digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))
        (ay_udbc_disj_right mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))
          (ay_udbc_disj_left parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))
            failure))))

theorem ay_udbc_checker_failure_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :
    checkerFailure ->
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure := by
  intro failure
  exact ay_udbc_failure_tail_forces_no_claim compressionFailure
    decompressorFailure digestFailure mapFailure parentFailure checkerFailure
    emptyClauseFailure fingerprintFailure reconstructionFailure archiveFailure
    (ay_udbc_disj_right decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))))
      (ay_udbc_disj_right digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))
        (ay_udbc_disj_right mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))
          (ay_udbc_disj_right parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))
            (ay_udbc_disj_left checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))
              failure)))))

theorem ay_udbc_empty_clause_failure_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :
    emptyClauseFailure ->
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure := by
  intro failure
  exact ay_udbc_failure_tail_forces_no_claim compressionFailure
    decompressorFailure digestFailure mapFailure parentFailure checkerFailure
    emptyClauseFailure fingerprintFailure reconstructionFailure archiveFailure
    (ay_udbc_disj_right decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))))
      (ay_udbc_disj_right digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))
        (ay_udbc_disj_right mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))
          (ay_udbc_disj_right parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))
            (ay_udbc_disj_right checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))
              (ay_udbc_disj_left emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))
                failure))))))

theorem ay_udbc_fingerprint_failure_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :
    fingerprintFailure ->
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure := by
  intro failure
  exact ay_udbc_failure_tail_forces_no_claim compressionFailure
    decompressorFailure digestFailure mapFailure parentFailure checkerFailure
    emptyClauseFailure fingerprintFailure reconstructionFailure archiveFailure
    (ay_udbc_disj_right decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))))
      (ay_udbc_disj_right digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))
        (ay_udbc_disj_right mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))
          (ay_udbc_disj_right parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))
            (ay_udbc_disj_right checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))
              (ay_udbc_disj_right emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))
                (ay_udbc_disj_left fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)
                  failure)))))))

theorem ay_udbc_reconstruction_failure_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :
    reconstructionFailure ->
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure := by
  intro failure
  exact ay_udbc_failure_tail_forces_no_claim compressionFailure
    decompressorFailure digestFailure mapFailure parentFailure checkerFailure
    emptyClauseFailure fingerprintFailure reconstructionFailure archiveFailure
    (ay_udbc_disj_right decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))))
      (ay_udbc_disj_right digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))
        (ay_udbc_disj_right mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))
          (ay_udbc_disj_right parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))
            (ay_udbc_disj_right checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))
              (ay_udbc_disj_right emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))
                (ay_udbc_disj_right fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)
                  (ay_udbc_disj_left reconstructionFailure archiveFailure
                    failure))))))))

theorem ay_udbc_archive_failure_forces_no_claim
    (compressionFailure : Prop) (decompressorFailure : Prop)
    (digestFailure : Prop) (mapFailure : Prop) (parentFailure : Prop)
    (checkerFailure : Prop) (emptyClauseFailure : Prop)
    (fingerprintFailure : Prop) (reconstructionFailure : Prop)
    (archiveFailure : Prop) :
    archiveFailure ->
    AyUDBCFailureReason compressionFailure decompressorFailure digestFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure archiveFailure := by
  intro failure
  exact ay_udbc_failure_tail_forces_no_claim compressionFailure
    decompressorFailure digestFailure mapFailure parentFailure checkerFailure
    emptyClauseFailure fingerprintFailure reconstructionFailure archiveFailure
    (ay_udbc_disj_right decompressorFailure
      (AyUDBCDisj digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))))
      (ay_udbc_disj_right digestFailure
        (AyUDBCDisj mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))))
        (ay_udbc_disj_right mapFailure
          (AyUDBCDisj parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))))
          (ay_udbc_disj_right parentFailure
            (AyUDBCDisj checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))))
            (ay_udbc_disj_right checkerFailure
              (AyUDBCDisj emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)))
              (ay_udbc_disj_right emptyClauseFailure
                (AyUDBCDisj fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure))
                (ay_udbc_disj_right fingerprintFailure
                  (AyUDBCDisj reconstructionFailure archiveFailure)
                  (ay_udbc_disj_right reconstructionFailure archiveFailure
                    failure))))))))
