-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT resolution-chain compression soundness for ay.
-- Propositions stand for compression maps, representative clauses, parent
-- coverage, deletion/retention lineage, replay epochs, digest membership,
-- checker transcripts, reconstruction handles, original fingerprints, and
-- fail-closed no-claim/recompute diagnostics.

def AyURCCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyURCCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyURCCMap (source : Prop) (target : Prop) :=
  source -> target

def AyURCCCompressionMap
    (compressionMap : Prop) (representativeClauses : Prop)
    (compressedChain : Prop) :=
  AyURCCConj compressionMap
    (AyURCCConj
      (AyURCCMap compressionMap representativeClauses)
      (AyURCCMap representativeClauses compressedChain))

def AyURCCParentCoverage
    (compressedChain : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :=
  AyURCCConj
    (AyURCCMap compressedChain parentCoverage)
    (AyURCCMap parentCoverage emptyClause)

def AyURCCLineage
    (compressedChain : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) :=
  AyURCCConj
    (AyURCCMap compressedChain retentionLineage)
    (AyURCCMap retentionLineage lineageAccepted)

def AyURCCEpoch
    (compressedChain : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) :=
  AyURCCConj
    (AyURCCMap compressedChain replayEpoch)
    (AyURCCMap replayEpoch epochAccepted)

def AyURCCDigest
    (compressedChain : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :=
  AyURCCConj
    (AyURCCMap compressedChain digestMember)
    (AyURCCMap digestMember digestAccepted)

def AyURCCReplay
    (compressedChain : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) :=
  AyURCCConj
    (AyURCCMap compressedChain checkerTranscript)
    (AyURCCMap checkerTranscript replayAccepted)

def AyURCCReconstruction
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyURCCConj reconstructionHandle
    (AyURCCConj
      (AyURCCMap emptyClause visibleUnsat)
      (AyURCCMap visibleUnsat originalUnsat))

def AyURCCFingerprint
    (compressedChain : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyURCCConj
    (AyURCCMap compressedChain fingerprintAgrees)
    (AyURCCMap fingerprintAgrees visibleUnsat)

def AyURCCAcceptedEvidence
    (compressionMap : Prop) (representativeClauses : Prop)
    (compressedChain : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (reconstructionHandle : Prop)
    (fingerprintAgrees : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyURCCConj
    (AyURCCCompressionMap compressionMap representativeClauses
      compressedChain)
    (AyURCCConj
      (AyURCCParentCoverage compressedChain parentCoverage emptyClause)
      (AyURCCConj
        (AyURCCLineage compressedChain retentionLineage lineageAccepted)
        (AyURCCConj
          (AyURCCEpoch compressedChain replayEpoch epochAccepted)
          (AyURCCConj
            (AyURCCDigest compressedChain digestMember digestAccepted)
            (AyURCCConj
              (AyURCCReplay compressedChain checkerTranscript
                replayAccepted)
              (AyURCCConj
                (AyURCCReconstruction emptyClause reconstructionHandle
                  visibleUnsat originalUnsat)
                (AyURCCFingerprint compressedChain fingerprintAgrees
                  visibleUnsat)))))))

def AyURCCAcceptedCompression
    (compressionMap : Prop) (representativeClauses : Prop)
    (compressedChain : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (reconstructionHandle : Prop)
    (fingerprintAgrees : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyURCCConj
    (AyURCCAcceptedEvidence compressionMap representativeClauses
      compressedChain parentCoverage emptyClause retentionLineage
      lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
      checkerTranscript replayAccepted reconstructionHandle
      fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat

def AyURCCBadCompression
    (missingRepresentative : Prop) (parentCoverageGap : Prop)
    (unretainedDeletion : Prop) (compressionMapDrift : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyURCCConj
    (AyURCCConj noClaim recompute)
    (AyURCCDisj missingRepresentative
      (AyURCCDisj parentCoverageGap
        (AyURCCDisj unretainedDeletion
          (AyURCCDisj compressionMapDrift
            (AyURCCDisj epochDrift
              (AyURCCDisj digestMismatch
                (AyURCCDisj replayRejected fingerprintDrift)))))))

def AyURCCPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyURCCDisj noClaim originalUnsat

theorem ay_urcc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyURCCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_urcc_conj_left
    (p : Prop) (q : Prop) :
    AyURCCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_urcc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyURCCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_urcc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyURCCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_urcc_compression_map
    (compressionMap : Prop) (representativeClauses : Prop)
    (compressedChain : Prop) :
    AyURCCCompressionMap compressionMap representativeClauses
      compressedChain ->
    compressionMap := by
  intro compression
  exact ay_urcc_conj_left compressionMap
    (AyURCCConj
      (AyURCCMap compressionMap representativeClauses)
      (AyURCCMap representativeClauses compressedChain))
    compression

theorem ay_urcc_representative_clauses
    (compressionMap : Prop) (representativeClauses : Prop)
    (compressedChain : Prop) :
    AyURCCCompressionMap compressionMap representativeClauses
      compressedChain ->
    representativeClauses := by
  intro compression
  exact compression representativeClauses
    (fun map tail =>
      tail representativeClauses
        (fun map_to_representative _representative_to_chain =>
          map_to_representative map))

theorem ay_urcc_compressed_chain
    (compressionMap : Prop) (representativeClauses : Prop)
    (compressedChain : Prop) :
    AyURCCCompressionMap compressionMap representativeClauses
      compressedChain ->
    compressedChain := by
  intro compression
  exact compression compressedChain
    (fun map tail =>
      tail compressedChain
        (fun map_to_representative representative_to_chain =>
          representative_to_chain (map_to_representative map)))

theorem ay_urcc_parent_coverage
    (compressedChain : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyURCCParentCoverage compressedChain parentCoverage emptyClause ->
    compressedChain ->
    parentCoverage := by
  intro coverage
  exact coverage (compressedChain -> parentCoverage)
    (fun chain_to_parents _parents_to_empty => chain_to_parents)

theorem ay_urcc_empty_clause
    (compressedChain : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyURCCParentCoverage compressedChain parentCoverage emptyClause ->
    parentCoverage ->
    emptyClause := by
  intro coverage
  exact coverage (parentCoverage -> emptyClause)
    (fun _chain_to_parents parents_to_empty => parents_to_empty)

theorem ay_urcc_retention_lineage
    (compressedChain : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) :
    AyURCCLineage compressedChain retentionLineage lineageAccepted ->
    compressedChain ->
    retentionLineage := by
  intro lineage
  exact lineage (compressedChain -> retentionLineage)
    (fun chain_to_lineage _lineage_to_accept => chain_to_lineage)

theorem ay_urcc_lineage_accepted
    (compressedChain : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) :
    AyURCCLineage compressedChain retentionLineage lineageAccepted ->
    retentionLineage ->
    lineageAccepted := by
  intro lineage
  exact lineage (retentionLineage -> lineageAccepted)
    (fun _chain_to_lineage lineage_to_accept => lineage_to_accept)

theorem ay_urcc_replay_epoch
    (compressedChain : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) :
    AyURCCEpoch compressedChain replayEpoch epochAccepted ->
    compressedChain ->
    replayEpoch := by
  intro epoch
  exact epoch (compressedChain -> replayEpoch)
    (fun chain_to_epoch _epoch_to_accept => chain_to_epoch)

theorem ay_urcc_epoch_accepted
    (compressedChain : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) :
    AyURCCEpoch compressedChain replayEpoch epochAccepted ->
    replayEpoch ->
    epochAccepted := by
  intro epoch
  exact epoch (replayEpoch -> epochAccepted)
    (fun _chain_to_epoch epoch_to_accept => epoch_to_accept)

theorem ay_urcc_digest_member
    (compressedChain : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyURCCDigest compressedChain digestMember digestAccepted ->
    compressedChain ->
    digestMember := by
  intro digest
  exact digest (compressedChain -> digestMember)
    (fun chain_to_digest _digest_to_accept => chain_to_digest)

theorem ay_urcc_digest_accepted
    (compressedChain : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyURCCDigest compressedChain digestMember digestAccepted ->
    digestMember ->
    digestAccepted := by
  intro digest
  exact digest (digestMember -> digestAccepted)
    (fun _chain_to_digest digest_to_accept => digest_to_accept)

theorem ay_urcc_checker_transcript
    (compressedChain : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) :
    AyURCCReplay compressedChain checkerTranscript replayAccepted ->
    compressedChain ->
    checkerTranscript := by
  intro replay
  exact replay (compressedChain -> checkerTranscript)
    (fun chain_to_transcript _transcript_to_accept => chain_to_transcript)

theorem ay_urcc_replay_accepted
    (compressedChain : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) :
    AyURCCReplay compressedChain checkerTranscript replayAccepted ->
    checkerTranscript ->
    replayAccepted := by
  intro replay
  exact replay (checkerTranscript -> replayAccepted)
    (fun _chain_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_urcc_reconstruction_handle
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCCReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    reconstructionHandle := by
  intro reconstruction
  exact ay_urcc_conj_left reconstructionHandle
    (AyURCCConj
      (AyURCCMap emptyClause visibleUnsat)
      (AyURCCMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_urcc_visible_unsat_from_empty
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCCReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClause -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_urcc_original_unsat_from_visible
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCCReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original => visible_to_original))

theorem ay_urcc_fingerprint_agrees
    (compressedChain : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyURCCFingerprint compressedChain fingerprintAgrees visibleUnsat ->
    compressedChain ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (compressedChain -> fingerprintAgrees)
    (fun chain_to_fingerprint _fingerprint_to_visible =>
      chain_to_fingerprint)

theorem ay_urcc_visible_unsat_from_fingerprint
    (compressedChain : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyURCCFingerprint compressedChain fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _chain_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_urcc_accepted_evidence
    (compressionMap : Prop) (representativeClauses : Prop)
    (compressedChain : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (reconstructionHandle : Prop)
    (fingerprintAgrees : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyURCCAcceptedCompression compressionMap representativeClauses
      compressedChain parentCoverage emptyClause retentionLineage
      lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
      checkerTranscript replayAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat ->
    AyURCCAcceptedEvidence compressionMap representativeClauses
      compressedChain parentCoverage emptyClause retentionLineage
      lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
      checkerTranscript replayAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat := by
  intro accepted
  exact ay_urcc_conj_left
    (AyURCCAcceptedEvidence compressionMap representativeClauses
      compressedChain parentCoverage emptyClause retentionLineage
      lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
      checkerTranscript replayAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_urcc_accepted_original_unsat
    (compressionMap : Prop) (representativeClauses : Prop)
    (compressedChain : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (reconstructionHandle : Prop)
    (fingerprintAgrees : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyURCCAcceptedCompression compressionMap representativeClauses
      compressedChain parentCoverage emptyClause retentionLineage
      lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
      checkerTranscript replayAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_urcc_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyURCCPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_urcc_disj_right noClaim originalUnsat unsat

theorem ay_urcc_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyURCCPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_urcc_disj_left noClaim originalUnsat no_claim

theorem ay_urcc_accepted_compression_publish_sound
    (compressionMap : Prop) (representativeClauses : Prop)
    (compressedChain : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (reconstructionHandle : Prop)
    (fingerprintAgrees : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyURCCAcceptedCompression compressionMap representativeClauses
      compressedChain parentCoverage emptyClause retentionLineage
      lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
      checkerTranscript replayAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat ->
    AyURCCPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_urcc_public_unsat_report noClaim originalUnsat
    (ay_urcc_accepted_original_unsat compressionMap representativeClauses
      compressedChain parentCoverage emptyClause retentionLineage
      lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
      checkerTranscript replayAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat accepted)

theorem ay_urcc_bad_compression_no_claim
    (missingRepresentative : Prop) (parentCoverageGap : Prop)
    (unretainedDeletion : Prop) (compressionMapDrift : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyURCCBadCompression missingRepresentative parentCoverageGap
      unretainedDeletion compressionMapDrift epochDrift digestMismatch
      replayRejected fingerprintDrift noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_urcc_conj_left noClaim recompute fail_closed)

theorem ay_urcc_bad_compression_recompute
    (missingRepresentative : Prop) (parentCoverageGap : Prop)
    (unretainedDeletion : Prop) (compressionMapDrift : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyURCCBadCompression missingRepresentative parentCoverageGap
      unretainedDeletion compressionMapDrift epochDrift digestMismatch
      replayRejected fingerprintDrift noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_urcc_bad_compression_public_no_claim
    (missingRepresentative : Prop) (parentCoverageGap : Prop)
    (unretainedDeletion : Prop) (compressionMapDrift : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyURCCBadCompression missingRepresentative parentCoverageGap
      unretainedDeletion compressionMapDrift epochDrift digestMismatch
      replayRejected fingerprintDrift noClaim recompute ->
    AyURCCPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_urcc_public_no_claim_report noClaim originalUnsat
    (ay_urcc_bad_compression_no_claim missingRepresentative
      parentCoverageGap unretainedDeletion compressionMapDrift epochDrift
      digestMismatch replayRejected fingerprintDrift noClaim recompute bad)

theorem ay_urcc_bad_compression_cannot_publish
    (missingRepresentative : Prop) (parentCoverageGap : Prop)
    (unretainedDeletion : Prop) (compressionMapDrift : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyURCCBadCompression missingRepresentative parentCoverageGap
      unretainedDeletion compressionMapDrift epochDrift digestMismatch
      replayRejected fingerprintDrift noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_urcc_bad_compression_no_claim missingRepresentative
      parentCoverageGap unretainedDeletion compressionMapDrift epochDrift
      digestMismatch replayRejected fingerprintDrift noClaim recompute bad)
    unsat
