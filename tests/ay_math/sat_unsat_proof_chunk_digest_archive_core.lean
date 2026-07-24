-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded proof-chunk digest archive replay soundness for ay sequential-main
-- SAT-COMP UNSAT checking. Propositions stand for chunk boundary evidence,
-- parent coverage, step-map evidence, epoch/digest membership, checker
-- transcripts, reconstruction handles, original fingerprints, and fail-closed
-- no-claim/recompute diagnostics.

def AyUPDAConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPDADisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPDAMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPDAChunkBoundary
    (archivedChunk : Prop) (chunkBoundary : Prop)
    (chunkReplay : Prop) :=
  AyUPDAConj archivedChunk
    (AyUPDAConj
      (AyUPDAMap archivedChunk chunkBoundary)
      (AyUPDAMap chunkBoundary chunkReplay))

def AyUPDAParentCoverage
    (chunkReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :=
  AyUPDAConj
    (AyUPDAMap chunkReplay parentCoverage)
    (AyUPDAMap parentCoverage emptyClause)

def AyUPDAStepMap
    (chunkReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :=
  AyUPDAConj
    (AyUPDAMap chunkReplay stepMapEvidence)
    (AyUPDAMap stepMapEvidence stepMapAccepted)

def AyUPDAEpochDigest
    (chunkReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :=
  AyUPDAConj
    (AyUPDAMap chunkReplay epochMember)
    (AyUPDAConj
      (AyUPDAMap epochMember digestMember)
      (AyUPDAMap digestMember epochDigestAccepted))

def AyUPDACheckerTranscript
    (chunkReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :=
  AyUPDAConj
    (AyUPDAMap chunkReplay checkerTranscript)
    (AyUPDAMap checkerTranscript checkerAccepted)

def AyUPDAReconstruction
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPDAConj reconstructionHandle
    (AyUPDAConj
      (AyUPDAMap emptyClause visibleUnsat)
      (AyUPDAMap visibleUnsat originalUnsat))

def AyUPDAFingerprint
    (chunkReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUPDAConj
    (AyUPDAMap chunkReplay fingerprintAgrees)
    (AyUPDAMap fingerprintAgrees visibleUnsat)

def AyUPDAAcceptedEvidence
    (archivedChunk : Prop) (chunkBoundary : Prop)
    (chunkReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPDAConj
    (AyUPDAChunkBoundary archivedChunk chunkBoundary chunkReplay)
    (AyUPDAConj
      (AyUPDAParentCoverage chunkReplay parentCoverage emptyClause)
      (AyUPDAConj
        (AyUPDAStepMap chunkReplay stepMapEvidence stepMapAccepted)
        (AyUPDAConj
          (AyUPDAEpochDigest chunkReplay epochMember digestMember
            epochDigestAccepted)
          (AyUPDAConj
            (AyUPDACheckerTranscript chunkReplay checkerTranscript
              checkerAccepted)
            (AyUPDAConj
              (AyUPDAReconstruction emptyClause reconstructionHandle
                visibleUnsat originalUnsat)
              (AyUPDAFingerprint chunkReplay fingerprintAgrees
                visibleUnsat))))))

def AyUPDAAcceptedReplay
    (archivedChunk : Prop) (chunkBoundary : Prop)
    (chunkReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPDAConj
    (AyUPDAAcceptedEvidence archivedChunk chunkBoundary chunkReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat

def AyUPDABadArchive
    (missingChunk : Prop) (digestDrift : Prop)
    (missingCheckerReplay : Prop) (boundaryDrift : Prop)
    (parentGap : Prop) (stepMapMismatch : Prop)
    (epochDrift : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUPDAConj
    (AyUPDAConj noClaim recompute)
    (AyUPDADisj missingChunk
      (AyUPDADisj digestDrift
        (AyUPDADisj missingCheckerReplay
          (AyUPDADisj boundaryDrift
            (AyUPDADisj parentGap
              (AyUPDADisj stepMapMismatch
                (AyUPDADisj epochDrift fingerprintDrift)))))))

def AyUPDAPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPDADisj noClaim originalUnsat

theorem ay_upda_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPDAConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_upda_conj_left
    (p : Prop) (q : Prop) :
    AyUPDAConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_upda_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPDADisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_upda_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPDADisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_upda_archived_chunk
    (archivedChunk : Prop) (chunkBoundary : Prop)
    (chunkReplay : Prop) :
    AyUPDAChunkBoundary archivedChunk chunkBoundary chunkReplay ->
    archivedChunk := by
  intro boundary
  exact ay_upda_conj_left archivedChunk
    (AyUPDAConj
      (AyUPDAMap archivedChunk chunkBoundary)
      (AyUPDAMap chunkBoundary chunkReplay))
    boundary

theorem ay_upda_chunk_boundary
    (archivedChunk : Prop) (chunkBoundary : Prop)
    (chunkReplay : Prop) :
    AyUPDAChunkBoundary archivedChunk chunkBoundary chunkReplay ->
    chunkBoundary := by
  intro boundary
  exact boundary chunkBoundary
    (fun chunk tail =>
      tail chunkBoundary
        (fun chunk_to_boundary _boundary_to_replay =>
          chunk_to_boundary chunk))

theorem ay_upda_chunk_replay
    (archivedChunk : Prop) (chunkBoundary : Prop)
    (chunkReplay : Prop) :
    AyUPDAChunkBoundary archivedChunk chunkBoundary chunkReplay ->
    chunkReplay := by
  intro boundary
  exact boundary chunkReplay
    (fun chunk tail =>
      tail chunkReplay
        (fun chunk_to_boundary boundary_to_replay =>
          boundary_to_replay (chunk_to_boundary chunk)))

theorem ay_upda_parent_coverage
    (chunkReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUPDAParentCoverage chunkReplay parentCoverage emptyClause ->
    chunkReplay ->
    parentCoverage := by
  intro parents
  exact parents (chunkReplay -> parentCoverage)
    (fun replay_to_parents _parents_to_empty => replay_to_parents)

theorem ay_upda_empty_clause
    (chunkReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUPDAParentCoverage chunkReplay parentCoverage emptyClause ->
    parentCoverage ->
    emptyClause := by
  intro parents
  exact parents (parentCoverage -> emptyClause)
    (fun _replay_to_parents parents_to_empty => parents_to_empty)

theorem ay_upda_step_map_evidence
    (chunkReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :
    AyUPDAStepMap chunkReplay stepMapEvidence stepMapAccepted ->
    chunkReplay ->
    stepMapEvidence := by
  intro step_map
  exact step_map (chunkReplay -> stepMapEvidence)
    (fun replay_to_step_map _step_map_to_accept => replay_to_step_map)

theorem ay_upda_step_map_accepted
    (chunkReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :
    AyUPDAStepMap chunkReplay stepMapEvidence stepMapAccepted ->
    stepMapEvidence ->
    stepMapAccepted := by
  intro step_map
  exact step_map (stepMapEvidence -> stepMapAccepted)
    (fun _replay_to_step_map step_map_to_accept => step_map_to_accept)

theorem ay_upda_epoch_member
    (chunkReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUPDAEpochDigest chunkReplay epochMember digestMember
      epochDigestAccepted ->
    chunkReplay ->
    epochMember := by
  intro epoch_digest
  exact epoch_digest (chunkReplay -> epochMember)
    (fun replay_to_epoch _tail => replay_to_epoch)

theorem ay_upda_digest_member
    (chunkReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUPDAEpochDigest chunkReplay epochMember digestMember
      epochDigestAccepted ->
    epochMember ->
    digestMember := by
  intro epoch_digest
  exact epoch_digest (epochMember -> digestMember)
    (fun _replay_to_epoch tail =>
      tail (epochMember -> digestMember)
        (fun epoch_to_digest _digest_to_accept => epoch_to_digest))

theorem ay_upda_epoch_digest_accepted
    (chunkReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUPDAEpochDigest chunkReplay epochMember digestMember
      epochDigestAccepted ->
    digestMember ->
    epochDigestAccepted := by
  intro epoch_digest
  exact epoch_digest (digestMember -> epochDigestAccepted)
    (fun _replay_to_epoch tail =>
      tail (digestMember -> epochDigestAccepted)
        (fun _epoch_to_digest digest_to_accept => digest_to_accept))

theorem ay_upda_checker_transcript
    (chunkReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUPDACheckerTranscript chunkReplay checkerTranscript checkerAccepted ->
    chunkReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (chunkReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_upda_checker_accepted
    (chunkReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUPDACheckerTranscript chunkReplay checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> checkerAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_upda_reconstruction_handle
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPDAReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    reconstructionHandle := by
  intro reconstruction
  exact ay_upda_conj_left reconstructionHandle
    (AyUPDAConj
      (AyUPDAMap emptyClause visibleUnsat)
      (AyUPDAMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_upda_visible_unsat_from_empty
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPDAReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClause -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_upda_original_unsat_from_visible
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPDAReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original => visible_to_original))

theorem ay_upda_fingerprint_agrees
    (chunkReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUPDAFingerprint chunkReplay fingerprintAgrees visibleUnsat ->
    chunkReplay ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (chunkReplay -> fingerprintAgrees)
    (fun replay_to_fingerprint _fingerprint_to_visible =>
      replay_to_fingerprint)

theorem ay_upda_visible_unsat_from_fingerprint
    (chunkReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUPDAFingerprint chunkReplay fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _replay_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_upda_accepted_evidence
    (archivedChunk : Prop) (chunkBoundary : Prop)
    (chunkReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPDAAcceptedReplay archivedChunk chunkBoundary chunkReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPDAAcceptedEvidence archivedChunk chunkBoundary chunkReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat := by
  intro accepted
  exact ay_upda_conj_left
    (AyUPDAAcceptedEvidence archivedChunk chunkBoundary chunkReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_upda_accepted_original_unsat
    (archivedChunk : Prop) (chunkBoundary : Prop)
    (chunkReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPDAAcceptedReplay archivedChunk chunkBoundary chunkReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_upda_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUPDAPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_upda_disj_right noClaim originalUnsat unsat

theorem ay_upda_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUPDAPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_upda_disj_left noClaim originalUnsat no_claim

theorem ay_upda_accepted_archive_publish_sound
    (archivedChunk : Prop) (chunkBoundary : Prop)
    (chunkReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUPDAAcceptedReplay archivedChunk chunkBoundary chunkReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPDAPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_upda_public_unsat_report noClaim originalUnsat
    (ay_upda_accepted_original_unsat archivedChunk chunkBoundary chunkReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat
      accepted)

theorem ay_upda_bad_archive_no_claim
    (missingChunk : Prop) (digestDrift : Prop)
    (missingCheckerReplay : Prop) (boundaryDrift : Prop)
    (parentGap : Prop) (stepMapMismatch : Prop)
    (epochDrift : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPDABadArchive missingChunk digestDrift missingCheckerReplay
      boundaryDrift parentGap stepMapMismatch epochDrift fingerprintDrift
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_upda_conj_left noClaim recompute fail_closed)

theorem ay_upda_bad_archive_recompute
    (missingChunk : Prop) (digestDrift : Prop)
    (missingCheckerReplay : Prop) (boundaryDrift : Prop)
    (parentGap : Prop) (stepMapMismatch : Prop)
    (epochDrift : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPDABadArchive missingChunk digestDrift missingCheckerReplay
      boundaryDrift parentGap stepMapMismatch epochDrift fingerprintDrift
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_upda_bad_archive_public_no_claim
    (missingChunk : Prop) (digestDrift : Prop)
    (missingCheckerReplay : Prop) (boundaryDrift : Prop)
    (parentGap : Prop) (stepMapMismatch : Prop)
    (epochDrift : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPDABadArchive missingChunk digestDrift missingCheckerReplay
      boundaryDrift parentGap stepMapMismatch epochDrift fingerprintDrift
      noClaim recompute ->
    AyUPDAPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_upda_public_no_claim_report noClaim originalUnsat
    (ay_upda_bad_archive_no_claim missingChunk digestDrift
      missingCheckerReplay boundaryDrift parentGap stepMapMismatch
      epochDrift fingerprintDrift noClaim recompute bad)

theorem ay_upda_bad_archive_cannot_publish
    (missingChunk : Prop) (digestDrift : Prop)
    (missingCheckerReplay : Prop) (boundaryDrift : Prop)
    (parentGap : Prop) (stepMapMismatch : Prop)
    (epochDrift : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPDABadArchive missingChunk digestDrift missingCheckerReplay
      boundaryDrift parentGap stepMapMismatch epochDrift fingerprintDrift
      noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_upda_bad_archive_no_claim missingChunk digestDrift
      missingCheckerReplay boundaryDrift parentGap stepMapMismatch
      epochDrift fingerprintDrift noClaim recompute bad)
    unsat

theorem ay_upda_missing_chunk_forces_no_claim
    (missingChunk : Prop) (digestDrift : Prop)
    (missingCheckerReplay : Prop) (boundaryDrift : Prop)
    (parentGap : Prop) (stepMapMismatch : Prop)
    (epochDrift : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    missingChunk ->
    AyUPDAConj noClaim recompute ->
    AyUPDABadArchive missingChunk digestDrift missingCheckerReplay
      boundaryDrift parentGap stepMapMismatch epochDrift fingerprintDrift
      noClaim recompute := by
  intro missing
  intro fail_closed
  exact ay_upda_conj_intro
    (AyUPDAConj noClaim recompute)
    (AyUPDADisj missingChunk
      (AyUPDADisj digestDrift
        (AyUPDADisj missingCheckerReplay
          (AyUPDADisj boundaryDrift
            (AyUPDADisj parentGap
              (AyUPDADisj stepMapMismatch
                (AyUPDADisj epochDrift fingerprintDrift)))))))
    fail_closed
    (ay_upda_disj_left missingChunk
      (AyUPDADisj digestDrift
        (AyUPDADisj missingCheckerReplay
          (AyUPDADisj boundaryDrift
            (AyUPDADisj parentGap
              (AyUPDADisj stepMapMismatch
                (AyUPDADisj epochDrift fingerprintDrift))))))
      missing)

theorem ay_upda_digest_drift_forces_no_claim
    (missingChunk : Prop) (digestDrift : Prop)
    (missingCheckerReplay : Prop) (boundaryDrift : Prop)
    (parentGap : Prop) (stepMapMismatch : Prop)
    (epochDrift : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    digestDrift ->
    AyUPDAConj noClaim recompute ->
    AyUPDABadArchive missingChunk digestDrift missingCheckerReplay
      boundaryDrift parentGap stepMapMismatch epochDrift fingerprintDrift
      noClaim recompute := by
  intro drift
  intro fail_closed
  exact ay_upda_conj_intro
    (AyUPDAConj noClaim recompute)
    (AyUPDADisj missingChunk
      (AyUPDADisj digestDrift
        (AyUPDADisj missingCheckerReplay
          (AyUPDADisj boundaryDrift
            (AyUPDADisj parentGap
              (AyUPDADisj stepMapMismatch
                (AyUPDADisj epochDrift fingerprintDrift)))))))
    fail_closed
    (ay_upda_disj_right missingChunk
      (AyUPDADisj digestDrift
        (AyUPDADisj missingCheckerReplay
          (AyUPDADisj boundaryDrift
            (AyUPDADisj parentGap
              (AyUPDADisj stepMapMismatch
                (AyUPDADisj epochDrift fingerprintDrift))))))
      (ay_upda_disj_left digestDrift
        (AyUPDADisj missingCheckerReplay
          (AyUPDADisj boundaryDrift
            (AyUPDADisj parentGap
              (AyUPDADisj stepMapMismatch
                (AyUPDADisj epochDrift fingerprintDrift)))))
        drift))

theorem ay_upda_missing_checker_replay_forces_no_claim
    (missingChunk : Prop) (digestDrift : Prop)
    (missingCheckerReplay : Prop) (boundaryDrift : Prop)
    (parentGap : Prop) (stepMapMismatch : Prop)
    (epochDrift : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    missingCheckerReplay ->
    AyUPDAConj noClaim recompute ->
    AyUPDABadArchive missingChunk digestDrift missingCheckerReplay
      boundaryDrift parentGap stepMapMismatch epochDrift fingerprintDrift
      noClaim recompute := by
  intro missing_checker
  intro fail_closed
  exact ay_upda_conj_intro
    (AyUPDAConj noClaim recompute)
    (AyUPDADisj missingChunk
      (AyUPDADisj digestDrift
        (AyUPDADisj missingCheckerReplay
          (AyUPDADisj boundaryDrift
            (AyUPDADisj parentGap
              (AyUPDADisj stepMapMismatch
                (AyUPDADisj epochDrift fingerprintDrift)))))))
    fail_closed
    (ay_upda_disj_right missingChunk
      (AyUPDADisj digestDrift
        (AyUPDADisj missingCheckerReplay
          (AyUPDADisj boundaryDrift
            (AyUPDADisj parentGap
              (AyUPDADisj stepMapMismatch
                (AyUPDADisj epochDrift fingerprintDrift))))))
      (ay_upda_disj_right digestDrift
        (AyUPDADisj missingCheckerReplay
          (AyUPDADisj boundaryDrift
            (AyUPDADisj parentGap
              (AyUPDADisj stepMapMismatch
                (AyUPDADisj epochDrift fingerprintDrift)))))
        (ay_upda_disj_left missingCheckerReplay
          (AyUPDADisj boundaryDrift
            (AyUPDADisj parentGap
              (AyUPDADisj stepMapMismatch
                (AyUPDADisj epochDrift fingerprintDrift))))
          missing_checker)))

theorem ay_upda_archived_chunk_without_checker_cannot_publish
    (missingChunk : Prop) (digestDrift : Prop)
    (missingCheckerReplay : Prop) (boundaryDrift : Prop)
    (parentGap : Prop) (stepMapMismatch : Prop)
    (epochDrift : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPDABadArchive missingChunk digestDrift missingCheckerReplay
      boundaryDrift parentGap stepMapMismatch epochDrift fingerprintDrift
      noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_upda_bad_archive_cannot_publish missingChunk digestDrift
    missingCheckerReplay boundaryDrift parentGap stepMapMismatch epochDrift
    fingerprintDrift noClaim recompute originalUnsat bad
