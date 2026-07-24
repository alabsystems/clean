-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT certificate dependency-slice soundness for ay. Propositions
-- stand for sliced proofs, preserved dependencies, empty-clause witnesses,
-- checker replay, archive digests, original reconstruction, and
-- no-claim/recompute diagnostics for omitted dependencies, stale digests,
-- checker rejection, or reconstruction mismatch.

def AyUCDSConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCDSDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCDSMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCDSSliceCoverage
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) :=
  AyUCDSConj slicedProof
    (AyUCDSConj
      (AyUCDSMap slicedProof dependencySlice)
      (AyUCDSMap dependencySlice emptyClause))

def AyUCDSArchiveDigest
    (slicedProof : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop) :=
  AyUCDSConj
    (AyUCDSMap slicedProof sliceDigest)
    (AyUCDSConj
      (AyUCDSMap sliceDigest archiveDigest)
      (AyUCDSMap archiveDigest digestAccepted))

def AyUCDSReplay
    (slicedProof : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUCDSConj
    (AyUCDSMap slicedProof checkerReplay)
    (AyUCDSMap checkerReplay replayAccepted)

def AyUCDSReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUCDSConj
    (AyUCDSMap emptyClause visibleUnsat)
    (AyUCDSMap visibleUnsat originalUnsat)

def AyUCDSAcceptedSlice
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCDSConj
    (AyUCDSSliceCoverage slicedProof dependencySlice emptyClause)
    (AyUCDSConj
      (AyUCDSArchiveDigest slicedProof sliceDigest archiveDigest
        digestAccepted)
      (AyUCDSConj
        (AyUCDSReplay slicedProof checkerReplay replayAccepted)
        (AyUCDSReconstruction emptyClause visibleUnsat originalUnsat)))

def AyUCDSBadSlice
    (omittedDependency : Prop) (staleArchiveDigest : Prop)
    (checkerRejected : Prop) (reconstructionMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUCDSConj
    (AyUCDSConj noClaim recompute)
    (AyUCDSDisj omittedDependency
      (AyUCDSDisj staleArchiveDigest
        (AyUCDSDisj checkerRejected reconstructionMismatch)))

def AyUCDSPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCDSDisj noClaim originalUnsat

theorem ay_ucds_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCDSConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucds_conj_left
    (p : Prop) (q : Prop) :
    AyUCDSConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucds_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCDSDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucds_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCDSDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucds_sliced_proof
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) :
    AyUCDSSliceCoverage slicedProof dependencySlice emptyClause ->
    slicedProof := by
  intro coverage
  exact ay_ucds_conj_left slicedProof
    (AyUCDSConj
      (AyUCDSMap slicedProof dependencySlice)
      (AyUCDSMap dependencySlice emptyClause))
    coverage

theorem ay_ucds_dependency_slice
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) :
    AyUCDSSliceCoverage slicedProof dependencySlice emptyClause ->
    dependencySlice := by
  intro coverage
  exact coverage dependencySlice
    (fun sliced tail =>
      tail dependencySlice
        (fun sliced_to_dependencies _dependencies_to_empty =>
          sliced_to_dependencies sliced))

theorem ay_ucds_empty_clause
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) :
    AyUCDSSliceCoverage slicedProof dependencySlice emptyClause ->
    emptyClause := by
  intro coverage
  exact coverage emptyClause
    (fun sliced tail =>
      tail emptyClause
        (fun sliced_to_dependencies dependencies_to_empty =>
          dependencies_to_empty (sliced_to_dependencies sliced)))

theorem ay_ucds_slice_digest_value
    (slicedProof : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop) :
    AyUCDSArchiveDigest slicedProof sliceDigest archiveDigest
      digestAccepted ->
    slicedProof ->
    sliceDigest := by
  intro digest
  exact digest (slicedProof -> sliceDigest)
    (fun sliced_to_digest _tail => sliced_to_digest)

theorem ay_ucds_archive_digest_value
    (slicedProof : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop) :
    AyUCDSArchiveDigest slicedProof sliceDigest archiveDigest
      digestAccepted ->
    sliceDigest ->
    archiveDigest := by
  intro digest
  exact digest (sliceDigest -> archiveDigest)
    (fun _sliced_to_digest tail =>
      tail (sliceDigest -> archiveDigest)
        (fun slice_to_archive _archive_to_accept => slice_to_archive))

theorem ay_ucds_digest_accepted
    (slicedProof : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop) :
    AyUCDSArchiveDigest slicedProof sliceDigest archiveDigest
      digestAccepted ->
    archiveDigest ->
    digestAccepted := by
  intro digest
  exact digest (archiveDigest -> digestAccepted)
    (fun _sliced_to_digest tail =>
      tail (archiveDigest -> digestAccepted)
        (fun _slice_to_archive archive_to_accept => archive_to_accept))

theorem ay_ucds_replay_transcript
    (slicedProof : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCDSReplay slicedProof checkerReplay replayAccepted ->
    slicedProof ->
    checkerReplay := by
  intro replay
  exact replay (slicedProof -> checkerReplay)
    (fun sliced_to_replay _replay_to_accept => sliced_to_replay)

theorem ay_ucds_replay_accepted
    (slicedProof : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCDSReplay slicedProof checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _sliced_to_replay replay_to_accept => replay_to_accept)

theorem ay_ucds_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCDSReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_ucds_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCDSReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_ucds_slice_coverage
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDSAcceptedSlice slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat ->
    AyUCDSSliceCoverage slicedProof dependencySlice emptyClause := by
  intro accepted
  exact ay_ucds_conj_left
    (AyUCDSSliceCoverage slicedProof dependencySlice emptyClause)
    (AyUCDSConj
      (AyUCDSArchiveDigest slicedProof sliceDigest archiveDigest
        digestAccepted)
      (AyUCDSConj
        (AyUCDSReplay slicedProof checkerReplay replayAccepted)
        (AyUCDSReconstruction emptyClause visibleUnsat originalUnsat)))
    accepted

theorem ay_ucds_slice_digest
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDSAcceptedSlice slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat ->
    AyUCDSArchiveDigest slicedProof sliceDigest archiveDigest
      digestAccepted := by
  intro accepted
  exact accepted
    (AyUCDSArchiveDigest slicedProof sliceDigest archiveDigest
      digestAccepted)
    (fun _coverage tail =>
      tail
        (AyUCDSArchiveDigest slicedProof sliceDigest archiveDigest
          digestAccepted)
        (fun digest _rest => digest))

theorem ay_ucds_slice_replay
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDSAcceptedSlice slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat ->
    AyUCDSReplay slicedProof checkerReplay replayAccepted := by
  intro accepted
  exact accepted
    (AyUCDSReplay slicedProof checkerReplay replayAccepted)
    (fun _coverage tail =>
      tail (AyUCDSReplay slicedProof checkerReplay replayAccepted)
        (fun _digest rest =>
          rest (AyUCDSReplay slicedProof checkerReplay replayAccepted)
            (fun replay _reconstruction => replay)))

theorem ay_ucds_slice_reconstruction
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDSAcceptedSlice slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat ->
    AyUCDSReconstruction emptyClause visibleUnsat originalUnsat := by
  intro accepted
  exact accepted (AyUCDSReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _coverage tail =>
      tail (AyUCDSReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _digest rest =>
          rest (AyUCDSReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _replay reconstruction => reconstruction)))

theorem ay_ucds_slice_digest_accepted
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDSAcceptedSlice slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat ->
    digestAccepted := by
  intro accepted
  have coverage :
      AyUCDSSliceCoverage slicedProof dependencySlice emptyClause :=
    ay_ucds_slice_coverage slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have digest :
      AyUCDSArchiveDigest slicedProof sliceDigest archiveDigest
        digestAccepted :=
    ay_ucds_slice_digest slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have sliced : slicedProof :=
    ay_ucds_sliced_proof slicedProof dependencySlice emptyClause coverage
  have slice_digest : sliceDigest :=
    ay_ucds_slice_digest_value slicedProof sliceDigest archiveDigest
      digestAccepted digest sliced
  have archive_digest : archiveDigest :=
    ay_ucds_archive_digest_value slicedProof sliceDigest archiveDigest
      digestAccepted digest slice_digest
  exact ay_ucds_digest_accepted slicedProof sliceDigest archiveDigest
    digestAccepted digest archive_digest

theorem ay_ucds_slice_checker_accepted
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDSAcceptedSlice slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat ->
    replayAccepted := by
  intro accepted
  have coverage :
      AyUCDSSliceCoverage slicedProof dependencySlice emptyClause :=
    ay_ucds_slice_coverage slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have replay :
      AyUCDSReplay slicedProof checkerReplay replayAccepted :=
    ay_ucds_slice_replay slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have sliced : slicedProof :=
    ay_ucds_sliced_proof slicedProof dependencySlice emptyClause coverage
  have transcript : checkerReplay :=
    ay_ucds_replay_transcript slicedProof checkerReplay replayAccepted
      replay sliced
  exact ay_ucds_replay_accepted slicedProof checkerReplay replayAccepted
    replay transcript

theorem ay_ucds_accepted_slice_original_unsat
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDSAcceptedSlice slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  have coverage :
      AyUCDSSliceCoverage slicedProof dependencySlice emptyClause :=
    ay_ucds_slice_coverage slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have empty : emptyClause :=
    ay_ucds_empty_clause slicedProof dependencySlice emptyClause coverage
  have reconstruction :
      AyUCDSReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_ucds_slice_reconstruction slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have visible : visibleUnsat :=
    ay_ucds_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_ucds_original_unsat_from_visible emptyClause visibleUnsat
    originalUnsat reconstruction visible

theorem ay_ucds_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUCDSPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucds_disj_right noClaim originalUnsat unsat

theorem ay_ucds_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUCDSPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucds_disj_left noClaim originalUnsat no_claim

theorem ay_ucds_accepted_slice_publish_sound
    (slicedProof : Prop) (dependencySlice : Prop)
    (emptyClause : Prop) (sliceDigest : Prop)
    (archiveDigest : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (noClaim : Prop) :
    AyUCDSAcceptedSlice slicedProof dependencySlice emptyClause
      sliceDigest archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat ->
    AyUCDSPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_ucds_public_unsat_report noClaim originalUnsat
    (ay_ucds_accepted_slice_original_unsat slicedProof dependencySlice
      emptyClause sliceDigest archiveDigest digestAccepted checkerReplay
      replayAccepted visibleUnsat originalUnsat accepted)

theorem ay_ucds_bad_slice_no_claim
    (omittedDependency : Prop) (staleArchiveDigest : Prop)
    (checkerRejected : Prop) (reconstructionMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDSBadSlice omittedDependency staleArchiveDigest checkerRejected
      reconstructionMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_ucds_bad_slice_recompute
    (omittedDependency : Prop) (staleArchiveDigest : Prop)
    (checkerRejected : Prop) (reconstructionMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDSBadSlice omittedDependency staleArchiveDigest checkerRejected
      reconstructionMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_ucds_bad_slice_public_no_claim
    (omittedDependency : Prop) (staleArchiveDigest : Prop)
    (checkerRejected : Prop) (reconstructionMismatch : Prop)
    (noClaim : Prop) (originalUnsat : Prop) (recompute : Prop) :
    AyUCDSBadSlice omittedDependency staleArchiveDigest checkerRejected
      reconstructionMismatch noClaim recompute ->
    AyUCDSPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucds_public_no_claim_report noClaim originalUnsat
    (ay_ucds_bad_slice_no_claim omittedDependency staleArchiveDigest
      checkerRejected reconstructionMismatch noClaim recompute bad)

theorem ay_ucds_bad_slice_cannot_publish_unsat
    (omittedDependency : Prop) (staleArchiveDigest : Prop)
    (checkerRejected : Prop) (reconstructionMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDSBadSlice omittedDependency staleArchiveDigest checkerRejected
      reconstructionMismatch noClaim recompute ->
    AyUCDSConj noClaim recompute := by
  intro bad
  exact bad (AyUCDSConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

