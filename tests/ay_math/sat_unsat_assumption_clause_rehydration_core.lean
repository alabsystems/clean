-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded assumption-clause rehydration soundness for ay UNSAT proofs.
-- Propositions stand for assumption frame lineage, activation maps, clause
-- dependency coverage, archive digests, checker replay, original reconstruction,
-- and fail-closed no-claim/recompute diagnostics.

def AyUACHConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUACHDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUACHMap (source : Prop) (target : Prop) :=
  source -> target

def AyUACHFrameLineage
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) :=
  AyUACHConj assumptionFrame
    (AyUACHConj
      (AyUACHMap assumptionFrame frameFresh)
      (AyUACHMap frameFresh assumptionClause))

def AyUACHActivationMap
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) :=
  AyUACHConj
    (AyUACHMap assumptionClause activationMap)
    (AyUACHMap activationMap rehydratedClause)

def AyUACHClauseCoverage
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :=
  AyUACHConj
    (AyUACHMap rehydratedClause dependencyCoverage)
    (AyUACHMap dependencyCoverage emptyClause)

def AyUACHArchiveDigest
    (rehydratedClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) :=
  AyUACHConj
    (AyUACHMap rehydratedClause archiveDigest)
    (AyUACHMap archiveDigest digestAccepted)

def AyUACHCheckerReplay
    (rehydratedClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUACHConj
    (AyUACHMap rehydratedClause checkerReplay)
    (AyUACHMap checkerReplay replayAccepted)

def AyUACHReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUACHConj
    (AyUACHMap emptyClause visibleUnsat)
    (AyUACHMap visibleUnsat originalUnsat)

def AyUACHAcceptedRehydration
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUACHConj
    (AyUACHFrameLineage assumptionFrame frameFresh assumptionClause)
    (AyUACHConj
      (AyUACHActivationMap assumptionClause activationMap rehydratedClause)
      (AyUACHConj
        (AyUACHClauseCoverage rehydratedClause dependencyCoverage
          emptyClause)
        (AyUACHConj
          (AyUACHArchiveDigest rehydratedClause archiveDigest
            digestAccepted)
          (AyUACHConj
            (AyUACHCheckerReplay rehydratedClause checkerReplay
              replayAccepted)
            (AyUACHReconstruction emptyClause visibleUnsat
              originalUnsat)))))

def AyUACHBadRehydration
    (staleFrame : Prop) (missingActivation : Prop)
    (missingDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUACHConj
    (AyUACHConj noClaim recompute)
    (AyUACHDisj staleFrame
      (AyUACHDisj missingActivation
        (AyUACHDisj missingDependency
          (AyUACHDisj digestMismatch replayRejected))))

def AyUACHPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUACHDisj noClaim originalUnsat

theorem ay_uach_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUACHConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uach_conj_left
    (p : Prop) (q : Prop) :
    AyUACHConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uach_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUACHDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uach_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUACHDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uach_frame
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) :
    AyUACHFrameLineage assumptionFrame frameFresh assumptionClause ->
    assumptionFrame := by
  intro lineage
  exact ay_uach_conj_left assumptionFrame
    (AyUACHConj
      (AyUACHMap assumptionFrame frameFresh)
      (AyUACHMap frameFresh assumptionClause))
    lineage

theorem ay_uach_frame_fresh
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) :
    AyUACHFrameLineage assumptionFrame frameFresh assumptionClause ->
    frameFresh := by
  intro lineage
  exact lineage frameFresh
    (fun frame tail =>
      tail frameFresh
        (fun frame_to_fresh _fresh_to_clause => frame_to_fresh frame))

theorem ay_uach_assumption_clause
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) :
    AyUACHFrameLineage assumptionFrame frameFresh assumptionClause ->
    assumptionClause := by
  intro lineage
  exact lineage assumptionClause
    (fun frame tail =>
      tail assumptionClause
        (fun frame_to_fresh fresh_to_clause =>
          fresh_to_clause (frame_to_fresh frame)))

theorem ay_uach_activation_map
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) :
    AyUACHActivationMap assumptionClause activationMap rehydratedClause ->
    assumptionClause ->
    activationMap := by
  intro activation
  exact activation (assumptionClause -> activationMap)
    (fun clause_to_activation _activation_to_rehydrated =>
      clause_to_activation)

theorem ay_uach_rehydrated_clause
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) :
    AyUACHActivationMap assumptionClause activationMap rehydratedClause ->
    activationMap ->
    rehydratedClause := by
  intro activation
  exact activation (activationMap -> rehydratedClause)
    (fun _clause_to_activation activation_to_rehydrated =>
      activation_to_rehydrated)

theorem ay_uach_dependency_coverage
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUACHClauseCoverage rehydratedClause dependencyCoverage emptyClause ->
    rehydratedClause ->
    dependencyCoverage := by
  intro coverage
  exact coverage (rehydratedClause -> dependencyCoverage)
    (fun rehydrated_to_coverage _coverage_to_empty =>
      rehydrated_to_coverage)

theorem ay_uach_empty_clause
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUACHClauseCoverage rehydratedClause dependencyCoverage emptyClause ->
    dependencyCoverage ->
    emptyClause := by
  intro coverage
  exact coverage (dependencyCoverage -> emptyClause)
    (fun _rehydrated_to_coverage coverage_to_empty => coverage_to_empty)

theorem ay_uach_archive_digest
    (rehydratedClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) :
    AyUACHArchiveDigest rehydratedClause archiveDigest digestAccepted ->
    rehydratedClause ->
    archiveDigest := by
  intro digest
  exact digest (rehydratedClause -> archiveDigest)
    (fun rehydrated_to_digest _digest_to_accept => rehydrated_to_digest)

theorem ay_uach_digest_accepted
    (rehydratedClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) :
    AyUACHArchiveDigest rehydratedClause archiveDigest digestAccepted ->
    archiveDigest ->
    digestAccepted := by
  intro digest
  exact digest (archiveDigest -> digestAccepted)
    (fun _rehydrated_to_digest digest_to_accept => digest_to_accept)

theorem ay_uach_replay_transcript
    (rehydratedClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUACHCheckerReplay rehydratedClause checkerReplay replayAccepted ->
    rehydratedClause ->
    checkerReplay := by
  intro replay
  exact replay (rehydratedClause -> checkerReplay)
    (fun rehydrated_to_replay _replay_to_accept => rehydrated_to_replay)

theorem ay_uach_replay_accepted
    (rehydratedClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUACHCheckerReplay rehydratedClause checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _rehydrated_to_replay replay_to_accept => replay_to_accept)

theorem ay_uach_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_uach_original_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_uach_rehydration_lineage
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHAcceptedRehydration assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUACHFrameLineage assumptionFrame frameFresh assumptionClause := by
  intro accepted
  exact ay_uach_conj_left
    (AyUACHFrameLineage assumptionFrame frameFresh assumptionClause)
    (AyUACHConj
      (AyUACHActivationMap assumptionClause activationMap rehydratedClause)
      (AyUACHConj
        (AyUACHClauseCoverage rehydratedClause dependencyCoverage
          emptyClause)
        (AyUACHConj
          (AyUACHArchiveDigest rehydratedClause archiveDigest digestAccepted)
          (AyUACHConj
            (AyUACHCheckerReplay rehydratedClause checkerReplay
              replayAccepted)
            (AyUACHReconstruction emptyClause visibleUnsat
              originalUnsat)))))
    accepted

theorem ay_uach_rehydration_activation
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHAcceptedRehydration assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUACHActivationMap assumptionClause activationMap
      rehydratedClause := by
  intro accepted
  exact accepted
    (AyUACHActivationMap assumptionClause activationMap rehydratedClause)
    (fun _lineage tail =>
      tail (AyUACHActivationMap assumptionClause activationMap
        rehydratedClause)
        (fun activation _rest => activation))

theorem ay_uach_rehydration_coverage
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHAcceptedRehydration assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUACHClauseCoverage rehydratedClause dependencyCoverage
      emptyClause := by
  intro accepted
  exact accepted
    (AyUACHClauseCoverage rehydratedClause dependencyCoverage emptyClause)
    (fun _lineage tail =>
      tail (AyUACHClauseCoverage rehydratedClause dependencyCoverage
        emptyClause)
        (fun _activation rest =>
          rest (AyUACHClauseCoverage rehydratedClause dependencyCoverage
            emptyClause)
            (fun coverage _tail => coverage)))

theorem ay_uach_rehydration_digest
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHAcceptedRehydration assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUACHArchiveDigest rehydratedClause archiveDigest digestAccepted := by
  intro accepted
  exact accepted (AyUACHArchiveDigest rehydratedClause archiveDigest
    digestAccepted)
    (fun _lineage tail =>
      tail (AyUACHArchiveDigest rehydratedClause archiveDigest
        digestAccepted)
        (fun _activation rest =>
          rest (AyUACHArchiveDigest rehydratedClause archiveDigest
            digestAccepted)
            (fun _coverage tail2 =>
              tail2 (AyUACHArchiveDigest rehydratedClause archiveDigest
                digestAccepted)
                (fun digest _tail => digest))))

theorem ay_uach_rehydration_replay
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHAcceptedRehydration assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUACHCheckerReplay rehydratedClause checkerReplay replayAccepted := by
  intro accepted
  exact accepted (AyUACHCheckerReplay rehydratedClause checkerReplay
    replayAccepted)
    (fun _lineage tail =>
      tail (AyUACHCheckerReplay rehydratedClause checkerReplay
        replayAccepted)
        (fun _activation rest =>
          rest (AyUACHCheckerReplay rehydratedClause checkerReplay
            replayAccepted)
            (fun _coverage tail2 =>
              tail2 (AyUACHCheckerReplay rehydratedClause checkerReplay
                replayAccepted)
                (fun _digest tail3 =>
                  tail3 (AyUACHCheckerReplay rehydratedClause checkerReplay
                    replayAccepted)
                    (fun replay _reconstruction => replay)))))

theorem ay_uach_rehydration_reconstruction
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHAcceptedRehydration assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUACHReconstruction emptyClause visibleUnsat originalUnsat := by
  intro accepted
  exact accepted (AyUACHReconstruction emptyClause visibleUnsat
    originalUnsat)
    (fun _lineage tail =>
      tail (AyUACHReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _activation rest =>
          rest (AyUACHReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _coverage tail2 =>
              tail2
                (AyUACHReconstruction emptyClause visibleUnsat originalUnsat)
                (fun _digest tail3 =>
                  tail3
                    (AyUACHReconstruction emptyClause visibleUnsat
                      originalUnsat)
                    (fun _replay reconstruction => reconstruction)))))

theorem ay_uach_rehydrated_from_frame
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) :
    AyUACHFrameLineage assumptionFrame frameFresh assumptionClause ->
    AyUACHActivationMap assumptionClause activationMap rehydratedClause ->
    rehydratedClause := by
  intro lineage
  intro activation
  have clause : assumptionClause :=
    ay_uach_assumption_clause assumptionFrame frameFresh assumptionClause
      lineage
  have activation_map : activationMap :=
    ay_uach_activation_map assumptionClause activationMap rehydratedClause
      activation clause
  exact ay_uach_rehydrated_clause assumptionClause activationMap
    rehydratedClause activation activation_map

theorem ay_uach_accepted_empty_clause
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHAcceptedRehydration assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    emptyClause := by
  intro accepted
  have lineage :
      AyUACHFrameLineage assumptionFrame frameFresh assumptionClause :=
    ay_uach_rehydration_lineage assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have activation :
      AyUACHActivationMap assumptionClause activationMap rehydratedClause :=
    ay_uach_rehydration_activation assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have coverage :
      AyUACHClauseCoverage rehydratedClause dependencyCoverage emptyClause :=
    ay_uach_rehydration_coverage assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have rehydrated : rehydratedClause :=
    ay_uach_rehydrated_from_frame assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause lineage activation
  have covered : dependencyCoverage :=
    ay_uach_dependency_coverage rehydratedClause dependencyCoverage
      emptyClause coverage rehydrated
  exact ay_uach_empty_clause rehydratedClause dependencyCoverage
    emptyClause coverage covered

theorem ay_uach_accepted_digest
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHAcceptedRehydration assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    digestAccepted := by
  intro accepted
  have lineage :
      AyUACHFrameLineage assumptionFrame frameFresh assumptionClause :=
    ay_uach_rehydration_lineage assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have activation :
      AyUACHActivationMap assumptionClause activationMap rehydratedClause :=
    ay_uach_rehydration_activation assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have digest :
      AyUACHArchiveDigest rehydratedClause archiveDigest digestAccepted :=
    ay_uach_rehydration_digest assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have rehydrated : rehydratedClause :=
    ay_uach_rehydrated_from_frame assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause lineage activation
  have archive : archiveDigest :=
    ay_uach_archive_digest rehydratedClause archiveDigest digestAccepted
      digest rehydrated
  exact ay_uach_digest_accepted rehydratedClause archiveDigest
    digestAccepted digest archive

theorem ay_uach_accepted_replay
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHAcceptedRehydration assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    replayAccepted := by
  intro accepted
  have lineage :
      AyUACHFrameLineage assumptionFrame frameFresh assumptionClause :=
    ay_uach_rehydration_lineage assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have activation :
      AyUACHActivationMap assumptionClause activationMap rehydratedClause :=
    ay_uach_rehydration_activation assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have replay :
      AyUACHCheckerReplay rehydratedClause checkerReplay replayAccepted :=
    ay_uach_rehydration_replay assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have rehydrated : rehydratedClause :=
    ay_uach_rehydrated_from_frame assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause lineage activation
  have transcript : checkerReplay :=
    ay_uach_replay_transcript rehydratedClause checkerReplay replayAccepted
      replay rehydrated
  exact ay_uach_replay_accepted rehydratedClause checkerReplay
    replayAccepted replay transcript

theorem ay_uach_accepted_original_unsat
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACHAcceptedRehydration assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_uach_accepted_empty_clause assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have reconstruction :
      AyUACHReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_uach_rehydration_reconstruction assumptionFrame frameFresh
      assumptionClause activationMap rehydratedClause dependencyCoverage
      emptyClause archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have visible : visibleUnsat :=
    ay_uach_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_uach_original_unsat emptyClause visibleUnsat originalUnsat
    reconstruction visible

theorem ay_uach_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUACHPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_uach_disj_right noClaim originalUnsat unsat

theorem ay_uach_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUACHPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_uach_disj_left noClaim originalUnsat no_claim

theorem ay_uach_accepted_rehydration_publish_sound
    (assumptionFrame : Prop) (frameFresh : Prop)
    (assumptionClause : Prop) (activationMap : Prop)
    (rehydratedClause : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyUACHAcceptedRehydration assumptionFrame frameFresh assumptionClause
      activationMap rehydratedClause dependencyCoverage emptyClause
      archiveDigest digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUACHPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_uach_public_unsat_report noClaim originalUnsat
    (ay_uach_accepted_original_unsat assumptionFrame frameFresh
      assumptionClause activationMap rehydratedClause dependencyCoverage
      emptyClause archiveDigest digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted)

theorem ay_uach_bad_rehydration_no_claim
    (staleFrame : Prop) (missingActivation : Prop)
    (missingDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUACHBadRehydration staleFrame missingActivation missingDependency
      digestMismatch replayRejected noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_uach_bad_rehydration_recompute
    (staleFrame : Prop) (missingActivation : Prop)
    (missingDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUACHBadRehydration staleFrame missingActivation missingDependency
      digestMismatch replayRejected noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_uach_bad_rehydration_public_no_claim
    (staleFrame : Prop) (missingActivation : Prop)
    (missingDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUACHBadRehydration staleFrame missingActivation missingDependency
      digestMismatch replayRejected noClaim recompute ->
    AyUACHPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_uach_public_no_claim_report noClaim originalUnsat
    (ay_uach_bad_rehydration_no_claim staleFrame missingActivation
      missingDependency digestMismatch replayRejected noClaim recompute bad)

theorem ay_uach_bad_rehydration_cannot_publish
    (staleFrame : Prop) (missingActivation : Prop)
    (missingDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUACHBadRehydration staleFrame missingActivation missingDependency
      digestMismatch replayRejected noClaim recompute ->
    AyUACHConj noClaim recompute := by
  intro bad
  exact bad (AyUACHConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

