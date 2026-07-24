-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT core minimization/projection soundness for ay. Propositions
-- stand for minimized cores, preserved dependencies, assumption-frame lineage,
-- projection/reconstruction evidence, digest membership, checker replay, and
-- fail-closed no-claim/recompute diagnostics.

def AyUCMPConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCMPDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCMPMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCMPMinimizedCore
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) :=
  AyUCMPConj minimizedCore
    (AyUCMPConj
      (AyUCMPMap minimizedCore neededDependencies)
      (AyUCMPMap neededDependencies emptyClause))

def AyUCMPFrameLineage
    (assumptionFrame : Prop) (frameValid : Prop)
    (minimizedCore : Prop) :=
  AyUCMPConj assumptionFrame
    (AyUCMPConj
      (AyUCMPMap assumptionFrame frameValid)
      (AyUCMPMap frameValid minimizedCore))

def AyUCMPProjection
    (emptyClause : Prop) (projectedCore : Prop)
    (parentUnsat : Prop) (pruningSound : Prop) :=
  AyUCMPConj
    (AyUCMPMap emptyClause projectedCore)
    (AyUCMPConj
      (AyUCMPMap projectedCore parentUnsat)
      (AyUCMPMap parentUnsat pruningSound))

def AyUCMPDigestMembership
    (minimizedCore : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :=
  AyUCMPConj
    (AyUCMPMap minimizedCore digestMember)
    (AyUCMPMap digestMember digestAccepted)

def AyUCMPCheckerReplay
    (minimizedCore : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUCMPConj
    (AyUCMPMap minimizedCore checkerReplay)
    (AyUCMPMap checkerReplay replayAccepted)

def AyUCMPAcceptedProjection
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) (assumptionFrame : Prop) (frameValid : Prop)
    (projectedCore : Prop) (parentUnsat : Prop) (pruningSound : Prop)
    (digestMember : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop) :=
  AyUCMPConj
    (AyUCMPMinimizedCore minimizedCore neededDependencies emptyClause)
    (AyUCMPConj
      (AyUCMPFrameLineage assumptionFrame frameValid minimizedCore)
      (AyUCMPConj
        (AyUCMPProjection emptyClause projectedCore parentUnsat
          pruningSound)
        (AyUCMPConj
          (AyUCMPDigestMembership minimizedCore digestMember digestAccepted)
          (AyUCMPCheckerReplay minimizedCore checkerReplay
            replayAccepted))))

def AyUCMPBadProjection
    (omittedDependency : Prop) (staleFrame : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUCMPConj
    (AyUCMPConj noClaim recompute)
    (AyUCMPDisj omittedDependency
      (AyUCMPDisj staleFrame
        (AyUCMPDisj projectionMismatch
          (AyUCMPDisj digestMismatch replayRejected))))

def AyUCMPPublicReport
    (noClaim : Prop) (parentUnsat : Prop) (pruningSound : Prop) :=
  AyUCMPDisj noClaim (AyUCMPConj parentUnsat pruningSound)

theorem ay_ucmp_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCMPConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucmp_conj_left
    (p : Prop) (q : Prop) :
    AyUCMPConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucmp_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCMPDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucmp_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCMPDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucmp_minimized_core
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) :
    AyUCMPMinimizedCore minimizedCore neededDependencies emptyClause ->
    minimizedCore := by
  intro core
  exact ay_ucmp_conj_left minimizedCore
    (AyUCMPConj
      (AyUCMPMap minimizedCore neededDependencies)
      (AyUCMPMap neededDependencies emptyClause))
    core

theorem ay_ucmp_needed_dependencies
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) :
    AyUCMPMinimizedCore minimizedCore neededDependencies emptyClause ->
    neededDependencies := by
  intro core
  exact core neededDependencies
    (fun minimized tail =>
      tail neededDependencies
        (fun minimized_to_dependencies _dependencies_to_empty =>
          minimized_to_dependencies minimized))

theorem ay_ucmp_empty_clause
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) :
    AyUCMPMinimizedCore minimizedCore neededDependencies emptyClause ->
    emptyClause := by
  intro core
  exact core emptyClause
    (fun minimized tail =>
      tail emptyClause
        (fun minimized_to_dependencies dependencies_to_empty =>
          dependencies_to_empty (minimized_to_dependencies minimized)))

theorem ay_ucmp_frame
    (assumptionFrame : Prop) (frameValid : Prop)
    (minimizedCore : Prop) :
    AyUCMPFrameLineage assumptionFrame frameValid minimizedCore ->
    assumptionFrame := by
  intro lineage
  exact ay_ucmp_conj_left assumptionFrame
    (AyUCMPConj
      (AyUCMPMap assumptionFrame frameValid)
      (AyUCMPMap frameValid minimizedCore))
    lineage

theorem ay_ucmp_frame_valid
    (assumptionFrame : Prop) (frameValid : Prop)
    (minimizedCore : Prop) :
    AyUCMPFrameLineage assumptionFrame frameValid minimizedCore ->
    frameValid := by
  intro lineage
  exact lineage frameValid
    (fun frame tail =>
      tail frameValid
        (fun frame_to_valid _valid_to_core => frame_to_valid frame))

theorem ay_ucmp_core_from_frame
    (assumptionFrame : Prop) (frameValid : Prop)
    (minimizedCore : Prop) :
    AyUCMPFrameLineage assumptionFrame frameValid minimizedCore ->
    minimizedCore := by
  intro lineage
  exact lineage minimizedCore
    (fun frame tail =>
      tail minimizedCore
        (fun frame_to_valid valid_to_core =>
          valid_to_core (frame_to_valid frame)))

theorem ay_ucmp_projected_core
    (emptyClause : Prop) (projectedCore : Prop)
    (parentUnsat : Prop) (pruningSound : Prop) :
    AyUCMPProjection emptyClause projectedCore parentUnsat pruningSound ->
    emptyClause ->
    projectedCore := by
  intro projection
  exact projection (emptyClause -> projectedCore)
    (fun empty_to_projected _tail => empty_to_projected)

theorem ay_ucmp_parent_unsat
    (emptyClause : Prop) (projectedCore : Prop)
    (parentUnsat : Prop) (pruningSound : Prop) :
    AyUCMPProjection emptyClause projectedCore parentUnsat pruningSound ->
    projectedCore ->
    parentUnsat := by
  intro projection
  exact projection (projectedCore -> parentUnsat)
    (fun _empty_to_projected tail =>
      tail (projectedCore -> parentUnsat)
        (fun projected_to_parent _parent_to_pruning =>
          projected_to_parent))

theorem ay_ucmp_pruning_sound
    (emptyClause : Prop) (projectedCore : Prop)
    (parentUnsat : Prop) (pruningSound : Prop) :
    AyUCMPProjection emptyClause projectedCore parentUnsat pruningSound ->
    parentUnsat ->
    pruningSound := by
  intro projection
  exact projection (parentUnsat -> pruningSound)
    (fun _empty_to_projected tail =>
      tail (parentUnsat -> pruningSound)
        (fun _projected_to_parent parent_to_pruning =>
          parent_to_pruning))

theorem ay_ucmp_digest_member
    (minimizedCore : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUCMPDigestMembership minimizedCore digestMember digestAccepted ->
    minimizedCore ->
    digestMember := by
  intro digest
  exact digest (minimizedCore -> digestMember)
    (fun core_to_digest _digest_to_accept => core_to_digest)

theorem ay_ucmp_digest_accepted
    (minimizedCore : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUCMPDigestMembership minimizedCore digestMember digestAccepted ->
    digestMember ->
    digestAccepted := by
  intro digest
  exact digest (digestMember -> digestAccepted)
    (fun _core_to_digest digest_to_accept => digest_to_accept)

theorem ay_ucmp_replay_transcript
    (minimizedCore : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCMPCheckerReplay minimizedCore checkerReplay replayAccepted ->
    minimizedCore ->
    checkerReplay := by
  intro replay
  exact replay (minimizedCore -> checkerReplay)
    (fun core_to_replay _replay_to_accept => core_to_replay)

theorem ay_ucmp_replay_accepted
    (minimizedCore : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCMPCheckerReplay minimizedCore checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _core_to_replay replay_to_accept => replay_to_accept)

theorem ay_ucmp_accepted_core
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) (assumptionFrame : Prop) (frameValid : Prop)
    (projectedCore : Prop) (parentUnsat : Prop) (pruningSound : Prop)
    (digestMember : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop) :
    AyUCMPAcceptedProjection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted ->
    AyUCMPMinimizedCore minimizedCore neededDependencies emptyClause := by
  intro accepted
  exact ay_ucmp_conj_left
    (AyUCMPMinimizedCore minimizedCore neededDependencies emptyClause)
    (AyUCMPConj
      (AyUCMPFrameLineage assumptionFrame frameValid minimizedCore)
      (AyUCMPConj
        (AyUCMPProjection emptyClause projectedCore parentUnsat pruningSound)
        (AyUCMPConj
          (AyUCMPDigestMembership minimizedCore digestMember digestAccepted)
          (AyUCMPCheckerReplay minimizedCore checkerReplay replayAccepted))))
    accepted

theorem ay_ucmp_accepted_lineage
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) (assumptionFrame : Prop) (frameValid : Prop)
    (projectedCore : Prop) (parentUnsat : Prop) (pruningSound : Prop)
    (digestMember : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop) :
    AyUCMPAcceptedProjection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted ->
    AyUCMPFrameLineage assumptionFrame frameValid minimizedCore := by
  intro accepted
  exact accepted
    (AyUCMPFrameLineage assumptionFrame frameValid minimizedCore)
    (fun _core tail =>
      tail (AyUCMPFrameLineage assumptionFrame frameValid minimizedCore)
        (fun lineage _rest => lineage))

theorem ay_ucmp_accepted_projection
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) (assumptionFrame : Prop) (frameValid : Prop)
    (projectedCore : Prop) (parentUnsat : Prop) (pruningSound : Prop)
    (digestMember : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop) :
    AyUCMPAcceptedProjection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted ->
    AyUCMPProjection emptyClause projectedCore parentUnsat pruningSound := by
  intro accepted
  exact accepted
    (AyUCMPProjection emptyClause projectedCore parentUnsat pruningSound)
    (fun _core tail =>
      tail (AyUCMPProjection emptyClause projectedCore parentUnsat pruningSound)
        (fun _lineage rest =>
          rest
            (AyUCMPProjection emptyClause projectedCore parentUnsat
              pruningSound)
            (fun projection _tail => projection)))

theorem ay_ucmp_accepted_digest
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) (assumptionFrame : Prop) (frameValid : Prop)
    (projectedCore : Prop) (parentUnsat : Prop) (pruningSound : Prop)
    (digestMember : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop) :
    AyUCMPAcceptedProjection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted ->
    AyUCMPDigestMembership minimizedCore digestMember digestAccepted := by
  intro accepted
  exact accepted
    (AyUCMPDigestMembership minimizedCore digestMember digestAccepted)
    (fun _core tail =>
      tail (AyUCMPDigestMembership minimizedCore digestMember digestAccepted)
        (fun _lineage rest =>
          rest
            (AyUCMPDigestMembership minimizedCore digestMember digestAccepted)
            (fun _projection tail2 =>
              tail2
                (AyUCMPDigestMembership minimizedCore digestMember
                  digestAccepted)
                (fun digest _replay => digest))))

theorem ay_ucmp_accepted_replay
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) (assumptionFrame : Prop) (frameValid : Prop)
    (projectedCore : Prop) (parentUnsat : Prop) (pruningSound : Prop)
    (digestMember : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop) :
    AyUCMPAcceptedProjection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted ->
    AyUCMPCheckerReplay minimizedCore checkerReplay replayAccepted := by
  intro accepted
  exact accepted (AyUCMPCheckerReplay minimizedCore checkerReplay
    replayAccepted)
    (fun _core tail =>
      tail (AyUCMPCheckerReplay minimizedCore checkerReplay replayAccepted)
        (fun _lineage rest =>
          rest (AyUCMPCheckerReplay minimizedCore checkerReplay
            replayAccepted)
            (fun _projection tail2 =>
              tail2
                (AyUCMPCheckerReplay minimizedCore checkerReplay
                  replayAccepted)
                (fun _digest replay => replay))))

theorem ay_ucmp_parent_unsat_from_accepted
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) (assumptionFrame : Prop) (frameValid : Prop)
    (projectedCore : Prop) (parentUnsat : Prop) (pruningSound : Prop)
    (digestMember : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop) :
    AyUCMPAcceptedProjection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted ->
    parentUnsat := by
  intro accepted
  have core :
      AyUCMPMinimizedCore minimizedCore neededDependencies emptyClause :=
    ay_ucmp_accepted_core minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted accepted
  have projection :
      AyUCMPProjection emptyClause projectedCore parentUnsat pruningSound :=
    ay_ucmp_accepted_projection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted accepted
  have empty : emptyClause :=
    ay_ucmp_empty_clause minimizedCore neededDependencies emptyClause core
  have projected : projectedCore :=
    ay_ucmp_projected_core emptyClause projectedCore parentUnsat
      pruningSound projection empty
  exact ay_ucmp_parent_unsat emptyClause projectedCore parentUnsat
    pruningSound projection projected

theorem ay_ucmp_pruning_from_accepted
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) (assumptionFrame : Prop) (frameValid : Prop)
    (projectedCore : Prop) (parentUnsat : Prop) (pruningSound : Prop)
    (digestMember : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop) :
    AyUCMPAcceptedProjection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted ->
    pruningSound := by
  intro accepted
  have parent : parentUnsat :=
    ay_ucmp_parent_unsat_from_accepted minimizedCore neededDependencies
      emptyClause assumptionFrame frameValid projectedCore parentUnsat
      pruningSound digestMember digestAccepted checkerReplay replayAccepted
      accepted
  have projection :
      AyUCMPProjection emptyClause projectedCore parentUnsat pruningSound :=
    ay_ucmp_accepted_projection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted accepted
  exact ay_ucmp_pruning_sound emptyClause projectedCore parentUnsat
    pruningSound projection parent

theorem ay_ucmp_digest_from_accepted
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) (assumptionFrame : Prop) (frameValid : Prop)
    (projectedCore : Prop) (parentUnsat : Prop) (pruningSound : Prop)
    (digestMember : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop) :
    AyUCMPAcceptedProjection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted ->
    digestAccepted := by
  intro accepted
  have core :
      AyUCMPMinimizedCore minimizedCore neededDependencies emptyClause :=
    ay_ucmp_accepted_core minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted accepted
  have digest :
      AyUCMPDigestMembership minimizedCore digestMember digestAccepted :=
    ay_ucmp_accepted_digest minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted accepted
  have minimized : minimizedCore :=
    ay_ucmp_minimized_core minimizedCore neededDependencies emptyClause core
  have member : digestMember :=
    ay_ucmp_digest_member minimizedCore digestMember digestAccepted
      digest minimized
  exact ay_ucmp_digest_accepted minimizedCore digestMember digestAccepted
    digest member

theorem ay_ucmp_replay_from_accepted
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) (assumptionFrame : Prop) (frameValid : Prop)
    (projectedCore : Prop) (parentUnsat : Prop) (pruningSound : Prop)
    (digestMember : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop) :
    AyUCMPAcceptedProjection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted ->
    replayAccepted := by
  intro accepted
  have core :
      AyUCMPMinimizedCore minimizedCore neededDependencies emptyClause :=
    ay_ucmp_accepted_core minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted accepted
  have replay :
      AyUCMPCheckerReplay minimizedCore checkerReplay replayAccepted :=
    ay_ucmp_accepted_replay minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted accepted
  have minimized : minimizedCore :=
    ay_ucmp_minimized_core minimizedCore neededDependencies emptyClause core
  have transcript : checkerReplay :=
    ay_ucmp_replay_transcript minimizedCore checkerReplay replayAccepted
      replay minimized
  exact ay_ucmp_replay_accepted minimizedCore checkerReplay replayAccepted
    replay transcript

theorem ay_ucmp_public_unsat_pruning_report
    (noClaim : Prop) (parentUnsat : Prop) (pruningSound : Prop) :
    parentUnsat ->
    pruningSound ->
    AyUCMPPublicReport noClaim parentUnsat pruningSound := by
  intro parent
  intro pruning
  exact ay_ucmp_disj_right noClaim
    (AyUCMPConj parentUnsat pruningSound)
    (ay_ucmp_conj_intro parentUnsat pruningSound parent pruning)

theorem ay_ucmp_public_no_claim_report
    (noClaim : Prop) (parentUnsat : Prop) (pruningSound : Prop) :
    noClaim -> AyUCMPPublicReport noClaim parentUnsat pruningSound := by
  intro no_claim
  exact ay_ucmp_disj_left noClaim
    (AyUCMPConj parentUnsat pruningSound) no_claim

theorem ay_ucmp_accepted_projection_publish_sound
    (minimizedCore : Prop) (neededDependencies : Prop)
    (emptyClause : Prop) (assumptionFrame : Prop) (frameValid : Prop)
    (projectedCore : Prop) (parentUnsat : Prop) (pruningSound : Prop)
    (digestMember : Prop) (digestAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop) (noClaim : Prop) :
    AyUCMPAcceptedProjection minimizedCore neededDependencies emptyClause
      assumptionFrame frameValid projectedCore parentUnsat pruningSound
      digestMember digestAccepted checkerReplay replayAccepted ->
    AyUCMPPublicReport noClaim parentUnsat pruningSound := by
  intro accepted
  exact ay_ucmp_public_unsat_pruning_report noClaim parentUnsat pruningSound
    (ay_ucmp_parent_unsat_from_accepted minimizedCore neededDependencies
      emptyClause assumptionFrame frameValid projectedCore parentUnsat
      pruningSound digestMember digestAccepted checkerReplay replayAccepted
      accepted)
    (ay_ucmp_pruning_from_accepted minimizedCore neededDependencies
      emptyClause assumptionFrame frameValid projectedCore parentUnsat
      pruningSound digestMember digestAccepted checkerReplay replayAccepted
      accepted)

theorem ay_ucmp_bad_projection_no_claim
    (omittedDependency : Prop) (staleFrame : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCMPBadProjection omittedDependency staleFrame projectionMismatch
      digestMismatch replayRejected noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_ucmp_bad_projection_recompute
    (omittedDependency : Prop) (staleFrame : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCMPBadProjection omittedDependency staleFrame projectionMismatch
      digestMismatch replayRejected noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_ucmp_bad_projection_public_no_claim
    (omittedDependency : Prop) (staleFrame : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop)
    (parentUnsat : Prop) (pruningSound : Prop) :
    AyUCMPBadProjection omittedDependency staleFrame projectionMismatch
      digestMismatch replayRejected noClaim recompute ->
    AyUCMPPublicReport noClaim parentUnsat pruningSound := by
  intro bad
  exact ay_ucmp_public_no_claim_report noClaim parentUnsat pruningSound
    (ay_ucmp_bad_projection_no_claim omittedDependency staleFrame
      projectionMismatch digestMismatch replayRejected noClaim recompute bad)

theorem ay_ucmp_bad_projection_cannot_publish
    (omittedDependency : Prop) (staleFrame : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCMPBadProjection omittedDependency staleFrame projectionMismatch
      digestMismatch replayRejected noClaim recompute ->
    AyUCMPConj noClaim recompute := by
  intro bad
  exact bad (AyUCMPConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

