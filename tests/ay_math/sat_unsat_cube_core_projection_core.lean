-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded cube-core projection soundness for ay UNSAT replay. Propositions
-- stand for cube frame lineage, assumption activation maps, dependency
-- coverage, projection/reconstruction evidence, digest membership, checker
-- replay, and fail-closed diagnostics.

def AyUCCPConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCCPDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCCPMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCCPFrameLineage
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop) :=
  AyUCCPConj cubeFrame
    (AyUCCPConj
      (AyUCCPMap cubeFrame frameCovered)
      (AyUCCPMap frameCovered cubeCore))

def AyUCCPActivationMap
    (cubeCore : Prop) (assumptionMap : Prop) (activatedCore : Prop) :=
  AyUCCPConj
    (AyUCCPMap cubeCore assumptionMap)
    (AyUCCPMap assumptionMap activatedCore)

def AyUCCPCoreCoverage
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) :=
  AyUCCPConj
    (AyUCCPMap activatedCore coreDependencies)
    (AyUCCPMap coreDependencies emptyClause)

def AyUCCPProjection
    (emptyClause : Prop) (projectedCore : Prop)
    (parentUnsat : Prop) (parentPruningSound : Prop) :=
  AyUCCPConj
    (AyUCCPMap emptyClause projectedCore)
    (AyUCCPConj
      (AyUCCPMap projectedCore parentUnsat)
      (AyUCCPMap parentUnsat parentPruningSound))

def AyUCCPDigestMembership
    (activatedCore : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :=
  AyUCCPConj
    (AyUCCPMap activatedCore digestMember)
    (AyUCCPMap digestMember digestAccepted)

def AyUCCPCheckerReplay
    (activatedCore : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUCCPConj
    (AyUCCPMap activatedCore checkerReplay)
    (AyUCCPMap checkerReplay replayAccepted)

def AyUCCPAcceptedProjection
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUCCPConj
    (AyUCCPFrameLineage cubeFrame frameCovered cubeCore)
    (AyUCCPConj
      (AyUCCPActivationMap cubeCore assumptionMap activatedCore)
      (AyUCCPConj
        (AyUCCPCoreCoverage activatedCore coreDependencies emptyClause)
        (AyUCCPConj
          (AyUCCPProjection emptyClause projectedCore parentUnsat
            parentPruningSound)
          (AyUCCPConj
            (AyUCCPDigestMembership activatedCore digestMember
              digestAccepted)
            (AyUCCPCheckerReplay activatedCore checkerReplay
              replayAccepted)))))

def AyUCCPBadProjection
    (uncoveredCubeFrame : Prop) (droppedAssumption : Prop)
    (missingDependency : Prop) (projectionMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUCCPConj
    (AyUCCPConj noClaim recompute)
    (AyUCCPDisj uncoveredCubeFrame
      (AyUCCPDisj droppedAssumption
        (AyUCCPDisj missingDependency
          (AyUCCPDisj projectionMismatch replayRejected))))

def AyUCCPPublicReport
    (noClaim : Prop) (parentUnsat : Prop) (parentPruningSound : Prop) :=
  AyUCCPDisj noClaim (AyUCCPConj parentUnsat parentPruningSound)

theorem ay_uccp_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCCPConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uccp_conj_left
    (p : Prop) (q : Prop) :
    AyUCCPConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uccp_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCCPDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uccp_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCCPDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uccp_frame
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop) :
    AyUCCPFrameLineage cubeFrame frameCovered cubeCore ->
    cubeFrame := by
  intro lineage
  exact ay_uccp_conj_left cubeFrame
    (AyUCCPConj
      (AyUCCPMap cubeFrame frameCovered)
      (AyUCCPMap frameCovered cubeCore))
    lineage

theorem ay_uccp_frame_covered
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop) :
    AyUCCPFrameLineage cubeFrame frameCovered cubeCore ->
    frameCovered := by
  intro lineage
  exact lineage frameCovered
    (fun frame tail =>
      tail frameCovered
        (fun frame_to_covered _covered_to_core =>
          frame_to_covered frame))

theorem ay_uccp_cube_core
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop) :
    AyUCCPFrameLineage cubeFrame frameCovered cubeCore ->
    cubeCore := by
  intro lineage
  exact lineage cubeCore
    (fun frame tail =>
      tail cubeCore
        (fun frame_to_covered covered_to_core =>
          covered_to_core (frame_to_covered frame)))

theorem ay_uccp_assumption_map
    (cubeCore : Prop) (assumptionMap : Prop) (activatedCore : Prop) :
    AyUCCPActivationMap cubeCore assumptionMap activatedCore ->
    cubeCore ->
    assumptionMap := by
  intro mapping
  exact mapping (cubeCore -> assumptionMap)
    (fun core_to_map _map_to_activated => core_to_map)

theorem ay_uccp_activated_core
    (cubeCore : Prop) (assumptionMap : Prop) (activatedCore : Prop) :
    AyUCCPActivationMap cubeCore assumptionMap activatedCore ->
    assumptionMap ->
    activatedCore := by
  intro mapping
  exact mapping (assumptionMap -> activatedCore)
    (fun _core_to_map map_to_activated => map_to_activated)

theorem ay_uccp_core_dependencies
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) :
    AyUCCPCoreCoverage activatedCore coreDependencies emptyClause ->
    activatedCore ->
    coreDependencies := by
  intro coverage
  exact coverage (activatedCore -> coreDependencies)
    (fun activated_to_dependencies _dependencies_to_empty =>
      activated_to_dependencies)

theorem ay_uccp_empty_clause
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) :
    AyUCCPCoreCoverage activatedCore coreDependencies emptyClause ->
    coreDependencies ->
    emptyClause := by
  intro coverage
  exact coverage (coreDependencies -> emptyClause)
    (fun _activated_to_dependencies dependencies_to_empty =>
      dependencies_to_empty)

theorem ay_uccp_projected_core
    (emptyClause : Prop) (projectedCore : Prop)
    (parentUnsat : Prop) (parentPruningSound : Prop) :
    AyUCCPProjection emptyClause projectedCore parentUnsat
      parentPruningSound ->
    emptyClause ->
    projectedCore := by
  intro projection
  exact projection (emptyClause -> projectedCore)
    (fun empty_to_projected _tail => empty_to_projected)

theorem ay_uccp_parent_unsat
    (emptyClause : Prop) (projectedCore : Prop)
    (parentUnsat : Prop) (parentPruningSound : Prop) :
    AyUCCPProjection emptyClause projectedCore parentUnsat
      parentPruningSound ->
    projectedCore ->
    parentUnsat := by
  intro projection
  exact projection (projectedCore -> parentUnsat)
    (fun _empty_to_projected tail =>
      tail (projectedCore -> parentUnsat)
        (fun projected_to_parent _parent_to_pruning =>
          projected_to_parent))

theorem ay_uccp_parent_pruning
    (emptyClause : Prop) (projectedCore : Prop)
    (parentUnsat : Prop) (parentPruningSound : Prop) :
    AyUCCPProjection emptyClause projectedCore parentUnsat
      parentPruningSound ->
    parentUnsat ->
    parentPruningSound := by
  intro projection
  exact projection (parentUnsat -> parentPruningSound)
    (fun _empty_to_projected tail =>
      tail (parentUnsat -> parentPruningSound)
        (fun _projected_to_parent parent_to_pruning =>
          parent_to_pruning))

theorem ay_uccp_digest_member
    (activatedCore : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUCCPDigestMembership activatedCore digestMember digestAccepted ->
    activatedCore ->
    digestMember := by
  intro digest
  exact digest (activatedCore -> digestMember)
    (fun activated_to_digest _digest_to_accept => activated_to_digest)

theorem ay_uccp_digest_accepted
    (activatedCore : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUCCPDigestMembership activatedCore digestMember digestAccepted ->
    digestMember ->
    digestAccepted := by
  intro digest
  exact digest (digestMember -> digestAccepted)
    (fun _activated_to_digest digest_to_accept => digest_to_accept)

theorem ay_uccp_replay_transcript
    (activatedCore : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPCheckerReplay activatedCore checkerReplay replayAccepted ->
    activatedCore ->
    checkerReplay := by
  intro replay
  exact replay (activatedCore -> checkerReplay)
    (fun activated_to_replay _replay_to_accept => activated_to_replay)

theorem ay_uccp_replay_accepted
    (activatedCore : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPCheckerReplay activatedCore checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _activated_to_replay replay_to_accept => replay_to_accept)

theorem ay_uccp_projection_lineage
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    AyUCCPFrameLineage cubeFrame frameCovered cubeCore := by
  intro accepted
  exact ay_uccp_conj_left
    (AyUCCPFrameLineage cubeFrame frameCovered cubeCore)
    (AyUCCPConj
      (AyUCCPActivationMap cubeCore assumptionMap activatedCore)
      (AyUCCPConj
        (AyUCCPCoreCoverage activatedCore coreDependencies emptyClause)
        (AyUCCPConj
          (AyUCCPProjection emptyClause projectedCore parentUnsat
            parentPruningSound)
          (AyUCCPConj
            (AyUCCPDigestMembership activatedCore digestMember
              digestAccepted)
            (AyUCCPCheckerReplay activatedCore checkerReplay
              replayAccepted)))))
    accepted

theorem ay_uccp_projection_activation
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    AyUCCPActivationMap cubeCore assumptionMap activatedCore := by
  intro accepted
  exact accepted
    (AyUCCPActivationMap cubeCore assumptionMap activatedCore)
    (fun _lineage tail =>
      tail (AyUCCPActivationMap cubeCore assumptionMap activatedCore)
        (fun activation _rest => activation))

theorem ay_uccp_projection_coverage
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    AyUCCPCoreCoverage activatedCore coreDependencies emptyClause := by
  intro accepted
  exact accepted
    (AyUCCPCoreCoverage activatedCore coreDependencies emptyClause)
    (fun _lineage tail =>
      tail (AyUCCPCoreCoverage activatedCore coreDependencies emptyClause)
        (fun _activation rest =>
          rest (AyUCCPCoreCoverage activatedCore coreDependencies emptyClause)
            (fun coverage _tail => coverage)))

theorem ay_uccp_projection_evidence
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    AyUCCPProjection emptyClause projectedCore parentUnsat
      parentPruningSound := by
  intro accepted
  exact accepted
    (AyUCCPProjection emptyClause projectedCore parentUnsat
      parentPruningSound)
    (fun _lineage tail =>
      tail
        (AyUCCPProjection emptyClause projectedCore parentUnsat
          parentPruningSound)
        (fun _activation rest =>
          rest
            (AyUCCPProjection emptyClause projectedCore parentUnsat
              parentPruningSound)
            (fun _coverage tail2 =>
              tail2
                (AyUCCPProjection emptyClause projectedCore parentUnsat
                  parentPruningSound)
                (fun projection _tail => projection))))

theorem ay_uccp_projection_digest
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    AyUCCPDigestMembership activatedCore digestMember digestAccepted := by
  intro accepted
  exact accepted
    (AyUCCPDigestMembership activatedCore digestMember digestAccepted)
    (fun _lineage tail =>
      tail (AyUCCPDigestMembership activatedCore digestMember digestAccepted)
        (fun _activation rest =>
          rest (AyUCCPDigestMembership activatedCore digestMember
            digestAccepted)
            (fun _coverage tail2 =>
              tail2 (AyUCCPDigestMembership activatedCore digestMember
                digestAccepted)
                (fun _projection tail3 =>
                  tail3 (AyUCCPDigestMembership activatedCore digestMember
                    digestAccepted)
                    (fun digest _replay => digest)))))

theorem ay_uccp_projection_replay
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    AyUCCPCheckerReplay activatedCore checkerReplay replayAccepted := by
  intro accepted
  exact accepted (AyUCCPCheckerReplay activatedCore checkerReplay
    replayAccepted)
    (fun _lineage tail =>
      tail (AyUCCPCheckerReplay activatedCore checkerReplay replayAccepted)
        (fun _activation rest =>
          rest (AyUCCPCheckerReplay activatedCore checkerReplay
            replayAccepted)
            (fun _coverage tail2 =>
              tail2 (AyUCCPCheckerReplay activatedCore checkerReplay
                replayAccepted)
                (fun _projection tail3 =>
                  tail3 (AyUCCPCheckerReplay activatedCore checkerReplay
                    replayAccepted)
                    (fun _digest replay => replay)))))

theorem ay_uccp_activated_core_from_frame
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop) :
    AyUCCPFrameLineage cubeFrame frameCovered cubeCore ->
    AyUCCPActivationMap cubeCore assumptionMap activatedCore ->
    activatedCore := by
  intro lineage
  intro activation
  have core : cubeCore :=
    ay_uccp_cube_core cubeFrame frameCovered cubeCore lineage
  have map : assumptionMap :=
    ay_uccp_assumption_map cubeCore assumptionMap activatedCore
      activation core
  exact ay_uccp_activated_core cubeCore assumptionMap activatedCore
    activation map

theorem ay_uccp_accepted_empty_clause
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    emptyClause := by
  intro accepted
  have lineage :
      AyUCCPFrameLineage cubeFrame frameCovered cubeCore :=
    ay_uccp_projection_lineage cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have activation :
      AyUCCPActivationMap cubeCore assumptionMap activatedCore :=
    ay_uccp_projection_activation cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have coverage :
      AyUCCPCoreCoverage activatedCore coreDependencies emptyClause :=
    ay_uccp_projection_coverage cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have activated : activatedCore :=
    ay_uccp_activated_core_from_frame cubeFrame frameCovered cubeCore
      assumptionMap activatedCore lineage activation
  have deps : coreDependencies :=
    ay_uccp_core_dependencies activatedCore coreDependencies emptyClause
      coverage activated
  exact ay_uccp_empty_clause activatedCore coreDependencies emptyClause
    coverage deps

theorem ay_uccp_accepted_parent_unsat
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    parentUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_uccp_accepted_empty_clause cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have projection :
      AyUCCPProjection emptyClause projectedCore parentUnsat
        parentPruningSound :=
    ay_uccp_projection_evidence cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have projected : projectedCore :=
    ay_uccp_projected_core emptyClause projectedCore parentUnsat
      parentPruningSound projection empty
  exact ay_uccp_parent_unsat emptyClause projectedCore parentUnsat
    parentPruningSound projection projected

theorem ay_uccp_accepted_pruning_sound
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    parentPruningSound := by
  intro accepted
  have parent : parentUnsat :=
    ay_uccp_accepted_parent_unsat cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have projection :
      AyUCCPProjection emptyClause projectedCore parentUnsat
        parentPruningSound :=
    ay_uccp_projection_evidence cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  exact ay_uccp_parent_pruning emptyClause projectedCore parentUnsat
    parentPruningSound projection parent

theorem ay_uccp_accepted_digest
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    digestAccepted := by
  intro accepted
  have lineage :
      AyUCCPFrameLineage cubeFrame frameCovered cubeCore :=
    ay_uccp_projection_lineage cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have activation :
      AyUCCPActivationMap cubeCore assumptionMap activatedCore :=
    ay_uccp_projection_activation cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have digest :
      AyUCCPDigestMembership activatedCore digestMember digestAccepted :=
    ay_uccp_projection_digest cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have activated : activatedCore :=
    ay_uccp_activated_core_from_frame cubeFrame frameCovered cubeCore
      assumptionMap activatedCore lineage activation
  have member : digestMember :=
    ay_uccp_digest_member activatedCore digestMember digestAccepted
      digest activated
  exact ay_uccp_digest_accepted activatedCore digestMember digestAccepted
    digest member

theorem ay_uccp_accepted_replay
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    replayAccepted := by
  intro accepted
  have lineage :
      AyUCCPFrameLineage cubeFrame frameCovered cubeCore :=
    ay_uccp_projection_lineage cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have activation :
      AyUCCPActivationMap cubeCore assumptionMap activatedCore :=
    ay_uccp_projection_activation cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have replay : AyUCCPCheckerReplay activatedCore checkerReplay
      replayAccepted :=
    ay_uccp_projection_replay cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted
  have activated : activatedCore :=
    ay_uccp_activated_core_from_frame cubeFrame frameCovered cubeCore
      assumptionMap activatedCore lineage activation
  have transcript : checkerReplay :=
    ay_uccp_replay_transcript activatedCore checkerReplay replayAccepted
      replay activated
  exact ay_uccp_replay_accepted activatedCore checkerReplay replayAccepted
    replay transcript

theorem ay_uccp_public_unsat_pruning_report
    (noClaim : Prop) (parentUnsat : Prop) (parentPruningSound : Prop) :
    parentUnsat ->
    parentPruningSound ->
    AyUCCPPublicReport noClaim parentUnsat parentPruningSound := by
  intro parent
  intro pruning
  exact ay_uccp_disj_right noClaim
    (AyUCCPConj parentUnsat parentPruningSound)
    (ay_uccp_conj_intro parentUnsat parentPruningSound parent pruning)

theorem ay_uccp_public_no_claim_report
    (noClaim : Prop) (parentUnsat : Prop) (parentPruningSound : Prop) :
    noClaim -> AyUCCPPublicReport noClaim parentUnsat parentPruningSound := by
  intro no_claim
  exact ay_uccp_disj_left noClaim
    (AyUCCPConj parentUnsat parentPruningSound) no_claim

theorem ay_uccp_accepted_projection_publish_sound
    (cubeFrame : Prop) (frameCovered : Prop) (cubeCore : Prop)
    (assumptionMap : Prop) (activatedCore : Prop)
    (coreDependencies : Prop) (emptyClause : Prop)
    (projectedCore : Prop) (parentUnsat : Prop)
    (parentPruningSound : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (noClaim : Prop) :
    AyUCCPAcceptedProjection cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted ->
    AyUCCPPublicReport noClaim parentUnsat parentPruningSound := by
  intro accepted
  exact ay_uccp_public_unsat_pruning_report noClaim parentUnsat
    parentPruningSound
    (ay_uccp_accepted_parent_unsat cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted)
    (ay_uccp_accepted_pruning_sound cubeFrame frameCovered cubeCore
      assumptionMap activatedCore coreDependencies emptyClause projectedCore
      parentUnsat parentPruningSound digestMember digestAccepted
      checkerReplay replayAccepted accepted)

theorem ay_uccp_bad_projection_no_claim
    (uncoveredCubeFrame : Prop) (droppedAssumption : Prop)
    (missingDependency : Prop) (projectionMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCCPBadProjection uncoveredCubeFrame droppedAssumption
      missingDependency projectionMismatch replayRejected noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_uccp_bad_projection_recompute
    (uncoveredCubeFrame : Prop) (droppedAssumption : Prop)
    (missingDependency : Prop) (projectionMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCCPBadProjection uncoveredCubeFrame droppedAssumption
      missingDependency projectionMismatch replayRejected noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_uccp_bad_projection_public_no_claim
    (uncoveredCubeFrame : Prop) (droppedAssumption : Prop)
    (missingDependency : Prop) (projectionMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop)
    (parentUnsat : Prop) (parentPruningSound : Prop) :
    AyUCCPBadProjection uncoveredCubeFrame droppedAssumption
      missingDependency projectionMismatch replayRejected noClaim recompute ->
    AyUCCPPublicReport noClaim parentUnsat parentPruningSound := by
  intro bad
  exact ay_uccp_public_no_claim_report noClaim parentUnsat
    parentPruningSound
    (ay_uccp_bad_projection_no_claim uncoveredCubeFrame droppedAssumption
      missingDependency projectionMismatch replayRejected noClaim recompute bad)

theorem ay_uccp_bad_projection_cannot_publish
    (uncoveredCubeFrame : Prop) (droppedAssumption : Prop)
    (missingDependency : Prop) (projectionMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCCPBadProjection uncoveredCubeFrame droppedAssumption
      missingDependency projectionMismatch replayRejected noClaim recompute ->
    AyUCCPConj noClaim recompute := by
  intro bad
  exact bad (AyUCCPConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

