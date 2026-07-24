-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded incremental-assumption UNSAT core replay soundness for ay.
-- Propositions stand for assumption-frame lineage, activation literal maps,
-- core dependency coverage, checker replay, archive digests, original-formula
-- reconstruction, pruning soundness, and fail-closed diagnostics.

def AyUIACConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUIACDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUIACMap (source : Prop) (target : Prop) :=
  source -> target

def AyUIACFrameLineage
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) :=
  AyUIACConj assumptionFrame
    (AyUIACConj
      (AyUIACMap assumptionFrame lineageValid)
      (AyUIACMap lineageValid assumptionCore))

def AyUIACActivationMapping
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) :=
  AyUIACConj
    (AyUIACMap assumptionCore activationMap)
    (AyUIACMap activationMap activatedCore)

def AyUIACCoreCoverage
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) :=
  AyUIACConj
    (AyUIACMap activatedCore coreDependencies)
    (AyUIACMap coreDependencies emptyClause)

def AyUIACCheckerReplay
    (activatedCore : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUIACConj
    (AyUIACMap activatedCore checkerReplay)
    (AyUIACMap checkerReplay replayAccepted)

def AyUIACArchiveDigest
    (activatedCore : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) :=
  AyUIACConj
    (AyUIACMap activatedCore archiveDigest)
    (AyUIACMap archiveDigest digestAccepted)

def AyUIACReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :=
  AyUIACConj
    (AyUIACMap emptyClause visibleUnsat)
    (AyUIACConj
      (AyUIACMap visibleUnsat originalUnsat)
      (AyUIACMap originalUnsat pruningSound))

def AyUIACAcceptedCoreReplay
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :=
  AyUIACConj
    (AyUIACFrameLineage assumptionFrame lineageValid assumptionCore)
    (AyUIACConj
      (AyUIACActivationMapping assumptionCore activationMap activatedCore)
      (AyUIACConj
        (AyUIACCoreCoverage activatedCore coreDependencies emptyClause)
        (AyUIACConj
          (AyUIACCheckerReplay activatedCore checkerReplay replayAccepted)
          (AyUIACConj
            (AyUIACArchiveDigest activatedCore archiveDigest digestAccepted)
            (AyUIACReconstruction emptyClause visibleUnsat originalUnsat
              pruningSound)))))

def AyUIACBadCoreReplay
    (staleFrame : Prop) (droppedActivationLiteral : Prop)
    (missingCoreDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUIACConj
    (AyUIACConj noClaim recompute)
    (AyUIACDisj staleFrame
      (AyUIACDisj droppedActivationLiteral
        (AyUIACDisj missingCoreDependency
          (AyUIACDisj digestMismatch replayRejected))))

def AyUIACPublicReport
    (noClaim : Prop) (originalUnsat : Prop) (pruningSound : Prop) :=
  AyUIACDisj noClaim (AyUIACConj originalUnsat pruningSound)

theorem ay_uiac_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUIACConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uiac_conj_left
    (p : Prop) (q : Prop) :
    AyUIACConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uiac_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUIACDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uiac_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUIACDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uiac_frame
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) :
    AyUIACFrameLineage assumptionFrame lineageValid assumptionCore ->
    assumptionFrame := by
  intro lineage
  exact ay_uiac_conj_left assumptionFrame
    (AyUIACConj
      (AyUIACMap assumptionFrame lineageValid)
      (AyUIACMap lineageValid assumptionCore))
    lineage

theorem ay_uiac_lineage_valid
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) :
    AyUIACFrameLineage assumptionFrame lineageValid assumptionCore ->
    lineageValid := by
  intro lineage
  exact lineage lineageValid
    (fun frame tail =>
      tail lineageValid
        (fun frame_to_lineage _lineage_to_core =>
          frame_to_lineage frame))

theorem ay_uiac_assumption_core
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) :
    AyUIACFrameLineage assumptionFrame lineageValid assumptionCore ->
    assumptionCore := by
  intro lineage
  exact lineage assumptionCore
    (fun frame tail =>
      tail assumptionCore
        (fun frame_to_lineage lineage_to_core =>
          lineage_to_core (frame_to_lineage frame)))

theorem ay_uiac_activation_map
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) :
    AyUIACActivationMapping assumptionCore activationMap activatedCore ->
    assumptionCore ->
    activationMap := by
  intro mapping
  exact mapping (assumptionCore -> activationMap)
    (fun core_to_map _map_to_activated => core_to_map)

theorem ay_uiac_activated_core
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) :
    AyUIACActivationMapping assumptionCore activationMap activatedCore ->
    activationMap ->
    activatedCore := by
  intro mapping
  exact mapping (activationMap -> activatedCore)
    (fun _core_to_map map_to_activated => map_to_activated)

theorem ay_uiac_core_dependencies
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) :
    AyUIACCoreCoverage activatedCore coreDependencies emptyClause ->
    activatedCore ->
    coreDependencies := by
  intro coverage
  exact coverage (activatedCore -> coreDependencies)
    (fun activated_to_dependencies _dependencies_to_empty =>
      activated_to_dependencies)

theorem ay_uiac_empty_clause
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) :
    AyUIACCoreCoverage activatedCore coreDependencies emptyClause ->
    coreDependencies ->
    emptyClause := by
  intro coverage
  exact coverage (coreDependencies -> emptyClause)
    (fun _activated_to_dependencies dependencies_to_empty =>
      dependencies_to_empty)

theorem ay_uiac_replay_transcript
    (activatedCore : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUIACCheckerReplay activatedCore checkerReplay replayAccepted ->
    activatedCore ->
    checkerReplay := by
  intro replay
  exact replay (activatedCore -> checkerReplay)
    (fun activated_to_replay _replay_to_accept => activated_to_replay)

theorem ay_uiac_replay_accepted
    (activatedCore : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUIACCheckerReplay activatedCore checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _activated_to_replay replay_to_accept => replay_to_accept)

theorem ay_uiac_archive_digest
    (activatedCore : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) :
    AyUIACArchiveDigest activatedCore archiveDigest digestAccepted ->
    activatedCore ->
    archiveDigest := by
  intro digest
  exact digest (activatedCore -> archiveDigest)
    (fun activated_to_digest _digest_to_accept => activated_to_digest)

theorem ay_uiac_digest_accepted
    (activatedCore : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) :
    AyUIACArchiveDigest activatedCore archiveDigest digestAccepted ->
    archiveDigest ->
    digestAccepted := by
  intro digest
  exact digest (archiveDigest -> digestAccepted)
    (fun _activated_to_digest digest_to_accept => digest_to_accept)

theorem ay_uiac_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACReconstruction emptyClause visibleUnsat originalUnsat
      pruningSound ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _tail => empty_to_visible)

theorem ay_uiac_original_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACReconstruction emptyClause visibleUnsat originalUnsat
      pruningSound ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun visible_to_original _original_to_pruning =>
          visible_to_original))

theorem ay_uiac_pruning_sound
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACReconstruction emptyClause visibleUnsat originalUnsat
      pruningSound ->
    originalUnsat ->
    pruningSound := by
  intro reconstruction
  exact reconstruction (originalUnsat -> pruningSound)
    (fun _empty_to_visible tail =>
      tail (originalUnsat -> pruningSound)
        (fun _visible_to_original original_to_pruning =>
          original_to_pruning))

theorem ay_uiac_core_lineage
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    AyUIACFrameLineage assumptionFrame lineageValid assumptionCore := by
  intro accepted
  exact ay_uiac_conj_left
    (AyUIACFrameLineage assumptionFrame lineageValid assumptionCore)
    (AyUIACConj
      (AyUIACActivationMapping assumptionCore activationMap activatedCore)
      (AyUIACConj
        (AyUIACCoreCoverage activatedCore coreDependencies emptyClause)
        (AyUIACConj
          (AyUIACCheckerReplay activatedCore checkerReplay replayAccepted)
          (AyUIACConj
            (AyUIACArchiveDigest activatedCore archiveDigest digestAccepted)
            (AyUIACReconstruction emptyClause visibleUnsat originalUnsat
              pruningSound)))))
    accepted

theorem ay_uiac_core_activation
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    AyUIACActivationMapping assumptionCore activationMap activatedCore := by
  intro accepted
  exact accepted
    (AyUIACActivationMapping assumptionCore activationMap activatedCore)
    (fun _lineage tail =>
      tail (AyUIACActivationMapping assumptionCore activationMap
        activatedCore)
        (fun activation _rest => activation))

theorem ay_uiac_core_coverage
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    AyUIACCoreCoverage activatedCore coreDependencies emptyClause := by
  intro accepted
  exact accepted
    (AyUIACCoreCoverage activatedCore coreDependencies emptyClause)
    (fun _lineage tail =>
      tail (AyUIACCoreCoverage activatedCore coreDependencies emptyClause)
        (fun _activation rest =>
          rest (AyUIACCoreCoverage activatedCore coreDependencies emptyClause)
            (fun coverage _tail => coverage)))

theorem ay_uiac_core_replay
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    AyUIACCheckerReplay activatedCore checkerReplay replayAccepted := by
  intro accepted
  exact accepted (AyUIACCheckerReplay activatedCore checkerReplay
    replayAccepted)
    (fun _lineage tail =>
      tail (AyUIACCheckerReplay activatedCore checkerReplay replayAccepted)
        (fun _activation rest =>
          rest (AyUIACCheckerReplay activatedCore checkerReplay
            replayAccepted)
            (fun _coverage tail2 =>
              tail2 (AyUIACCheckerReplay activatedCore checkerReplay
                replayAccepted)
                (fun replay _tail => replay))))

theorem ay_uiac_core_digest
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    AyUIACArchiveDigest activatedCore archiveDigest digestAccepted := by
  intro accepted
  exact accepted (AyUIACArchiveDigest activatedCore archiveDigest
    digestAccepted)
    (fun _lineage tail =>
      tail (AyUIACArchiveDigest activatedCore archiveDigest digestAccepted)
        (fun _activation rest =>
          rest (AyUIACArchiveDigest activatedCore archiveDigest
            digestAccepted)
            (fun _coverage tail2 =>
              tail2 (AyUIACArchiveDigest activatedCore archiveDigest
                digestAccepted)
                (fun _replay tail3 =>
                  tail3 (AyUIACArchiveDigest activatedCore archiveDigest
                    digestAccepted)
                    (fun digest _reconstruction => digest)))))

theorem ay_uiac_core_reconstruction
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    AyUIACReconstruction emptyClause visibleUnsat originalUnsat
      pruningSound := by
  intro accepted
  exact accepted
    (AyUIACReconstruction emptyClause visibleUnsat originalUnsat
      pruningSound)
    (fun _lineage tail =>
      tail
        (AyUIACReconstruction emptyClause visibleUnsat originalUnsat
          pruningSound)
        (fun _activation rest =>
          rest
            (AyUIACReconstruction emptyClause visibleUnsat originalUnsat
              pruningSound)
            (fun _coverage tail2 =>
              tail2
                (AyUIACReconstruction emptyClause visibleUnsat originalUnsat
                  pruningSound)
                (fun _replay tail3 =>
                  tail3
                    (AyUIACReconstruction emptyClause visibleUnsat
                      originalUnsat pruningSound)
                    (fun _digest reconstruction => reconstruction)))))

theorem ay_uiac_activated_core_from_frame
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) :
    AyUIACFrameLineage assumptionFrame lineageValid assumptionCore ->
    AyUIACActivationMapping assumptionCore activationMap activatedCore ->
    activatedCore := by
  intro lineage
  intro activation
  have core : assumptionCore :=
    ay_uiac_assumption_core assumptionFrame lineageValid assumptionCore
      lineage
  have map : activationMap :=
    ay_uiac_activation_map assumptionCore activationMap activatedCore
      activation core
  exact ay_uiac_activated_core assumptionCore activationMap activatedCore
    activation map

theorem ay_uiac_core_empty_clause
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    emptyClause := by
  intro accepted
  have lineage :
      AyUIACFrameLineage assumptionFrame lineageValid assumptionCore :=
    ay_uiac_core_lineage assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  have activation :
      AyUIACActivationMapping assumptionCore activationMap activatedCore :=
    ay_uiac_core_activation assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  have coverage :
      AyUIACCoreCoverage activatedCore coreDependencies emptyClause :=
    ay_uiac_core_coverage assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  have activated : activatedCore :=
    ay_uiac_activated_core_from_frame assumptionFrame lineageValid
      assumptionCore activationMap activatedCore lineage activation
  have dependencies : coreDependencies :=
    ay_uiac_core_dependencies activatedCore coreDependencies emptyClause
      coverage activated
  exact ay_uiac_empty_clause activatedCore coreDependencies emptyClause
    coverage dependencies

theorem ay_uiac_core_replay_accepted
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    replayAccepted := by
  intro accepted
  have lineage :
      AyUIACFrameLineage assumptionFrame lineageValid assumptionCore :=
    ay_uiac_core_lineage assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  have activation :
      AyUIACActivationMapping assumptionCore activationMap activatedCore :=
    ay_uiac_core_activation assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  have replay : AyUIACCheckerReplay activatedCore checkerReplay
      replayAccepted :=
    ay_uiac_core_replay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  have activated : activatedCore :=
    ay_uiac_activated_core_from_frame assumptionFrame lineageValid
      assumptionCore activationMap activatedCore lineage activation
  have transcript : checkerReplay :=
    ay_uiac_replay_transcript activatedCore checkerReplay replayAccepted
      replay activated
  exact ay_uiac_replay_accepted activatedCore checkerReplay replayAccepted
    replay transcript

theorem ay_uiac_core_digest_accepted
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    digestAccepted := by
  intro accepted
  have lineage :
      AyUIACFrameLineage assumptionFrame lineageValid assumptionCore :=
    ay_uiac_core_lineage assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  have activation :
      AyUIACActivationMapping assumptionCore activationMap activatedCore :=
    ay_uiac_core_activation assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  have digest : AyUIACArchiveDigest activatedCore archiveDigest
      digestAccepted :=
    ay_uiac_core_digest assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  have activated : activatedCore :=
    ay_uiac_activated_core_from_frame assumptionFrame lineageValid
      assumptionCore activationMap activatedCore lineage activation
  have archive : archiveDigest :=
    ay_uiac_archive_digest activatedCore archiveDigest digestAccepted
      digest activated
  exact ay_uiac_digest_accepted activatedCore archiveDigest digestAccepted
    digest archive

theorem ay_uiac_accepted_core_original_unsat
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    originalUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_uiac_core_empty_clause assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  have reconstruction :
      AyUIACReconstruction emptyClause visibleUnsat originalUnsat
        pruningSound :=
    ay_uiac_core_reconstruction assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  have visible : visibleUnsat :=
    ay_uiac_visible_unsat emptyClause visibleUnsat originalUnsat
      pruningSound reconstruction empty
  exact ay_uiac_original_unsat emptyClause visibleUnsat originalUnsat
    pruningSound reconstruction visible

theorem ay_uiac_accepted_core_pruning_sound
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    pruningSound := by
  intro accepted
  have original : originalUnsat :=
    ay_uiac_accepted_core_original_unsat assumptionFrame lineageValid
      assumptionCore activationMap activatedCore coreDependencies emptyClause
      checkerReplay replayAccepted archiveDigest digestAccepted visibleUnsat
      originalUnsat pruningSound accepted
  have reconstruction :
      AyUIACReconstruction emptyClause visibleUnsat originalUnsat
        pruningSound :=
    ay_uiac_core_reconstruction assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound accepted
  exact ay_uiac_pruning_sound emptyClause visibleUnsat originalUnsat
    pruningSound reconstruction original

theorem ay_uiac_public_unsat_pruning_report
    (noClaim : Prop) (originalUnsat : Prop) (pruningSound : Prop) :
    originalUnsat ->
    pruningSound ->
    AyUIACPublicReport noClaim originalUnsat pruningSound := by
  intro original
  intro pruning
  exact ay_uiac_disj_right noClaim
    (AyUIACConj originalUnsat pruningSound)
    (ay_uiac_conj_intro originalUnsat pruningSound original pruning)

theorem ay_uiac_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (pruningSound : Prop) :
    noClaim -> AyUIACPublicReport noClaim originalUnsat pruningSound := by
  intro no_claim
  exact ay_uiac_disj_left noClaim
    (AyUIACConj originalUnsat pruningSound) no_claim

theorem ay_uiac_accepted_core_publish_sound
    (assumptionFrame : Prop) (lineageValid : Prop)
    (assumptionCore : Prop) (activationMap : Prop)
    (activatedCore : Prop) (coreDependencies : Prop)
    (emptyClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (pruningSound : Prop)
    (noClaim : Prop) :
    AyUIACAcceptedCoreReplay assumptionFrame lineageValid assumptionCore
      activationMap activatedCore coreDependencies emptyClause checkerReplay
      replayAccepted archiveDigest digestAccepted visibleUnsat originalUnsat
      pruningSound ->
    AyUIACPublicReport noClaim originalUnsat pruningSound := by
  intro accepted
  exact ay_uiac_public_unsat_pruning_report noClaim originalUnsat
    pruningSound
    (ay_uiac_accepted_core_original_unsat assumptionFrame lineageValid
      assumptionCore activationMap activatedCore coreDependencies emptyClause
      checkerReplay replayAccepted archiveDigest digestAccepted visibleUnsat
      originalUnsat pruningSound accepted)
    (ay_uiac_accepted_core_pruning_sound assumptionFrame lineageValid
      assumptionCore activationMap activatedCore coreDependencies emptyClause
      checkerReplay replayAccepted archiveDigest digestAccepted visibleUnsat
      originalUnsat pruningSound accepted)

theorem ay_uiac_bad_core_no_claim
    (staleFrame : Prop) (droppedActivationLiteral : Prop)
    (missingCoreDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIACBadCoreReplay staleFrame droppedActivationLiteral
      missingCoreDependency digestMismatch replayRejected noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_uiac_bad_core_recompute
    (staleFrame : Prop) (droppedActivationLiteral : Prop)
    (missingCoreDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIACBadCoreReplay staleFrame droppedActivationLiteral
      missingCoreDependency digestMismatch replayRejected noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_uiac_bad_core_public_no_claim
    (staleFrame : Prop) (droppedActivationLiteral : Prop)
    (missingCoreDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) (pruningSound : Prop) :
    AyUIACBadCoreReplay staleFrame droppedActivationLiteral
      missingCoreDependency digestMismatch replayRejected noClaim recompute ->
    AyUIACPublicReport noClaim originalUnsat pruningSound := by
  intro bad
  exact ay_uiac_public_no_claim_report noClaim originalUnsat pruningSound
    (ay_uiac_bad_core_no_claim staleFrame droppedActivationLiteral
      missingCoreDependency digestMismatch replayRejected noClaim recompute bad)

theorem ay_uiac_bad_core_cannot_publish_unsat
    (staleFrame : Prop) (droppedActivationLiteral : Prop)
    (missingCoreDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIACBadCoreReplay staleFrame droppedActivationLiteral
      missingCoreDependency digestMismatch replayRejected noClaim recompute ->
    AyUIACConj noClaim recompute := by
  intro bad
  exact bad (AyUIACConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

