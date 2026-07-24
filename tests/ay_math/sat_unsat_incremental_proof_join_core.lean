-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded incremental UNSAT proof-fragment join soundness for ay.
-- Propositions stand for fragment manifests, assumption/cube frame lineage,
-- dependency coverage, empty-clause reachability, digest membership, checker
-- replay, original UNSAT reconstruction, and fail-closed diagnostics.

def AyUIPJConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUIPJDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUIPJMap (source : Prop) (target : Prop) :=
  source -> target

def AyUIPJFragmentManifest
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) :=
  AyUIPJConj fragmentManifest
    (AyUIPJConj
      (AyUIPJMap fragmentManifest fragmentPresent)
      (AyUIPJMap fragmentPresent joinedFragments))

def AyUIPJFrameLineage
    (assumptionFrame : Prop) (frameConsistent : Prop)
    (joinedFragments : Prop) :=
  AyUIPJConj assumptionFrame
    (AyUIPJConj
      (AyUIPJMap assumptionFrame frameConsistent)
      (AyUIPJMap frameConsistent joinedFragments))

def AyUIPJDependencyCoverage
    (joinedFragments : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :=
  AyUIPJConj
    (AyUIPJMap joinedFragments dependencyCoverage)
    (AyUIPJMap dependencyCoverage emptyClause)

def AyUIPJDigestMembership
    (joinedFragments : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :=
  AyUIPJConj
    (AyUIPJMap joinedFragments digestMember)
    (AyUIPJMap digestMember digestAccepted)

def AyUIPJCheckerReplay
    (joinedFragments : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUIPJConj
    (AyUIPJMap joinedFragments checkerReplay)
    (AyUIPJMap checkerReplay replayAccepted)

def AyUIPJReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUIPJConj
    (AyUIPJMap emptyClause visibleUnsat)
    (AyUIPJMap visibleUnsat originalUnsat)

def AyUIPJAcceptedJoin
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUIPJConj
    (AyUIPJFragmentManifest fragmentManifest fragmentPresent
      joinedFragments)
    (AyUIPJConj
      (AyUIPJFrameLineage assumptionFrame frameConsistent joinedFragments)
      (AyUIPJConj
        (AyUIPJDependencyCoverage joinedFragments dependencyCoverage
          emptyClause)
        (AyUIPJConj
          (AyUIPJDigestMembership joinedFragments digestMember
            digestAccepted)
          (AyUIPJConj
            (AyUIPJCheckerReplay joinedFragments checkerReplay
              replayAccepted)
            (AyUIPJReconstruction emptyClause visibleUnsat
              originalUnsat)))))

def AyUIPJBadJoin
    (missingFragment : Prop) (inconsistentFrame : Prop)
    (uncoveredDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUIPJConj
    (AyUIPJConj noClaim recompute)
    (AyUIPJDisj missingFragment
      (AyUIPJDisj inconsistentFrame
        (AyUIPJDisj uncoveredDependency
          (AyUIPJDisj digestMismatch replayRejected))))

def AyUIPJPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUIPJDisj noClaim originalUnsat

theorem ay_uipj_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUIPJConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uipj_conj_left
    (p : Prop) (q : Prop) :
    AyUIPJConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uipj_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUIPJDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uipj_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUIPJDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uipj_manifest
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) :
    AyUIPJFragmentManifest fragmentManifest fragmentPresent
      joinedFragments ->
    fragmentManifest := by
  intro manifest
  exact ay_uipj_conj_left fragmentManifest
    (AyUIPJConj
      (AyUIPJMap fragmentManifest fragmentPresent)
      (AyUIPJMap fragmentPresent joinedFragments))
    manifest

theorem ay_uipj_fragment_present
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) :
    AyUIPJFragmentManifest fragmentManifest fragmentPresent
      joinedFragments ->
    fragmentPresent := by
  intro manifest
  exact manifest fragmentPresent
    (fun manifest_entry tail =>
      tail fragmentPresent
        (fun manifest_to_present _present_to_joined =>
          manifest_to_present manifest_entry))

theorem ay_uipj_joined_from_manifest
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) :
    AyUIPJFragmentManifest fragmentManifest fragmentPresent
      joinedFragments ->
    joinedFragments := by
  intro manifest
  exact manifest joinedFragments
    (fun manifest_entry tail =>
      tail joinedFragments
        (fun manifest_to_present present_to_joined =>
          present_to_joined (manifest_to_present manifest_entry)))

theorem ay_uipj_frame
    (assumptionFrame : Prop) (frameConsistent : Prop)
    (joinedFragments : Prop) :
    AyUIPJFrameLineage assumptionFrame frameConsistent joinedFragments ->
    assumptionFrame := by
  intro lineage
  exact ay_uipj_conj_left assumptionFrame
    (AyUIPJConj
      (AyUIPJMap assumptionFrame frameConsistent)
      (AyUIPJMap frameConsistent joinedFragments))
    lineage

theorem ay_uipj_frame_consistent
    (assumptionFrame : Prop) (frameConsistent : Prop)
    (joinedFragments : Prop) :
    AyUIPJFrameLineage assumptionFrame frameConsistent joinedFragments ->
    frameConsistent := by
  intro lineage
  exact lineage frameConsistent
    (fun frame tail =>
      tail frameConsistent
        (fun frame_to_consistent _consistent_to_joined =>
          frame_to_consistent frame))

theorem ay_uipj_joined_from_frame
    (assumptionFrame : Prop) (frameConsistent : Prop)
    (joinedFragments : Prop) :
    AyUIPJFrameLineage assumptionFrame frameConsistent joinedFragments ->
    joinedFragments := by
  intro lineage
  exact lineage joinedFragments
    (fun frame tail =>
      tail joinedFragments
        (fun frame_to_consistent consistent_to_joined =>
          consistent_to_joined (frame_to_consistent frame)))

theorem ay_uipj_dependency_coverage
    (joinedFragments : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUIPJDependencyCoverage joinedFragments dependencyCoverage
      emptyClause ->
    joinedFragments ->
    dependencyCoverage := by
  intro coverage
  exact coverage (joinedFragments -> dependencyCoverage)
    (fun joined_to_coverage _coverage_to_empty => joined_to_coverage)

theorem ay_uipj_empty_clause
    (joinedFragments : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUIPJDependencyCoverage joinedFragments dependencyCoverage
      emptyClause ->
    dependencyCoverage ->
    emptyClause := by
  intro coverage
  exact coverage (dependencyCoverage -> emptyClause)
    (fun _joined_to_coverage coverage_to_empty => coverage_to_empty)

theorem ay_uipj_digest_member
    (joinedFragments : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUIPJDigestMembership joinedFragments digestMember digestAccepted ->
    joinedFragments ->
    digestMember := by
  intro digest
  exact digest (joinedFragments -> digestMember)
    (fun joined_to_digest _digest_to_accept => joined_to_digest)

theorem ay_uipj_digest_accepted
    (joinedFragments : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUIPJDigestMembership joinedFragments digestMember digestAccepted ->
    digestMember ->
    digestAccepted := by
  intro digest
  exact digest (digestMember -> digestAccepted)
    (fun _joined_to_digest digest_to_accept => digest_to_accept)

theorem ay_uipj_replay_transcript
    (joinedFragments : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUIPJCheckerReplay joinedFragments checkerReplay replayAccepted ->
    joinedFragments ->
    checkerReplay := by
  intro replay
  exact replay (joinedFragments -> checkerReplay)
    (fun joined_to_replay _replay_to_accept => joined_to_replay)

theorem ay_uipj_replay_accepted
    (joinedFragments : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUIPJCheckerReplay joinedFragments checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _joined_to_replay replay_to_accept => replay_to_accept)

theorem ay_uipj_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_uipj_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_uipj_join_manifest
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUIPJFragmentManifest fragmentManifest fragmentPresent
      joinedFragments := by
  intro accepted
  exact ay_uipj_conj_left
    (AyUIPJFragmentManifest fragmentManifest fragmentPresent
      joinedFragments)
    (AyUIPJConj
      (AyUIPJFrameLineage assumptionFrame frameConsistent joinedFragments)
      (AyUIPJConj
        (AyUIPJDependencyCoverage joinedFragments dependencyCoverage
          emptyClause)
        (AyUIPJConj
          (AyUIPJDigestMembership joinedFragments digestMember
            digestAccepted)
          (AyUIPJConj
            (AyUIPJCheckerReplay joinedFragments checkerReplay
              replayAccepted)
            (AyUIPJReconstruction emptyClause visibleUnsat
              originalUnsat)))))
    accepted

theorem ay_uipj_join_lineage
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUIPJFrameLineage assumptionFrame frameConsistent joinedFragments := by
  intro accepted
  exact accepted
    (AyUIPJFrameLineage assumptionFrame frameConsistent joinedFragments)
    (fun _manifest tail =>
      tail (AyUIPJFrameLineage assumptionFrame frameConsistent
        joinedFragments)
        (fun lineage _rest => lineage))

theorem ay_uipj_join_coverage
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUIPJDependencyCoverage joinedFragments dependencyCoverage
      emptyClause := by
  intro accepted
  exact accepted
    (AyUIPJDependencyCoverage joinedFragments dependencyCoverage
      emptyClause)
    (fun _manifest tail =>
      tail
        (AyUIPJDependencyCoverage joinedFragments dependencyCoverage
          emptyClause)
        (fun _lineage rest =>
          rest
            (AyUIPJDependencyCoverage joinedFragments dependencyCoverage
              emptyClause)
            (fun coverage _tail => coverage)))

theorem ay_uipj_join_digest
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUIPJDigestMembership joinedFragments digestMember digestAccepted := by
  intro accepted
  exact accepted
    (AyUIPJDigestMembership joinedFragments digestMember digestAccepted)
    (fun _manifest tail =>
      tail (AyUIPJDigestMembership joinedFragments digestMember
        digestAccepted)
        (fun _lineage rest =>
          rest (AyUIPJDigestMembership joinedFragments digestMember
            digestAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyUIPJDigestMembership joinedFragments digestMember
                  digestAccepted)
                (fun digest _tail => digest))))

theorem ay_uipj_join_replay
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUIPJCheckerReplay joinedFragments checkerReplay replayAccepted := by
  intro accepted
  exact accepted
    (AyUIPJCheckerReplay joinedFragments checkerReplay replayAccepted)
    (fun _manifest tail =>
      tail (AyUIPJCheckerReplay joinedFragments checkerReplay replayAccepted)
        (fun _lineage rest =>
          rest (AyUIPJCheckerReplay joinedFragments checkerReplay
            replayAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyUIPJCheckerReplay joinedFragments checkerReplay
                  replayAccepted)
                (fun _digest tail3 =>
                  tail3
                    (AyUIPJCheckerReplay joinedFragments checkerReplay
                      replayAccepted)
                    (fun replay _reconstruction => replay)))))

theorem ay_uipj_join_reconstruction
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUIPJReconstruction emptyClause visibleUnsat originalUnsat := by
  intro accepted
  exact accepted (AyUIPJReconstruction emptyClause visibleUnsat
    originalUnsat)
    (fun _manifest tail =>
      tail (AyUIPJReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _lineage rest =>
          rest (AyUIPJReconstruction emptyClause visibleUnsat
            originalUnsat)
            (fun _coverage tail2 =>
              tail2
                (AyUIPJReconstruction emptyClause visibleUnsat
                  originalUnsat)
                (fun _digest tail3 =>
                  tail3
                    (AyUIPJReconstruction emptyClause visibleUnsat
                      originalUnsat)
                    (fun _replay reconstruction => reconstruction)))))

theorem ay_uipj_joined_fragments
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    joinedFragments := by
  intro accepted
  have manifest :
      AyUIPJFragmentManifest fragmentManifest fragmentPresent
        joinedFragments :=
    ay_uipj_join_manifest fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  exact ay_uipj_joined_from_manifest fragmentManifest fragmentPresent
    joinedFragments manifest

theorem ay_uipj_join_empty_clause
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    emptyClause := by
  intro accepted
  have joined : joinedFragments :=
    ay_uipj_joined_fragments fragmentManifest fragmentPresent
      joinedFragments assumptionFrame frameConsistent dependencyCoverage
      emptyClause digestMember digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have coverage :
      AyUIPJDependencyCoverage joinedFragments dependencyCoverage
        emptyClause :=
    ay_uipj_join_coverage fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have covered : dependencyCoverage :=
    ay_uipj_dependency_coverage joinedFragments dependencyCoverage
      emptyClause coverage joined
  exact ay_uipj_empty_clause joinedFragments dependencyCoverage emptyClause
    coverage covered

theorem ay_uipj_join_digest_accepted
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    digestAccepted := by
  intro accepted
  have joined : joinedFragments :=
    ay_uipj_joined_fragments fragmentManifest fragmentPresent
      joinedFragments assumptionFrame frameConsistent dependencyCoverage
      emptyClause digestMember digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have digest :
      AyUIPJDigestMembership joinedFragments digestMember digestAccepted :=
    ay_uipj_join_digest fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have member : digestMember :=
    ay_uipj_digest_member joinedFragments digestMember digestAccepted
      digest joined
  exact ay_uipj_digest_accepted joinedFragments digestMember digestAccepted
    digest member

theorem ay_uipj_join_replay_accepted
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    replayAccepted := by
  intro accepted
  have joined : joinedFragments :=
    ay_uipj_joined_fragments fragmentManifest fragmentPresent
      joinedFragments assumptionFrame frameConsistent dependencyCoverage
      emptyClause digestMember digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have replay : AyUIPJCheckerReplay joinedFragments checkerReplay
      replayAccepted :=
    ay_uipj_join_replay fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have transcript : checkerReplay :=
    ay_uipj_replay_transcript joinedFragments checkerReplay replayAccepted
      replay joined
  exact ay_uipj_replay_accepted joinedFragments checkerReplay
    replayAccepted replay transcript

theorem ay_uipj_accepted_join_original_unsat
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_uipj_join_empty_clause fragmentManifest fragmentPresent
      joinedFragments assumptionFrame frameConsistent dependencyCoverage
      emptyClause digestMember digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have reconstruction :
      AyUIPJReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_uipj_join_reconstruction fragmentManifest fragmentPresent
      joinedFragments assumptionFrame frameConsistent dependencyCoverage
      emptyClause digestMember digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted
  have visible : visibleUnsat :=
    ay_uipj_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_uipj_original_unsat_from_visible emptyClause visibleUnsat
    originalUnsat reconstruction visible

theorem ay_uipj_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUIPJPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_uipj_disj_right noClaim originalUnsat unsat

theorem ay_uipj_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUIPJPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_uipj_disj_left noClaim originalUnsat no_claim

theorem ay_uipj_accepted_join_publish_sound
    (fragmentManifest : Prop) (fragmentPresent : Prop)
    (joinedFragments : Prop) (assumptionFrame : Prop)
    (frameConsistent : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyUIPJAcceptedJoin fragmentManifest fragmentPresent joinedFragments
      assumptionFrame frameConsistent dependencyCoverage emptyClause
      digestMember digestAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat ->
    AyUIPJPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_uipj_public_unsat_report noClaim originalUnsat
    (ay_uipj_accepted_join_original_unsat fragmentManifest fragmentPresent
      joinedFragments assumptionFrame frameConsistent dependencyCoverage
      emptyClause digestMember digestAccepted checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted)

theorem ay_uipj_bad_join_no_claim
    (missingFragment : Prop) (inconsistentFrame : Prop)
    (uncoveredDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIPJBadJoin missingFragment inconsistentFrame uncoveredDependency
      digestMismatch replayRejected noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_uipj_bad_join_recompute
    (missingFragment : Prop) (inconsistentFrame : Prop)
    (uncoveredDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIPJBadJoin missingFragment inconsistentFrame uncoveredDependency
      digestMismatch replayRejected noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_uipj_bad_join_public_no_claim
    (missingFragment : Prop) (inconsistentFrame : Prop)
    (uncoveredDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUIPJBadJoin missingFragment inconsistentFrame uncoveredDependency
      digestMismatch replayRejected noClaim recompute ->
    AyUIPJPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_uipj_public_no_claim_report noClaim originalUnsat
    (ay_uipj_bad_join_no_claim missingFragment inconsistentFrame
      uncoveredDependency digestMismatch replayRejected noClaim recompute bad)

theorem ay_uipj_bad_join_cannot_publish
    (missingFragment : Prop) (inconsistentFrame : Prop)
    (uncoveredDependency : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIPJBadJoin missingFragment inconsistentFrame uncoveredDependency
      digestMismatch replayRejected noClaim recompute ->
    AyUIPJConj noClaim recompute := by
  intro bad
  exact bad (AyUIPJConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

