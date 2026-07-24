-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT binary-clause watch replay soundness for ay. Propositions
-- stand for watched binary implications, watch lists, implication edges,
-- parent coverage, retention lineage, propagation epochs, digest membership,
-- checker replay transcripts, original fingerprint agreement, and fail-closed
-- no-claim/recompute diagnostics.

def AyUBWRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUBWRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUBWRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUBWRWatchList
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) :=
  AyUBWRConj watchReplay
    (AyUBWRConj
      (AyUBWRMap watchReplay watchListsFresh)
      (AyUBWRMap watchListsFresh watchedImplications))

def AyUBWRImplicationEdges
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) :=
  AyUBWRConj
    (AyUBWRMap watchedImplications implicationEdges)
    (AyUBWRMap implicationEdges propagatedClauses)

def AyUBWRParentCoverage
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :=
  AyUBWRConj
    (AyUBWRMap propagatedClauses parentsCovered)
    (AyUBWRMap parentsCovered emptyClause)

def AyUBWRRetentionLineage
    (propagatedClauses : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) :=
  AyUBWRConj
    (AyUBWRMap propagatedClauses retainedParents)
    (AyUBWRMap retainedParents lineageAccepted)

def AyUBWRPropagationEpoch
    (propagatedClauses : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) :=
  AyUBWRConj
    (AyUBWRMap propagatedClauses propagationEpoch)
    (AyUBWRMap propagationEpoch epochAccepted)

def AyUBWRDigestMembership
    (propagatedClauses : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :=
  AyUBWRConj
    (AyUBWRMap propagatedClauses digestMember)
    (AyUBWRMap digestMember digestAccepted)

def AyUBWRCheckerReplay
    (propagatedClauses : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUBWRConj
    (AyUBWRMap propagatedClauses checkerReplay)
    (AyUBWRMap checkerReplay replayAccepted)

def AyUBWRFingerprint
    (propagatedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUBWRConj
    (AyUBWRMap propagatedClauses fingerprintAgrees)
    (AyUBWRMap fingerprintAgrees visibleUnsat)

def AyUBWRReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUBWRConj
    (AyUBWRMap emptyClause visibleUnsat)
    (AyUBWRMap visibleUnsat originalUnsat)

def AyUBWRAcceptedReplay
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUBWRConj
    (AyUBWRWatchList watchReplay watchListsFresh watchedImplications)
    (AyUBWRConj
      (AyUBWRImplicationEdges watchedImplications implicationEdges
        propagatedClauses)
      (AyUBWRConj
        (AyUBWRParentCoverage propagatedClauses parentsCovered emptyClause)
        (AyUBWRConj
          (AyUBWRRetentionLineage propagatedClauses retainedParents
            lineageAccepted)
          (AyUBWRConj
            (AyUBWRPropagationEpoch propagatedClauses propagationEpoch
              epochAccepted)
            (AyUBWRConj
              (AyUBWRDigestMembership propagatedClauses digestMember
                digestAccepted)
              (AyUBWRConj
                (AyUBWRCheckerReplay propagatedClauses checkerReplay
                  replayAccepted)
                (AyUBWRConj
                  (AyUBWRFingerprint propagatedClauses fingerprintAgrees
                    visibleUnsat)
                  (AyUBWRReconstruction emptyClause visibleUnsat
                    originalUnsat))))))))

def AyUBWRBadReplay
    (staleWatchLists : Prop) (missingImplicationEdge : Prop)
    (parentCoverageGap : Prop) (unretainedParent : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUBWRConj
    (AyUBWRConj noClaim recompute)
    (AyUBWRDisj staleWatchLists
      (AyUBWRDisj missingImplicationEdge
        (AyUBWRDisj parentCoverageGap
          (AyUBWRDisj unretainedParent
            (AyUBWRDisj digestMismatch
              (AyUBWRDisj replayRejected fingerprintDrift))))))

def AyUBWRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUBWRDisj noClaim originalUnsat

theorem ay_ubwr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUBWRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ubwr_conj_left
    (p : Prop) (q : Prop) :
    AyUBWRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ubwr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUBWRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ubwr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUBWRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ubwr_watch_replay
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) :
    AyUBWRWatchList watchReplay watchListsFresh watchedImplications ->
    watchReplay := by
  intro watches
  exact ay_ubwr_conj_left watchReplay
    (AyUBWRConj
      (AyUBWRMap watchReplay watchListsFresh)
      (AyUBWRMap watchListsFresh watchedImplications))
    watches

theorem ay_ubwr_watch_lists_fresh
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) :
    AyUBWRWatchList watchReplay watchListsFresh watchedImplications ->
    watchListsFresh := by
  intro watches
  exact watches watchListsFresh
    (fun watch tail =>
      tail watchListsFresh
        (fun watch_to_fresh _fresh_to_implications =>
          watch_to_fresh watch))

theorem ay_ubwr_watched_implications
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) :
    AyUBWRWatchList watchReplay watchListsFresh watchedImplications ->
    watchedImplications := by
  intro watches
  exact watches watchedImplications
    (fun watch tail =>
      tail watchedImplications
        (fun watch_to_fresh fresh_to_implications =>
          fresh_to_implications (watch_to_fresh watch)))

theorem ay_ubwr_implication_edges
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) :
    AyUBWRImplicationEdges watchedImplications implicationEdges
      propagatedClauses ->
    watchedImplications ->
    implicationEdges := by
  intro edges
  exact edges (watchedImplications -> implicationEdges)
    (fun watched_to_edges _edges_to_propagated => watched_to_edges)

theorem ay_ubwr_propagated_clauses
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) :
    AyUBWRImplicationEdges watchedImplications implicationEdges
      propagatedClauses ->
    implicationEdges ->
    propagatedClauses := by
  intro edges
  exact edges (implicationEdges -> propagatedClauses)
    (fun _watched_to_edges edges_to_propagated => edges_to_propagated)

theorem ay_ubwr_parents_covered
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :
    AyUBWRParentCoverage propagatedClauses parentsCovered emptyClause ->
    propagatedClauses ->
    parentsCovered := by
  intro coverage
  exact coverage (propagatedClauses -> parentsCovered)
    (fun propagated_to_parents _parents_to_empty => propagated_to_parents)

theorem ay_ubwr_empty_clause
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :
    AyUBWRParentCoverage propagatedClauses parentsCovered emptyClause ->
    parentsCovered ->
    emptyClause := by
  intro coverage
  exact coverage (parentsCovered -> emptyClause)
    (fun _propagated_to_parents parents_to_empty => parents_to_empty)

theorem ay_ubwr_retained_parents
    (propagatedClauses : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) :
    AyUBWRRetentionLineage propagatedClauses retainedParents
      lineageAccepted ->
    propagatedClauses ->
    retainedParents := by
  intro lineage
  exact lineage (propagatedClauses -> retainedParents)
    (fun propagated_to_retained _retained_to_lineage =>
      propagated_to_retained)

theorem ay_ubwr_lineage_accepted
    (propagatedClauses : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) :
    AyUBWRRetentionLineage propagatedClauses retainedParents
      lineageAccepted ->
    retainedParents ->
    lineageAccepted := by
  intro lineage
  exact lineage (retainedParents -> lineageAccepted)
    (fun _propagated_to_retained retained_to_lineage => retained_to_lineage)

theorem ay_ubwr_propagation_epoch
    (propagatedClauses : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) :
    AyUBWRPropagationEpoch propagatedClauses propagationEpoch
      epochAccepted ->
    propagatedClauses ->
    propagationEpoch := by
  intro epoch
  exact epoch (propagatedClauses -> propagationEpoch)
    (fun propagated_to_epoch _epoch_to_accept => propagated_to_epoch)

theorem ay_ubwr_epoch_accepted
    (propagatedClauses : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) :
    AyUBWRPropagationEpoch propagatedClauses propagationEpoch
      epochAccepted ->
    propagationEpoch ->
    epochAccepted := by
  intro epoch
  exact epoch (propagationEpoch -> epochAccepted)
    (fun _propagated_to_epoch epoch_to_accept => epoch_to_accept)

theorem ay_ubwr_digest_member
    (propagatedClauses : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUBWRDigestMembership propagatedClauses digestMember
      digestAccepted ->
    propagatedClauses ->
    digestMember := by
  intro digest
  exact digest (propagatedClauses -> digestMember)
    (fun propagated_to_digest _digest_to_accept => propagated_to_digest)

theorem ay_ubwr_digest_accepted
    (propagatedClauses : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUBWRDigestMembership propagatedClauses digestMember
      digestAccepted ->
    digestMember ->
    digestAccepted := by
  intro digest
  exact digest (digestMember -> digestAccepted)
    (fun _propagated_to_digest digest_to_accept => digest_to_accept)

theorem ay_ubwr_replay_transcript
    (propagatedClauses : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUBWRCheckerReplay propagatedClauses checkerReplay replayAccepted ->
    propagatedClauses ->
    checkerReplay := by
  intro replay
  exact replay (propagatedClauses -> checkerReplay)
    (fun propagated_to_replay _replay_to_accept => propagated_to_replay)

theorem ay_ubwr_replay_accepted
    (propagatedClauses : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUBWRCheckerReplay propagatedClauses checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _propagated_to_replay replay_to_accept => replay_to_accept)

theorem ay_ubwr_fingerprint_agrees
    (propagatedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUBWRFingerprint propagatedClauses fingerprintAgrees visibleUnsat ->
    propagatedClauses ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (propagatedClauses -> fingerprintAgrees)
    (fun propagated_to_fingerprint _fingerprint_to_visible =>
      propagated_to_fingerprint)

theorem ay_ubwr_visible_from_fingerprint
    (propagatedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUBWRFingerprint propagatedClauses fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _propagated_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_ubwr_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUBWRReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_ubwr_original_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUBWRReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_ubwr_accepted_watches
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUBWRWatchList watchReplay watchListsFresh watchedImplications := by
  intro accepted
  exact ay_ubwr_conj_left
    (AyUBWRWatchList watchReplay watchListsFresh watchedImplications)
    (AyUBWRConj
      (AyUBWRImplicationEdges watchedImplications implicationEdges
        propagatedClauses)
      (AyUBWRConj
        (AyUBWRParentCoverage propagatedClauses parentsCovered emptyClause)
        (AyUBWRConj
          (AyUBWRRetentionLineage propagatedClauses retainedParents
            lineageAccepted)
          (AyUBWRConj
            (AyUBWRPropagationEpoch propagatedClauses propagationEpoch
              epochAccepted)
            (AyUBWRConj
              (AyUBWRDigestMembership propagatedClauses digestMember
                digestAccepted)
              (AyUBWRConj
                (AyUBWRCheckerReplay propagatedClauses checkerReplay
                  replayAccepted)
                (AyUBWRConj
                  (AyUBWRFingerprint propagatedClauses fingerprintAgrees
                    visibleUnsat)
                  (AyUBWRReconstruction emptyClause visibleUnsat
                    originalUnsat))))))))
    accepted

theorem ay_ubwr_accepted_edges
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUBWRImplicationEdges watchedImplications implicationEdges
      propagatedClauses := by
  intro accepted
  exact accepted
    (AyUBWRImplicationEdges watchedImplications implicationEdges
      propagatedClauses)
    (fun _watches tail =>
      tail
        (AyUBWRImplicationEdges watchedImplications implicationEdges
          propagatedClauses)
        (fun edges _rest => edges))

theorem ay_ubwr_accepted_coverage
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUBWRParentCoverage propagatedClauses parentsCovered emptyClause := by
  intro accepted
  exact accepted
    (AyUBWRParentCoverage propagatedClauses parentsCovered emptyClause)
    (fun _watches tail =>
      tail (AyUBWRParentCoverage propagatedClauses parentsCovered emptyClause)
        (fun _edges rest =>
          rest (AyUBWRParentCoverage propagatedClauses parentsCovered
            emptyClause)
            (fun coverage _tail => coverage)))

theorem ay_ubwr_accepted_lineage
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUBWRRetentionLineage propagatedClauses retainedParents
      lineageAccepted := by
  intro accepted
  exact accepted
    (AyUBWRRetentionLineage propagatedClauses retainedParents
      lineageAccepted)
    (fun _watches tail =>
      tail
        (AyUBWRRetentionLineage propagatedClauses retainedParents
          lineageAccepted)
        (fun _edges rest =>
          rest
            (AyUBWRRetentionLineage propagatedClauses retainedParents
              lineageAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyUBWRRetentionLineage propagatedClauses retainedParents
                  lineageAccepted)
                (fun lineage _tail => lineage))))

theorem ay_ubwr_accepted_epoch
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUBWRPropagationEpoch propagatedClauses propagationEpoch
      epochAccepted := by
  intro accepted
  exact accepted
    (AyUBWRPropagationEpoch propagatedClauses propagationEpoch
      epochAccepted)
    (fun _watches tail =>
      tail
        (AyUBWRPropagationEpoch propagatedClauses propagationEpoch
          epochAccepted)
        (fun _edges rest =>
          rest
            (AyUBWRPropagationEpoch propagatedClauses propagationEpoch
              epochAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyUBWRPropagationEpoch propagatedClauses propagationEpoch
                  epochAccepted)
                (fun _lineage tail3 =>
                  tail3
                    (AyUBWRPropagationEpoch propagatedClauses
                      propagationEpoch epochAccepted)
                    (fun epoch _tail => epoch)))))

theorem ay_ubwr_accepted_digest
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUBWRDigestMembership propagatedClauses digestMember digestAccepted := by
  intro accepted
  exact accepted
    (AyUBWRDigestMembership propagatedClauses digestMember digestAccepted)
    (fun _watches tail =>
      tail (AyUBWRDigestMembership propagatedClauses digestMember
        digestAccepted)
        (fun _edges rest =>
          rest (AyUBWRDigestMembership propagatedClauses digestMember
            digestAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyUBWRDigestMembership propagatedClauses digestMember
                  digestAccepted)
                (fun _lineage tail3 =>
                  tail3
                    (AyUBWRDigestMembership propagatedClauses digestMember
                      digestAccepted)
                    (fun _epoch tail4 =>
                      tail4
                        (AyUBWRDigestMembership propagatedClauses
                          digestMember digestAccepted)
                        (fun digest _tail => digest))))))

theorem ay_ubwr_accepted_replay_witness
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUBWRCheckerReplay propagatedClauses checkerReplay replayAccepted := by
  intro accepted
  exact accepted
    (AyUBWRCheckerReplay propagatedClauses checkerReplay replayAccepted)
    (fun _watches tail =>
      tail (AyUBWRCheckerReplay propagatedClauses checkerReplay replayAccepted)
        (fun _edges rest =>
          rest (AyUBWRCheckerReplay propagatedClauses checkerReplay
            replayAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyUBWRCheckerReplay propagatedClauses checkerReplay
                  replayAccepted)
                (fun _lineage tail3 =>
                  tail3
                    (AyUBWRCheckerReplay propagatedClauses checkerReplay
                      replayAccepted)
                    (fun _epoch tail4 =>
                      tail4
                        (AyUBWRCheckerReplay propagatedClauses checkerReplay
                          replayAccepted)
                        (fun _digest tail5 =>
                          tail5
                            (AyUBWRCheckerReplay propagatedClauses
                              checkerReplay replayAccepted)
                            (fun replay _tail => replay)))))))

theorem ay_ubwr_accepted_fingerprint
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUBWRFingerprint propagatedClauses fingerprintAgrees visibleUnsat := by
  intro accepted
  exact accepted
    (AyUBWRFingerprint propagatedClauses fingerprintAgrees visibleUnsat)
    (fun _watches tail =>
      tail (AyUBWRFingerprint propagatedClauses fingerprintAgrees
        visibleUnsat)
        (fun _edges rest =>
          rest (AyUBWRFingerprint propagatedClauses fingerprintAgrees
            visibleUnsat)
            (fun _coverage tail2 =>
              tail2
                (AyUBWRFingerprint propagatedClauses fingerprintAgrees
                  visibleUnsat)
                (fun _lineage tail3 =>
                  tail3
                    (AyUBWRFingerprint propagatedClauses fingerprintAgrees
                      visibleUnsat)
                    (fun _epoch tail4 =>
                      tail4
                        (AyUBWRFingerprint propagatedClauses
                          fingerprintAgrees visibleUnsat)
                        (fun _digest tail5 =>
                          tail5
                            (AyUBWRFingerprint propagatedClauses
                              fingerprintAgrees visibleUnsat)
                            (fun _replay tail6 =>
                              tail6
                                (AyUBWRFingerprint propagatedClauses
                                  fingerprintAgrees visibleUnsat)
                                (fun fingerprint _reconstruction =>
                                  fingerprint))))))))

theorem ay_ubwr_accepted_reconstruction
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUBWRReconstruction emptyClause visibleUnsat originalUnsat := by
  intro accepted
  exact accepted (AyUBWRReconstruction emptyClause visibleUnsat
    originalUnsat)
    (fun _watches tail =>
      tail (AyUBWRReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _edges rest =>
          rest (AyUBWRReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _coverage tail2 =>
              tail2
                (AyUBWRReconstruction emptyClause visibleUnsat originalUnsat)
                (fun _lineage tail3 =>
                  tail3
                    (AyUBWRReconstruction emptyClause visibleUnsat
                      originalUnsat)
                    (fun _epoch tail4 =>
                      tail4
                        (AyUBWRReconstruction emptyClause visibleUnsat
                          originalUnsat)
                        (fun _digest tail5 =>
                          tail5
                            (AyUBWRReconstruction emptyClause visibleUnsat
                              originalUnsat)
                            (fun _replay tail6 =>
                              tail6
                                (AyUBWRReconstruction emptyClause
                                  visibleUnsat originalUnsat)
                                (fun _fingerprint reconstruction =>
                                  reconstruction))))))))

theorem ay_ubwr_accepted_propagated_clauses
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    propagatedClauses := by
  intro accepted
  have watches :
      AyUBWRWatchList watchReplay watchListsFresh watchedImplications :=
    ay_ubwr_accepted_watches watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have edges :
      AyUBWRImplicationEdges watchedImplications implicationEdges
        propagatedClauses :=
    ay_ubwr_accepted_edges watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have watched : watchedImplications :=
    ay_ubwr_watched_implications watchReplay watchListsFresh
      watchedImplications watches
  have edge : implicationEdges :=
    ay_ubwr_implication_edges watchedImplications implicationEdges
      propagatedClauses edges watched
  exact ay_ubwr_propagated_clauses watchedImplications implicationEdges
    propagatedClauses edges edge

theorem ay_ubwr_accepted_empty_clause
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    emptyClause := by
  intro accepted
  have propagated : propagatedClauses :=
    ay_ubwr_accepted_propagated_clauses watchReplay watchListsFresh
      watchedImplications implicationEdges propagatedClauses parentsCovered
      emptyClause retainedParents lineageAccepted propagationEpoch
      epochAccepted digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have coverage :
      AyUBWRParentCoverage propagatedClauses parentsCovered emptyClause :=
    ay_ubwr_accepted_coverage watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have parents : parentsCovered :=
    ay_ubwr_parents_covered propagatedClauses parentsCovered emptyClause
      coverage propagated
  exact ay_ubwr_empty_clause propagatedClauses parentsCovered emptyClause
    coverage parents

theorem ay_ubwr_accepted_lineage_valid
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    lineageAccepted := by
  intro accepted
  have propagated : propagatedClauses :=
    ay_ubwr_accepted_propagated_clauses watchReplay watchListsFresh
      watchedImplications implicationEdges propagatedClauses parentsCovered
      emptyClause retainedParents lineageAccepted propagationEpoch
      epochAccepted digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have lineage :
      AyUBWRRetentionLineage propagatedClauses retainedParents
        lineageAccepted :=
    ay_ubwr_accepted_lineage watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have retained : retainedParents :=
    ay_ubwr_retained_parents propagatedClauses retainedParents
      lineageAccepted lineage propagated
  exact ay_ubwr_lineage_accepted propagatedClauses retainedParents
    lineageAccepted lineage retained

theorem ay_ubwr_accepted_epoch_valid
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    epochAccepted := by
  intro accepted
  have propagated : propagatedClauses :=
    ay_ubwr_accepted_propagated_clauses watchReplay watchListsFresh
      watchedImplications implicationEdges propagatedClauses parentsCovered
      emptyClause retainedParents lineageAccepted propagationEpoch
      epochAccepted digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have epoch :
      AyUBWRPropagationEpoch propagatedClauses propagationEpoch
        epochAccepted :=
    ay_ubwr_accepted_epoch watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have epoch_value : propagationEpoch :=
    ay_ubwr_propagation_epoch propagatedClauses propagationEpoch
      epochAccepted epoch propagated
  exact ay_ubwr_epoch_accepted propagatedClauses propagationEpoch
    epochAccepted epoch epoch_value

theorem ay_ubwr_accepted_digest_valid
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    digestAccepted := by
  intro accepted
  have propagated : propagatedClauses :=
    ay_ubwr_accepted_propagated_clauses watchReplay watchListsFresh
      watchedImplications implicationEdges propagatedClauses parentsCovered
      emptyClause retainedParents lineageAccepted propagationEpoch
      epochAccepted digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have digest :
      AyUBWRDigestMembership propagatedClauses digestMember digestAccepted :=
    ay_ubwr_accepted_digest watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have member : digestMember :=
    ay_ubwr_digest_member propagatedClauses digestMember digestAccepted
      digest propagated
  exact ay_ubwr_digest_accepted propagatedClauses digestMember
    digestAccepted digest member

theorem ay_ubwr_accepted_replay
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    replayAccepted := by
  intro accepted
  have propagated : propagatedClauses :=
    ay_ubwr_accepted_propagated_clauses watchReplay watchListsFresh
      watchedImplications implicationEdges propagatedClauses parentsCovered
      emptyClause retainedParents lineageAccepted propagationEpoch
      epochAccepted digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have replay :
      AyUBWRCheckerReplay propagatedClauses checkerReplay replayAccepted :=
    ay_ubwr_accepted_replay_witness watchReplay watchListsFresh
      watchedImplications implicationEdges propagatedClauses parentsCovered
      emptyClause retainedParents lineageAccepted propagationEpoch
      epochAccepted digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have transcript : checkerReplay :=
    ay_ubwr_replay_transcript propagatedClauses checkerReplay replayAccepted
      replay propagated
  exact ay_ubwr_replay_accepted propagatedClauses checkerReplay replayAccepted
    replay transcript

theorem ay_ubwr_accepted_original_unsat
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_ubwr_accepted_empty_clause watchReplay watchListsFresh
      watchedImplications implicationEdges propagatedClauses parentsCovered
      emptyClause retainedParents lineageAccepted propagationEpoch
      epochAccepted digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have reconstruction :
      AyUBWRReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_ubwr_accepted_reconstruction watchReplay watchListsFresh
      watchedImplications implicationEdges propagatedClauses parentsCovered
      emptyClause retainedParents lineageAccepted propagationEpoch
      epochAccepted digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have visible : visibleUnsat :=
    ay_ubwr_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_ubwr_original_unsat emptyClause visibleUnsat originalUnsat
    reconstruction visible

theorem ay_ubwr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUBWRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ubwr_disj_right noClaim originalUnsat unsat

theorem ay_ubwr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUBWRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ubwr_disj_left noClaim originalUnsat no_claim

theorem ay_ubwr_accepted_watch_replay_publish_sound
    (watchReplay : Prop) (watchListsFresh : Prop)
    (watchedImplications : Prop) (implicationEdges : Prop)
    (propagatedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUBWRAcceptedReplay watchReplay watchListsFresh watchedImplications
      implicationEdges propagatedClauses parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUBWRPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_ubwr_public_unsat_report noClaim originalUnsat
    (ay_ubwr_accepted_original_unsat watchReplay watchListsFresh
      watchedImplications implicationEdges propagatedClauses parentsCovered
      emptyClause retainedParents lineageAccepted propagationEpoch
      epochAccepted digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted)

theorem ay_ubwr_bad_replay_no_claim
    (staleWatchLists : Prop) (missingImplicationEdge : Prop)
    (parentCoverageGap : Prop) (unretainedParent : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUBWRBadReplay staleWatchLists missingImplicationEdge parentCoverageGap
      unretainedParent digestMismatch replayRejected fingerprintDrift
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_ubwr_bad_replay_recompute
    (staleWatchLists : Prop) (missingImplicationEdge : Prop)
    (parentCoverageGap : Prop) (unretainedParent : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUBWRBadReplay staleWatchLists missingImplicationEdge parentCoverageGap
      unretainedParent digestMismatch replayRejected fingerprintDrift
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_ubwr_bad_replay_public_no_claim
    (staleWatchLists : Prop) (missingImplicationEdge : Prop)
    (parentCoverageGap : Prop) (unretainedParent : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUBWRBadReplay staleWatchLists missingImplicationEdge parentCoverageGap
      unretainedParent digestMismatch replayRejected fingerprintDrift
      noClaim recompute ->
    AyUBWRPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ubwr_public_no_claim_report noClaim originalUnsat
    (ay_ubwr_bad_replay_no_claim staleWatchLists missingImplicationEdge
      parentCoverageGap unretainedParent digestMismatch replayRejected
      fingerprintDrift noClaim recompute bad)

theorem ay_ubwr_bad_replay_cannot_publish
    (staleWatchLists : Prop) (missingImplicationEdge : Prop)
    (parentCoverageGap : Prop) (unretainedParent : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUBWRBadReplay staleWatchLists missingImplicationEdge parentCoverageGap
      unretainedParent digestMismatch replayRejected fingerprintDrift
      noClaim recompute ->
    AyUBWRConj noClaim recompute := by
  intro bad
  exact bad (AyUBWRConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)
