-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT unit-propagation trace-slice soundness for ay.
-- Propositions stand for slice boundaries, unit clauses, implication edges,
-- parent coverage, retention lineage, propagation epochs, digest membership,
-- checker replay transcripts, original fingerprint agreement, and fail-closed
-- no-claim/recompute diagnostics.

def AyUPTSConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPTSDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPTSMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPTSSliceBoundary
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) :=
  AyUPTSConj traceSlice
    (AyUPTSConj
      (AyUPTSMap traceSlice boundaryStable)
      (AyUPTSMap boundaryStable unitClauses))

def AyUPTSImplicationEdges
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) :=
  AyUPTSConj
    (AyUPTSMap unitClauses implicationEdges)
    (AyUPTSMap implicationEdges propagatedTrace)

def AyUPTSParentCoverage
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :=
  AyUPTSConj
    (AyUPTSMap propagatedTrace parentsCovered)
    (AyUPTSMap parentsCovered emptyClause)

def AyUPTSRetentionLineage
    (propagatedTrace : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) :=
  AyUPTSConj
    (AyUPTSMap propagatedTrace retainedParents)
    (AyUPTSMap retainedParents lineageAccepted)

def AyUPTSEpoch
    (propagatedTrace : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) :=
  AyUPTSConj
    (AyUPTSMap propagatedTrace propagationEpoch)
    (AyUPTSMap propagationEpoch epochAccepted)

def AyUPTSDigest
    (propagatedTrace : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :=
  AyUPTSConj
    (AyUPTSMap propagatedTrace digestMember)
    (AyUPTSMap digestMember digestAccepted)

def AyUPTSReplay
    (propagatedTrace : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUPTSConj
    (AyUPTSMap propagatedTrace checkerReplay)
    (AyUPTSMap checkerReplay replayAccepted)

def AyUPTSFingerprint
    (propagatedTrace : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUPTSConj
    (AyUPTSMap propagatedTrace fingerprintAgrees)
    (AyUPTSMap fingerprintAgrees visibleUnsat)

def AyUPTSReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUPTSConj
    (AyUPTSMap emptyClause visibleUnsat)
    (AyUPTSMap visibleUnsat originalUnsat)

def AyUPTSAcceptedSlice
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPTSConj
    (AyUPTSSliceBoundary traceSlice boundaryStable unitClauses)
    (AyUPTSConj
      (AyUPTSImplicationEdges unitClauses implicationEdges propagatedTrace)
      (AyUPTSConj
        (AyUPTSParentCoverage propagatedTrace parentsCovered emptyClause)
        (AyUPTSConj
          (AyUPTSRetentionLineage propagatedTrace retainedParents
            lineageAccepted)
          (AyUPTSConj
            (AyUPTSEpoch propagatedTrace propagationEpoch epochAccepted)
            (AyUPTSConj
              (AyUPTSDigest propagatedTrace digestMember digestAccepted)
              (AyUPTSConj
                (AyUPTSReplay propagatedTrace checkerReplay replayAccepted)
                (AyUPTSConj
                  (AyUPTSFingerprint propagatedTrace fingerprintAgrees
                    visibleUnsat)
                  (AyUPTSReconstruction emptyClause visibleUnsat
                    originalUnsat))))))))

def AyUPTSBadSlice
    (boundaryDrift : Prop) (missingUnitClause : Prop)
    (missingImplicationEdge : Prop) (parentCoverageGap : Prop)
    (unretainedParent : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUPTSConj
    (AyUPTSConj noClaim recompute)
    (AyUPTSDisj boundaryDrift
      (AyUPTSDisj missingUnitClause
        (AyUPTSDisj missingImplicationEdge
          (AyUPTSDisj parentCoverageGap
            (AyUPTSDisj unretainedParent
              (AyUPTSDisj digestMismatch
                (AyUPTSDisj replayRejected fingerprintDrift)))))))

def AyUPTSPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPTSDisj noClaim originalUnsat

theorem ay_upts_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPTSConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_upts_conj_left
    (p : Prop) (q : Prop) :
    AyUPTSConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_upts_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPTSDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_upts_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPTSDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_upts_trace_slice
    (traceSlice : Prop) (boundaryStable : Prop) (unitClauses : Prop) :
    AyUPTSSliceBoundary traceSlice boundaryStable unitClauses ->
    traceSlice := by
  intro boundary
  exact ay_upts_conj_left traceSlice
    (AyUPTSConj
      (AyUPTSMap traceSlice boundaryStable)
      (AyUPTSMap boundaryStable unitClauses))
    boundary

theorem ay_upts_boundary_stable
    (traceSlice : Prop) (boundaryStable : Prop) (unitClauses : Prop) :
    AyUPTSSliceBoundary traceSlice boundaryStable unitClauses ->
    boundaryStable := by
  intro boundary
  exact boundary boundaryStable
    (fun slice tail =>
      tail boundaryStable
        (fun slice_to_boundary _boundary_to_units =>
          slice_to_boundary slice))

theorem ay_upts_unit_clauses
    (traceSlice : Prop) (boundaryStable : Prop) (unitClauses : Prop) :
    AyUPTSSliceBoundary traceSlice boundaryStable unitClauses ->
    unitClauses := by
  intro boundary
  exact boundary unitClauses
    (fun slice tail =>
      tail unitClauses
        (fun slice_to_boundary boundary_to_units =>
          boundary_to_units (slice_to_boundary slice)))

theorem ay_upts_implication_edges
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) :
    AyUPTSImplicationEdges unitClauses implicationEdges propagatedTrace ->
    unitClauses ->
    implicationEdges := by
  intro edges
  exact edges (unitClauses -> implicationEdges)
    (fun units_to_edges _edges_to_trace => units_to_edges)

theorem ay_upts_propagated_trace
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) :
    AyUPTSImplicationEdges unitClauses implicationEdges propagatedTrace ->
    implicationEdges ->
    propagatedTrace := by
  intro edges
  exact edges (implicationEdges -> propagatedTrace)
    (fun _units_to_edges edges_to_trace => edges_to_trace)

theorem ay_upts_parents_covered
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :
    AyUPTSParentCoverage propagatedTrace parentsCovered emptyClause ->
    propagatedTrace ->
    parentsCovered := by
  intro coverage
  exact coverage (propagatedTrace -> parentsCovered)
    (fun trace_to_parents _parents_to_empty => trace_to_parents)

theorem ay_upts_empty_clause
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :
    AyUPTSParentCoverage propagatedTrace parentsCovered emptyClause ->
    parentsCovered ->
    emptyClause := by
  intro coverage
  exact coverage (parentsCovered -> emptyClause)
    (fun _trace_to_parents parents_to_empty => parents_to_empty)

theorem ay_upts_retained_parents
    (propagatedTrace : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) :
    AyUPTSRetentionLineage propagatedTrace retainedParents lineageAccepted ->
    propagatedTrace ->
    retainedParents := by
  intro lineage
  exact lineage (propagatedTrace -> retainedParents)
    (fun trace_to_retained _retained_to_lineage => trace_to_retained)

theorem ay_upts_lineage_accepted
    (propagatedTrace : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) :
    AyUPTSRetentionLineage propagatedTrace retainedParents lineageAccepted ->
    retainedParents ->
    lineageAccepted := by
  intro lineage
  exact lineage (retainedParents -> lineageAccepted)
    (fun _trace_to_retained retained_to_lineage => retained_to_lineage)

theorem ay_upts_propagation_epoch
    (propagatedTrace : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) :
    AyUPTSEpoch propagatedTrace propagationEpoch epochAccepted ->
    propagatedTrace ->
    propagationEpoch := by
  intro epoch
  exact epoch (propagatedTrace -> propagationEpoch)
    (fun trace_to_epoch _epoch_to_accept => trace_to_epoch)

theorem ay_upts_epoch_accepted
    (propagatedTrace : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) :
    AyUPTSEpoch propagatedTrace propagationEpoch epochAccepted ->
    propagationEpoch ->
    epochAccepted := by
  intro epoch
  exact epoch (propagationEpoch -> epochAccepted)
    (fun _trace_to_epoch epoch_to_accept => epoch_to_accept)

theorem ay_upts_digest_member
    (propagatedTrace : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUPTSDigest propagatedTrace digestMember digestAccepted ->
    propagatedTrace ->
    digestMember := by
  intro digest
  exact digest (propagatedTrace -> digestMember)
    (fun trace_to_digest _digest_to_accept => trace_to_digest)

theorem ay_upts_digest_accepted
    (propagatedTrace : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUPTSDigest propagatedTrace digestMember digestAccepted ->
    digestMember ->
    digestAccepted := by
  intro digest
  exact digest (digestMember -> digestAccepted)
    (fun _trace_to_digest digest_to_accept => digest_to_accept)

theorem ay_upts_replay_transcript
    (propagatedTrace : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUPTSReplay propagatedTrace checkerReplay replayAccepted ->
    propagatedTrace ->
    checkerReplay := by
  intro replay
  exact replay (propagatedTrace -> checkerReplay)
    (fun trace_to_replay _replay_to_accept => trace_to_replay)

theorem ay_upts_replay_accepted
    (propagatedTrace : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUPTSReplay propagatedTrace checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _trace_to_replay replay_to_accept => replay_to_accept)

theorem ay_upts_fingerprint_agrees
    (propagatedTrace : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUPTSFingerprint propagatedTrace fingerprintAgrees visibleUnsat ->
    propagatedTrace ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (propagatedTrace -> fingerprintAgrees)
    (fun trace_to_fingerprint _fingerprint_to_visible =>
      trace_to_fingerprint)

theorem ay_upts_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPTSReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_upts_original_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPTSReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_upts_slice_boundary
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPTSSliceBoundary traceSlice boundaryStable unitClauses := by
  intro accepted
  exact ay_upts_conj_left
    (AyUPTSSliceBoundary traceSlice boundaryStable unitClauses)
    (AyUPTSConj
      (AyUPTSImplicationEdges unitClauses implicationEdges propagatedTrace)
      (AyUPTSConj
        (AyUPTSParentCoverage propagatedTrace parentsCovered emptyClause)
        (AyUPTSConj
          (AyUPTSRetentionLineage propagatedTrace retainedParents
            lineageAccepted)
          (AyUPTSConj
            (AyUPTSEpoch propagatedTrace propagationEpoch epochAccepted)
            (AyUPTSConj
              (AyUPTSDigest propagatedTrace digestMember digestAccepted)
              (AyUPTSConj
                (AyUPTSReplay propagatedTrace checkerReplay replayAccepted)
                (AyUPTSConj
                  (AyUPTSFingerprint propagatedTrace fingerprintAgrees
                    visibleUnsat)
                  (AyUPTSReconstruction emptyClause visibleUnsat
                    originalUnsat))))))))
    accepted

theorem ay_upts_slice_edges
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPTSImplicationEdges unitClauses implicationEdges
      propagatedTrace := by
  intro accepted
  exact accepted
    (AyUPTSImplicationEdges unitClauses implicationEdges propagatedTrace)
    (fun _boundary tail =>
      tail (AyUPTSImplicationEdges unitClauses implicationEdges
        propagatedTrace)
        (fun edges _rest => edges))

theorem ay_upts_slice_coverage
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPTSParentCoverage propagatedTrace parentsCovered emptyClause := by
  intro accepted
  exact accepted
    (AyUPTSParentCoverage propagatedTrace parentsCovered emptyClause)
    (fun _boundary tail =>
      tail (AyUPTSParentCoverage propagatedTrace parentsCovered emptyClause)
        (fun _edges rest =>
          rest (AyUPTSParentCoverage propagatedTrace parentsCovered
            emptyClause)
            (fun coverage _tail => coverage)))

theorem ay_upts_slice_lineage
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPTSRetentionLineage propagatedTrace retainedParents
      lineageAccepted := by
  intro accepted
  exact accepted
    (AyUPTSRetentionLineage propagatedTrace retainedParents lineageAccepted)
    (fun _boundary tail =>
      tail
        (AyUPTSRetentionLineage propagatedTrace retainedParents
          lineageAccepted)
        (fun _edges rest =>
          rest
            (AyUPTSRetentionLineage propagatedTrace retainedParents
              lineageAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyUPTSRetentionLineage propagatedTrace retainedParents
                  lineageAccepted)
                (fun lineage _tail => lineage))))

theorem ay_upts_slice_digest
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPTSDigest propagatedTrace digestMember digestAccepted := by
  intro accepted
  exact accepted (AyUPTSDigest propagatedTrace digestMember digestAccepted)
    (fun _boundary tail =>
      tail (AyUPTSDigest propagatedTrace digestMember digestAccepted)
        (fun _edges rest =>
          rest (AyUPTSDigest propagatedTrace digestMember digestAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyUPTSDigest propagatedTrace digestMember digestAccepted)
                (fun _lineage tail3 =>
                  tail3
                    (AyUPTSDigest propagatedTrace digestMember
                      digestAccepted)
                    (fun _epoch tail4 =>
                      tail4
                        (AyUPTSDigest propagatedTrace digestMember
                          digestAccepted)
                        (fun digest _tail => digest))))))

theorem ay_upts_slice_replay
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPTSReplay propagatedTrace checkerReplay replayAccepted := by
  intro accepted
  exact accepted (AyUPTSReplay propagatedTrace checkerReplay replayAccepted)
    (fun _boundary tail =>
      tail (AyUPTSReplay propagatedTrace checkerReplay replayAccepted)
        (fun _edges rest =>
          rest (AyUPTSReplay propagatedTrace checkerReplay replayAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyUPTSReplay propagatedTrace checkerReplay replayAccepted)
                (fun _lineage tail3 =>
                  tail3
                    (AyUPTSReplay propagatedTrace checkerReplay
                      replayAccepted)
                    (fun _epoch tail4 =>
                      tail4
                        (AyUPTSReplay propagatedTrace checkerReplay
                          replayAccepted)
                        (fun _digest tail5 =>
                          tail5
                            (AyUPTSReplay propagatedTrace checkerReplay
                              replayAccepted)
                            (fun replay _tail => replay)))))))

theorem ay_upts_slice_reconstruction
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPTSReconstruction emptyClause visibleUnsat originalUnsat := by
  intro accepted
  exact accepted (AyUPTSReconstruction emptyClause visibleUnsat
    originalUnsat)
    (fun _boundary tail =>
      tail (AyUPTSReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _edges rest =>
          rest (AyUPTSReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _coverage tail2 =>
              tail2
                (AyUPTSReconstruction emptyClause visibleUnsat originalUnsat)
                (fun _lineage tail3 =>
                  tail3
                    (AyUPTSReconstruction emptyClause visibleUnsat
                      originalUnsat)
                    (fun _epoch tail4 =>
                      tail4
                        (AyUPTSReconstruction emptyClause visibleUnsat
                          originalUnsat)
                        (fun _digest tail5 =>
                          tail5
                            (AyUPTSReconstruction emptyClause visibleUnsat
                              originalUnsat)
                            (fun _replay tail6 =>
                              tail6
                                (AyUPTSReconstruction emptyClause visibleUnsat
                                  originalUnsat)
                                (fun _fingerprint reconstruction =>
                                  reconstruction))))))))

theorem ay_upts_accepted_propagated_trace
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    propagatedTrace := by
  intro accepted
  have boundary :
      AyUPTSSliceBoundary traceSlice boundaryStable unitClauses :=
    ay_upts_slice_boundary traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have edges :
      AyUPTSImplicationEdges unitClauses implicationEdges propagatedTrace :=
    ay_upts_slice_edges traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have units : unitClauses :=
    ay_upts_unit_clauses traceSlice boundaryStable unitClauses boundary
  have edge : implicationEdges :=
    ay_upts_implication_edges unitClauses implicationEdges propagatedTrace
      edges units
  exact ay_upts_propagated_trace unitClauses implicationEdges
    propagatedTrace edges edge

theorem ay_upts_accepted_empty_clause
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    emptyClause := by
  intro accepted
  have trace : propagatedTrace :=
    ay_upts_accepted_propagated_trace traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have coverage :
      AyUPTSParentCoverage propagatedTrace parentsCovered emptyClause :=
    ay_upts_slice_coverage traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have parents : parentsCovered :=
    ay_upts_parents_covered propagatedTrace parentsCovered emptyClause
      coverage trace
  exact ay_upts_empty_clause propagatedTrace parentsCovered emptyClause
    coverage parents

theorem ay_upts_accepted_digest
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    digestAccepted := by
  intro accepted
  have trace : propagatedTrace :=
    ay_upts_accepted_propagated_trace traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have digest : AyUPTSDigest propagatedTrace digestMember digestAccepted :=
    ay_upts_slice_digest traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have member : digestMember :=
    ay_upts_digest_member propagatedTrace digestMember digestAccepted
      digest trace
  exact ay_upts_digest_accepted propagatedTrace digestMember digestAccepted
    digest member

theorem ay_upts_accepted_replay
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    replayAccepted := by
  intro accepted
  have trace : propagatedTrace :=
    ay_upts_accepted_propagated_trace traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have replay : AyUPTSReplay propagatedTrace checkerReplay replayAccepted :=
    ay_upts_slice_replay traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have transcript : checkerReplay :=
    ay_upts_replay_transcript propagatedTrace checkerReplay replayAccepted
      replay trace
  exact ay_upts_replay_accepted propagatedTrace checkerReplay replayAccepted
    replay transcript

theorem ay_upts_accepted_original_unsat
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_upts_accepted_empty_clause traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have reconstruction :
      AyUPTSReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_upts_slice_reconstruction traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have visible : visibleUnsat :=
    ay_upts_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_upts_original_unsat emptyClause visibleUnsat originalUnsat
    reconstruction visible

theorem ay_upts_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUPTSPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_upts_disj_right noClaim originalUnsat unsat

theorem ay_upts_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUPTSPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_upts_disj_left noClaim originalUnsat no_claim

theorem ay_upts_accepted_slice_publish_sound
    (traceSlice : Prop) (boundaryStable : Prop)
    (unitClauses : Prop) (implicationEdges : Prop)
    (propagatedTrace : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (propagationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUPTSAcceptedSlice traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPTSPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_upts_public_unsat_report noClaim originalUnsat
    (ay_upts_accepted_original_unsat traceSlice boundaryStable unitClauses
      implicationEdges propagatedTrace parentsCovered emptyClause
      retainedParents lineageAccepted propagationEpoch epochAccepted
      digestMember digestAccepted checkerReplay replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted)

theorem ay_upts_bad_slice_no_claim
    (boundaryDrift : Prop) (missingUnitClause : Prop)
    (missingImplicationEdge : Prop) (parentCoverageGap : Prop)
    (unretainedParent : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPTSBadSlice boundaryDrift missingUnitClause missingImplicationEdge
      parentCoverageGap unretainedParent digestMismatch replayRejected
      fingerprintDrift noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_upts_bad_slice_recompute
    (boundaryDrift : Prop) (missingUnitClause : Prop)
    (missingImplicationEdge : Prop) (parentCoverageGap : Prop)
    (unretainedParent : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPTSBadSlice boundaryDrift missingUnitClause missingImplicationEdge
      parentCoverageGap unretainedParent digestMismatch replayRejected
      fingerprintDrift noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_upts_bad_slice_public_no_claim
    (boundaryDrift : Prop) (missingUnitClause : Prop)
    (missingImplicationEdge : Prop) (parentCoverageGap : Prop)
    (unretainedParent : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPTSBadSlice boundaryDrift missingUnitClause missingImplicationEdge
      parentCoverageGap unretainedParent digestMismatch replayRejected
      fingerprintDrift noClaim recompute ->
    AyUPTSPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_upts_public_no_claim_report noClaim originalUnsat
    (ay_upts_bad_slice_no_claim boundaryDrift missingUnitClause
      missingImplicationEdge parentCoverageGap unretainedParent
      digestMismatch replayRejected fingerprintDrift noClaim recompute bad)

theorem ay_upts_bad_slice_cannot_publish
    (boundaryDrift : Prop) (missingUnitClause : Prop)
    (missingImplicationEdge : Prop) (parentCoverageGap : Prop)
    (unretainedParent : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPTSBadSlice boundaryDrift missingUnitClause missingImplicationEdge
      parentCoverageGap unretainedParent digestMismatch replayRejected
      fingerprintDrift noClaim recompute ->
    AyUPTSConj noClaim recompute := by
  intro bad
  exact bad (AyUPTSConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

