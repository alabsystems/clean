-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT clause-minimization replay-guard soundness for ay.
-- Propositions stand for minimized learned clauses, redundancy evidence for
-- removed literals, parent coverage, retained lineage, minimization epochs,
-- digest membership, checker replay transcripts, original fingerprint
-- agreement, and fail-closed no-claim/recompute diagnostics.

def AyUCMRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCMRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCMRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCMRRedundancyEvidence
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) :=
  AyUCMRConj minimizedClause
    (AyUCMRConj
      (AyUCMRMap minimizedClause removedLiteralEvidence)
      (AyUCMRMap removedLiteralEvidence guardedClause))

def AyUCMRParentCoverage
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :=
  AyUCMRConj
    (AyUCMRMap guardedClause parentsCovered)
    (AyUCMRMap parentsCovered emptyClause)

def AyUCMRRetainedLineage
    (guardedClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) :=
  AyUCMRConj
    (AyUCMRMap guardedClause retainedParents)
    (AyUCMRMap retainedParents lineageAccepted)

def AyUCMREpochGuard
    (guardedClause : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) :=
  AyUCMRConj
    (AyUCMRMap guardedClause minimizationEpoch)
    (AyUCMRMap minimizationEpoch epochAccepted)

def AyUCMRDigestMembership
    (guardedClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :=
  AyUCMRConj
    (AyUCMRMap guardedClause digestMember)
    (AyUCMRMap digestMember digestAccepted)

def AyUCMRCheckerReplay
    (guardedClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUCMRConj
    (AyUCMRMap guardedClause checkerReplay)
    (AyUCMRMap checkerReplay replayAccepted)

def AyUCMRFingerprint
    (guardedClause : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUCMRConj
    (AyUCMRMap guardedClause fingerprintAgrees)
    (AyUCMRMap fingerprintAgrees visibleUnsat)

def AyUCMRReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUCMRConj
    (AyUCMRMap emptyClause visibleUnsat)
    (AyUCMRMap visibleUnsat originalUnsat)

def AyUCMRAcceptedGuard
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCMRConj
    (AyUCMRRedundancyEvidence minimizedClause removedLiteralEvidence
      guardedClause)
    (AyUCMRConj
      (AyUCMRParentCoverage guardedClause parentsCovered emptyClause)
      (AyUCMRConj
        (AyUCMRRetainedLineage guardedClause retainedParents
          lineageAccepted)
        (AyUCMRConj
          (AyUCMREpochGuard guardedClause minimizationEpoch epochAccepted)
          (AyUCMRConj
            (AyUCMRDigestMembership guardedClause digestMember
              digestAccepted)
            (AyUCMRConj
              (AyUCMRCheckerReplay guardedClause checkerReplay
                replayAccepted)
              (AyUCMRConj
                (AyUCMRFingerprint guardedClause fingerprintAgrees
                  visibleUnsat)
                (AyUCMRReconstruction emptyClause visibleUnsat
                  originalUnsat)))))))

def AyUCMRBadGuard
    (missingRedundancyEvidence : Prop) (staleParentCoverage : Prop)
    (unretainedParent : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUCMRConj
    (AyUCMRConj noClaim recompute)
    (AyUCMRDisj missingRedundancyEvidence
      (AyUCMRDisj staleParentCoverage
        (AyUCMRDisj unretainedParent
          (AyUCMRDisj digestMismatch
            (AyUCMRDisj replayRejected fingerprintDrift)))))

def AyUCMRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCMRDisj noClaim originalUnsat

theorem ay_ucmr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCMRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucmr_conj_left
    (p : Prop) (q : Prop) :
    AyUCMRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucmr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCMRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucmr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCMRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucmr_minimized_clause
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) :
    AyUCMRRedundancyEvidence minimizedClause removedLiteralEvidence
      guardedClause ->
    minimizedClause := by
  intro evidence
  exact ay_ucmr_conj_left minimizedClause
    (AyUCMRConj
      (AyUCMRMap minimizedClause removedLiteralEvidence)
      (AyUCMRMap removedLiteralEvidence guardedClause))
    evidence

theorem ay_ucmr_removed_literal_evidence
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) :
    AyUCMRRedundancyEvidence minimizedClause removedLiteralEvidence
      guardedClause ->
    removedLiteralEvidence := by
  intro evidence
  exact evidence removedLiteralEvidence
    (fun minimized tail =>
      tail removedLiteralEvidence
        (fun minimized_to_evidence _evidence_to_guarded =>
          minimized_to_evidence minimized))

theorem ay_ucmr_guarded_clause
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) :
    AyUCMRRedundancyEvidence minimizedClause removedLiteralEvidence
      guardedClause ->
    guardedClause := by
  intro evidence
  exact evidence guardedClause
    (fun minimized tail =>
      tail guardedClause
        (fun minimized_to_evidence evidence_to_guarded =>
          evidence_to_guarded (minimized_to_evidence minimized)))

theorem ay_ucmr_parents_covered
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :
    AyUCMRParentCoverage guardedClause parentsCovered emptyClause ->
    guardedClause ->
    parentsCovered := by
  intro coverage
  exact coverage (guardedClause -> parentsCovered)
    (fun guarded_to_parents _parents_to_empty => guarded_to_parents)

theorem ay_ucmr_empty_clause
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :
    AyUCMRParentCoverage guardedClause parentsCovered emptyClause ->
    parentsCovered ->
    emptyClause := by
  intro coverage
  exact coverage (parentsCovered -> emptyClause)
    (fun _guarded_to_parents parents_to_empty => parents_to_empty)

theorem ay_ucmr_retained_parents
    (guardedClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) :
    AyUCMRRetainedLineage guardedClause retainedParents
      lineageAccepted ->
    guardedClause ->
    retainedParents := by
  intro lineage
  exact lineage (guardedClause -> retainedParents)
    (fun guarded_to_retained _retained_to_lineage => guarded_to_retained)

theorem ay_ucmr_lineage_accepted
    (guardedClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) :
    AyUCMRRetainedLineage guardedClause retainedParents
      lineageAccepted ->
    retainedParents ->
    lineageAccepted := by
  intro lineage
  exact lineage (retainedParents -> lineageAccepted)
    (fun _guarded_to_retained retained_to_lineage => retained_to_lineage)

theorem ay_ucmr_minimization_epoch
    (guardedClause : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) :
    AyUCMREpochGuard guardedClause minimizationEpoch epochAccepted ->
    guardedClause ->
    minimizationEpoch := by
  intro epoch
  exact epoch (guardedClause -> minimizationEpoch)
    (fun guarded_to_epoch _epoch_to_accept => guarded_to_epoch)

theorem ay_ucmr_epoch_accepted
    (guardedClause : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) :
    AyUCMREpochGuard guardedClause minimizationEpoch epochAccepted ->
    minimizationEpoch ->
    epochAccepted := by
  intro epoch
  exact epoch (minimizationEpoch -> epochAccepted)
    (fun _guarded_to_epoch epoch_to_accept => epoch_to_accept)

theorem ay_ucmr_digest_member
    (guardedClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUCMRDigestMembership guardedClause digestMember digestAccepted ->
    guardedClause ->
    digestMember := by
  intro digest
  exact digest (guardedClause -> digestMember)
    (fun guarded_to_digest _digest_to_accept => guarded_to_digest)

theorem ay_ucmr_digest_accepted
    (guardedClause : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUCMRDigestMembership guardedClause digestMember digestAccepted ->
    digestMember ->
    digestAccepted := by
  intro digest
  exact digest (digestMember -> digestAccepted)
    (fun _guarded_to_digest digest_to_accept => digest_to_accept)

theorem ay_ucmr_replay_transcript
    (guardedClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCMRCheckerReplay guardedClause checkerReplay replayAccepted ->
    guardedClause ->
    checkerReplay := by
  intro replay
  exact replay (guardedClause -> checkerReplay)
    (fun guarded_to_replay _replay_to_accept => guarded_to_replay)

theorem ay_ucmr_replay_accepted
    (guardedClause : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCMRCheckerReplay guardedClause checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _guarded_to_replay replay_to_accept => replay_to_accept)

theorem ay_ucmr_fingerprint_agrees
    (guardedClause : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUCMRFingerprint guardedClause fingerprintAgrees visibleUnsat ->
    guardedClause ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (guardedClause -> fingerprintAgrees)
    (fun guarded_to_fingerprint _fingerprint_to_visible =>
      guarded_to_fingerprint)

theorem ay_ucmr_visible_from_fingerprint
    (guardedClause : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUCMRFingerprint guardedClause fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _guarded_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_ucmr_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCMRReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_ucmr_original_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCMRReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_ucmr_guard_evidence
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    AyUCMRRedundancyEvidence minimizedClause removedLiteralEvidence
      guardedClause := by
  intro accepted
  exact ay_ucmr_conj_left
    (AyUCMRRedundancyEvidence minimizedClause removedLiteralEvidence
      guardedClause)
    (AyUCMRConj
      (AyUCMRParentCoverage guardedClause parentsCovered emptyClause)
      (AyUCMRConj
        (AyUCMRRetainedLineage guardedClause retainedParents
          lineageAccepted)
        (AyUCMRConj
          (AyUCMREpochGuard guardedClause minimizationEpoch epochAccepted)
          (AyUCMRConj
            (AyUCMRDigestMembership guardedClause digestMember
              digestAccepted)
            (AyUCMRConj
              (AyUCMRCheckerReplay guardedClause checkerReplay
                replayAccepted)
              (AyUCMRConj
                (AyUCMRFingerprint guardedClause fingerprintAgrees
                  visibleUnsat)
                (AyUCMRReconstruction emptyClause visibleUnsat
                  originalUnsat)))))))
    accepted

theorem ay_ucmr_guard_coverage
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    AyUCMRParentCoverage guardedClause parentsCovered emptyClause := by
  intro accepted
  exact accepted (AyUCMRParentCoverage guardedClause parentsCovered
    emptyClause)
    (fun _evidence tail =>
      tail (AyUCMRParentCoverage guardedClause parentsCovered emptyClause)
        (fun coverage _rest => coverage))

theorem ay_ucmr_guard_lineage
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    AyUCMRRetainedLineage guardedClause retainedParents
      lineageAccepted := by
  intro accepted
  exact accepted
    (AyUCMRRetainedLineage guardedClause retainedParents lineageAccepted)
    (fun _evidence tail =>
      tail
        (AyUCMRRetainedLineage guardedClause retainedParents
          lineageAccepted)
        (fun _coverage rest =>
          rest
            (AyUCMRRetainedLineage guardedClause retainedParents
              lineageAccepted)
            (fun lineage _tail => lineage)))

theorem ay_ucmr_guard_epoch
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    AyUCMREpochGuard guardedClause minimizationEpoch epochAccepted := by
  intro accepted
  exact accepted (AyUCMREpochGuard guardedClause minimizationEpoch
    epochAccepted)
    (fun _evidence tail =>
      tail (AyUCMREpochGuard guardedClause minimizationEpoch epochAccepted)
        (fun _coverage rest =>
          rest (AyUCMREpochGuard guardedClause minimizationEpoch
            epochAccepted)
            (fun _lineage tail2 =>
              tail2
                (AyUCMREpochGuard guardedClause minimizationEpoch
                  epochAccepted)
                (fun epoch _tail => epoch))))

theorem ay_ucmr_guard_digest
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    AyUCMRDigestMembership guardedClause digestMember digestAccepted := by
  intro accepted
  exact accepted
    (AyUCMRDigestMembership guardedClause digestMember digestAccepted)
    (fun _evidence tail =>
      tail (AyUCMRDigestMembership guardedClause digestMember digestAccepted)
        (fun _coverage rest =>
          rest (AyUCMRDigestMembership guardedClause digestMember
            digestAccepted)
            (fun _lineage tail2 =>
              tail2
                (AyUCMRDigestMembership guardedClause digestMember
                  digestAccepted)
                (fun _epoch tail3 =>
                  tail3
                    (AyUCMRDigestMembership guardedClause digestMember
                      digestAccepted)
                    (fun digest _tail => digest)))))

theorem ay_ucmr_guard_replay
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    AyUCMRCheckerReplay guardedClause checkerReplay replayAccepted := by
  intro accepted
  exact accepted (AyUCMRCheckerReplay guardedClause checkerReplay
    replayAccepted)
    (fun _evidence tail =>
      tail (AyUCMRCheckerReplay guardedClause checkerReplay replayAccepted)
        (fun _coverage rest =>
          rest (AyUCMRCheckerReplay guardedClause checkerReplay
            replayAccepted)
            (fun _lineage tail2 =>
              tail2
                (AyUCMRCheckerReplay guardedClause checkerReplay
                  replayAccepted)
                (fun _epoch tail3 =>
                  tail3
                    (AyUCMRCheckerReplay guardedClause checkerReplay
                      replayAccepted)
                    (fun _digest tail4 =>
                      tail4
                        (AyUCMRCheckerReplay guardedClause checkerReplay
                          replayAccepted)
                        (fun replay _tail => replay))))))

theorem ay_ucmr_guard_fingerprint
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    AyUCMRFingerprint guardedClause fingerprintAgrees visibleUnsat := by
  intro accepted
  exact accepted
    (AyUCMRFingerprint guardedClause fingerprintAgrees visibleUnsat)
    (fun _evidence tail =>
      tail (AyUCMRFingerprint guardedClause fingerprintAgrees visibleUnsat)
        (fun _coverage rest =>
          rest (AyUCMRFingerprint guardedClause fingerprintAgrees visibleUnsat)
            (fun _lineage tail2 =>
              tail2
                (AyUCMRFingerprint guardedClause fingerprintAgrees
                  visibleUnsat)
                (fun _epoch tail3 =>
                  tail3
                    (AyUCMRFingerprint guardedClause fingerprintAgrees
                      visibleUnsat)
                    (fun _digest tail4 =>
                      tail4
                        (AyUCMRFingerprint guardedClause fingerprintAgrees
                          visibleUnsat)
                        (fun _replay tail5 =>
                          tail5
                            (AyUCMRFingerprint guardedClause
                              fingerprintAgrees visibleUnsat)
                            (fun fingerprint _reconstruction =>
                              fingerprint)))))))

theorem ay_ucmr_guard_reconstruction
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    AyUCMRReconstruction emptyClause visibleUnsat originalUnsat := by
  intro accepted
  exact accepted (AyUCMRReconstruction emptyClause visibleUnsat
    originalUnsat)
    (fun _evidence tail =>
      tail (AyUCMRReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _coverage rest =>
          rest (AyUCMRReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _lineage tail2 =>
              tail2
                (AyUCMRReconstruction emptyClause visibleUnsat originalUnsat)
                (fun _epoch tail3 =>
                  tail3
                    (AyUCMRReconstruction emptyClause visibleUnsat
                      originalUnsat)
                    (fun _digest tail4 =>
                      tail4
                        (AyUCMRReconstruction emptyClause visibleUnsat
                          originalUnsat)
                        (fun _replay tail5 =>
                          tail5
                            (AyUCMRReconstruction emptyClause visibleUnsat
                              originalUnsat)
                            (fun _fingerprint reconstruction =>
                              reconstruction)))))))

theorem ay_ucmr_accepted_guarded_clause
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    guardedClause := by
  intro accepted
  have evidence :
      AyUCMRRedundancyEvidence minimizedClause removedLiteralEvidence
        guardedClause :=
    ay_ucmr_guard_evidence minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  exact ay_ucmr_guarded_clause minimizedClause removedLiteralEvidence
    guardedClause evidence

theorem ay_ucmr_accepted_empty_clause
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    emptyClause := by
  intro accepted
  have guarded : guardedClause :=
    ay_ucmr_accepted_guarded_clause minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have coverage :
      AyUCMRParentCoverage guardedClause parentsCovered emptyClause :=
    ay_ucmr_guard_coverage minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have parents : parentsCovered :=
    ay_ucmr_parents_covered guardedClause parentsCovered emptyClause
      coverage guarded
  exact ay_ucmr_empty_clause guardedClause parentsCovered emptyClause
    coverage parents

theorem ay_ucmr_accepted_lineage
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    lineageAccepted := by
  intro accepted
  have guarded : guardedClause :=
    ay_ucmr_accepted_guarded_clause minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have lineage :
      AyUCMRRetainedLineage guardedClause retainedParents
        lineageAccepted :=
    ay_ucmr_guard_lineage minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have retained : retainedParents :=
    ay_ucmr_retained_parents guardedClause retainedParents lineageAccepted
      lineage guarded
  exact ay_ucmr_lineage_accepted guardedClause retainedParents
    lineageAccepted lineage retained

theorem ay_ucmr_accepted_epoch
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    epochAccepted := by
  intro accepted
  have guarded : guardedClause :=
    ay_ucmr_accepted_guarded_clause minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have epoch :
      AyUCMREpochGuard guardedClause minimizationEpoch epochAccepted :=
    ay_ucmr_guard_epoch minimizedClause removedLiteralEvidence guardedClause
      parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have epoch_value : minimizationEpoch :=
    ay_ucmr_minimization_epoch guardedClause minimizationEpoch
      epochAccepted epoch guarded
  exact ay_ucmr_epoch_accepted guardedClause minimizationEpoch
    epochAccepted epoch epoch_value

theorem ay_ucmr_accepted_digest
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    digestAccepted := by
  intro accepted
  have guarded : guardedClause :=
    ay_ucmr_accepted_guarded_clause minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have digest :
      AyUCMRDigestMembership guardedClause digestMember digestAccepted :=
    ay_ucmr_guard_digest minimizedClause removedLiteralEvidence guardedClause
      parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have member : digestMember :=
    ay_ucmr_digest_member guardedClause digestMember digestAccepted
      digest guarded
  exact ay_ucmr_digest_accepted guardedClause digestMember digestAccepted
    digest member

theorem ay_ucmr_accepted_replay
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    replayAccepted := by
  intro accepted
  have guarded : guardedClause :=
    ay_ucmr_accepted_guarded_clause minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have replay :
      AyUCMRCheckerReplay guardedClause checkerReplay replayAccepted :=
    ay_ucmr_guard_replay minimizedClause removedLiteralEvidence guardedClause
      parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have transcript : checkerReplay :=
    ay_ucmr_replay_transcript guardedClause checkerReplay replayAccepted
      replay guarded
  exact ay_ucmr_replay_accepted guardedClause checkerReplay replayAccepted
    replay transcript

theorem ay_ucmr_accepted_original_unsat
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_ucmr_accepted_empty_clause minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have reconstruction :
      AyUCMRReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_ucmr_guard_reconstruction minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have visible : visibleUnsat :=
    ay_ucmr_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_ucmr_original_unsat emptyClause visibleUnsat originalUnsat
    reconstruction visible

theorem ay_ucmr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUCMRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucmr_disj_right noClaim originalUnsat unsat

theorem ay_ucmr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUCMRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucmr_disj_left noClaim originalUnsat no_claim

theorem ay_ucmr_accepted_guard_publish_sound
    (minimizedClause : Prop) (removedLiteralEvidence : Prop)
    (guardedClause : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedParents : Prop)
    (lineageAccepted : Prop) (minimizationEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUCMRAcceptedGuard minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents
      lineageAccepted minimizationEpoch epochAccepted digestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat ->
    AyUCMRPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_ucmr_public_unsat_report noClaim originalUnsat
    (ay_ucmr_accepted_original_unsat minimizedClause removedLiteralEvidence
      guardedClause parentsCovered emptyClause retainedParents lineageAccepted
      minimizationEpoch epochAccepted digestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted)

theorem ay_ucmr_bad_guard_no_claim
    (missingRedundancyEvidence : Prop) (staleParentCoverage : Prop)
    (unretainedParent : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCMRBadGuard missingRedundancyEvidence staleParentCoverage
      unretainedParent digestMismatch replayRejected fingerprintDrift
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_ucmr_bad_guard_recompute
    (missingRedundancyEvidence : Prop) (staleParentCoverage : Prop)
    (unretainedParent : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCMRBadGuard missingRedundancyEvidence staleParentCoverage
      unretainedParent digestMismatch replayRejected fingerprintDrift
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_ucmr_bad_guard_public_no_claim
    (missingRedundancyEvidence : Prop) (staleParentCoverage : Prop)
    (unretainedParent : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCMRBadGuard missingRedundancyEvidence staleParentCoverage
      unretainedParent digestMismatch replayRejected fingerprintDrift
      noClaim recompute ->
    AyUCMRPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucmr_public_no_claim_report noClaim originalUnsat
    (ay_ucmr_bad_guard_no_claim missingRedundancyEvidence
      staleParentCoverage unretainedParent digestMismatch replayRejected
      fingerprintDrift noClaim recompute bad)

theorem ay_ucmr_bad_guard_cannot_publish
    (missingRedundancyEvidence : Prop) (staleParentCoverage : Prop)
    (unretainedParent : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCMRBadGuard missingRedundancyEvidence staleParentCoverage
      unretainedParent digestMismatch replayRejected fingerprintDrift
      noClaim recompute ->
    AyUCMRConj noClaim recompute := by
  intro bad
  exact bad (AyUCMRConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

