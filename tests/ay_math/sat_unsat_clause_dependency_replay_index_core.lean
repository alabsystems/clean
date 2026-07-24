-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT clause dependency replay-index soundness for ay.
-- Propositions stand for stable learned-clause IDs, parent coverage,
-- deletion/retention lineage, archive digest membership, replay transcript
-- coverage, original-instance fingerprint agreement, and fail-closed
-- no-claim/recompute diagnostics.

def AyUCDIConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCDIDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCDIMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCDIStableClauseIds
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) :=
  AyUCDIConj dependencyIndex
    (AyUCDIConj
      (AyUCDIMap dependencyIndex stableClauseIds)
      (AyUCDIMap stableClauseIds indexedClauses))

def AyUCDIParentCoverage
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :=
  AyUCDIConj
    (AyUCDIMap indexedClauses parentsCovered)
    (AyUCDIMap parentsCovered emptyClause)

def AyUCDIDeletionLineage
    (indexedClauses : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) :=
  AyUCDIConj
    (AyUCDIMap indexedClauses retainedOrRehydrated)
    (AyUCDIMap retainedOrRehydrated lineageAccepted)

def AyUCDIArchiveDigest
    (indexedClauses : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) :=
  AyUCDIConj
    (AyUCDIMap indexedClauses archiveDigestMember)
    (AyUCDIMap archiveDigestMember digestAccepted)

def AyUCDIReplayTranscript
    (indexedClauses : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) :=
  AyUCDIConj
    (AyUCDIMap indexedClauses replayCovered)
    (AyUCDIMap replayCovered replayAccepted)

def AyUCDIFingerprint
    (indexedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUCDIConj
    (AyUCDIMap indexedClauses fingerprintAgrees)
    (AyUCDIMap fingerprintAgrees visibleUnsat)

def AyUCDIReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUCDIConj
    (AyUCDIMap emptyClause visibleUnsat)
    (AyUCDIMap visibleUnsat originalUnsat)

def AyUCDIAcceptedIndex
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCDIConj
    (AyUCDIStableClauseIds dependencyIndex stableClauseIds indexedClauses)
    (AyUCDIConj
      (AyUCDIParentCoverage indexedClauses parentsCovered emptyClause)
      (AyUCDIConj
        (AyUCDIDeletionLineage indexedClauses retainedOrRehydrated
          lineageAccepted)
        (AyUCDIConj
          (AyUCDIArchiveDigest indexedClauses archiveDigestMember
            digestAccepted)
          (AyUCDIConj
            (AyUCDIReplayTranscript indexedClauses replayCovered
              replayAccepted)
            (AyUCDIConj
              (AyUCDIFingerprint indexedClauses fingerprintAgrees
                visibleUnsat)
              (AyUCDIReconstruction emptyClause visibleUnsat
                originalUnsat))))))

def AyUCDIBadIndex
    (missingParent : Prop) (deletedUnretained : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUCDIConj
    (AyUCDIConj noClaim recompute)
    (AyUCDIDisj missingParent
      (AyUCDIDisj deletedUnretained
        (AyUCDIDisj digestMismatch
          (AyUCDIDisj replayRejected fingerprintDrift))))

def AyUCDIPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCDIDisj noClaim originalUnsat

theorem ay_ucdi_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCDIConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucdi_conj_left
    (p : Prop) (q : Prop) :
    AyUCDIConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucdi_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCDIDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucdi_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCDIDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucdi_dependency_index
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) :
    AyUCDIStableClauseIds dependencyIndex stableClauseIds indexedClauses ->
    dependencyIndex := by
  intro ids
  exact ay_ucdi_conj_left dependencyIndex
    (AyUCDIConj
      (AyUCDIMap dependencyIndex stableClauseIds)
      (AyUCDIMap stableClauseIds indexedClauses))
    ids

theorem ay_ucdi_stable_clause_ids
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) :
    AyUCDIStableClauseIds dependencyIndex stableClauseIds indexedClauses ->
    stableClauseIds := by
  intro ids
  exact ids stableClauseIds
    (fun index tail =>
      tail stableClauseIds
        (fun index_to_stable _stable_to_indexed =>
          index_to_stable index))

theorem ay_ucdi_indexed_clauses
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) :
    AyUCDIStableClauseIds dependencyIndex stableClauseIds indexedClauses ->
    indexedClauses := by
  intro ids
  exact ids indexedClauses
    (fun index tail =>
      tail indexedClauses
        (fun index_to_stable stable_to_indexed =>
          stable_to_indexed (index_to_stable index)))

theorem ay_ucdi_parents_covered
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :
    AyUCDIParentCoverage indexedClauses parentsCovered emptyClause ->
    indexedClauses ->
    parentsCovered := by
  intro coverage
  exact coverage (indexedClauses -> parentsCovered)
    (fun indexed_to_parents _parents_to_empty => indexed_to_parents)

theorem ay_ucdi_empty_clause
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :
    AyUCDIParentCoverage indexedClauses parentsCovered emptyClause ->
    parentsCovered ->
    emptyClause := by
  intro coverage
  exact coverage (parentsCovered -> emptyClause)
    (fun _indexed_to_parents parents_to_empty => parents_to_empty)

theorem ay_ucdi_retained_or_rehydrated
    (indexedClauses : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) :
    AyUCDIDeletionLineage indexedClauses retainedOrRehydrated
      lineageAccepted ->
    indexedClauses ->
    retainedOrRehydrated := by
  intro lineage
  exact lineage (indexedClauses -> retainedOrRehydrated)
    (fun indexed_to_retained _retained_to_lineage =>
      indexed_to_retained)

theorem ay_ucdi_lineage_accepted
    (indexedClauses : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) :
    AyUCDIDeletionLineage indexedClauses retainedOrRehydrated
      lineageAccepted ->
    retainedOrRehydrated ->
    lineageAccepted := by
  intro lineage
  exact lineage (retainedOrRehydrated -> lineageAccepted)
    (fun _indexed_to_retained retained_to_lineage => retained_to_lineage)

theorem ay_ucdi_archive_digest_member
    (indexedClauses : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) :
    AyUCDIArchiveDigest indexedClauses archiveDigestMember
      digestAccepted ->
    indexedClauses ->
    archiveDigestMember := by
  intro digest
  exact digest (indexedClauses -> archiveDigestMember)
    (fun indexed_to_digest _digest_to_accept => indexed_to_digest)

theorem ay_ucdi_digest_accepted
    (indexedClauses : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) :
    AyUCDIArchiveDigest indexedClauses archiveDigestMember
      digestAccepted ->
    archiveDigestMember ->
    digestAccepted := by
  intro digest
  exact digest (archiveDigestMember -> digestAccepted)
    (fun _indexed_to_digest digest_to_accept => digest_to_accept)

theorem ay_ucdi_replay_covered
    (indexedClauses : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) :
    AyUCDIReplayTranscript indexedClauses replayCovered replayAccepted ->
    indexedClauses ->
    replayCovered := by
  intro replay
  exact replay (indexedClauses -> replayCovered)
    (fun indexed_to_replay _replay_to_accept => indexed_to_replay)

theorem ay_ucdi_replay_accepted
    (indexedClauses : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) :
    AyUCDIReplayTranscript indexedClauses replayCovered replayAccepted ->
    replayCovered ->
    replayAccepted := by
  intro replay
  exact replay (replayCovered -> replayAccepted)
    (fun _indexed_to_replay replay_to_accept => replay_to_accept)

theorem ay_ucdi_fingerprint_agrees
    (indexedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUCDIFingerprint indexedClauses fingerprintAgrees visibleUnsat ->
    indexedClauses ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (indexedClauses -> fingerprintAgrees)
    (fun indexed_to_fingerprint _fingerprint_to_visible =>
      indexed_to_fingerprint)

theorem ay_ucdi_visible_from_fingerprint
    (indexedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUCDIFingerprint indexedClauses fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _indexed_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_ucdi_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCDIReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_ucdi_original_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCDIReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_ucdi_index_stable_ids
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCDIStableClauseIds dependencyIndex stableClauseIds indexedClauses := by
  intro accepted
  exact ay_ucdi_conj_left
    (AyUCDIStableClauseIds dependencyIndex stableClauseIds indexedClauses)
    (AyUCDIConj
      (AyUCDIParentCoverage indexedClauses parentsCovered emptyClause)
      (AyUCDIConj
        (AyUCDIDeletionLineage indexedClauses retainedOrRehydrated
          lineageAccepted)
        (AyUCDIConj
          (AyUCDIArchiveDigest indexedClauses archiveDigestMember
            digestAccepted)
          (AyUCDIConj
            (AyUCDIReplayTranscript indexedClauses replayCovered
              replayAccepted)
            (AyUCDIConj
              (AyUCDIFingerprint indexedClauses fingerprintAgrees
                visibleUnsat)
              (AyUCDIReconstruction emptyClause visibleUnsat
                originalUnsat))))))
    accepted

theorem ay_ucdi_index_parent_coverage
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCDIParentCoverage indexedClauses parentsCovered emptyClause := by
  intro accepted
  exact accepted (AyUCDIParentCoverage indexedClauses parentsCovered
    emptyClause)
    (fun _ids tail =>
      tail (AyUCDIParentCoverage indexedClauses parentsCovered emptyClause)
        (fun coverage _rest => coverage))

theorem ay_ucdi_index_lineage
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCDIDeletionLineage indexedClauses retainedOrRehydrated
      lineageAccepted := by
  intro accepted
  exact accepted
    (AyUCDIDeletionLineage indexedClauses retainedOrRehydrated
      lineageAccepted)
    (fun _ids tail =>
      tail
        (AyUCDIDeletionLineage indexedClauses retainedOrRehydrated
          lineageAccepted)
        (fun _coverage rest =>
          rest
            (AyUCDIDeletionLineage indexedClauses retainedOrRehydrated
              lineageAccepted)
            (fun lineage _tail => lineage)))

theorem ay_ucdi_index_digest
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCDIArchiveDigest indexedClauses archiveDigestMember digestAccepted := by
  intro accepted
  exact accepted
    (AyUCDIArchiveDigest indexedClauses archiveDigestMember digestAccepted)
    (fun _ids tail =>
      tail
        (AyUCDIArchiveDigest indexedClauses archiveDigestMember
          digestAccepted)
        (fun _coverage rest =>
          rest
            (AyUCDIArchiveDigest indexedClauses archiveDigestMember
              digestAccepted)
            (fun _lineage tail2 =>
              tail2
                (AyUCDIArchiveDigest indexedClauses archiveDigestMember
                  digestAccepted)
                (fun digest _tail => digest))))

theorem ay_ucdi_index_replay
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCDIReplayTranscript indexedClauses replayCovered replayAccepted := by
  intro accepted
  exact accepted
    (AyUCDIReplayTranscript indexedClauses replayCovered replayAccepted)
    (fun _ids tail =>
      tail (AyUCDIReplayTranscript indexedClauses replayCovered
        replayAccepted)
        (fun _coverage rest =>
          rest (AyUCDIReplayTranscript indexedClauses replayCovered
            replayAccepted)
            (fun _lineage tail2 =>
              tail2
                (AyUCDIReplayTranscript indexedClauses replayCovered
                  replayAccepted)
                (fun _digest tail3 =>
                  tail3
                    (AyUCDIReplayTranscript indexedClauses replayCovered
                      replayAccepted)
                    (fun replay _tail => replay)))))

theorem ay_ucdi_index_fingerprint
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCDIFingerprint indexedClauses fingerprintAgrees visibleUnsat := by
  intro accepted
  exact accepted
    (AyUCDIFingerprint indexedClauses fingerprintAgrees visibleUnsat)
    (fun _ids tail =>
      tail (AyUCDIFingerprint indexedClauses fingerprintAgrees visibleUnsat)
        (fun _coverage rest =>
          rest (AyUCDIFingerprint indexedClauses fingerprintAgrees
            visibleUnsat)
            (fun _lineage tail2 =>
              tail2
                (AyUCDIFingerprint indexedClauses fingerprintAgrees
                  visibleUnsat)
                (fun _digest tail3 =>
                  tail3
                    (AyUCDIFingerprint indexedClauses fingerprintAgrees
                      visibleUnsat)
                    (fun _replay tail4 =>
                      tail4
                        (AyUCDIFingerprint indexedClauses fingerprintAgrees
                          visibleUnsat)
                        (fun fingerprint _reconstruction =>
                          fingerprint))))))

theorem ay_ucdi_index_reconstruction
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCDIReconstruction emptyClause visibleUnsat originalUnsat := by
  intro accepted
  exact accepted (AyUCDIReconstruction emptyClause visibleUnsat
    originalUnsat)
    (fun _ids tail =>
      tail (AyUCDIReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _coverage rest =>
          rest (AyUCDIReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _lineage tail2 =>
              tail2 (AyUCDIReconstruction emptyClause visibleUnsat
                originalUnsat)
                (fun _digest tail3 =>
                  tail3
                    (AyUCDIReconstruction emptyClause visibleUnsat
                      originalUnsat)
                    (fun _replay tail4 =>
                      tail4
                        (AyUCDIReconstruction emptyClause visibleUnsat
                          originalUnsat)
                        (fun _fingerprint reconstruction =>
                          reconstruction))))))

theorem ay_ucdi_accepted_indexed_clauses
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    indexedClauses := by
  intro accepted
  have ids :
      AyUCDIStableClauseIds dependencyIndex stableClauseIds
        indexedClauses :=
    ay_ucdi_index_stable_ids dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  exact ay_ucdi_indexed_clauses dependencyIndex stableClauseIds
    indexedClauses ids

theorem ay_ucdi_accepted_empty_clause
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    emptyClause := by
  intro accepted
  have indexed : indexedClauses :=
    ay_ucdi_accepted_indexed_clauses dependencyIndex stableClauseIds
      indexedClauses parentsCovered emptyClause retainedOrRehydrated
      lineageAccepted archiveDigestMember digestAccepted replayCovered
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat accepted
  have coverage :
      AyUCDIParentCoverage indexedClauses parentsCovered emptyClause :=
    ay_ucdi_index_parent_coverage dependencyIndex stableClauseIds
      indexedClauses parentsCovered emptyClause retainedOrRehydrated
      lineageAccepted archiveDigestMember digestAccepted replayCovered
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat accepted
  have parents : parentsCovered :=
    ay_ucdi_parents_covered indexedClauses parentsCovered emptyClause
      coverage indexed
  exact ay_ucdi_empty_clause indexedClauses parentsCovered emptyClause
    coverage parents

theorem ay_ucdi_accepted_lineage
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    lineageAccepted := by
  intro accepted
  have indexed : indexedClauses :=
    ay_ucdi_accepted_indexed_clauses dependencyIndex stableClauseIds
      indexedClauses parentsCovered emptyClause retainedOrRehydrated
      lineageAccepted archiveDigestMember digestAccepted replayCovered
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat accepted
  have lineage :
      AyUCDIDeletionLineage indexedClauses retainedOrRehydrated
        lineageAccepted :=
    ay_ucdi_index_lineage dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have retained : retainedOrRehydrated :=
    ay_ucdi_retained_or_rehydrated indexedClauses retainedOrRehydrated
      lineageAccepted lineage indexed
  exact ay_ucdi_lineage_accepted indexedClauses retainedOrRehydrated
    lineageAccepted lineage retained

theorem ay_ucdi_accepted_digest
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    digestAccepted := by
  intro accepted
  have indexed : indexedClauses :=
    ay_ucdi_accepted_indexed_clauses dependencyIndex stableClauseIds
      indexedClauses parentsCovered emptyClause retainedOrRehydrated
      lineageAccepted archiveDigestMember digestAccepted replayCovered
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat accepted
  have digest :
      AyUCDIArchiveDigest indexedClauses archiveDigestMember
        digestAccepted :=
    ay_ucdi_index_digest dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have member : archiveDigestMember :=
    ay_ucdi_archive_digest_member indexedClauses archiveDigestMember
      digestAccepted digest indexed
  exact ay_ucdi_digest_accepted indexedClauses archiveDigestMember
    digestAccepted digest member

theorem ay_ucdi_accepted_replay
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    replayAccepted := by
  intro accepted
  have indexed : indexedClauses :=
    ay_ucdi_accepted_indexed_clauses dependencyIndex stableClauseIds
      indexedClauses parentsCovered emptyClause retainedOrRehydrated
      lineageAccepted archiveDigestMember digestAccepted replayCovered
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat accepted
  have replay :
      AyUCDIReplayTranscript indexedClauses replayCovered replayAccepted :=
    ay_ucdi_index_replay dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat accepted
  have covered : replayCovered :=
    ay_ucdi_replay_covered indexedClauses replayCovered replayAccepted
      replay indexed
  exact ay_ucdi_replay_accepted indexedClauses replayCovered replayAccepted
    replay covered

theorem ay_ucdi_accepted_original_unsat
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_ucdi_accepted_empty_clause dependencyIndex stableClauseIds
      indexedClauses parentsCovered emptyClause retainedOrRehydrated
      lineageAccepted archiveDigestMember digestAccepted replayCovered
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat accepted
  have reconstruction :
      AyUCDIReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_ucdi_index_reconstruction dependencyIndex stableClauseIds
      indexedClauses parentsCovered emptyClause retainedOrRehydrated
      lineageAccepted archiveDigestMember digestAccepted replayCovered
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat accepted
  have visible : visibleUnsat :=
    ay_ucdi_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_ucdi_original_unsat emptyClause visibleUnsat originalUnsat
    reconstruction visible

theorem ay_ucdi_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUCDIPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucdi_disj_right noClaim originalUnsat unsat

theorem ay_ucdi_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUCDIPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucdi_disj_left noClaim originalUnsat no_claim

theorem ay_ucdi_accepted_index_publish_sound
    (dependencyIndex : Prop) (stableClauseIds : Prop)
    (indexedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retainedOrRehydrated : Prop)
    (lineageAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (replayCovered : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUCDIAcceptedIndex dependencyIndex stableClauseIds indexedClauses
      parentsCovered emptyClause retainedOrRehydrated lineageAccepted
      archiveDigestMember digestAccepted replayCovered replayAccepted
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCDIPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_ucdi_public_unsat_report noClaim originalUnsat
    (ay_ucdi_accepted_original_unsat dependencyIndex stableClauseIds
      indexedClauses parentsCovered emptyClause retainedOrRehydrated
      lineageAccepted archiveDigestMember digestAccepted replayCovered
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat accepted)

theorem ay_ucdi_bad_index_no_claim
    (missingParent : Prop) (deletedUnretained : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCDIBadIndex missingParent deletedUnretained digestMismatch
      replayRejected fingerprintDrift noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_ucdi_bad_index_recompute
    (missingParent : Prop) (deletedUnretained : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCDIBadIndex missingParent deletedUnretained digestMismatch
      replayRejected fingerprintDrift noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_ucdi_bad_index_public_no_claim
    (missingParent : Prop) (deletedUnretained : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUCDIBadIndex missingParent deletedUnretained digestMismatch
      replayRejected fingerprintDrift noClaim recompute ->
    AyUCDIPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucdi_public_no_claim_report noClaim originalUnsat
    (ay_ucdi_bad_index_no_claim missingParent deletedUnretained
      digestMismatch replayRejected fingerprintDrift noClaim recompute bad)

theorem ay_ucdi_bad_index_cannot_publish
    (missingParent : Prop) (deletedUnretained : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCDIBadIndex missingParent deletedUnretained digestMismatch
      replayRejected fingerprintDrift noClaim recompute ->
    AyUCDIConj noClaim recompute := by
  intro bad
  exact bad (AyUCDIConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

