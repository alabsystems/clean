-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT clause-activity replay archive soundness for ay.
-- Propositions stand for activity ledgers, retained clause IDs, parent
-- coverage, deletion/retention lineage, replay epochs, digest membership,
-- checker replay transcripts, original fingerprint agreement, and fail-closed
-- no-claim/recompute diagnostics.

def AyUCAAConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCAADisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCAAMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCAAActivityLedger
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) :=
  AyUCAAConj activityLedger
    (AyUCAAConj
      (AyUCAAMap activityLedger retainedClauseIds)
      (AyUCAAMap retainedClauseIds rankedClauses))

def AyUCAAParentCoverage
    (rankedClauses : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :=
  AyUCAAConj
    (AyUCAAMap rankedClauses parentCoverage)
    (AyUCAAMap parentCoverage emptyClause)

def AyUCAALineage
    (rankedClauses : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) :=
  AyUCAAConj
    (AyUCAAMap rankedClauses retentionLineage)
    (AyUCAAMap retentionLineage lineageAccepted)

def AyUCAAEpoch
    (rankedClauses : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) :=
  AyUCAAConj
    (AyUCAAMap rankedClauses replayEpoch)
    (AyUCAAMap replayEpoch epochAccepted)

def AyUCAADigest
    (rankedClauses : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :=
  AyUCAAConj
    (AyUCAAMap rankedClauses digestMember)
    (AyUCAAMap digestMember digestAccepted)

def AyUCAAReplay
    (rankedClauses : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) :=
  AyUCAAConj
    (AyUCAAMap rankedClauses checkerTranscript)
    (AyUCAAMap checkerTranscript replayAccepted)

def AyUCAAFingerprint
    (rankedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUCAAConj
    (AyUCAAMap rankedClauses fingerprintAgrees)
    (AyUCAAMap fingerprintAgrees visibleUnsat)

def AyUCAAReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUCAAConj
    (AyUCAAMap emptyClause visibleUnsat)
    (AyUCAAMap visibleUnsat originalUnsat)

def AyUCAAAcceptedArchive
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCAAConj
    (AyUCAAActivityLedger activityLedger retainedClauseIds rankedClauses)
    (AyUCAAConj
      (AyUCAAParentCoverage rankedClauses parentCoverage emptyClause)
      (AyUCAAConj
        (AyUCAALineage rankedClauses retentionLineage lineageAccepted)
        (AyUCAAConj
          (AyUCAAEpoch rankedClauses replayEpoch epochAccepted)
          (AyUCAAConj
            (AyUCAADigest rankedClauses digestMember digestAccepted)
            (AyUCAAConj
              (AyUCAAReplay rankedClauses checkerTranscript replayAccepted)
              (AyUCAAConj
                (AyUCAAFingerprint rankedClauses fingerprintAgrees
                  visibleUnsat)
                (AyUCAAReconstruction emptyClause visibleUnsat
                  originalUnsat)))))))

def AyUCAABadArchive
    (missingLedger : Prop) (staleRetainedClauseId : Prop)
    (parentGap : Prop) (unretainedDeletion : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUCAAConj
    (AyUCAAConj noClaim recompute)
    (AyUCAADisj missingLedger
      (AyUCAADisj staleRetainedClauseId
        (AyUCAADisj parentGap
          (AyUCAADisj unretainedDeletion
            (AyUCAADisj epochDrift
              (AyUCAADisj digestMismatch
                (AyUCAADisj replayRejected fingerprintDrift)))))))

def AyUCAAPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCAADisj noClaim originalUnsat

theorem ay_ucaa_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCAAConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucaa_conj_left
    (p : Prop) (q : Prop) :
    AyUCAAConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucaa_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCAADisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucaa_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCAADisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucaa_activity_ledger
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) :
    AyUCAAActivityLedger activityLedger retainedClauseIds rankedClauses ->
    activityLedger := by
  intro ledger
  exact ay_ucaa_conj_left activityLedger
    (AyUCAAConj
      (AyUCAAMap activityLedger retainedClauseIds)
      (AyUCAAMap retainedClauseIds rankedClauses))
    ledger

theorem ay_ucaa_retained_clause_ids
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) :
    AyUCAAActivityLedger activityLedger retainedClauseIds rankedClauses ->
    retainedClauseIds := by
  intro ledger
  exact ledger retainedClauseIds
    (fun activity tail =>
      tail retainedClauseIds
        (fun activity_to_ids _ids_to_ranked =>
          activity_to_ids activity))

theorem ay_ucaa_ranked_clauses
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) :
    AyUCAAActivityLedger activityLedger retainedClauseIds rankedClauses ->
    rankedClauses := by
  intro ledger
  exact ledger rankedClauses
    (fun activity tail =>
      tail rankedClauses
        (fun activity_to_ids ids_to_ranked =>
          ids_to_ranked (activity_to_ids activity)))

theorem ay_ucaa_parent_coverage
    (rankedClauses : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUCAAParentCoverage rankedClauses parentCoverage emptyClause ->
    rankedClauses ->
    parentCoverage := by
  intro coverage
  exact coverage (rankedClauses -> parentCoverage)
    (fun ranked_to_parents _parents_to_empty => ranked_to_parents)

theorem ay_ucaa_empty_clause
    (rankedClauses : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUCAAParentCoverage rankedClauses parentCoverage emptyClause ->
    parentCoverage ->
    emptyClause := by
  intro coverage
  exact coverage (parentCoverage -> emptyClause)
    (fun _ranked_to_parents parents_to_empty => parents_to_empty)

theorem ay_ucaa_retention_lineage
    (rankedClauses : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) :
    AyUCAALineage rankedClauses retentionLineage lineageAccepted ->
    rankedClauses ->
    retentionLineage := by
  intro lineage
  exact lineage (rankedClauses -> retentionLineage)
    (fun ranked_to_lineage _lineage_to_accept => ranked_to_lineage)

theorem ay_ucaa_lineage_accepted
    (rankedClauses : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) :
    AyUCAALineage rankedClauses retentionLineage lineageAccepted ->
    retentionLineage ->
    lineageAccepted := by
  intro lineage
  exact lineage (retentionLineage -> lineageAccepted)
    (fun _ranked_to_lineage lineage_to_accept => lineage_to_accept)

theorem ay_ucaa_replay_epoch
    (rankedClauses : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) :
    AyUCAAEpoch rankedClauses replayEpoch epochAccepted ->
    rankedClauses ->
    replayEpoch := by
  intro epoch
  exact epoch (rankedClauses -> replayEpoch)
    (fun ranked_to_epoch _epoch_to_accept => ranked_to_epoch)

theorem ay_ucaa_epoch_accepted
    (rankedClauses : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) :
    AyUCAAEpoch rankedClauses replayEpoch epochAccepted ->
    replayEpoch ->
    epochAccepted := by
  intro epoch
  exact epoch (replayEpoch -> epochAccepted)
    (fun _ranked_to_epoch epoch_to_accept => epoch_to_accept)

theorem ay_ucaa_digest_member
    (rankedClauses : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUCAADigest rankedClauses digestMember digestAccepted ->
    rankedClauses ->
    digestMember := by
  intro digest
  exact digest (rankedClauses -> digestMember)
    (fun ranked_to_digest _digest_to_accept => ranked_to_digest)

theorem ay_ucaa_digest_accepted
    (rankedClauses : Prop) (digestMember : Prop)
    (digestAccepted : Prop) :
    AyUCAADigest rankedClauses digestMember digestAccepted ->
    digestMember ->
    digestAccepted := by
  intro digest
  exact digest (digestMember -> digestAccepted)
    (fun _ranked_to_digest digest_to_accept => digest_to_accept)

theorem ay_ucaa_checker_transcript
    (rankedClauses : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) :
    AyUCAAReplay rankedClauses checkerTranscript replayAccepted ->
    rankedClauses ->
    checkerTranscript := by
  intro replay
  exact replay (rankedClauses -> checkerTranscript)
    (fun ranked_to_transcript _transcript_to_accept => ranked_to_transcript)

theorem ay_ucaa_replay_accepted
    (rankedClauses : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) :
    AyUCAAReplay rankedClauses checkerTranscript replayAccepted ->
    checkerTranscript ->
    replayAccepted := by
  intro replay
  exact replay (checkerTranscript -> replayAccepted)
    (fun _ranked_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_ucaa_fingerprint_agrees
    (rankedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUCAAFingerprint rankedClauses fingerprintAgrees visibleUnsat ->
    rankedClauses ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (rankedClauses -> fingerprintAgrees)
    (fun ranked_to_fingerprint _fingerprint_to_visible =>
      ranked_to_fingerprint)

theorem ay_ucaa_visible_unsat
    (rankedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUCAAFingerprint rankedClauses fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _ranked_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_ucaa_reconstructed_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCAAReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_ucaa_original_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCAAReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_ucaa_archive_ledger
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCAAAcceptedArchive activityLedger retainedClauseIds rankedClauses
      parentCoverage emptyClause retentionLineage lineageAccepted replayEpoch
      epochAccepted digestMember digestAccepted checkerTranscript
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCAAActivityLedger activityLedger retainedClauseIds rankedClauses := by
  intro archive
  exact ay_ucaa_conj_left
    (AyUCAAActivityLedger activityLedger retainedClauseIds rankedClauses)
    (AyUCAAConj
      (AyUCAAParentCoverage rankedClauses parentCoverage emptyClause)
      (AyUCAAConj
        (AyUCAALineage rankedClauses retentionLineage lineageAccepted)
        (AyUCAAConj
          (AyUCAAEpoch rankedClauses replayEpoch epochAccepted)
          (AyUCAAConj
            (AyUCAADigest rankedClauses digestMember digestAccepted)
            (AyUCAAConj
              (AyUCAAReplay rankedClauses checkerTranscript replayAccepted)
              (AyUCAAConj
                (AyUCAAFingerprint rankedClauses fingerprintAgrees
                  visibleUnsat)
                (AyUCAAReconstruction emptyClause visibleUnsat
                  originalUnsat)))))))
    archive

theorem ay_ucaa_archive_parent_coverage
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCAAAcceptedArchive activityLedger retainedClauseIds rankedClauses
      parentCoverage emptyClause retentionLineage lineageAccepted replayEpoch
      epochAccepted digestMember digestAccepted checkerTranscript
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCAAParentCoverage rankedClauses parentCoverage emptyClause := by
  intro archive
  exact archive (AyUCAAParentCoverage rankedClauses parentCoverage emptyClause)
    (fun _ledger tail =>
      ay_ucaa_conj_left
        (AyUCAAParentCoverage rankedClauses parentCoverage emptyClause)
        (AyUCAAConj
          (AyUCAALineage rankedClauses retentionLineage lineageAccepted)
          (AyUCAAConj
            (AyUCAAEpoch rankedClauses replayEpoch epochAccepted)
            (AyUCAAConj
              (AyUCAADigest rankedClauses digestMember digestAccepted)
              (AyUCAAConj
                (AyUCAAReplay rankedClauses checkerTranscript
                  replayAccepted)
                (AyUCAAConj
                  (AyUCAAFingerprint rankedClauses fingerprintAgrees
                    visibleUnsat)
                  (AyUCAAReconstruction emptyClause visibleUnsat
                    originalUnsat))))))
        tail)

theorem ay_ucaa_archive_ranked_clauses
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCAAAcceptedArchive activityLedger retainedClauseIds rankedClauses
      parentCoverage emptyClause retentionLineage lineageAccepted replayEpoch
      epochAccepted digestMember digestAccepted checkerTranscript
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat ->
    rankedClauses := by
  intro archive
  exact ay_ucaa_ranked_clauses activityLedger retainedClauseIds rankedClauses
    (ay_ucaa_archive_ledger activityLedger retainedClauseIds rankedClauses
      parentCoverage emptyClause retentionLineage lineageAccepted replayEpoch
      epochAccepted digestMember digestAccepted checkerTranscript
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat archive)

theorem ay_ucaa_archive_empty_clause
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCAAAcceptedArchive activityLedger retainedClauseIds rankedClauses
      parentCoverage emptyClause retentionLineage lineageAccepted replayEpoch
      epochAccepted digestMember digestAccepted checkerTranscript
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat ->
    emptyClause := by
  intro archive
  exact ay_ucaa_empty_clause rankedClauses parentCoverage emptyClause
    (ay_ucaa_archive_parent_coverage activityLedger retainedClauseIds
      rankedClauses parentCoverage emptyClause retentionLineage
      lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
      checkerTranscript replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat archive)
    (ay_ucaa_parent_coverage rankedClauses parentCoverage emptyClause
      (ay_ucaa_archive_parent_coverage activityLedger retainedClauseIds
        rankedClauses parentCoverage emptyClause retentionLineage
        lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
        checkerTranscript replayAccepted fingerprintAgrees visibleUnsat
        originalUnsat archive)
      (ay_ucaa_archive_ranked_clauses activityLedger retainedClauseIds
        rankedClauses parentCoverage emptyClause retentionLineage
        lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
        checkerTranscript replayAccepted fingerprintAgrees visibleUnsat
        originalUnsat archive))

theorem ay_ucaa_archive_reconstruction
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCAAAcceptedArchive activityLedger retainedClauseIds rankedClauses
      parentCoverage emptyClause retentionLineage lineageAccepted replayEpoch
      epochAccepted digestMember digestAccepted checkerTranscript
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCAAReconstruction emptyClause visibleUnsat originalUnsat := by
  intro archive
  exact archive (AyUCAAReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _ledger tail =>
      tail (AyUCAAReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _coverage tail2 =>
          tail2 (AyUCAAReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _lineage tail3 =>
              tail3
                (AyUCAAReconstruction emptyClause visibleUnsat originalUnsat)
                (fun _epoch tail4 =>
                  tail4
                    (AyUCAAReconstruction emptyClause visibleUnsat
                      originalUnsat)
                    (fun _digest tail5 =>
                      tail5
                        (AyUCAAReconstruction emptyClause visibleUnsat
                          originalUnsat)
                        (fun _replay tail6 =>
                          tail6
                            (AyUCAAReconstruction emptyClause visibleUnsat
                              originalUnsat)
                            (fun _fingerprint reconstruction =>
                              reconstruction)))))))

theorem ay_ucaa_archive_original_unsat
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCAAAcceptedArchive activityLedger retainedClauseIds rankedClauses
      parentCoverage emptyClause retentionLineage lineageAccepted replayEpoch
      epochAccepted digestMember digestAccepted checkerTranscript
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro archive
  have reconstruction :
      AyUCAAReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_ucaa_archive_reconstruction activityLedger retainedClauseIds
      rankedClauses parentCoverage emptyClause retentionLineage
      lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
      checkerTranscript replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat archive
  have empty : emptyClause :=
    ay_ucaa_archive_empty_clause activityLedger retainedClauseIds rankedClauses
      parentCoverage emptyClause retentionLineage lineageAccepted replayEpoch
      epochAccepted digestMember digestAccepted checkerTranscript
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat archive
  have visible : visibleUnsat :=
    ay_ucaa_reconstructed_visible_unsat emptyClause visibleUnsat
      originalUnsat reconstruction empty
  exact ay_ucaa_original_unsat emptyClause visibleUnsat originalUnsat
    reconstruction visible

theorem ay_ucaa_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUCAAPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucaa_disj_right noClaim originalUnsat unsat

theorem ay_ucaa_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUCAAPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucaa_disj_left noClaim originalUnsat no_claim

theorem ay_ucaa_accepted_archive_publish_sound
    (activityLedger : Prop) (retainedClauseIds : Prop)
    (rankedClauses : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (retentionLineage : Prop)
    (lineageAccepted : Prop) (replayEpoch : Prop)
    (epochAccepted : Prop) (digestMember : Prop)
    (digestAccepted : Prop) (checkerTranscript : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUCAAAcceptedArchive activityLedger retainedClauseIds rankedClauses
      parentCoverage emptyClause retentionLineage lineageAccepted replayEpoch
      epochAccepted digestMember digestAccepted checkerTranscript
      replayAccepted fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCAAPublicReport noClaim originalUnsat := by
  intro archive
  exact ay_ucaa_public_unsat_report noClaim originalUnsat
    (ay_ucaa_archive_original_unsat activityLedger retainedClauseIds
      rankedClauses parentCoverage emptyClause retentionLineage
      lineageAccepted replayEpoch epochAccepted digestMember digestAccepted
      checkerTranscript replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat archive)

theorem ay_ucaa_bad_archive_no_claim
    (missingLedger : Prop) (staleRetainedClauseId : Prop)
    (parentGap : Prop) (unretainedDeletion : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCAABadArchive missingLedger staleRetainedClauseId parentGap
      unretainedDeletion epochDrift digestMismatch replayRejected
      fingerprintDrift noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_ucaa_conj_left noClaim recompute fail_closed)

theorem ay_ucaa_bad_archive_recompute
    (missingLedger : Prop) (staleRetainedClauseId : Prop)
    (parentGap : Prop) (unretainedDeletion : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCAABadArchive missingLedger staleRetainedClauseId parentGap
      unretainedDeletion epochDrift digestMismatch replayRejected
      fingerprintDrift noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_ucaa_bad_archive_public_no_claim
    (missingLedger : Prop) (staleRetainedClauseId : Prop)
    (parentGap : Prop) (unretainedDeletion : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCAABadArchive missingLedger staleRetainedClauseId parentGap
      unretainedDeletion epochDrift digestMismatch replayRejected
      fingerprintDrift noClaim recompute ->
    AyUCAAPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucaa_public_no_claim_report noClaim originalUnsat
    (ay_ucaa_bad_archive_no_claim missingLedger staleRetainedClauseId
      parentGap unretainedDeletion epochDrift digestMismatch replayRejected
      fingerprintDrift noClaim recompute bad)

theorem ay_ucaa_bad_archive_cannot_publish
    (missingLedger : Prop) (staleRetainedClauseId : Prop)
    (parentGap : Prop) (unretainedDeletion : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCAABadArchive missingLedger staleRetainedClauseId parentGap
      unretainedDeletion epochDrift digestMismatch replayRejected
      fingerprintDrift noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_ucaa_bad_archive_no_claim missingLedger staleRetainedClauseId
      parentGap unretainedDeletion epochDrift digestMismatch replayRejected
      fingerprintDrift noClaim recompute bad)
    unsat
