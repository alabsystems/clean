-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded clause addition/deletion log soundness for ay UNSAT replay.
-- Propositions stand for compact add/delete logs, deletion safety, rehydration
-- before citation, dependency-covered additions, empty-clause reachability,
-- digest roots, checker replay, original reconstruction, and fail-closed
-- no-claim/recompute diagnostics.

def AyUCDLConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCDLDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCDLMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCDLDeletionSafety
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop) :=
  AyUCDLConj compactLog
    (AyUCDLConj
      (AyUCDLMap compactLog deletedUnused)
      (AyUCDLConj
        (AyUCDLMap compactLog rehydratedBeforeCitation)
        (AyUCDLMap
          (AyUCDLConj deletedUnused rehydratedBeforeCitation)
          deletionSafe)))

def AyUCDLAdditionCoverage
    (compactLog : Prop) (addedClausesCovered : Prop)
    (emptyClause : Prop) :=
  AyUCDLConj
    (AyUCDLMap compactLog addedClausesCovered)
    (AyUCDLMap addedClausesCovered emptyClause)

def AyUCDLDigestRoot
    (compactLog : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) :=
  AyUCDLConj
    (AyUCDLMap compactLog digestRoot)
    (AyUCDLMap digestRoot rootAccepted)

def AyUCDLCheckerReplay
    (compactLog : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUCDLConj
    (AyUCDLMap compactLog checkerReplay)
    (AyUCDLMap checkerReplay replayAccepted)

def AyUCDLReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUCDLConj
    (AyUCDLMap emptyClause visibleUnsat)
    (AyUCDLMap visibleUnsat originalUnsat)

def AyUCDLAcceptedLog
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop)
    (addedClausesCovered : Prop) (emptyClause : Prop)
    (digestRoot : Prop) (rootAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCDLConj
    (AyUCDLDeletionSafety compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe)
    (AyUCDLConj
      (AyUCDLAdditionCoverage compactLog addedClausesCovered emptyClause)
      (AyUCDLConj
        (AyUCDLDigestRoot compactLog digestRoot rootAccepted)
        (AyUCDLConj
          (AyUCDLCheckerReplay compactLog checkerReplay replayAccepted)
          (AyUCDLReconstruction emptyClause visibleUnsat originalUnsat))))

def AyUCDLBadLog
    (citesDeletedClause : Prop) (missingAddition : Prop)
    (staleDigestRoot : Prop) (replayRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUCDLConj
    (AyUCDLConj noClaim recompute)
    (AyUCDLDisj citesDeletedClause
      (AyUCDLDisj missingAddition
        (AyUCDLDisj staleDigestRoot replayRejected)))

def AyUCDLPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCDLDisj noClaim originalUnsat

theorem ay_ucdl_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCDLConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucdl_conj_left
    (p : Prop) (q : Prop) :
    AyUCDLConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucdl_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCDLDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucdl_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCDLDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucdl_deletion_compact_log
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop) :
    AyUCDLDeletionSafety compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe ->
    compactLog := by
  intro safety
  exact ay_ucdl_conj_left compactLog
    (AyUCDLConj
      (AyUCDLMap compactLog deletedUnused)
      (AyUCDLConj
        (AyUCDLMap compactLog rehydratedBeforeCitation)
        (AyUCDLMap
          (AyUCDLConj deletedUnused rehydratedBeforeCitation)
          deletionSafe)))
    safety

theorem ay_ucdl_deleted_unused
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop) :
    AyUCDLDeletionSafety compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe ->
    deletedUnused := by
  intro safety
  exact safety deletedUnused
    (fun log tail =>
      tail deletedUnused
        (fun log_to_unused _rest => log_to_unused log))

theorem ay_ucdl_rehydrated_before_citation
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop) :
    AyUCDLDeletionSafety compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe ->
    rehydratedBeforeCitation := by
  intro safety
  exact safety rehydratedBeforeCitation
    (fun log tail =>
      tail rehydratedBeforeCitation
        (fun _log_to_unused rest =>
          rest rehydratedBeforeCitation
            (fun log_to_rehydrated _both_to_safe =>
              log_to_rehydrated log)))

theorem ay_ucdl_deletion_safe
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop) :
    AyUCDLDeletionSafety compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe ->
    deletionSafe := by
  intro safety
  have unused : deletedUnused :=
    ay_ucdl_deleted_unused compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe safety
  have rehydrated : rehydratedBeforeCitation :=
    ay_ucdl_rehydrated_before_citation compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe safety
  exact safety deletionSafe
    (fun _log tail =>
      tail deletionSafe
        (fun _log_to_unused rest =>
          rest deletionSafe
            (fun _log_to_rehydrated both_to_safe =>
              both_to_safe
                (ay_ucdl_conj_intro deletedUnused rehydratedBeforeCitation
                  unused rehydrated))))

theorem ay_ucdl_added_clauses_covered
    (compactLog : Prop) (addedClausesCovered : Prop)
    (emptyClause : Prop) :
    AyUCDLAdditionCoverage compactLog addedClausesCovered emptyClause ->
    compactLog ->
    addedClausesCovered := by
  intro coverage
  exact coverage (compactLog -> addedClausesCovered)
    (fun log_to_covered _covered_to_empty => log_to_covered)

theorem ay_ucdl_empty_clause_from_additions
    (compactLog : Prop) (addedClausesCovered : Prop)
    (emptyClause : Prop) :
    AyUCDLAdditionCoverage compactLog addedClausesCovered emptyClause ->
    addedClausesCovered ->
    emptyClause := by
  intro coverage
  exact coverage (addedClausesCovered -> emptyClause)
    (fun _log_to_covered covered_to_empty => covered_to_empty)

theorem ay_ucdl_digest_root_value
    (compactLog : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) :
    AyUCDLDigestRoot compactLog digestRoot rootAccepted ->
    compactLog ->
    digestRoot := by
  intro root
  exact root (compactLog -> digestRoot)
    (fun log_to_root _root_to_accept => log_to_root)

theorem ay_ucdl_root_accepted
    (compactLog : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) :
    AyUCDLDigestRoot compactLog digestRoot rootAccepted ->
    digestRoot ->
    rootAccepted := by
  intro root
  exact root (digestRoot -> rootAccepted)
    (fun _log_to_root root_to_accept => root_to_accept)

theorem ay_ucdl_checker_replay_value
    (compactLog : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCDLCheckerReplay compactLog checkerReplay replayAccepted ->
    compactLog ->
    checkerReplay := by
  intro replay
  exact replay (compactLog -> checkerReplay)
    (fun log_to_replay _replay_to_accept => log_to_replay)

theorem ay_ucdl_replay_accepted
    (compactLog : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUCDLCheckerReplay compactLog checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _log_to_replay replay_to_accept => replay_to_accept)

theorem ay_ucdl_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCDLReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_ucdl_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCDLReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_ucdl_log_deletion_safety
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop)
    (addedClausesCovered : Prop) (emptyClause : Prop)
    (digestRoot : Prop) (rootAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDLAcceptedLog compactLog deletedUnused rehydratedBeforeCitation
      deletionSafe addedClausesCovered emptyClause digestRoot rootAccepted
      checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUCDLDeletionSafety compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe := by
  intro accepted
  exact ay_ucdl_conj_left
    (AyUCDLDeletionSafety compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe)
    (AyUCDLConj
      (AyUCDLAdditionCoverage compactLog addedClausesCovered emptyClause)
      (AyUCDLConj
        (AyUCDLDigestRoot compactLog digestRoot rootAccepted)
        (AyUCDLConj
          (AyUCDLCheckerReplay compactLog checkerReplay replayAccepted)
          (AyUCDLReconstruction emptyClause visibleUnsat originalUnsat))))
    accepted

theorem ay_ucdl_log_addition_coverage
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop)
    (addedClausesCovered : Prop) (emptyClause : Prop)
    (digestRoot : Prop) (rootAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDLAcceptedLog compactLog deletedUnused rehydratedBeforeCitation
      deletionSafe addedClausesCovered emptyClause digestRoot rootAccepted
      checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUCDLAdditionCoverage compactLog addedClausesCovered emptyClause := by
  intro accepted
  exact accepted
    (AyUCDLAdditionCoverage compactLog addedClausesCovered emptyClause)
    (fun _safety tail =>
      tail (AyUCDLAdditionCoverage compactLog addedClausesCovered emptyClause)
        (fun coverage _rest => coverage))

theorem ay_ucdl_log_digest_root
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop)
    (addedClausesCovered : Prop) (emptyClause : Prop)
    (digestRoot : Prop) (rootAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDLAcceptedLog compactLog deletedUnused rehydratedBeforeCitation
      deletionSafe addedClausesCovered emptyClause digestRoot rootAccepted
      checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUCDLDigestRoot compactLog digestRoot rootAccepted := by
  intro accepted
  exact accepted (AyUCDLDigestRoot compactLog digestRoot rootAccepted)
    (fun _safety tail =>
      tail (AyUCDLDigestRoot compactLog digestRoot rootAccepted)
        (fun _coverage rest =>
          rest (AyUCDLDigestRoot compactLog digestRoot rootAccepted)
            (fun root _tail => root)))

theorem ay_ucdl_log_checker_replay
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop)
    (addedClausesCovered : Prop) (emptyClause : Prop)
    (digestRoot : Prop) (rootAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDLAcceptedLog compactLog deletedUnused rehydratedBeforeCitation
      deletionSafe addedClausesCovered emptyClause digestRoot rootAccepted
      checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUCDLCheckerReplay compactLog checkerReplay replayAccepted := by
  intro accepted
  exact accepted (AyUCDLCheckerReplay compactLog checkerReplay replayAccepted)
    (fun _safety tail =>
      tail (AyUCDLCheckerReplay compactLog checkerReplay replayAccepted)
        (fun _coverage rest =>
          rest (AyUCDLCheckerReplay compactLog checkerReplay replayAccepted)
            (fun _root tail2 =>
              tail2
                (AyUCDLCheckerReplay compactLog checkerReplay replayAccepted)
                (fun replay _reconstruction => replay))))

theorem ay_ucdl_log_reconstruction
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop)
    (addedClausesCovered : Prop) (emptyClause : Prop)
    (digestRoot : Prop) (rootAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDLAcceptedLog compactLog deletedUnused rehydratedBeforeCitation
      deletionSafe addedClausesCovered emptyClause digestRoot rootAccepted
      checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUCDLReconstruction emptyClause visibleUnsat originalUnsat := by
  intro accepted
  exact accepted (AyUCDLReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _safety tail =>
      tail (AyUCDLReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _coverage rest =>
          rest (AyUCDLReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _root tail2 =>
              tail2
                (AyUCDLReconstruction emptyClause visibleUnsat originalUnsat)
                (fun _replay reconstruction => reconstruction))))

theorem ay_ucdl_log_root_accepted
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop)
    (addedClausesCovered : Prop) (emptyClause : Prop)
    (digestRoot : Prop) (rootAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDLAcceptedLog compactLog deletedUnused rehydratedBeforeCitation
      deletionSafe addedClausesCovered emptyClause digestRoot rootAccepted
      checkerReplay replayAccepted visibleUnsat originalUnsat ->
    rootAccepted := by
  intro accepted
  have safety :
      AyUCDLDeletionSafety compactLog deletedUnused
        rehydratedBeforeCitation deletionSafe :=
    ay_ucdl_log_deletion_safety compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe addedClausesCovered emptyClause
      digestRoot rootAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have root : AyUCDLDigestRoot compactLog digestRoot rootAccepted :=
    ay_ucdl_log_digest_root compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe addedClausesCovered emptyClause
      digestRoot rootAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have log : compactLog :=
    ay_ucdl_deletion_compact_log compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe safety
  have digest : digestRoot :=
    ay_ucdl_digest_root_value compactLog digestRoot rootAccepted root log
  exact ay_ucdl_root_accepted compactLog digestRoot rootAccepted root digest

theorem ay_ucdl_log_replay_accepted
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop)
    (addedClausesCovered : Prop) (emptyClause : Prop)
    (digestRoot : Prop) (rootAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDLAcceptedLog compactLog deletedUnused rehydratedBeforeCitation
      deletionSafe addedClausesCovered emptyClause digestRoot rootAccepted
      checkerReplay replayAccepted visibleUnsat originalUnsat ->
    replayAccepted := by
  intro accepted
  have safety :
      AyUCDLDeletionSafety compactLog deletedUnused
        rehydratedBeforeCitation deletionSafe :=
    ay_ucdl_log_deletion_safety compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe addedClausesCovered emptyClause
      digestRoot rootAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have replay : AyUCDLCheckerReplay compactLog checkerReplay replayAccepted :=
    ay_ucdl_log_checker_replay compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe addedClausesCovered emptyClause
      digestRoot rootAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have log : compactLog :=
    ay_ucdl_deletion_compact_log compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe safety
  have transcript : checkerReplay :=
    ay_ucdl_checker_replay_value compactLog checkerReplay replayAccepted
      replay log
  exact ay_ucdl_replay_accepted compactLog checkerReplay replayAccepted
    replay transcript

theorem ay_ucdl_log_empty_clause
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop)
    (addedClausesCovered : Prop) (emptyClause : Prop)
    (digestRoot : Prop) (rootAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDLAcceptedLog compactLog deletedUnused rehydratedBeforeCitation
      deletionSafe addedClausesCovered emptyClause digestRoot rootAccepted
      checkerReplay replayAccepted visibleUnsat originalUnsat ->
    emptyClause := by
  intro accepted
  have safety :
      AyUCDLDeletionSafety compactLog deletedUnused
        rehydratedBeforeCitation deletionSafe :=
    ay_ucdl_log_deletion_safety compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe addedClausesCovered emptyClause
      digestRoot rootAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have coverage :
      AyUCDLAdditionCoverage compactLog addedClausesCovered emptyClause :=
    ay_ucdl_log_addition_coverage compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe addedClausesCovered emptyClause
      digestRoot rootAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have log : compactLog :=
    ay_ucdl_deletion_compact_log compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe safety
  have covered : addedClausesCovered :=
    ay_ucdl_added_clauses_covered compactLog addedClausesCovered
      emptyClause coverage log
  exact ay_ucdl_empty_clause_from_additions compactLog
    addedClausesCovered emptyClause coverage covered

theorem ay_ucdl_accepted_log_original_unsat
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop)
    (addedClausesCovered : Prop) (emptyClause : Prop)
    (digestRoot : Prop) (rootAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDLAcceptedLog compactLog deletedUnused rehydratedBeforeCitation
      deletionSafe addedClausesCovered emptyClause digestRoot rootAccepted
      checkerReplay replayAccepted visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_ucdl_log_empty_clause compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe addedClausesCovered emptyClause
      digestRoot rootAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have reconstruction :
      AyUCDLReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_ucdl_log_reconstruction compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe addedClausesCovered emptyClause
      digestRoot rootAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted
  have visible : visibleUnsat :=
    ay_ucdl_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_ucdl_original_unsat_from_visible emptyClause visibleUnsat
    originalUnsat reconstruction visible

theorem ay_ucdl_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUCDLPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucdl_disj_right noClaim originalUnsat unsat

theorem ay_ucdl_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUCDLPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucdl_disj_left noClaim originalUnsat no_claim

theorem ay_ucdl_accepted_log_publish_sound
    (compactLog : Prop) (deletedUnused : Prop)
    (rehydratedBeforeCitation : Prop) (deletionSafe : Prop)
    (addedClausesCovered : Prop) (emptyClause : Prop)
    (digestRoot : Prop) (rootAccepted : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (noClaim : Prop) :
    AyUCDLAcceptedLog compactLog deletedUnused rehydratedBeforeCitation
      deletionSafe addedClausesCovered emptyClause digestRoot rootAccepted
      checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUCDLPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_ucdl_public_unsat_report noClaim originalUnsat
    (ay_ucdl_accepted_log_original_unsat compactLog deletedUnused
      rehydratedBeforeCitation deletionSafe addedClausesCovered emptyClause
      digestRoot rootAccepted checkerReplay replayAccepted visibleUnsat
      originalUnsat accepted)

theorem ay_ucdl_bad_log_no_claim
    (citesDeletedClause : Prop) (missingAddition : Prop)
    (staleDigestRoot : Prop) (replayRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDLBadLog citesDeletedClause missingAddition staleDigestRoot
      replayRejected noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_ucdl_bad_log_recompute
    (citesDeletedClause : Prop) (missingAddition : Prop)
    (staleDigestRoot : Prop) (replayRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDLBadLog citesDeletedClause missingAddition staleDigestRoot
      replayRejected noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_ucdl_bad_log_public_no_claim
    (citesDeletedClause : Prop) (missingAddition : Prop)
    (staleDigestRoot : Prop) (replayRejected : Prop)
    (noClaim : Prop) (originalUnsat : Prop) (recompute : Prop) :
    AyUCDLBadLog citesDeletedClause missingAddition staleDigestRoot
      replayRejected noClaim recompute ->
    AyUCDLPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucdl_public_no_claim_report noClaim originalUnsat
    (ay_ucdl_bad_log_no_claim citesDeletedClause missingAddition
      staleDigestRoot replayRejected noClaim recompute bad)

theorem ay_ucdl_bad_log_cannot_publish_unsat
    (citesDeletedClause : Prop) (missingAddition : Prop)
    (staleDigestRoot : Prop) (replayRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDLBadLog citesDeletedClause missingAddition staleDigestRoot
      replayRejected noClaim recompute ->
    AyUCDLConj noClaim recompute := by
  intro bad
  exact bad (AyUCDLConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

