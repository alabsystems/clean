-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT restart clause-retention soundness for ay. Propositions stand
-- for stable retained-clause IDs, restart epoch lineage, parent coverage,
-- deletion/retention audit records, archive digest membership, checker replay
-- transcripts, original-instance fingerprint agreement, and fail-closed
-- no-claim/recompute diagnostics.

def AyURCRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyURCRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyURCRMap (source : Prop) (target : Prop) :=
  source -> target

def AyURCRStableClauseIds
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) :=
  AyURCRConj retentionIndex
    (AyURCRConj
      (AyURCRMap retentionIndex stableClauseIds)
      (AyURCRMap stableClauseIds retainedClauses))

def AyURCREpochLineage
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) :=
  AyURCRConj
    (AyURCRMap retainedClauses restartEpochLineage)
    (AyURCRMap restartEpochLineage epochAccepted)

def AyURCRParentCoverage
    (retainedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :=
  AyURCRConj
    (AyURCRMap retainedClauses parentsCovered)
    (AyURCRMap parentsCovered emptyClause)

def AyURCRAuditRecord
    (retainedClauses : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) :=
  AyURCRConj
    (AyURCRMap retainedClauses retentionAudit)
    (AyURCRMap retentionAudit auditAccepted)

def AyURCRArchiveDigest
    (retainedClauses : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) :=
  AyURCRConj
    (AyURCRMap retainedClauses archiveDigestMember)
    (AyURCRMap archiveDigestMember digestAccepted)

def AyURCRCheckerReplay
    (retainedClauses : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyURCRConj
    (AyURCRMap retainedClauses checkerReplay)
    (AyURCRMap checkerReplay replayAccepted)

def AyURCRFingerprint
    (retainedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyURCRConj
    (AyURCRMap retainedClauses fingerprintAgrees)
    (AyURCRMap fingerprintAgrees visibleUnsat)

def AyURCRReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyURCRConj
    (AyURCRMap emptyClause visibleUnsat)
    (AyURCRMap visibleUnsat originalUnsat)

def AyURCRAcceptedRetention
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyURCRConj
    (AyURCRStableClauseIds retentionIndex stableClauseIds retainedClauses)
    (AyURCRConj
      (AyURCREpochLineage retainedClauses restartEpochLineage
        epochAccepted)
      (AyURCRConj
        (AyURCRParentCoverage retainedClauses parentsCovered emptyClause)
        (AyURCRConj
          (AyURCRAuditRecord retainedClauses retentionAudit auditAccepted)
          (AyURCRConj
            (AyURCRArchiveDigest retainedClauses archiveDigestMember
              digestAccepted)
            (AyURCRConj
              (AyURCRCheckerReplay retainedClauses checkerReplay
                replayAccepted)
              (AyURCRConj
                (AyURCRFingerprint retainedClauses fingerprintAgrees
                  visibleUnsat)
                (AyURCRReconstruction emptyClause visibleUnsat
                  originalUnsat)))))))

def AyURCRBadRetention
    (missingRetainedParent : Prop) (staleEpochLineage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (contradictoryAudit : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyURCRConj
    (AyURCRConj noClaim recompute)
    (AyURCRDisj missingRetainedParent
      (AyURCRDisj staleEpochLineage
        (AyURCRDisj digestMismatch
          (AyURCRDisj replayRejected
            (AyURCRDisj fingerprintDrift contradictoryAudit)))))

def AyURCRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyURCRDisj noClaim originalUnsat

theorem ay_urcr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyURCRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_urcr_conj_left
    (p : Prop) (q : Prop) :
    AyURCRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_urcr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyURCRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_urcr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyURCRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_urcr_retention_index
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) :
    AyURCRStableClauseIds retentionIndex stableClauseIds retainedClauses ->
    retentionIndex := by
  intro ids
  exact ay_urcr_conj_left retentionIndex
    (AyURCRConj
      (AyURCRMap retentionIndex stableClauseIds)
      (AyURCRMap stableClauseIds retainedClauses))
    ids

theorem ay_urcr_stable_clause_ids
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) :
    AyURCRStableClauseIds retentionIndex stableClauseIds retainedClauses ->
    stableClauseIds := by
  intro ids
  exact ids stableClauseIds
    (fun index tail =>
      tail stableClauseIds
        (fun index_to_stable _stable_to_retained =>
          index_to_stable index))

theorem ay_urcr_retained_clauses
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) :
    AyURCRStableClauseIds retentionIndex stableClauseIds retainedClauses ->
    retainedClauses := by
  intro ids
  exact ids retainedClauses
    (fun index tail =>
      tail retainedClauses
        (fun index_to_stable stable_to_retained =>
          stable_to_retained (index_to_stable index)))

theorem ay_urcr_epoch_lineage
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) :
    AyURCREpochLineage retainedClauses restartEpochLineage
      epochAccepted ->
    retainedClauses ->
    restartEpochLineage := by
  intro epoch
  exact epoch (retainedClauses -> restartEpochLineage)
    (fun retained_to_epoch _epoch_to_accept => retained_to_epoch)

theorem ay_urcr_epoch_accepted
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) :
    AyURCREpochLineage retainedClauses restartEpochLineage
      epochAccepted ->
    restartEpochLineage ->
    epochAccepted := by
  intro epoch
  exact epoch (restartEpochLineage -> epochAccepted)
    (fun _retained_to_epoch epoch_to_accept => epoch_to_accept)

theorem ay_urcr_parents_covered
    (retainedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :
    AyURCRParentCoverage retainedClauses parentsCovered emptyClause ->
    retainedClauses ->
    parentsCovered := by
  intro coverage
  exact coverage (retainedClauses -> parentsCovered)
    (fun retained_to_parents _parents_to_empty => retained_to_parents)

theorem ay_urcr_empty_clause
    (retainedClauses : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) :
    AyURCRParentCoverage retainedClauses parentsCovered emptyClause ->
    parentsCovered ->
    emptyClause := by
  intro coverage
  exact coverage (parentsCovered -> emptyClause)
    (fun _retained_to_parents parents_to_empty => parents_to_empty)

theorem ay_urcr_retention_audit
    (retainedClauses : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) :
    AyURCRAuditRecord retainedClauses retentionAudit auditAccepted ->
    retainedClauses ->
    retentionAudit := by
  intro audit
  exact audit (retainedClauses -> retentionAudit)
    (fun retained_to_audit _audit_to_accept => retained_to_audit)

theorem ay_urcr_audit_accepted
    (retainedClauses : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) :
    AyURCRAuditRecord retainedClauses retentionAudit auditAccepted ->
    retentionAudit ->
    auditAccepted := by
  intro audit
  exact audit (retentionAudit -> auditAccepted)
    (fun _retained_to_audit audit_to_accept => audit_to_accept)

theorem ay_urcr_archive_digest_member
    (retainedClauses : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) :
    AyURCRArchiveDigest retainedClauses archiveDigestMember
      digestAccepted ->
    retainedClauses ->
    archiveDigestMember := by
  intro digest
  exact digest (retainedClauses -> archiveDigestMember)
    (fun retained_to_digest _digest_to_accept => retained_to_digest)

theorem ay_urcr_digest_accepted
    (retainedClauses : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) :
    AyURCRArchiveDigest retainedClauses archiveDigestMember
      digestAccepted ->
    archiveDigestMember ->
    digestAccepted := by
  intro digest
  exact digest (archiveDigestMember -> digestAccepted)
    (fun _retained_to_digest digest_to_accept => digest_to_accept)

theorem ay_urcr_replay_transcript
    (retainedClauses : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyURCRCheckerReplay retainedClauses checkerReplay replayAccepted ->
    retainedClauses ->
    checkerReplay := by
  intro replay
  exact replay (retainedClauses -> checkerReplay)
    (fun retained_to_replay _replay_to_accept => retained_to_replay)

theorem ay_urcr_replay_accepted
    (retainedClauses : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyURCRCheckerReplay retainedClauses checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _retained_to_replay replay_to_accept => replay_to_accept)

theorem ay_urcr_fingerprint_agrees
    (retainedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyURCRFingerprint retainedClauses fingerprintAgrees visibleUnsat ->
    retainedClauses ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (retainedClauses -> fingerprintAgrees)
    (fun retained_to_fingerprint _fingerprint_to_visible =>
      retained_to_fingerprint)

theorem ay_urcr_visible_from_fingerprint
    (retainedClauses : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyURCRFingerprint retainedClauses fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _retained_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_urcr_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyURCRReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_urcr_original_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyURCRReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_urcr_accepted_stable_ids
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    AyURCRStableClauseIds retentionIndex stableClauseIds retainedClauses := by
  intro accepted
  exact ay_urcr_conj_left
    (AyURCRStableClauseIds retentionIndex stableClauseIds retainedClauses)
    (AyURCRConj
      (AyURCREpochLineage retainedClauses restartEpochLineage
        epochAccepted)
      (AyURCRConj
        (AyURCRParentCoverage retainedClauses parentsCovered emptyClause)
        (AyURCRConj
          (AyURCRAuditRecord retainedClauses retentionAudit auditAccepted)
          (AyURCRConj
            (AyURCRArchiveDigest retainedClauses archiveDigestMember
              digestAccepted)
            (AyURCRConj
              (AyURCRCheckerReplay retainedClauses checkerReplay
                replayAccepted)
              (AyURCRConj
                (AyURCRFingerprint retainedClauses fingerprintAgrees
                  visibleUnsat)
                (AyURCRReconstruction emptyClause visibleUnsat
                  originalUnsat)))))))
    accepted

theorem ay_urcr_accepted_epoch
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    AyURCREpochLineage retainedClauses restartEpochLineage
      epochAccepted := by
  intro accepted
  exact accepted
    (AyURCREpochLineage retainedClauses restartEpochLineage
      epochAccepted)
    (fun _ids tail =>
      tail
        (AyURCREpochLineage retainedClauses restartEpochLineage
          epochAccepted)
        (fun epoch _rest => epoch))

theorem ay_urcr_accepted_coverage
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    AyURCRParentCoverage retainedClauses parentsCovered emptyClause := by
  intro accepted
  exact accepted
    (AyURCRParentCoverage retainedClauses parentsCovered emptyClause)
    (fun _ids tail =>
      tail (AyURCRParentCoverage retainedClauses parentsCovered emptyClause)
        (fun _epoch rest =>
          rest (AyURCRParentCoverage retainedClauses parentsCovered
            emptyClause)
            (fun coverage _tail => coverage)))

theorem ay_urcr_accepted_audit
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    AyURCRAuditRecord retainedClauses retentionAudit auditAccepted := by
  intro accepted
  exact accepted
    (AyURCRAuditRecord retainedClauses retentionAudit auditAccepted)
    (fun _ids tail =>
      tail (AyURCRAuditRecord retainedClauses retentionAudit auditAccepted)
        (fun _epoch rest =>
          rest (AyURCRAuditRecord retainedClauses retentionAudit auditAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyURCRAuditRecord retainedClauses retentionAudit
                  auditAccepted)
                (fun audit _tail => audit))))

theorem ay_urcr_accepted_digest
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    AyURCRArchiveDigest retainedClauses archiveDigestMember digestAccepted := by
  intro accepted
  exact accepted
    (AyURCRArchiveDigest retainedClauses archiveDigestMember digestAccepted)
    (fun _ids tail =>
      tail
        (AyURCRArchiveDigest retainedClauses archiveDigestMember
          digestAccepted)
        (fun _epoch rest =>
          rest
            (AyURCRArchiveDigest retainedClauses archiveDigestMember
              digestAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyURCRArchiveDigest retainedClauses archiveDigestMember
                  digestAccepted)
                (fun _audit tail3 =>
                  tail3
                    (AyURCRArchiveDigest retainedClauses archiveDigestMember
                      digestAccepted)
                    (fun digest _tail => digest)))))

theorem ay_urcr_accepted_replay_witness
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    AyURCRCheckerReplay retainedClauses checkerReplay replayAccepted := by
  intro accepted
  exact accepted
    (AyURCRCheckerReplay retainedClauses checkerReplay replayAccepted)
    (fun _ids tail =>
      tail (AyURCRCheckerReplay retainedClauses checkerReplay replayAccepted)
        (fun _epoch rest =>
          rest (AyURCRCheckerReplay retainedClauses checkerReplay
            replayAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyURCRCheckerReplay retainedClauses checkerReplay
                  replayAccepted)
                (fun _audit tail3 =>
                  tail3
                    (AyURCRCheckerReplay retainedClauses checkerReplay
                      replayAccepted)
                    (fun _digest tail4 =>
                      tail4
                        (AyURCRCheckerReplay retainedClauses checkerReplay
                          replayAccepted)
                        (fun replay _tail => replay))))))

theorem ay_urcr_accepted_fingerprint
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    AyURCRFingerprint retainedClauses fingerprintAgrees visibleUnsat := by
  intro accepted
  exact accepted
    (AyURCRFingerprint retainedClauses fingerprintAgrees visibleUnsat)
    (fun _ids tail =>
      tail (AyURCRFingerprint retainedClauses fingerprintAgrees visibleUnsat)
        (fun _epoch rest =>
          rest (AyURCRFingerprint retainedClauses fingerprintAgrees
            visibleUnsat)
            (fun _coverage tail2 =>
              tail2
                (AyURCRFingerprint retainedClauses fingerprintAgrees
                  visibleUnsat)
                (fun _audit tail3 =>
                  tail3
                    (AyURCRFingerprint retainedClauses fingerprintAgrees
                      visibleUnsat)
                    (fun _digest tail4 =>
                      tail4
                        (AyURCRFingerprint retainedClauses fingerprintAgrees
                          visibleUnsat)
                        (fun _replay tail5 =>
                          tail5
                            (AyURCRFingerprint retainedClauses
                              fingerprintAgrees visibleUnsat)
                            (fun fingerprint _reconstruction =>
                              fingerprint)))))))

theorem ay_urcr_accepted_reconstruction
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    AyURCRReconstruction emptyClause visibleUnsat originalUnsat := by
  intro accepted
  exact accepted (AyURCRReconstruction emptyClause visibleUnsat
    originalUnsat)
    (fun _ids tail =>
      tail (AyURCRReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _epoch rest =>
          rest (AyURCRReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _coverage tail2 =>
              tail2
                (AyURCRReconstruction emptyClause visibleUnsat originalUnsat)
                (fun _audit tail3 =>
                  tail3
                    (AyURCRReconstruction emptyClause visibleUnsat
                      originalUnsat)
                    (fun _digest tail4 =>
                      tail4
                        (AyURCRReconstruction emptyClause visibleUnsat
                          originalUnsat)
                        (fun _replay tail5 =>
                          tail5
                            (AyURCRReconstruction emptyClause visibleUnsat
                              originalUnsat)
                            (fun _fingerprint reconstruction =>
                              reconstruction)))))))

theorem ay_urcr_accepted_retained_clauses
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    retainedClauses := by
  intro accepted
  have ids :
      AyURCRStableClauseIds retentionIndex stableClauseIds retainedClauses :=
    ay_urcr_accepted_stable_ids retentionIndex stableClauseIds
      retainedClauses restartEpochLineage epochAccepted parentsCovered
      emptyClause retentionAudit auditAccepted archiveDigestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat accepted
  exact ay_urcr_retained_clauses retentionIndex stableClauseIds
    retainedClauses ids

theorem ay_urcr_accepted_empty_clause
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    emptyClause := by
  intro accepted
  have retained : retainedClauses :=
    ay_urcr_accepted_retained_clauses retentionIndex stableClauseIds
      retainedClauses restartEpochLineage epochAccepted parentsCovered
      emptyClause retentionAudit auditAccepted archiveDigestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat accepted
  have coverage :
      AyURCRParentCoverage retainedClauses parentsCovered emptyClause :=
    ay_urcr_accepted_coverage retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have parents : parentsCovered :=
    ay_urcr_parents_covered retainedClauses parentsCovered emptyClause
      coverage retained
  exact ay_urcr_empty_clause retainedClauses parentsCovered emptyClause
    coverage parents

theorem ay_urcr_accepted_epoch_valid
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    epochAccepted := by
  intro accepted
  have retained : retainedClauses :=
    ay_urcr_accepted_retained_clauses retentionIndex stableClauseIds
      retainedClauses restartEpochLineage epochAccepted parentsCovered
      emptyClause retentionAudit auditAccepted archiveDigestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat accepted
  have epoch :
      AyURCREpochLineage retainedClauses restartEpochLineage
        epochAccepted :=
    ay_urcr_accepted_epoch retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have lineage : restartEpochLineage :=
    ay_urcr_epoch_lineage retainedClauses restartEpochLineage
      epochAccepted epoch retained
  exact ay_urcr_epoch_accepted retainedClauses restartEpochLineage
    epochAccepted epoch lineage

theorem ay_urcr_accepted_audit_valid
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    auditAccepted := by
  intro accepted
  have retained : retainedClauses :=
    ay_urcr_accepted_retained_clauses retentionIndex stableClauseIds
      retainedClauses restartEpochLineage epochAccepted parentsCovered
      emptyClause retentionAudit auditAccepted archiveDigestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat accepted
  have audit :
      AyURCRAuditRecord retainedClauses retentionAudit auditAccepted :=
    ay_urcr_accepted_audit retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have audit_record : retentionAudit :=
    ay_urcr_retention_audit retainedClauses retentionAudit auditAccepted
      audit retained
  exact ay_urcr_audit_accepted retainedClauses retentionAudit
    auditAccepted audit audit_record

theorem ay_urcr_accepted_digest_valid
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    digestAccepted := by
  intro accepted
  have retained : retainedClauses :=
    ay_urcr_accepted_retained_clauses retentionIndex stableClauseIds
      retainedClauses restartEpochLineage epochAccepted parentsCovered
      emptyClause retentionAudit auditAccepted archiveDigestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat accepted
  have digest :
      AyURCRArchiveDigest retainedClauses archiveDigestMember
        digestAccepted :=
    ay_urcr_accepted_digest retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat accepted
  have member : archiveDigestMember :=
    ay_urcr_archive_digest_member retainedClauses archiveDigestMember
      digestAccepted digest retained
  exact ay_urcr_digest_accepted retainedClauses archiveDigestMember
    digestAccepted digest member

theorem ay_urcr_accepted_replay_valid
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    replayAccepted := by
  intro accepted
  have retained : retainedClauses :=
    ay_urcr_accepted_retained_clauses retentionIndex stableClauseIds
      retainedClauses restartEpochLineage epochAccepted parentsCovered
      emptyClause retentionAudit auditAccepted archiveDigestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat accepted
  have replay :
      AyURCRCheckerReplay retainedClauses checkerReplay replayAccepted :=
    ay_urcr_accepted_replay_witness retentionIndex stableClauseIds
      retainedClauses restartEpochLineage epochAccepted parentsCovered
      emptyClause retentionAudit auditAccepted archiveDigestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat accepted
  have transcript : checkerReplay :=
    ay_urcr_replay_transcript retainedClauses checkerReplay replayAccepted
      replay retained
  exact ay_urcr_replay_accepted retainedClauses checkerReplay
    replayAccepted replay transcript

theorem ay_urcr_accepted_original_unsat
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_urcr_accepted_empty_clause retentionIndex stableClauseIds
      retainedClauses restartEpochLineage epochAccepted parentsCovered
      emptyClause retentionAudit auditAccepted archiveDigestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat accepted
  have reconstruction :
      AyURCRReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_urcr_accepted_reconstruction retentionIndex stableClauseIds
      retainedClauses restartEpochLineage epochAccepted parentsCovered
      emptyClause retentionAudit auditAccepted archiveDigestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat accepted
  have visible : visibleUnsat :=
    ay_urcr_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_urcr_original_unsat emptyClause visibleUnsat originalUnsat
    reconstruction visible

theorem ay_urcr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyURCRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_urcr_disj_right noClaim originalUnsat unsat

theorem ay_urcr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyURCRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_urcr_disj_left noClaim originalUnsat no_claim

theorem ay_urcr_accepted_retention_publish_sound
    (retentionIndex : Prop) (stableClauseIds : Prop)
    (retainedClauses : Prop) (restartEpochLineage : Prop)
    (epochAccepted : Prop) (parentsCovered : Prop)
    (emptyClause : Prop) (retentionAudit : Prop)
    (auditAccepted : Prop) (archiveDigestMember : Prop)
    (digestAccepted : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyURCRAcceptedRetention retentionIndex stableClauseIds retainedClauses
      restartEpochLineage epochAccepted parentsCovered emptyClause
      retentionAudit auditAccepted archiveDigestMember digestAccepted
      checkerReplay replayAccepted fingerprintAgrees visibleUnsat
      originalUnsat ->
    AyURCRPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_urcr_public_unsat_report noClaim originalUnsat
    (ay_urcr_accepted_original_unsat retentionIndex stableClauseIds
      retainedClauses restartEpochLineage epochAccepted parentsCovered
      emptyClause retentionAudit auditAccepted archiveDigestMember
      digestAccepted checkerReplay replayAccepted fingerprintAgrees
      visibleUnsat originalUnsat accepted)

theorem ay_urcr_bad_retention_no_claim
    (missingRetainedParent : Prop) (staleEpochLineage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (contradictoryAudit : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyURCRBadRetention missingRetainedParent staleEpochLineage
      digestMismatch replayRejected fingerprintDrift contradictoryAudit
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_urcr_bad_retention_recompute
    (missingRetainedParent : Prop) (staleEpochLineage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (contradictoryAudit : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyURCRBadRetention missingRetainedParent staleEpochLineage
      digestMismatch replayRejected fingerprintDrift contradictoryAudit
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_urcr_bad_retention_public_no_claim
    (missingRetainedParent : Prop) (staleEpochLineage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (contradictoryAudit : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyURCRBadRetention missingRetainedParent staleEpochLineage
      digestMismatch replayRejected fingerprintDrift contradictoryAudit
      noClaim recompute ->
    AyURCRPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_urcr_public_no_claim_report noClaim originalUnsat
    (ay_urcr_bad_retention_no_claim missingRetainedParent
      staleEpochLineage digestMismatch replayRejected fingerprintDrift
      contradictoryAudit noClaim recompute bad)

theorem ay_urcr_bad_retention_cannot_publish
    (missingRetainedParent : Prop) (staleEpochLineage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (contradictoryAudit : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyURCRBadRetention missingRetainedParent staleEpochLineage
      digestMismatch replayRejected fingerprintDrift contradictoryAudit
      noClaim recompute ->
    AyURCRConj noClaim recompute := by
  intro bad
  exact bad (AyURCRConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

