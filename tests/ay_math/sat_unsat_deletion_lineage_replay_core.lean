-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded learned-clause deletion/resurrection lineage replay soundness for
-- ay sequential-main SAT-COMP UNSAT checking. Propositions stand for final
-- proof parents, deletion/retention lineage, epoch/digest membership, checker
-- transcripts, reconstruction handles, original fingerprints, and fail-closed
-- no-claim/recompute diagnostics.

def AyUDLRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUDLRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUDLRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUDLRParentLineage
    (finalParents : Prop) (deletionLineage : Prop)
    (retentionLineage : Prop) (lineageAccepted : Prop) :=
  AyUDLRConj
    (AyUDLRMap finalParents deletionLineage)
    (AyUDLRConj
      (AyUDLRMap deletionLineage retentionLineage)
      (AyUDLRMap retentionLineage lineageAccepted))

def AyUDLREmptyReplay
    (finalParents : Prop) (lineageAccepted : Prop)
    (emptyClause : Prop) :=
  AyUDLRConj
    (AyUDLRMap finalParents lineageAccepted)
    (AyUDLRMap lineageAccepted emptyClause)

def AyUDLREpochDigest
    (finalParents : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :=
  AyUDLRConj
    (AyUDLRMap finalParents epochMember)
    (AyUDLRConj
      (AyUDLRMap epochMember digestMember)
      (AyUDLRMap digestMember epochDigestAccepted))

def AyUDLRCheckerTranscript
    (finalParents : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :=
  AyUDLRConj
    (AyUDLRMap finalParents checkerTranscript)
    (AyUDLRMap checkerTranscript checkerAccepted)

def AyUDLRReconstruction
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUDLRConj reconstructionHandle
    (AyUDLRConj
      (AyUDLRMap emptyClause visibleUnsat)
      (AyUDLRMap visibleUnsat originalUnsat))

def AyUDLRFingerprint
    (finalParents : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUDLRConj
    (AyUDLRMap finalParents fingerprintAgrees)
    (AyUDLRMap fingerprintAgrees visibleUnsat)

def AyUDLRAcceptedEvidence
    (finalParents : Prop) (deletionLineage : Prop)
    (retentionLineage : Prop) (lineageAccepted : Prop)
    (emptyClause : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUDLRConj finalParents
    (AyUDLRConj
      (AyUDLRParentLineage finalParents deletionLineage retentionLineage
        lineageAccepted)
      (AyUDLRConj
        (AyUDLREmptyReplay finalParents lineageAccepted emptyClause)
        (AyUDLRConj
          (AyUDLREpochDigest finalParents epochMember digestMember
            epochDigestAccepted)
          (AyUDLRConj
            (AyUDLRCheckerTranscript finalParents checkerTranscript
              checkerAccepted)
            (AyUDLRConj
              (AyUDLRReconstruction emptyClause reconstructionHandle
                visibleUnsat originalUnsat)
              (AyUDLRFingerprint finalParents fingerprintAgrees
                visibleUnsat))))))

def AyUDLRAcceptedReplay
    (finalParents : Prop) (deletionLineage : Prop)
    (retentionLineage : Prop) (lineageAccepted : Prop)
    (emptyClause : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUDLRConj
    (AyUDLRAcceptedEvidence finalParents deletionLineage retentionLineage
      lineageAccepted emptyClause epochMember digestMember epochDigestAccepted
      checkerTranscript checkerAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat)
    originalUnsat

def AyUDLRBadReplay
    (lineageGap : Prop) (missingDeletedParent : Prop)
    (unretainedParent : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUDLRConj
    (AyUDLRConj noClaim recompute)
    (AyUDLRDisj lineageGap
      (AyUDLRDisj missingDeletedParent
        (AyUDLRDisj unretainedParent
          (AyUDLRDisj epochDrift
            (AyUDLRDisj digestMismatch
              (AyUDLRDisj checkerRejected
                (AyUDLRDisj reconstructionMismatch fingerprintDrift)))))))

def AyUDLRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUDLRDisj noClaim originalUnsat

theorem ay_udlr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUDLRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_udlr_conj_left
    (p : Prop) (q : Prop) :
    AyUDLRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_udlr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUDLRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_udlr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUDLRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_udlr_deletion_lineage
    (finalParents : Prop) (deletionLineage : Prop)
    (retentionLineage : Prop) (lineageAccepted : Prop) :
    AyUDLRParentLineage finalParents deletionLineage retentionLineage
      lineageAccepted ->
    finalParents ->
    deletionLineage := by
  intro lineage
  exact lineage (finalParents -> deletionLineage)
    (fun parents_to_deletion _tail => parents_to_deletion)

theorem ay_udlr_retention_lineage
    (finalParents : Prop) (deletionLineage : Prop)
    (retentionLineage : Prop) (lineageAccepted : Prop) :
    AyUDLRParentLineage finalParents deletionLineage retentionLineage
      lineageAccepted ->
    deletionLineage ->
    retentionLineage := by
  intro lineage
  exact lineage (deletionLineage -> retentionLineage)
    (fun _parents_to_deletion tail =>
      tail (deletionLineage -> retentionLineage)
        (fun deletion_to_retention _retention_to_accept =>
          deletion_to_retention))

theorem ay_udlr_lineage_accepted
    (finalParents : Prop) (deletionLineage : Prop)
    (retentionLineage : Prop) (lineageAccepted : Prop) :
    AyUDLRParentLineage finalParents deletionLineage retentionLineage
      lineageAccepted ->
    retentionLineage ->
    lineageAccepted := by
  intro lineage
  exact lineage (retentionLineage -> lineageAccepted)
    (fun _parents_to_deletion tail =>
      tail (retentionLineage -> lineageAccepted)
        (fun _deletion_to_retention retention_to_accept =>
          retention_to_accept))

theorem ay_udlr_empty_clause
    (finalParents : Prop) (lineageAccepted : Prop)
    (emptyClause : Prop) :
    AyUDLREmptyReplay finalParents lineageAccepted emptyClause ->
    lineageAccepted ->
    emptyClause := by
  intro replay
  exact replay (lineageAccepted -> emptyClause)
    (fun _parents_to_lineage lineage_to_empty => lineage_to_empty)

theorem ay_udlr_epoch_member
    (finalParents : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUDLREpochDigest finalParents epochMember digestMember
      epochDigestAccepted ->
    finalParents ->
    epochMember := by
  intro epoch_digest
  exact epoch_digest (finalParents -> epochMember)
    (fun parents_to_epoch _tail => parents_to_epoch)

theorem ay_udlr_digest_member
    (finalParents : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUDLREpochDigest finalParents epochMember digestMember
      epochDigestAccepted ->
    epochMember ->
    digestMember := by
  intro epoch_digest
  exact epoch_digest (epochMember -> digestMember)
    (fun _parents_to_epoch tail =>
      tail (epochMember -> digestMember)
        (fun epoch_to_digest _digest_to_accept => epoch_to_digest))

theorem ay_udlr_epoch_digest_accepted
    (finalParents : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUDLREpochDigest finalParents epochMember digestMember
      epochDigestAccepted ->
    digestMember ->
    epochDigestAccepted := by
  intro epoch_digest
  exact epoch_digest (digestMember -> epochDigestAccepted)
    (fun _parents_to_epoch tail =>
      tail (digestMember -> epochDigestAccepted)
        (fun _epoch_to_digest digest_to_accept => digest_to_accept))

theorem ay_udlr_checker_transcript
    (finalParents : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUDLRCheckerTranscript finalParents checkerTranscript
      checkerAccepted ->
    finalParents ->
    checkerTranscript := by
  intro transcript
  exact transcript (finalParents -> checkerTranscript)
    (fun parents_to_transcript _transcript_to_accept =>
      parents_to_transcript)

theorem ay_udlr_checker_accepted
    (finalParents : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUDLRCheckerTranscript finalParents checkerTranscript
      checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> checkerAccepted)
    (fun _parents_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_udlr_reconstruction_handle
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDLRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    reconstructionHandle := by
  intro reconstruction
  exact ay_udlr_conj_left reconstructionHandle
    (AyUDLRConj
      (AyUDLRMap emptyClause visibleUnsat)
      (AyUDLRMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_udlr_visible_unsat_from_empty
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDLRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClause -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_udlr_original_unsat_from_visible
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDLRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original => visible_to_original))

theorem ay_udlr_fingerprint_agrees
    (finalParents : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUDLRFingerprint finalParents fingerprintAgrees visibleUnsat ->
    finalParents ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (finalParents -> fingerprintAgrees)
    (fun parents_to_fingerprint _fingerprint_to_visible =>
      parents_to_fingerprint)

theorem ay_udlr_visible_unsat_from_fingerprint
    (finalParents : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUDLRFingerprint finalParents fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _parents_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_udlr_accepted_evidence
    (finalParents : Prop) (deletionLineage : Prop)
    (retentionLineage : Prop) (lineageAccepted : Prop)
    (emptyClause : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDLRAcceptedReplay finalParents deletionLineage retentionLineage
      lineageAccepted emptyClause epochMember digestMember
      epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUDLRAcceptedEvidence finalParents deletionLineage retentionLineage
      lineageAccepted emptyClause epochMember digestMember
      epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat := by
  intro accepted
  exact ay_udlr_conj_left
    (AyUDLRAcceptedEvidence finalParents deletionLineage retentionLineage
      lineageAccepted emptyClause epochMember digestMember
      epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_udlr_accepted_original_unsat
    (finalParents : Prop) (deletionLineage : Prop)
    (retentionLineage : Prop) (lineageAccepted : Prop)
    (emptyClause : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDLRAcceptedReplay finalParents deletionLineage retentionLineage
      lineageAccepted emptyClause epochMember digestMember
      epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_udlr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUDLRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_udlr_disj_right noClaim originalUnsat unsat

theorem ay_udlr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUDLRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_udlr_disj_left noClaim originalUnsat no_claim

theorem ay_udlr_accepted_replay_publish_sound
    (finalParents : Prop) (deletionLineage : Prop)
    (retentionLineage : Prop) (lineageAccepted : Prop)
    (emptyClause : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUDLRAcceptedReplay finalParents deletionLineage retentionLineage
      lineageAccepted emptyClause epochMember digestMember
      epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUDLRPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_udlr_public_unsat_report noClaim originalUnsat
    (ay_udlr_accepted_original_unsat finalParents deletionLineage
      retentionLineage lineageAccepted emptyClause epochMember digestMember
      epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat
      accepted)

theorem ay_udlr_bad_replay_no_claim
    (lineageGap : Prop) (missingDeletedParent : Prop)
    (unretainedParent : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUDLRBadReplay lineageGap missingDeletedParent unretainedParent
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_udlr_conj_left noClaim recompute fail_closed)

theorem ay_udlr_bad_replay_recompute
    (lineageGap : Prop) (missingDeletedParent : Prop)
    (unretainedParent : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUDLRBadReplay lineageGap missingDeletedParent unretainedParent
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_udlr_bad_replay_public_no_claim
    (lineageGap : Prop) (missingDeletedParent : Prop)
    (unretainedParent : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUDLRBadReplay lineageGap missingDeletedParent unretainedParent
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute ->
    AyUDLRPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_udlr_public_no_claim_report noClaim originalUnsat
    (ay_udlr_bad_replay_no_claim lineageGap missingDeletedParent
      unretainedParent epochDrift digestMismatch checkerRejected
      reconstructionMismatch fingerprintDrift noClaim recompute bad)

theorem ay_udlr_bad_replay_cannot_publish
    (lineageGap : Prop) (missingDeletedParent : Prop)
    (unretainedParent : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUDLRBadReplay lineageGap missingDeletedParent unretainedParent
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_udlr_bad_replay_no_claim lineageGap missingDeletedParent
      unretainedParent epochDrift digestMismatch checkerRejected
      reconstructionMismatch fingerprintDrift noClaim recompute bad)
    unsat

theorem ay_udlr_lineage_gap_forces_no_claim
    (lineageGap : Prop) (missingDeletedParent : Prop)
    (unretainedParent : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    lineageGap ->
    AyUDLRConj noClaim recompute ->
    AyUDLRBadReplay lineageGap missingDeletedParent unretainedParent
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute := by
  intro gap
  intro fail_closed
  exact ay_udlr_conj_intro
    (AyUDLRConj noClaim recompute)
    (AyUDLRDisj lineageGap
      (AyUDLRDisj missingDeletedParent
        (AyUDLRDisj unretainedParent
          (AyUDLRDisj epochDrift
            (AyUDLRDisj digestMismatch
              (AyUDLRDisj checkerRejected
                (AyUDLRDisj reconstructionMismatch fingerprintDrift)))))))
    fail_closed
    (ay_udlr_disj_left lineageGap
      (AyUDLRDisj missingDeletedParent
        (AyUDLRDisj unretainedParent
          (AyUDLRDisj epochDrift
            (AyUDLRDisj digestMismatch
              (AyUDLRDisj checkerRejected
                (AyUDLRDisj reconstructionMismatch fingerprintDrift))))))
      gap)

theorem ay_udlr_missing_deleted_parent_forces_no_claim
    (lineageGap : Prop) (missingDeletedParent : Prop)
    (unretainedParent : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    missingDeletedParent ->
    AyUDLRConj noClaim recompute ->
    AyUDLRBadReplay lineageGap missingDeletedParent unretainedParent
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute := by
  intro missing_parent
  intro fail_closed
  exact ay_udlr_conj_intro
    (AyUDLRConj noClaim recompute)
    (AyUDLRDisj lineageGap
      (AyUDLRDisj missingDeletedParent
        (AyUDLRDisj unretainedParent
          (AyUDLRDisj epochDrift
            (AyUDLRDisj digestMismatch
              (AyUDLRDisj checkerRejected
                (AyUDLRDisj reconstructionMismatch fingerprintDrift)))))))
    fail_closed
    (ay_udlr_disj_right lineageGap
      (AyUDLRDisj missingDeletedParent
        (AyUDLRDisj unretainedParent
          (AyUDLRDisj epochDrift
            (AyUDLRDisj digestMismatch
              (AyUDLRDisj checkerRejected
                (AyUDLRDisj reconstructionMismatch fingerprintDrift))))))
      (ay_udlr_disj_left missingDeletedParent
        (AyUDLRDisj unretainedParent
          (AyUDLRDisj epochDrift
            (AyUDLRDisj digestMismatch
              (AyUDLRDisj checkerRejected
                (AyUDLRDisj reconstructionMismatch fingerprintDrift)))))
        missing_parent))

theorem ay_udlr_missing_deleted_parent_cannot_publish
    (lineageGap : Prop) (missingDeletedParent : Prop)
    (unretainedParent : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUDLRBadReplay lineageGap missingDeletedParent unretainedParent
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_udlr_bad_replay_cannot_publish lineageGap missingDeletedParent
    unretainedParent epochDrift digestMismatch checkerRejected
    reconstructionMismatch fingerprintDrift noClaim recompute originalUnsat
    bad
