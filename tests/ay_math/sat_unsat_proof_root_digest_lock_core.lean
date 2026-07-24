-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded public UNSAT root digest-lock soundness for ay sequential-main
-- SAT-COMP checking. Propositions stand for root clause evidence, parent
-- coverage, step-map evidence, epoch/digest membership, checker transcripts,
-- reconstruction handles, original fingerprints, and fail-closed
-- no-claim/recompute diagnostics.

def AyUPRDConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPRDDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPRDMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPRDRootLock
    (rootDigestLock : Prop) (rootClauseEvidence : Prop)
    (lockedRootReplay : Prop) :=
  AyUPRDConj rootDigestLock
    (AyUPRDConj
      (AyUPRDMap rootDigestLock rootClauseEvidence)
      (AyUPRDMap rootClauseEvidence lockedRootReplay))

def AyUPRDParentCoverage
    (lockedRootReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :=
  AyUPRDConj
    (AyUPRDMap lockedRootReplay parentCoverage)
    (AyUPRDMap parentCoverage emptyClause)

def AyUPRDStepMap
    (lockedRootReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :=
  AyUPRDConj
    (AyUPRDMap lockedRootReplay stepMapEvidence)
    (AyUPRDMap stepMapEvidence stepMapAccepted)

def AyUPRDEpochDigest
    (lockedRootReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :=
  AyUPRDConj
    (AyUPRDMap lockedRootReplay epochMember)
    (AyUPRDConj
      (AyUPRDMap epochMember digestMember)
      (AyUPRDMap digestMember epochDigestAccepted))

def AyUPRDCheckerTranscript
    (lockedRootReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :=
  AyUPRDConj
    (AyUPRDMap lockedRootReplay checkerTranscript)
    (AyUPRDMap checkerTranscript checkerAccepted)

def AyUPRDReconstruction
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPRDConj reconstructionHandle
    (AyUPRDConj
      (AyUPRDMap emptyClause visibleUnsat)
      (AyUPRDMap visibleUnsat originalUnsat))

def AyUPRDFingerprint
    (lockedRootReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUPRDConj
    (AyUPRDMap lockedRootReplay fingerprintAgrees)
    (AyUPRDMap fingerprintAgrees visibleUnsat)

def AyUPRDAcceptedEvidence
    (rootDigestLock : Prop) (rootClauseEvidence : Prop)
    (lockedRootReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPRDConj
    (AyUPRDRootLock rootDigestLock rootClauseEvidence lockedRootReplay)
    (AyUPRDConj
      (AyUPRDParentCoverage lockedRootReplay parentCoverage emptyClause)
      (AyUPRDConj
        (AyUPRDStepMap lockedRootReplay stepMapEvidence stepMapAccepted)
        (AyUPRDConj
          (AyUPRDEpochDigest lockedRootReplay epochMember digestMember
            epochDigestAccepted)
          (AyUPRDConj
            (AyUPRDCheckerTranscript lockedRootReplay checkerTranscript
              checkerAccepted)
            (AyUPRDConj
              (AyUPRDReconstruction emptyClause reconstructionHandle
                visibleUnsat originalUnsat)
              (AyUPRDFingerprint lockedRootReplay fingerprintAgrees
                visibleUnsat))))))

def AyUPRDAcceptedReplay
    (rootDigestLock : Prop) (rootClauseEvidence : Prop)
    (lockedRootReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPRDConj
    (AyUPRDAcceptedEvidence rootDigestLock rootClauseEvidence
      lockedRootReplay parentCoverage emptyClause stepMapEvidence
      stepMapAccepted epochMember digestMember epochDigestAccepted
      checkerTranscript checkerAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat)
    originalUnsat

def AyUPRDBadLock
    (rootDigestDrift : Prop) (missingRootClauseEvidence : Prop)
    (uncheckedRootLock : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUPRDConj
    (AyUPRDConj noClaim recompute)
    (AyUPRDDisj rootDigestDrift
      (AyUPRDDisj missingRootClauseEvidence
        (AyUPRDDisj uncheckedRootLock
          (AyUPRDDisj parentGap
            (AyUPRDDisj stepMapMismatch
              (AyUPRDDisj epochDrift
                (AyUPRDDisj digestMismatch checkerRejected)))))))

def AyUPRDPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPRDDisj noClaim originalUnsat

theorem ay_uprd_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPRDConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uprd_conj_left
    (p : Prop) (q : Prop) :
    AyUPRDConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uprd_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPRDDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uprd_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPRDDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uprd_root_digest_lock
    (rootDigestLock : Prop) (rootClauseEvidence : Prop)
    (lockedRootReplay : Prop) :
    AyUPRDRootLock rootDigestLock rootClauseEvidence lockedRootReplay ->
    rootDigestLock := by
  intro root
  exact ay_uprd_conj_left rootDigestLock
    (AyUPRDConj
      (AyUPRDMap rootDigestLock rootClauseEvidence)
      (AyUPRDMap rootClauseEvidence lockedRootReplay))
    root

theorem ay_uprd_root_clause_evidence
    (rootDigestLock : Prop) (rootClauseEvidence : Prop)
    (lockedRootReplay : Prop) :
    AyUPRDRootLock rootDigestLock rootClauseEvidence lockedRootReplay ->
    rootClauseEvidence := by
  intro root
  exact root rootClauseEvidence
    (fun digest tail =>
      tail rootClauseEvidence
        (fun digest_to_evidence _evidence_to_replay =>
          digest_to_evidence digest))

theorem ay_uprd_locked_root_replay
    (rootDigestLock : Prop) (rootClauseEvidence : Prop)
    (lockedRootReplay : Prop) :
    AyUPRDRootLock rootDigestLock rootClauseEvidence lockedRootReplay ->
    lockedRootReplay := by
  intro root
  exact root lockedRootReplay
    (fun digest tail =>
      tail lockedRootReplay
        (fun digest_to_evidence evidence_to_replay =>
          evidence_to_replay (digest_to_evidence digest)))

theorem ay_uprd_parent_coverage
    (lockedRootReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUPRDParentCoverage lockedRootReplay parentCoverage emptyClause ->
    lockedRootReplay ->
    parentCoverage := by
  intro parents
  exact parents (lockedRootReplay -> parentCoverage)
    (fun replay_to_parents _parents_to_empty => replay_to_parents)

theorem ay_uprd_empty_clause
    (lockedRootReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUPRDParentCoverage lockedRootReplay parentCoverage emptyClause ->
    parentCoverage ->
    emptyClause := by
  intro parents
  exact parents (parentCoverage -> emptyClause)
    (fun _replay_to_parents parents_to_empty => parents_to_empty)

theorem ay_uprd_step_map_evidence
    (lockedRootReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :
    AyUPRDStepMap lockedRootReplay stepMapEvidence stepMapAccepted ->
    lockedRootReplay ->
    stepMapEvidence := by
  intro step_map
  exact step_map (lockedRootReplay -> stepMapEvidence)
    (fun replay_to_step_map _step_map_to_accept => replay_to_step_map)

theorem ay_uprd_step_map_accepted
    (lockedRootReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :
    AyUPRDStepMap lockedRootReplay stepMapEvidence stepMapAccepted ->
    stepMapEvidence ->
    stepMapAccepted := by
  intro step_map
  exact step_map (stepMapEvidence -> stepMapAccepted)
    (fun _replay_to_step_map step_map_to_accept => step_map_to_accept)

theorem ay_uprd_epoch_member
    (lockedRootReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUPRDEpochDigest lockedRootReplay epochMember digestMember
      epochDigestAccepted ->
    lockedRootReplay ->
    epochMember := by
  intro epoch_digest
  exact epoch_digest (lockedRootReplay -> epochMember)
    (fun replay_to_epoch _tail => replay_to_epoch)

theorem ay_uprd_digest_member
    (lockedRootReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUPRDEpochDigest lockedRootReplay epochMember digestMember
      epochDigestAccepted ->
    epochMember ->
    digestMember := by
  intro epoch_digest
  exact epoch_digest (epochMember -> digestMember)
    (fun _replay_to_epoch tail =>
      tail (epochMember -> digestMember)
        (fun epoch_to_digest _digest_to_accept => epoch_to_digest))

theorem ay_uprd_epoch_digest_accepted
    (lockedRootReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUPRDEpochDigest lockedRootReplay epochMember digestMember
      epochDigestAccepted ->
    digestMember ->
    epochDigestAccepted := by
  intro epoch_digest
  exact epoch_digest (digestMember -> epochDigestAccepted)
    (fun _replay_to_epoch tail =>
      tail (digestMember -> epochDigestAccepted)
        (fun _epoch_to_digest digest_to_accept => digest_to_accept))

theorem ay_uprd_checker_transcript
    (lockedRootReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUPRDCheckerTranscript lockedRootReplay checkerTranscript
      checkerAccepted ->
    lockedRootReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (lockedRootReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_uprd_checker_accepted
    (lockedRootReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUPRDCheckerTranscript lockedRootReplay checkerTranscript
      checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> checkerAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_uprd_reconstruction_handle
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPRDReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    reconstructionHandle := by
  intro reconstruction
  exact ay_uprd_conj_left reconstructionHandle
    (AyUPRDConj
      (AyUPRDMap emptyClause visibleUnsat)
      (AyUPRDMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_uprd_visible_unsat_from_empty
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPRDReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClause -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_uprd_original_unsat_from_visible
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPRDReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original => visible_to_original))

theorem ay_uprd_fingerprint_agrees
    (lockedRootReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUPRDFingerprint lockedRootReplay fingerprintAgrees visibleUnsat ->
    lockedRootReplay ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (lockedRootReplay -> fingerprintAgrees)
    (fun replay_to_fingerprint _fingerprint_to_visible =>
      replay_to_fingerprint)

theorem ay_uprd_visible_unsat_from_fingerprint
    (lockedRootReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUPRDFingerprint lockedRootReplay fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _replay_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_uprd_accepted_evidence
    (rootDigestLock : Prop) (rootClauseEvidence : Prop)
    (lockedRootReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPRDAcceptedReplay rootDigestLock rootClauseEvidence lockedRootReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPRDAcceptedEvidence rootDigestLock rootClauseEvidence lockedRootReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat := by
  intro accepted
  exact ay_uprd_conj_left
    (AyUPRDAcceptedEvidence rootDigestLock rootClauseEvidence
      lockedRootReplay parentCoverage emptyClause stepMapEvidence
      stepMapAccepted epochMember digestMember epochDigestAccepted
      checkerTranscript checkerAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_uprd_accepted_original_unsat
    (rootDigestLock : Prop) (rootClauseEvidence : Prop)
    (lockedRootReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPRDAcceptedReplay rootDigestLock rootClauseEvidence lockedRootReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_uprd_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUPRDPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_uprd_disj_right noClaim originalUnsat unsat

theorem ay_uprd_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUPRDPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_uprd_disj_left noClaim originalUnsat no_claim

theorem ay_uprd_accepted_root_lock_publish_sound
    (rootDigestLock : Prop) (rootClauseEvidence : Prop)
    (lockedRootReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUPRDAcceptedReplay rootDigestLock rootClauseEvidence lockedRootReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPRDPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_uprd_public_unsat_report noClaim originalUnsat
    (ay_uprd_accepted_original_unsat rootDigestLock rootClauseEvidence
      lockedRootReplay parentCoverage emptyClause stepMapEvidence
      stepMapAccepted epochMember digestMember epochDigestAccepted
      checkerTranscript checkerAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat accepted)

theorem ay_uprd_bad_lock_no_claim
    (rootDigestDrift : Prop) (missingRootClauseEvidence : Prop)
    (uncheckedRootLock : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPRDBadLock rootDigestDrift missingRootClauseEvidence
      uncheckedRootLock parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_uprd_conj_left noClaim recompute fail_closed)

theorem ay_uprd_bad_lock_recompute
    (rootDigestDrift : Prop) (missingRootClauseEvidence : Prop)
    (uncheckedRootLock : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPRDBadLock rootDigestDrift missingRootClauseEvidence
      uncheckedRootLock parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_uprd_bad_lock_public_no_claim
    (rootDigestDrift : Prop) (missingRootClauseEvidence : Prop)
    (uncheckedRootLock : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPRDBadLock rootDigestDrift missingRootClauseEvidence
      uncheckedRootLock parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute ->
    AyUPRDPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_uprd_public_no_claim_report noClaim originalUnsat
    (ay_uprd_bad_lock_no_claim rootDigestDrift missingRootClauseEvidence
      uncheckedRootLock parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute bad)

theorem ay_uprd_bad_lock_cannot_publish
    (rootDigestDrift : Prop) (missingRootClauseEvidence : Prop)
    (uncheckedRootLock : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPRDBadLock rootDigestDrift missingRootClauseEvidence
      uncheckedRootLock parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_uprd_bad_lock_no_claim rootDigestDrift missingRootClauseEvidence
      uncheckedRootLock parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute bad)
    unsat

theorem ay_uprd_root_digest_drift_forces_no_claim
    (rootDigestDrift : Prop) (missingRootClauseEvidence : Prop)
    (uncheckedRootLock : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    rootDigestDrift ->
    AyUPRDConj noClaim recompute ->
    AyUPRDBadLock rootDigestDrift missingRootClauseEvidence
      uncheckedRootLock parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute := by
  intro drift
  intro fail_closed
  exact ay_uprd_conj_intro
    (AyUPRDConj noClaim recompute)
    (AyUPRDDisj rootDigestDrift
      (AyUPRDDisj missingRootClauseEvidence
        (AyUPRDDisj uncheckedRootLock
          (AyUPRDDisj parentGap
            (AyUPRDDisj stepMapMismatch
              (AyUPRDDisj epochDrift
                (AyUPRDDisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_uprd_disj_left rootDigestDrift
      (AyUPRDDisj missingRootClauseEvidence
        (AyUPRDDisj uncheckedRootLock
          (AyUPRDDisj parentGap
            (AyUPRDDisj stepMapMismatch
              (AyUPRDDisj epochDrift
                (AyUPRDDisj digestMismatch checkerRejected))))))
      drift)

theorem ay_uprd_missing_root_clause_evidence_forces_no_claim
    (rootDigestDrift : Prop) (missingRootClauseEvidence : Prop)
    (uncheckedRootLock : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    missingRootClauseEvidence ->
    AyUPRDConj noClaim recompute ->
    AyUPRDBadLock rootDigestDrift missingRootClauseEvidence
      uncheckedRootLock parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute := by
  intro missing_root
  intro fail_closed
  exact ay_uprd_conj_intro
    (AyUPRDConj noClaim recompute)
    (AyUPRDDisj rootDigestDrift
      (AyUPRDDisj missingRootClauseEvidence
        (AyUPRDDisj uncheckedRootLock
          (AyUPRDDisj parentGap
            (AyUPRDDisj stepMapMismatch
              (AyUPRDDisj epochDrift
                (AyUPRDDisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_uprd_disj_right rootDigestDrift
      (AyUPRDDisj missingRootClauseEvidence
        (AyUPRDDisj uncheckedRootLock
          (AyUPRDDisj parentGap
            (AyUPRDDisj stepMapMismatch
              (AyUPRDDisj epochDrift
                (AyUPRDDisj digestMismatch checkerRejected))))))
      (ay_uprd_disj_left missingRootClauseEvidence
        (AyUPRDDisj uncheckedRootLock
          (AyUPRDDisj parentGap
            (AyUPRDDisj stepMapMismatch
              (AyUPRDDisj epochDrift
                (AyUPRDDisj digestMismatch checkerRejected)))))
        missing_root))

theorem ay_uprd_unchecked_root_lock_forces_no_claim
    (rootDigestDrift : Prop) (missingRootClauseEvidence : Prop)
    (uncheckedRootLock : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    uncheckedRootLock ->
    AyUPRDConj noClaim recompute ->
    AyUPRDBadLock rootDigestDrift missingRootClauseEvidence
      uncheckedRootLock parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute := by
  intro unchecked
  intro fail_closed
  exact ay_uprd_conj_intro
    (AyUPRDConj noClaim recompute)
    (AyUPRDDisj rootDigestDrift
      (AyUPRDDisj missingRootClauseEvidence
        (AyUPRDDisj uncheckedRootLock
          (AyUPRDDisj parentGap
            (AyUPRDDisj stepMapMismatch
              (AyUPRDDisj epochDrift
                (AyUPRDDisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_uprd_disj_right rootDigestDrift
      (AyUPRDDisj missingRootClauseEvidence
        (AyUPRDDisj uncheckedRootLock
          (AyUPRDDisj parentGap
            (AyUPRDDisj stepMapMismatch
              (AyUPRDDisj epochDrift
                (AyUPRDDisj digestMismatch checkerRejected))))))
      (ay_uprd_disj_right missingRootClauseEvidence
        (AyUPRDDisj uncheckedRootLock
          (AyUPRDDisj parentGap
            (AyUPRDDisj stepMapMismatch
              (AyUPRDDisj epochDrift
                (AyUPRDDisj digestMismatch checkerRejected)))))
        (ay_uprd_disj_left uncheckedRootLock
          (AyUPRDDisj parentGap
            (AyUPRDDisj stepMapMismatch
              (AyUPRDDisj epochDrift
                (AyUPRDDisj digestMismatch checkerRejected))))
          unchecked)))

theorem ay_uprd_unchecked_root_lock_cannot_publish
    (rootDigestDrift : Prop) (missingRootClauseEvidence : Prop)
    (uncheckedRootLock : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPRDBadLock rootDigestDrift missingRootClauseEvidence
      uncheckedRootLock parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_uprd_bad_lock_cannot_publish rootDigestDrift
    missingRootClauseEvidence uncheckedRootLock parentGap stepMapMismatch
    epochDrift digestMismatch checkerRejected noClaim recompute originalUnsat
    bad
