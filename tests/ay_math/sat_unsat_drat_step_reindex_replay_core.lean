-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded DRAT/LRAT step reindex replay soundness for ay sequential-main
-- SAT-COMP UNSAT checking. Propositions stand for compact proof IDs,
-- step-map injection/bijection evidence, parent coverage, epoch/digest
-- membership, checker transcripts, reconstruction handles, original
-- fingerprints, and fail-closed no-claim/recompute diagnostics.

def AyUDSRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUDSRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUDSRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUDSRStepMap
    (compactProofIds : Prop) (stepMapInjective : Prop)
    (stepMapBijective : Prop) (reindexedSteps : Prop) :=
  AyUDSRConj compactProofIds
    (AyUDSRConj
      (AyUDSRMap compactProofIds stepMapInjective)
      (AyUDSRConj
        (AyUDSRMap stepMapInjective stepMapBijective)
        (AyUDSRMap stepMapBijective reindexedSteps)))

def AyUDSRParentCoverage
    (reindexedSteps : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :=
  AyUDSRConj
    (AyUDSRMap reindexedSteps parentCoverage)
    (AyUDSRMap parentCoverage emptyClause)

def AyUDSREpochDigest
    (reindexedSteps : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :=
  AyUDSRConj
    (AyUDSRMap reindexedSteps epochMember)
    (AyUDSRConj
      (AyUDSRMap epochMember digestMember)
      (AyUDSRMap digestMember epochDigestAccepted))

def AyUDSRCheckerTranscript
    (reindexedSteps : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :=
  AyUDSRConj
    (AyUDSRMap reindexedSteps checkerTranscript)
    (AyUDSRMap checkerTranscript checkerAccepted)

def AyUDSRReconstruction
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUDSRConj reconstructionHandle
    (AyUDSRConj
      (AyUDSRMap emptyClause visibleUnsat)
      (AyUDSRMap visibleUnsat originalUnsat))

def AyUDSRFingerprint
    (reindexedSteps : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUDSRConj
    (AyUDSRMap reindexedSteps fingerprintAgrees)
    (AyUDSRMap fingerprintAgrees visibleUnsat)

def AyUDSRAcceptedEvidence
    (compactProofIds : Prop) (stepMapInjective : Prop)
    (stepMapBijective : Prop) (reindexedSteps : Prop)
    (parentCoverage : Prop) (emptyClause : Prop)
    (epochMember : Prop) (digestMember : Prop)
    (epochDigestAccepted : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (reconstructionHandle : Prop)
    (fingerprintAgrees : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUDSRConj
    (AyUDSRStepMap compactProofIds stepMapInjective stepMapBijective
      reindexedSteps)
    (AyUDSRConj
      (AyUDSRParentCoverage reindexedSteps parentCoverage emptyClause)
      (AyUDSRConj
        (AyUDSREpochDigest reindexedSteps epochMember digestMember
          epochDigestAccepted)
        (AyUDSRConj
          (AyUDSRCheckerTranscript reindexedSteps checkerTranscript
            checkerAccepted)
          (AyUDSRConj
            (AyUDSRReconstruction emptyClause reconstructionHandle
              visibleUnsat originalUnsat)
            (AyUDSRFingerprint reindexedSteps fingerprintAgrees
              visibleUnsat)))))

def AyUDSRAcceptedReplay
    (compactProofIds : Prop) (stepMapInjective : Prop)
    (stepMapBijective : Prop) (reindexedSteps : Prop)
    (parentCoverage : Prop) (emptyClause : Prop)
    (epochMember : Prop) (digestMember : Prop)
    (epochDigestAccepted : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (reconstructionHandle : Prop)
    (fingerprintAgrees : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUDSRConj
    (AyUDSRAcceptedEvidence compactProofIds stepMapInjective
      stepMapBijective reindexedSteps parentCoverage emptyClause epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat

def AyUDSRBadReplay
    (stepMapDrift : Prop) (parentMismatch : Prop)
    (uncheckedReindex : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUDSRConj
    (AyUDSRConj noClaim recompute)
    (AyUDSRDisj stepMapDrift
      (AyUDSRDisj parentMismatch
        (AyUDSRDisj uncheckedReindex
          (AyUDSRDisj epochDrift
            (AyUDSRDisj digestMismatch
              (AyUDSRDisj checkerRejected
                (AyUDSRDisj reconstructionMismatch fingerprintDrift)))))))

def AyUDSRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUDSRDisj noClaim originalUnsat

theorem ay_udsr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUDSRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_udsr_conj_left
    (p : Prop) (q : Prop) :
    AyUDSRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_udsr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUDSRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_udsr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUDSRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_udsr_compact_proof_ids
    (compactProofIds : Prop) (stepMapInjective : Prop)
    (stepMapBijective : Prop) (reindexedSteps : Prop) :
    AyUDSRStepMap compactProofIds stepMapInjective stepMapBijective
      reindexedSteps ->
    compactProofIds := by
  intro step_map
  exact ay_udsr_conj_left compactProofIds
    (AyUDSRConj
      (AyUDSRMap compactProofIds stepMapInjective)
      (AyUDSRConj
        (AyUDSRMap stepMapInjective stepMapBijective)
        (AyUDSRMap stepMapBijective reindexedSteps)))
    step_map

theorem ay_udsr_step_map_injective
    (compactProofIds : Prop) (stepMapInjective : Prop)
    (stepMapBijective : Prop) (reindexedSteps : Prop) :
    AyUDSRStepMap compactProofIds stepMapInjective stepMapBijective
      reindexedSteps ->
    stepMapInjective := by
  intro step_map
  exact step_map stepMapInjective
    (fun compact tail =>
      tail stepMapInjective
        (fun compact_to_injective _tail2 =>
          compact_to_injective compact))

theorem ay_udsr_step_map_bijective
    (compactProofIds : Prop) (stepMapInjective : Prop)
    (stepMapBijective : Prop) (reindexedSteps : Prop) :
    AyUDSRStepMap compactProofIds stepMapInjective stepMapBijective
      reindexedSteps ->
    stepMapBijective := by
  intro step_map
  exact step_map stepMapBijective
    (fun compact tail =>
      tail stepMapBijective
        (fun compact_to_injective tail2 =>
          tail2 stepMapBijective
            (fun injective_to_bijective _bijective_to_steps =>
              injective_to_bijective (compact_to_injective compact))))

theorem ay_udsr_reindexed_steps
    (compactProofIds : Prop) (stepMapInjective : Prop)
    (stepMapBijective : Prop) (reindexedSteps : Prop) :
    AyUDSRStepMap compactProofIds stepMapInjective stepMapBijective
      reindexedSteps ->
    reindexedSteps := by
  intro step_map
  exact step_map reindexedSteps
    (fun compact tail =>
      tail reindexedSteps
        (fun compact_to_injective tail2 =>
          tail2 reindexedSteps
            (fun injective_to_bijective bijective_to_steps =>
              bijective_to_steps
                (injective_to_bijective
                  (compact_to_injective compact)))))

theorem ay_udsr_parent_coverage
    (reindexedSteps : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUDSRParentCoverage reindexedSteps parentCoverage emptyClause ->
    reindexedSteps ->
    parentCoverage := by
  intro parents
  exact parents (reindexedSteps -> parentCoverage)
    (fun steps_to_parents _parents_to_empty => steps_to_parents)

theorem ay_udsr_empty_clause
    (reindexedSteps : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUDSRParentCoverage reindexedSteps parentCoverage emptyClause ->
    parentCoverage ->
    emptyClause := by
  intro parents
  exact parents (parentCoverage -> emptyClause)
    (fun _steps_to_parents parents_to_empty => parents_to_empty)

theorem ay_udsr_epoch_member
    (reindexedSteps : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUDSREpochDigest reindexedSteps epochMember digestMember
      epochDigestAccepted ->
    reindexedSteps ->
    epochMember := by
  intro epoch_digest
  exact epoch_digest (reindexedSteps -> epochMember)
    (fun steps_to_epoch _tail => steps_to_epoch)

theorem ay_udsr_digest_member
    (reindexedSteps : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUDSREpochDigest reindexedSteps epochMember digestMember
      epochDigestAccepted ->
    epochMember ->
    digestMember := by
  intro epoch_digest
  exact epoch_digest (epochMember -> digestMember)
    (fun _steps_to_epoch tail =>
      tail (epochMember -> digestMember)
        (fun epoch_to_digest _digest_to_accept => epoch_to_digest))

theorem ay_udsr_epoch_digest_accepted
    (reindexedSteps : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUDSREpochDigest reindexedSteps epochMember digestMember
      epochDigestAccepted ->
    digestMember ->
    epochDigestAccepted := by
  intro epoch_digest
  exact epoch_digest (digestMember -> epochDigestAccepted)
    (fun _steps_to_epoch tail =>
      tail (digestMember -> epochDigestAccepted)
        (fun _epoch_to_digest digest_to_accept => digest_to_accept))

theorem ay_udsr_checker_transcript
    (reindexedSteps : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUDSRCheckerTranscript reindexedSteps checkerTranscript
      checkerAccepted ->
    reindexedSteps ->
    checkerTranscript := by
  intro transcript
  exact transcript (reindexedSteps -> checkerTranscript)
    (fun steps_to_transcript _transcript_to_accept =>
      steps_to_transcript)

theorem ay_udsr_checker_accepted
    (reindexedSteps : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUDSRCheckerTranscript reindexedSteps checkerTranscript
      checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> checkerAccepted)
    (fun _steps_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_udsr_reconstruction_handle
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDSRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    reconstructionHandle := by
  intro reconstruction
  exact ay_udsr_conj_left reconstructionHandle
    (AyUDSRConj
      (AyUDSRMap emptyClause visibleUnsat)
      (AyUDSRMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_udsr_visible_unsat_from_empty
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDSRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClause -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_udsr_original_unsat_from_visible
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDSRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original => visible_to_original))

theorem ay_udsr_fingerprint_agrees
    (reindexedSteps : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUDSRFingerprint reindexedSteps fingerprintAgrees visibleUnsat ->
    reindexedSteps ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (reindexedSteps -> fingerprintAgrees)
    (fun steps_to_fingerprint _fingerprint_to_visible =>
      steps_to_fingerprint)

theorem ay_udsr_visible_unsat_from_fingerprint
    (reindexedSteps : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUDSRFingerprint reindexedSteps fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _steps_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_udsr_accepted_evidence
    (compactProofIds : Prop) (stepMapInjective : Prop)
    (stepMapBijective : Prop) (reindexedSteps : Prop)
    (parentCoverage : Prop) (emptyClause : Prop)
    (epochMember : Prop) (digestMember : Prop)
    (epochDigestAccepted : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (reconstructionHandle : Prop)
    (fingerprintAgrees : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDSRAcceptedReplay compactProofIds stepMapInjective stepMapBijective
      reindexedSteps parentCoverage emptyClause epochMember digestMember
      epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUDSRAcceptedEvidence compactProofIds stepMapInjective stepMapBijective
      reindexedSteps parentCoverage emptyClause epochMember digestMember
      epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat := by
  intro accepted
  exact ay_udsr_conj_left
    (AyUDSRAcceptedEvidence compactProofIds stepMapInjective
      stepMapBijective reindexedSteps parentCoverage emptyClause epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_udsr_accepted_original_unsat
    (compactProofIds : Prop) (stepMapInjective : Prop)
    (stepMapBijective : Prop) (reindexedSteps : Prop)
    (parentCoverage : Prop) (emptyClause : Prop)
    (epochMember : Prop) (digestMember : Prop)
    (epochDigestAccepted : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (reconstructionHandle : Prop)
    (fingerprintAgrees : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDSRAcceptedReplay compactProofIds stepMapInjective stepMapBijective
      reindexedSteps parentCoverage emptyClause epochMember digestMember
      epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_udsr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUDSRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_udsr_disj_right noClaim originalUnsat unsat

theorem ay_udsr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUDSRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_udsr_disj_left noClaim originalUnsat no_claim

theorem ay_udsr_accepted_reindex_publish_sound
    (compactProofIds : Prop) (stepMapInjective : Prop)
    (stepMapBijective : Prop) (reindexedSteps : Prop)
    (parentCoverage : Prop) (emptyClause : Prop)
    (epochMember : Prop) (digestMember : Prop)
    (epochDigestAccepted : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (reconstructionHandle : Prop)
    (fingerprintAgrees : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyUDSRAcceptedReplay compactProofIds stepMapInjective stepMapBijective
      reindexedSteps parentCoverage emptyClause epochMember digestMember
      epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUDSRPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_udsr_public_unsat_report noClaim originalUnsat
    (ay_udsr_accepted_original_unsat compactProofIds stepMapInjective
      stepMapBijective reindexedSteps parentCoverage emptyClause epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat
      accepted)

theorem ay_udsr_bad_replay_no_claim
    (stepMapDrift : Prop) (parentMismatch : Prop)
    (uncheckedReindex : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUDSRBadReplay stepMapDrift parentMismatch uncheckedReindex
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_udsr_conj_left noClaim recompute fail_closed)

theorem ay_udsr_bad_replay_recompute
    (stepMapDrift : Prop) (parentMismatch : Prop)
    (uncheckedReindex : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUDSRBadReplay stepMapDrift parentMismatch uncheckedReindex
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_udsr_bad_replay_public_no_claim
    (stepMapDrift : Prop) (parentMismatch : Prop)
    (uncheckedReindex : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUDSRBadReplay stepMapDrift parentMismatch uncheckedReindex
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute ->
    AyUDSRPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_udsr_public_no_claim_report noClaim originalUnsat
    (ay_udsr_bad_replay_no_claim stepMapDrift parentMismatch
      uncheckedReindex epochDrift digestMismatch checkerRejected
      reconstructionMismatch fingerprintDrift noClaim recompute bad)

theorem ay_udsr_bad_replay_cannot_publish
    (stepMapDrift : Prop) (parentMismatch : Prop)
    (uncheckedReindex : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUDSRBadReplay stepMapDrift parentMismatch uncheckedReindex
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_udsr_bad_replay_no_claim stepMapDrift parentMismatch
      uncheckedReindex epochDrift digestMismatch checkerRejected
      reconstructionMismatch fingerprintDrift noClaim recompute bad)
    unsat

theorem ay_udsr_step_map_drift_forces_no_claim
    (stepMapDrift : Prop) (parentMismatch : Prop)
    (uncheckedReindex : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    stepMapDrift ->
    AyUDSRConj noClaim recompute ->
    AyUDSRBadReplay stepMapDrift parentMismatch uncheckedReindex
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute := by
  intro drift
  intro fail_closed
  exact ay_udsr_conj_intro
    (AyUDSRConj noClaim recompute)
    (AyUDSRDisj stepMapDrift
      (AyUDSRDisj parentMismatch
        (AyUDSRDisj uncheckedReindex
          (AyUDSRDisj epochDrift
            (AyUDSRDisj digestMismatch
              (AyUDSRDisj checkerRejected
                (AyUDSRDisj reconstructionMismatch fingerprintDrift)))))))
    fail_closed
    (ay_udsr_disj_left stepMapDrift
      (AyUDSRDisj parentMismatch
        (AyUDSRDisj uncheckedReindex
          (AyUDSRDisj epochDrift
            (AyUDSRDisj digestMismatch
              (AyUDSRDisj checkerRejected
                (AyUDSRDisj reconstructionMismatch fingerprintDrift))))))
      drift)

theorem ay_udsr_parent_mismatch_forces_no_claim
    (stepMapDrift : Prop) (parentMismatch : Prop)
    (uncheckedReindex : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    parentMismatch ->
    AyUDSRConj noClaim recompute ->
    AyUDSRBadReplay stepMapDrift parentMismatch uncheckedReindex
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute := by
  intro mismatch
  intro fail_closed
  exact ay_udsr_conj_intro
    (AyUDSRConj noClaim recompute)
    (AyUDSRDisj stepMapDrift
      (AyUDSRDisj parentMismatch
        (AyUDSRDisj uncheckedReindex
          (AyUDSRDisj epochDrift
            (AyUDSRDisj digestMismatch
              (AyUDSRDisj checkerRejected
                (AyUDSRDisj reconstructionMismatch fingerprintDrift)))))))
    fail_closed
    (ay_udsr_disj_right stepMapDrift
      (AyUDSRDisj parentMismatch
        (AyUDSRDisj uncheckedReindex
          (AyUDSRDisj epochDrift
            (AyUDSRDisj digestMismatch
              (AyUDSRDisj checkerRejected
                (AyUDSRDisj reconstructionMismatch fingerprintDrift))))))
      (ay_udsr_disj_left parentMismatch
        (AyUDSRDisj uncheckedReindex
          (AyUDSRDisj epochDrift
            (AyUDSRDisj digestMismatch
              (AyUDSRDisj checkerRejected
                (AyUDSRDisj reconstructionMismatch fingerprintDrift)))))
        mismatch))

theorem ay_udsr_unchecked_reindex_forces_no_claim
    (stepMapDrift : Prop) (parentMismatch : Prop)
    (uncheckedReindex : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    uncheckedReindex ->
    AyUDSRConj noClaim recompute ->
    AyUDSRBadReplay stepMapDrift parentMismatch uncheckedReindex
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute := by
  intro unchecked
  intro fail_closed
  exact ay_udsr_conj_intro
    (AyUDSRConj noClaim recompute)
    (AyUDSRDisj stepMapDrift
      (AyUDSRDisj parentMismatch
        (AyUDSRDisj uncheckedReindex
          (AyUDSRDisj epochDrift
            (AyUDSRDisj digestMismatch
              (AyUDSRDisj checkerRejected
                (AyUDSRDisj reconstructionMismatch fingerprintDrift)))))))
    fail_closed
    (ay_udsr_disj_right stepMapDrift
      (AyUDSRDisj parentMismatch
        (AyUDSRDisj uncheckedReindex
          (AyUDSRDisj epochDrift
            (AyUDSRDisj digestMismatch
              (AyUDSRDisj checkerRejected
                (AyUDSRDisj reconstructionMismatch fingerprintDrift))))))
      (ay_udsr_disj_right parentMismatch
        (AyUDSRDisj uncheckedReindex
          (AyUDSRDisj epochDrift
            (AyUDSRDisj digestMismatch
              (AyUDSRDisj checkerRejected
                (AyUDSRDisj reconstructionMismatch fingerprintDrift)))))
        (ay_udsr_disj_left uncheckedReindex
          (AyUDSRDisj epochDrift
            (AyUDSRDisj digestMismatch
              (AyUDSRDisj checkerRejected
                (AyUDSRDisj reconstructionMismatch fingerprintDrift))))
          unchecked)))

theorem ay_udsr_unchecked_reindex_cannot_publish
    (stepMapDrift : Prop) (parentMismatch : Prop)
    (uncheckedReindex : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUDSRBadReplay stepMapDrift parentMismatch uncheckedReindex
      epochDrift digestMismatch checkerRejected reconstructionMismatch
      fingerprintDrift noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_udsr_bad_replay_cannot_publish stepMapDrift parentMismatch
    uncheckedReindex epochDrift digestMismatch checkerRejected
    reconstructionMismatch fingerprintDrift noClaim recompute originalUnsat bad
