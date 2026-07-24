-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded projected-core replay soundness for ay sequential-main SAT-COMP
-- UNSAT checking. Propositions stand for projected UNSAT cores, reduced proof
-- roots, parent coverage, step-map evidence, epoch/digest membership, checker
-- transcripts, reconstruction handles, original fingerprints, and fail-closed
-- no-claim/recompute diagnostics.

def AyUCPRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCPRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCPRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCPRProjection
    (coreProjection : Prop) (reducedProofRoot : Prop)
    (projectedReplay : Prop) :=
  AyUCPRConj coreProjection
    (AyUCPRConj
      (AyUCPRMap coreProjection reducedProofRoot)
      (AyUCPRMap reducedProofRoot projectedReplay))

def AyUCPRParentCoverage
    (projectedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :=
  AyUCPRConj
    (AyUCPRMap projectedReplay parentCoverage)
    (AyUCPRMap parentCoverage emptyClause)

def AyUCPRStepMap
    (projectedReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :=
  AyUCPRConj
    (AyUCPRMap projectedReplay stepMapEvidence)
    (AyUCPRMap stepMapEvidence stepMapAccepted)

def AyUCPREpochDigest
    (projectedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :=
  AyUCPRConj
    (AyUCPRMap projectedReplay epochMember)
    (AyUCPRConj
      (AyUCPRMap epochMember digestMember)
      (AyUCPRMap digestMember epochDigestAccepted))

def AyUCPRCheckerTranscript
    (projectedReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :=
  AyUCPRConj
    (AyUCPRMap projectedReplay checkerTranscript)
    (AyUCPRMap checkerTranscript checkerAccepted)

def AyUCPRReconstruction
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCPRConj reconstructionHandle
    (AyUCPRConj
      (AyUCPRMap emptyClause visibleUnsat)
      (AyUCPRMap visibleUnsat originalUnsat))

def AyUCPRFingerprint
    (projectedReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUCPRConj
    (AyUCPRMap projectedReplay fingerprintAgrees)
    (AyUCPRMap fingerprintAgrees visibleUnsat)

def AyUCPRAcceptedEvidence
    (coreProjection : Prop) (reducedProofRoot : Prop)
    (projectedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCPRConj
    (AyUCPRProjection coreProjection reducedProofRoot projectedReplay)
    (AyUCPRConj
      (AyUCPRParentCoverage projectedReplay parentCoverage emptyClause)
      (AyUCPRConj
        (AyUCPRStepMap projectedReplay stepMapEvidence stepMapAccepted)
        (AyUCPRConj
          (AyUCPREpochDigest projectedReplay epochMember digestMember
            epochDigestAccepted)
          (AyUCPRConj
            (AyUCPRCheckerTranscript projectedReplay checkerTranscript
              checkerAccepted)
            (AyUCPRConj
              (AyUCPRReconstruction emptyClause reconstructionHandle
                visibleUnsat originalUnsat)
              (AyUCPRFingerprint projectedReplay fingerprintAgrees
                visibleUnsat))))))

def AyUCPRAcceptedReplay
    (coreProjection : Prop) (reducedProofRoot : Prop)
    (projectedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCPRConj
    (AyUCPRAcceptedEvidence coreProjection reducedProofRoot projectedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat

def AyUCPRBadProjection
    (projectionDrift : Prop) (missingRootCoverage : Prop)
    (uncheckedProjection : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUCPRConj
    (AyUCPRConj noClaim recompute)
    (AyUCPRDisj projectionDrift
      (AyUCPRDisj missingRootCoverage
        (AyUCPRDisj uncheckedProjection
          (AyUCPRDisj parentGap
            (AyUCPRDisj stepMapMismatch
              (AyUCPRDisj epochDrift
                (AyUCPRDisj digestMismatch checkerRejected)))))))

def AyUCPRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCPRDisj noClaim originalUnsat

theorem ay_ucpr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCPRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucpr_conj_left
    (p : Prop) (q : Prop) :
    AyUCPRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucpr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCPRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucpr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCPRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucpr_core_projection
    (coreProjection : Prop) (reducedProofRoot : Prop)
    (projectedReplay : Prop) :
    AyUCPRProjection coreProjection reducedProofRoot projectedReplay ->
    coreProjection := by
  intro projection
  exact ay_ucpr_conj_left coreProjection
    (AyUCPRConj
      (AyUCPRMap coreProjection reducedProofRoot)
      (AyUCPRMap reducedProofRoot projectedReplay))
    projection

theorem ay_ucpr_reduced_proof_root
    (coreProjection : Prop) (reducedProofRoot : Prop)
    (projectedReplay : Prop) :
    AyUCPRProjection coreProjection reducedProofRoot projectedReplay ->
    reducedProofRoot := by
  intro projection
  exact projection reducedProofRoot
    (fun core tail =>
      tail reducedProofRoot
        (fun core_to_root _root_to_replay => core_to_root core))

theorem ay_ucpr_projected_replay
    (coreProjection : Prop) (reducedProofRoot : Prop)
    (projectedReplay : Prop) :
    AyUCPRProjection coreProjection reducedProofRoot projectedReplay ->
    projectedReplay := by
  intro projection
  exact projection projectedReplay
    (fun core tail =>
      tail projectedReplay
        (fun core_to_root root_to_replay =>
          root_to_replay (core_to_root core)))

theorem ay_ucpr_parent_coverage
    (projectedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUCPRParentCoverage projectedReplay parentCoverage emptyClause ->
    projectedReplay ->
    parentCoverage := by
  intro parents
  exact parents (projectedReplay -> parentCoverage)
    (fun replay_to_parents _parents_to_empty => replay_to_parents)

theorem ay_ucpr_empty_clause
    (projectedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUCPRParentCoverage projectedReplay parentCoverage emptyClause ->
    parentCoverage ->
    emptyClause := by
  intro parents
  exact parents (parentCoverage -> emptyClause)
    (fun _replay_to_parents parents_to_empty => parents_to_empty)

theorem ay_ucpr_step_map_evidence
    (projectedReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :
    AyUCPRStepMap projectedReplay stepMapEvidence stepMapAccepted ->
    projectedReplay ->
    stepMapEvidence := by
  intro step_map
  exact step_map (projectedReplay -> stepMapEvidence)
    (fun replay_to_step_map _step_map_to_accept => replay_to_step_map)

theorem ay_ucpr_step_map_accepted
    (projectedReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :
    AyUCPRStepMap projectedReplay stepMapEvidence stepMapAccepted ->
    stepMapEvidence ->
    stepMapAccepted := by
  intro step_map
  exact step_map (stepMapEvidence -> stepMapAccepted)
    (fun _replay_to_step_map step_map_to_accept => step_map_to_accept)

theorem ay_ucpr_epoch_member
    (projectedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUCPREpochDigest projectedReplay epochMember digestMember
      epochDigestAccepted ->
    projectedReplay ->
    epochMember := by
  intro epoch_digest
  exact epoch_digest (projectedReplay -> epochMember)
    (fun replay_to_epoch _tail => replay_to_epoch)

theorem ay_ucpr_digest_member
    (projectedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUCPREpochDigest projectedReplay epochMember digestMember
      epochDigestAccepted ->
    epochMember ->
    digestMember := by
  intro epoch_digest
  exact epoch_digest (epochMember -> digestMember)
    (fun _replay_to_epoch tail =>
      tail (epochMember -> digestMember)
        (fun epoch_to_digest _digest_to_accept => epoch_to_digest))

theorem ay_ucpr_epoch_digest_accepted
    (projectedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUCPREpochDigest projectedReplay epochMember digestMember
      epochDigestAccepted ->
    digestMember ->
    epochDigestAccepted := by
  intro epoch_digest
  exact epoch_digest (digestMember -> epochDigestAccepted)
    (fun _replay_to_epoch tail =>
      tail (digestMember -> epochDigestAccepted)
        (fun _epoch_to_digest digest_to_accept => digest_to_accept))

theorem ay_ucpr_checker_transcript
    (projectedReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUCPRCheckerTranscript projectedReplay checkerTranscript
      checkerAccepted ->
    projectedReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (projectedReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_ucpr_checker_accepted
    (projectedReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUCPRCheckerTranscript projectedReplay checkerTranscript
      checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> checkerAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_ucpr_reconstruction_handle
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCPRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    reconstructionHandle := by
  intro reconstruction
  exact ay_ucpr_conj_left reconstructionHandle
    (AyUCPRConj
      (AyUCPRMap emptyClause visibleUnsat)
      (AyUCPRMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_ucpr_visible_unsat_from_empty
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCPRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClause -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_ucpr_original_unsat_from_visible
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCPRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original => visible_to_original))

theorem ay_ucpr_fingerprint_agrees
    (projectedReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUCPRFingerprint projectedReplay fingerprintAgrees visibleUnsat ->
    projectedReplay ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (projectedReplay -> fingerprintAgrees)
    (fun replay_to_fingerprint _fingerprint_to_visible =>
      replay_to_fingerprint)

theorem ay_ucpr_visible_unsat_from_fingerprint
    (projectedReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUCPRFingerprint projectedReplay fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _replay_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_ucpr_accepted_evidence
    (coreProjection : Prop) (reducedProofRoot : Prop)
    (projectedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCPRAcceptedReplay coreProjection reducedProofRoot projectedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCPRAcceptedEvidence coreProjection reducedProofRoot projectedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat := by
  intro accepted
  exact ay_ucpr_conj_left
    (AyUCPRAcceptedEvidence coreProjection reducedProofRoot projectedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_ucpr_accepted_original_unsat
    (coreProjection : Prop) (reducedProofRoot : Prop)
    (projectedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCPRAcceptedReplay coreProjection reducedProofRoot projectedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_ucpr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUCPRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucpr_disj_right noClaim originalUnsat unsat

theorem ay_ucpr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUCPRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucpr_disj_left noClaim originalUnsat no_claim

theorem ay_ucpr_accepted_projection_publish_sound
    (coreProjection : Prop) (reducedProofRoot : Prop)
    (projectedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUCPRAcceptedReplay coreProjection reducedProofRoot projectedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCPRPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_ucpr_public_unsat_report noClaim originalUnsat
    (ay_ucpr_accepted_original_unsat coreProjection reducedProofRoot
      projectedReplay parentCoverage emptyClause stepMapEvidence
      stepMapAccepted epochMember digestMember epochDigestAccepted
      checkerTranscript checkerAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat accepted)

theorem ay_ucpr_bad_projection_no_claim
    (projectionDrift : Prop) (missingRootCoverage : Prop)
    (uncheckedProjection : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCPRBadProjection projectionDrift missingRootCoverage
      uncheckedProjection parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_ucpr_conj_left noClaim recompute fail_closed)

theorem ay_ucpr_bad_projection_recompute
    (projectionDrift : Prop) (missingRootCoverage : Prop)
    (uncheckedProjection : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCPRBadProjection projectionDrift missingRootCoverage
      uncheckedProjection parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_ucpr_bad_projection_public_no_claim
    (projectionDrift : Prop) (missingRootCoverage : Prop)
    (uncheckedProjection : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCPRBadProjection projectionDrift missingRootCoverage
      uncheckedProjection parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute ->
    AyUCPRPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucpr_public_no_claim_report noClaim originalUnsat
    (ay_ucpr_bad_projection_no_claim projectionDrift missingRootCoverage
      uncheckedProjection parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute bad)

theorem ay_ucpr_bad_projection_cannot_publish
    (projectionDrift : Prop) (missingRootCoverage : Prop)
    (uncheckedProjection : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCPRBadProjection projectionDrift missingRootCoverage
      uncheckedProjection parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_ucpr_bad_projection_no_claim projectionDrift missingRootCoverage
      uncheckedProjection parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute bad)
    unsat

theorem ay_ucpr_projection_drift_forces_no_claim
    (projectionDrift : Prop) (missingRootCoverage : Prop)
    (uncheckedProjection : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    projectionDrift ->
    AyUCPRConj noClaim recompute ->
    AyUCPRBadProjection projectionDrift missingRootCoverage
      uncheckedProjection parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute := by
  intro drift
  intro fail_closed
  exact ay_ucpr_conj_intro
    (AyUCPRConj noClaim recompute)
    (AyUCPRDisj projectionDrift
      (AyUCPRDisj missingRootCoverage
        (AyUCPRDisj uncheckedProjection
          (AyUCPRDisj parentGap
            (AyUCPRDisj stepMapMismatch
              (AyUCPRDisj epochDrift
                (AyUCPRDisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_ucpr_disj_left projectionDrift
      (AyUCPRDisj missingRootCoverage
        (AyUCPRDisj uncheckedProjection
          (AyUCPRDisj parentGap
            (AyUCPRDisj stepMapMismatch
              (AyUCPRDisj epochDrift
                (AyUCPRDisj digestMismatch checkerRejected))))))
      drift)

theorem ay_ucpr_missing_root_coverage_forces_no_claim
    (projectionDrift : Prop) (missingRootCoverage : Prop)
    (uncheckedProjection : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    missingRootCoverage ->
    AyUCPRConj noClaim recompute ->
    AyUCPRBadProjection projectionDrift missingRootCoverage
      uncheckedProjection parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute := by
  intro missing_root
  intro fail_closed
  exact ay_ucpr_conj_intro
    (AyUCPRConj noClaim recompute)
    (AyUCPRDisj projectionDrift
      (AyUCPRDisj missingRootCoverage
        (AyUCPRDisj uncheckedProjection
          (AyUCPRDisj parentGap
            (AyUCPRDisj stepMapMismatch
              (AyUCPRDisj epochDrift
                (AyUCPRDisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_ucpr_disj_right projectionDrift
      (AyUCPRDisj missingRootCoverage
        (AyUCPRDisj uncheckedProjection
          (AyUCPRDisj parentGap
            (AyUCPRDisj stepMapMismatch
              (AyUCPRDisj epochDrift
                (AyUCPRDisj digestMismatch checkerRejected))))))
      (ay_ucpr_disj_left missingRootCoverage
        (AyUCPRDisj uncheckedProjection
          (AyUCPRDisj parentGap
            (AyUCPRDisj stepMapMismatch
              (AyUCPRDisj epochDrift
                (AyUCPRDisj digestMismatch checkerRejected)))))
        missing_root))

theorem ay_ucpr_unchecked_projection_forces_no_claim
    (projectionDrift : Prop) (missingRootCoverage : Prop)
    (uncheckedProjection : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    uncheckedProjection ->
    AyUCPRConj noClaim recompute ->
    AyUCPRBadProjection projectionDrift missingRootCoverage
      uncheckedProjection parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute := by
  intro unchecked
  intro fail_closed
  exact ay_ucpr_conj_intro
    (AyUCPRConj noClaim recompute)
    (AyUCPRDisj projectionDrift
      (AyUCPRDisj missingRootCoverage
        (AyUCPRDisj uncheckedProjection
          (AyUCPRDisj parentGap
            (AyUCPRDisj stepMapMismatch
              (AyUCPRDisj epochDrift
                (AyUCPRDisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_ucpr_disj_right projectionDrift
      (AyUCPRDisj missingRootCoverage
        (AyUCPRDisj uncheckedProjection
          (AyUCPRDisj parentGap
            (AyUCPRDisj stepMapMismatch
              (AyUCPRDisj epochDrift
                (AyUCPRDisj digestMismatch checkerRejected))))))
      (ay_ucpr_disj_right missingRootCoverage
        (AyUCPRDisj uncheckedProjection
          (AyUCPRDisj parentGap
            (AyUCPRDisj stepMapMismatch
              (AyUCPRDisj epochDrift
                (AyUCPRDisj digestMismatch checkerRejected)))))
        (ay_ucpr_disj_left uncheckedProjection
          (AyUCPRDisj parentGap
            (AyUCPRDisj stepMapMismatch
              (AyUCPRDisj epochDrift
                (AyUCPRDisj digestMismatch checkerRejected))))
          unchecked)))

theorem ay_ucpr_unchecked_projection_cannot_publish
    (projectionDrift : Prop) (missingRootCoverage : Prop)
    (uncheckedProjection : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCPRBadProjection projectionDrift missingRootCoverage
      uncheckedProjection parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_ucpr_bad_projection_cannot_publish projectionDrift
    missingRootCoverage uncheckedProjection parentGap stepMapMismatch
    epochDrift digestMismatch checkerRejected noClaim recompute originalUnsat
    bad
