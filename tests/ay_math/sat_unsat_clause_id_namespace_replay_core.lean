-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded compact clause-id namespace replay soundness for ay sequential-main
-- SAT-COMP checking. Propositions stand for namespace maps, cross-chunk ID
-- remapping, parent coverage, step-map evidence, epoch/digest membership,
-- checker transcripts, reconstruction handles, original fingerprints, and
-- fail-closed no-claim/recompute diagnostics.

def AyUCINConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCINDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCINMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCINNamespaceMap
    (namespaceMap : Prop) (crossChunkRemap : Prop)
    (namespacedReplay : Prop) :=
  AyUCINConj namespaceMap
    (AyUCINConj
      (AyUCINMap namespaceMap crossChunkRemap)
      (AyUCINMap crossChunkRemap namespacedReplay))

def AyUCINParentCoverage
    (namespacedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :=
  AyUCINConj
    (AyUCINMap namespacedReplay parentCoverage)
    (AyUCINMap parentCoverage emptyClause)

def AyUCINStepMap
    (namespacedReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :=
  AyUCINConj
    (AyUCINMap namespacedReplay stepMapEvidence)
    (AyUCINMap stepMapEvidence stepMapAccepted)

def AyUCINEpochDigest
    (namespacedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :=
  AyUCINConj
    (AyUCINMap namespacedReplay epochMember)
    (AyUCINConj
      (AyUCINMap epochMember digestMember)
      (AyUCINMap digestMember epochDigestAccepted))

def AyUCINCheckerTranscript
    (namespacedReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :=
  AyUCINConj
    (AyUCINMap namespacedReplay checkerTranscript)
    (AyUCINMap checkerTranscript checkerAccepted)

def AyUCINReconstruction
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCINConj reconstructionHandle
    (AyUCINConj
      (AyUCINMap emptyClause visibleUnsat)
      (AyUCINMap visibleUnsat originalUnsat))

def AyUCINFingerprint
    (namespacedReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUCINConj
    (AyUCINMap namespacedReplay fingerprintAgrees)
    (AyUCINMap fingerprintAgrees visibleUnsat)

def AyUCINAcceptedEvidence
    (namespaceMap : Prop) (crossChunkRemap : Prop)
    (namespacedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCINConj
    (AyUCINNamespaceMap namespaceMap crossChunkRemap namespacedReplay)
    (AyUCINConj
      (AyUCINParentCoverage namespacedReplay parentCoverage emptyClause)
      (AyUCINConj
        (AyUCINStepMap namespacedReplay stepMapEvidence stepMapAccepted)
        (AyUCINConj
          (AyUCINEpochDigest namespacedReplay epochMember digestMember
            epochDigestAccepted)
          (AyUCINConj
            (AyUCINCheckerTranscript namespacedReplay checkerTranscript
              checkerAccepted)
            (AyUCINConj
              (AyUCINReconstruction emptyClause reconstructionHandle
                visibleUnsat originalUnsat)
              (AyUCINFingerprint namespacedReplay fingerprintAgrees
                visibleUnsat))))))

def AyUCINAcceptedReplay
    (namespaceMap : Prop) (crossChunkRemap : Prop)
    (namespacedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCINConj
    (AyUCINAcceptedEvidence namespaceMap crossChunkRemap namespacedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat

def AyUCINBadNamespace
    (namespaceCollision : Prop) (idDrift : Prop)
    (uncheckedRemap : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUCINConj
    (AyUCINConj noClaim recompute)
    (AyUCINDisj namespaceCollision
      (AyUCINDisj idDrift
        (AyUCINDisj uncheckedRemap
          (AyUCINDisj parentGap
            (AyUCINDisj stepMapMismatch
              (AyUCINDisj epochDrift
                (AyUCINDisj digestMismatch checkerRejected)))))))

def AyUCINPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCINDisj noClaim originalUnsat

theorem ay_ucin_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCINConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucin_conj_left
    (p : Prop) (q : Prop) :
    AyUCINConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucin_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCINDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucin_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCINDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucin_namespace_map
    (nsMap : Prop) (crossChunkRemap : Prop)
    (namespacedReplay : Prop) :
    AyUCINNamespaceMap nsMap crossChunkRemap namespacedReplay ->
    nsMap := by
  intro ns
  exact ns nsMap
    (fun map_proof _tail => map_proof)

theorem ay_ucin_cross_chunk_remap
    (nsMap : Prop) (crossChunkRemap : Prop)
    (namespacedReplay : Prop) :
    AyUCINNamespaceMap nsMap crossChunkRemap namespacedReplay ->
    crossChunkRemap := by
  intro ns
  exact ns crossChunkRemap
    (fun (map_proof : nsMap) tail =>
      tail crossChunkRemap
        (fun (map_to_remap : AyUCINMap nsMap crossChunkRemap)
          (_remap_to_replay : AyUCINMap crossChunkRemap namespacedReplay) =>
          map_to_remap map_proof))

theorem ay_ucin_namespaced_replay
    (nsMap : Prop) (crossChunkRemap : Prop)
    (namespacedReplay : Prop) :
    AyUCINNamespaceMap nsMap crossChunkRemap namespacedReplay ->
    namespacedReplay := by
  intro ns
  exact ns namespacedReplay
    (fun (map_proof : nsMap) tail =>
      tail namespacedReplay
        (fun (map_to_remap : AyUCINMap nsMap crossChunkRemap)
          (remap_to_replay : AyUCINMap crossChunkRemap namespacedReplay) =>
          remap_to_replay (map_to_remap map_proof)))

theorem ay_ucin_parent_coverage
    (namespacedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUCINParentCoverage namespacedReplay parentCoverage emptyClause ->
    namespacedReplay ->
    parentCoverage := by
  intro parents
  exact parents (namespacedReplay -> parentCoverage)
    (fun replay_to_parents _parents_to_empty => replay_to_parents)

theorem ay_ucin_empty_clause
    (namespacedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUCINParentCoverage namespacedReplay parentCoverage emptyClause ->
    parentCoverage ->
    emptyClause := by
  intro parents
  exact parents (parentCoverage -> emptyClause)
    (fun _replay_to_parents parents_to_empty => parents_to_empty)

theorem ay_ucin_step_map_evidence
    (namespacedReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :
    AyUCINStepMap namespacedReplay stepMapEvidence stepMapAccepted ->
    namespacedReplay ->
    stepMapEvidence := by
  intro step_map
  exact step_map (namespacedReplay -> stepMapEvidence)
    (fun replay_to_step_map _step_map_to_accept => replay_to_step_map)

theorem ay_ucin_step_map_accepted
    (namespacedReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :
    AyUCINStepMap namespacedReplay stepMapEvidence stepMapAccepted ->
    stepMapEvidence ->
    stepMapAccepted := by
  intro step_map
  exact step_map (stepMapEvidence -> stepMapAccepted)
    (fun _replay_to_step_map step_map_to_accept => step_map_to_accept)

theorem ay_ucin_epoch_member
    (namespacedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUCINEpochDigest namespacedReplay epochMember digestMember
      epochDigestAccepted ->
    namespacedReplay ->
    epochMember := by
  intro epoch_digest
  exact epoch_digest (namespacedReplay -> epochMember)
    (fun replay_to_epoch _tail => replay_to_epoch)

theorem ay_ucin_digest_member
    (namespacedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUCINEpochDigest namespacedReplay epochMember digestMember
      epochDigestAccepted ->
    epochMember ->
    digestMember := by
  intro epoch_digest
  exact epoch_digest (epochMember -> digestMember)
    (fun _replay_to_epoch tail =>
      tail (epochMember -> digestMember)
        (fun epoch_to_digest _digest_to_accept => epoch_to_digest))

theorem ay_ucin_epoch_digest_accepted
    (namespacedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUCINEpochDigest namespacedReplay epochMember digestMember
      epochDigestAccepted ->
    digestMember ->
    epochDigestAccepted := by
  intro epoch_digest
  exact epoch_digest (digestMember -> epochDigestAccepted)
    (fun _replay_to_epoch tail =>
      tail (digestMember -> epochDigestAccepted)
        (fun _epoch_to_digest digest_to_accept => digest_to_accept))

theorem ay_ucin_checker_transcript
    (namespacedReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUCINCheckerTranscript namespacedReplay checkerTranscript
      checkerAccepted ->
    namespacedReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (namespacedReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_ucin_checker_accepted
    (namespacedReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUCINCheckerTranscript namespacedReplay checkerTranscript
      checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> checkerAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_ucin_reconstruction_handle
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCINReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    reconstructionHandle := by
  intro reconstruction
  exact ay_ucin_conj_left reconstructionHandle
    (AyUCINConj
      (AyUCINMap emptyClause visibleUnsat)
      (AyUCINMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_ucin_visible_unsat_from_empty
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCINReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClause -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_ucin_original_unsat_from_visible
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCINReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original => visible_to_original))

theorem ay_ucin_fingerprint_agrees
    (namespacedReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUCINFingerprint namespacedReplay fingerprintAgrees visibleUnsat ->
    namespacedReplay ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (namespacedReplay -> fingerprintAgrees)
    (fun replay_to_fingerprint _fingerprint_to_visible =>
      replay_to_fingerprint)

theorem ay_ucin_visible_unsat_from_fingerprint
    (namespacedReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUCINFingerprint namespacedReplay fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _replay_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_ucin_accepted_evidence
    (namespaceMap : Prop) (crossChunkRemap : Prop)
    (namespacedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCINAcceptedReplay namespaceMap crossChunkRemap namespacedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCINAcceptedEvidence namespaceMap crossChunkRemap namespacedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat := by
  intro accepted
  exact ay_ucin_conj_left
    (AyUCINAcceptedEvidence namespaceMap crossChunkRemap namespacedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_ucin_accepted_original_unsat
    (namespaceMap : Prop) (crossChunkRemap : Prop)
    (namespacedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCINAcceptedReplay namespaceMap crossChunkRemap namespacedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_ucin_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUCINPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucin_disj_right noClaim originalUnsat unsat

theorem ay_ucin_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUCINPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucin_disj_left noClaim originalUnsat no_claim

theorem ay_ucin_accepted_namespace_publish_sound
    (namespaceMap : Prop) (crossChunkRemap : Prop)
    (namespacedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUCINAcceptedReplay namespaceMap crossChunkRemap namespacedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUCINPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_ucin_public_unsat_report noClaim originalUnsat
    (ay_ucin_accepted_original_unsat namespaceMap crossChunkRemap
      namespacedReplay parentCoverage emptyClause stepMapEvidence
      stepMapAccepted epochMember digestMember epochDigestAccepted
      checkerTranscript checkerAccepted reconstructionHandle fingerprintAgrees
      visibleUnsat originalUnsat accepted)

theorem ay_ucin_bad_namespace_no_claim
    (namespaceCollision : Prop) (idDrift : Prop)
    (uncheckedRemap : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCINBadNamespace namespaceCollision idDrift uncheckedRemap parentGap
      stepMapMismatch epochDrift digestMismatch checkerRejected noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_ucin_conj_left noClaim recompute fail_closed)

theorem ay_ucin_bad_namespace_recompute
    (namespaceCollision : Prop) (idDrift : Prop)
    (uncheckedRemap : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCINBadNamespace namespaceCollision idDrift uncheckedRemap parentGap
      stepMapMismatch epochDrift digestMismatch checkerRejected noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_ucin_bad_namespace_public_no_claim
    (namespaceCollision : Prop) (idDrift : Prop)
    (uncheckedRemap : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCINBadNamespace namespaceCollision idDrift uncheckedRemap parentGap
      stepMapMismatch epochDrift digestMismatch checkerRejected noClaim
      recompute ->
    AyUCINPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucin_public_no_claim_report noClaim originalUnsat
    (ay_ucin_bad_namespace_no_claim namespaceCollision idDrift
      uncheckedRemap parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute bad)

theorem ay_ucin_bad_namespace_cannot_publish
    (namespaceCollision : Prop) (idDrift : Prop)
    (uncheckedRemap : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCINBadNamespace namespaceCollision idDrift uncheckedRemap parentGap
      stepMapMismatch epochDrift digestMismatch checkerRejected noClaim
      recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_ucin_bad_namespace_no_claim namespaceCollision idDrift
      uncheckedRemap parentGap stepMapMismatch epochDrift digestMismatch
      checkerRejected noClaim recompute bad)
    unsat

theorem ay_ucin_namespace_collision_forces_no_claim
    (namespaceCollision : Prop) (idDrift : Prop)
    (uncheckedRemap : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    namespaceCollision ->
    AyUCINConj noClaim recompute ->
    AyUCINBadNamespace namespaceCollision idDrift uncheckedRemap parentGap
      stepMapMismatch epochDrift digestMismatch checkerRejected noClaim
      recompute := by
  intro collision
  intro fail_closed
  exact ay_ucin_conj_intro
    (AyUCINConj noClaim recompute)
    (AyUCINDisj namespaceCollision
      (AyUCINDisj idDrift
        (AyUCINDisj uncheckedRemap
          (AyUCINDisj parentGap
            (AyUCINDisj stepMapMismatch
              (AyUCINDisj epochDrift
                (AyUCINDisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_ucin_disj_left namespaceCollision
      (AyUCINDisj idDrift
        (AyUCINDisj uncheckedRemap
          (AyUCINDisj parentGap
            (AyUCINDisj stepMapMismatch
              (AyUCINDisj epochDrift
                (AyUCINDisj digestMismatch checkerRejected))))))
      collision)

theorem ay_ucin_id_drift_forces_no_claim
    (namespaceCollision : Prop) (idDrift : Prop)
    (uncheckedRemap : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    idDrift ->
    AyUCINConj noClaim recompute ->
    AyUCINBadNamespace namespaceCollision idDrift uncheckedRemap parentGap
      stepMapMismatch epochDrift digestMismatch checkerRejected noClaim
      recompute := by
  intro drift
  intro fail_closed
  exact ay_ucin_conj_intro
    (AyUCINConj noClaim recompute)
    (AyUCINDisj namespaceCollision
      (AyUCINDisj idDrift
        (AyUCINDisj uncheckedRemap
          (AyUCINDisj parentGap
            (AyUCINDisj stepMapMismatch
              (AyUCINDisj epochDrift
                (AyUCINDisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_ucin_disj_right namespaceCollision
      (AyUCINDisj idDrift
        (AyUCINDisj uncheckedRemap
          (AyUCINDisj parentGap
            (AyUCINDisj stepMapMismatch
              (AyUCINDisj epochDrift
                (AyUCINDisj digestMismatch checkerRejected))))))
      (ay_ucin_disj_left idDrift
        (AyUCINDisj uncheckedRemap
          (AyUCINDisj parentGap
            (AyUCINDisj stepMapMismatch
              (AyUCINDisj epochDrift
                (AyUCINDisj digestMismatch checkerRejected)))))
        drift))

theorem ay_ucin_unchecked_remap_forces_no_claim
    (namespaceCollision : Prop) (idDrift : Prop)
    (uncheckedRemap : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    uncheckedRemap ->
    AyUCINConj noClaim recompute ->
    AyUCINBadNamespace namespaceCollision idDrift uncheckedRemap parentGap
      stepMapMismatch epochDrift digestMismatch checkerRejected noClaim
      recompute := by
  intro unchecked
  intro fail_closed
  exact ay_ucin_conj_intro
    (AyUCINConj noClaim recompute)
    (AyUCINDisj namespaceCollision
      (AyUCINDisj idDrift
        (AyUCINDisj uncheckedRemap
          (AyUCINDisj parentGap
            (AyUCINDisj stepMapMismatch
              (AyUCINDisj epochDrift
                (AyUCINDisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_ucin_disj_right namespaceCollision
      (AyUCINDisj idDrift
        (AyUCINDisj uncheckedRemap
          (AyUCINDisj parentGap
            (AyUCINDisj stepMapMismatch
              (AyUCINDisj epochDrift
                (AyUCINDisj digestMismatch checkerRejected))))))
      (ay_ucin_disj_right idDrift
        (AyUCINDisj uncheckedRemap
          (AyUCINDisj parentGap
            (AyUCINDisj stepMapMismatch
              (AyUCINDisj epochDrift
                (AyUCINDisj digestMismatch checkerRejected)))))
        (ay_ucin_disj_left uncheckedRemap
          (AyUCINDisj parentGap
            (AyUCINDisj stepMapMismatch
              (AyUCINDisj epochDrift
                (AyUCINDisj digestMismatch checkerRejected))))
          unchecked)))

theorem ay_ucin_unchecked_remap_cannot_publish
    (namespaceCollision : Prop) (idDrift : Prop)
    (uncheckedRemap : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCINBadNamespace namespaceCollision idDrift uncheckedRemap parentGap
      stepMapMismatch epochDrift digestMismatch checkerRejected noClaim
      recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_ucin_bad_namespace_cannot_publish namespaceCollision idDrift
    uncheckedRemap parentGap stepMapMismatch epochDrift digestMismatch
    checkerRejected noClaim recompute originalUnsat bad
