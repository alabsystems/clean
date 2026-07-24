-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded proof-chunk order-independence replay soundness for ay
-- sequential-main SAT-COMP checking. Propositions stand for chunk order maps,
-- dependency order, parent coverage, step-map evidence, epoch/digest
-- membership, checker transcripts, reconstruction handles, original
-- fingerprints, and fail-closed no-claim/recompute diagnostics.

def AyUPCOConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPCODisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPCOMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPCOChunkOrder
    (chunkOrderMap : Prop) (dependencyOrder : Prop)
    (orderedReplay : Prop) :=
  AyUPCOConj chunkOrderMap
    (AyUPCOConj
      (AyUPCOMap chunkOrderMap dependencyOrder)
      (AyUPCOMap dependencyOrder orderedReplay))

def AyUPCOParentCoverage
    (orderedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :=
  AyUPCOConj
    (AyUPCOMap orderedReplay parentCoverage)
    (AyUPCOMap parentCoverage emptyClause)

def AyUPCOStepMap
    (orderedReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :=
  AyUPCOConj
    (AyUPCOMap orderedReplay stepMapEvidence)
    (AyUPCOMap stepMapEvidence stepMapAccepted)

def AyUPCOEpochDigest
    (orderedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :=
  AyUPCOConj
    (AyUPCOMap orderedReplay epochMember)
    (AyUPCOConj
      (AyUPCOMap epochMember digestMember)
      (AyUPCOMap digestMember epochDigestAccepted))

def AyUPCOCheckerTranscript
    (orderedReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :=
  AyUPCOConj
    (AyUPCOMap orderedReplay checkerTranscript)
    (AyUPCOMap checkerTranscript checkerAccepted)

def AyUPCOReconstruction
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPCOConj reconstructionHandle
    (AyUPCOConj
      (AyUPCOMap emptyClause visibleUnsat)
      (AyUPCOMap visibleUnsat originalUnsat))

def AyUPCOFingerprint
    (orderedReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUPCOConj
    (AyUPCOMap orderedReplay fingerprintAgrees)
    (AyUPCOMap fingerprintAgrees visibleUnsat)

def AyUPCOAcceptedEvidence
    (chunkOrderMap : Prop) (dependencyOrder : Prop)
    (orderedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPCOConj
    (AyUPCOChunkOrder chunkOrderMap dependencyOrder orderedReplay)
    (AyUPCOConj
      (AyUPCOParentCoverage orderedReplay parentCoverage emptyClause)
      (AyUPCOConj
        (AyUPCOStepMap orderedReplay stepMapEvidence stepMapAccepted)
        (AyUPCOConj
          (AyUPCOEpochDigest orderedReplay epochMember digestMember
            epochDigestAccepted)
          (AyUPCOConj
            (AyUPCOCheckerTranscript orderedReplay checkerTranscript
              checkerAccepted)
            (AyUPCOConj
              (AyUPCOReconstruction emptyClause reconstructionHandle
                visibleUnsat originalUnsat)
              (AyUPCOFingerprint orderedReplay fingerprintAgrees
                visibleUnsat))))))

def AyUPCOAcceptedReplay
    (chunkOrderMap : Prop) (dependencyOrder : Prop)
    (orderedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPCOConj
    (AyUPCOAcceptedEvidence chunkOrderMap dependencyOrder orderedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat

def AyUPCOBadOrder
    (chunkPermutationDrift : Prop) (missingDependencyOrder : Prop)
    (uncheckedChunkOrdering : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUPCOConj
    (AyUPCOConj noClaim recompute)
    (AyUPCODisj chunkPermutationDrift
      (AyUPCODisj missingDependencyOrder
        (AyUPCODisj uncheckedChunkOrdering
          (AyUPCODisj parentGap
            (AyUPCODisj stepMapMismatch
              (AyUPCODisj epochDrift
                (AyUPCODisj digestMismatch checkerRejected)))))))

def AyUPCOPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPCODisj noClaim originalUnsat

theorem ay_upco_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPCOConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_upco_conj_left
    (p : Prop) (q : Prop) :
    AyUPCOConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_upco_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPCODisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_upco_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPCODisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_upco_chunk_order_map
    (chunkOrderMap : Prop) (dependencyOrder : Prop)
    (orderedReplay : Prop) :
    AyUPCOChunkOrder chunkOrderMap dependencyOrder orderedReplay ->
    chunkOrderMap := by
  intro order
  exact order chunkOrderMap
    (fun order_map _tail => order_map)

theorem ay_upco_dependency_order
    (chunkOrderMap : Prop) (dependencyOrder : Prop)
    (orderedReplay : Prop) :
    AyUPCOChunkOrder chunkOrderMap dependencyOrder orderedReplay ->
    dependencyOrder := by
  intro order
  exact order dependencyOrder
    (fun (order_map : chunkOrderMap) tail =>
      tail dependencyOrder
        (fun order_to_dependency _dependency_to_replay =>
          order_to_dependency order_map))

theorem ay_upco_ordered_replay
    (chunkOrderMap : Prop) (dependencyOrder : Prop)
    (orderedReplay : Prop) :
    AyUPCOChunkOrder chunkOrderMap dependencyOrder orderedReplay ->
    orderedReplay := by
  intro order
  exact order orderedReplay
    (fun (order_map : chunkOrderMap) tail =>
      tail orderedReplay
        (fun order_to_dependency dependency_to_replay =>
          dependency_to_replay (order_to_dependency order_map)))

theorem ay_upco_parent_coverage
    (orderedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUPCOParentCoverage orderedReplay parentCoverage emptyClause ->
    orderedReplay ->
    parentCoverage := by
  intro parents
  exact parents (orderedReplay -> parentCoverage)
    (fun replay_to_parents _parents_to_empty => replay_to_parents)

theorem ay_upco_empty_clause
    (orderedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUPCOParentCoverage orderedReplay parentCoverage emptyClause ->
    parentCoverage ->
    emptyClause := by
  intro parents
  exact parents (parentCoverage -> emptyClause)
    (fun _replay_to_parents parents_to_empty => parents_to_empty)

theorem ay_upco_step_map_evidence
    (orderedReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :
    AyUPCOStepMap orderedReplay stepMapEvidence stepMapAccepted ->
    orderedReplay ->
    stepMapEvidence := by
  intro step_map
  exact step_map (orderedReplay -> stepMapEvidence)
    (fun replay_to_step_map _step_map_to_accept => replay_to_step_map)

theorem ay_upco_step_map_accepted
    (orderedReplay : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) :
    AyUPCOStepMap orderedReplay stepMapEvidence stepMapAccepted ->
    stepMapEvidence ->
    stepMapAccepted := by
  intro step_map
  exact step_map (stepMapEvidence -> stepMapAccepted)
    (fun _replay_to_step_map step_map_to_accept => step_map_to_accept)

theorem ay_upco_epoch_member
    (orderedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUPCOEpochDigest orderedReplay epochMember digestMember
      epochDigestAccepted ->
    orderedReplay ->
    epochMember := by
  intro epoch_digest
  exact epoch_digest (orderedReplay -> epochMember)
    (fun replay_to_epoch _tail => replay_to_epoch)

theorem ay_upco_digest_member
    (orderedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUPCOEpochDigest orderedReplay epochMember digestMember
      epochDigestAccepted ->
    epochMember ->
    digestMember := by
  intro epoch_digest
  exact epoch_digest (epochMember -> digestMember)
    (fun _replay_to_epoch tail =>
      tail (epochMember -> digestMember)
        (fun epoch_to_digest _digest_to_accept => epoch_to_digest))

theorem ay_upco_epoch_digest_accepted
    (orderedReplay : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUPCOEpochDigest orderedReplay epochMember digestMember
      epochDigestAccepted ->
    digestMember ->
    epochDigestAccepted := by
  intro epoch_digest
  exact epoch_digest (digestMember -> epochDigestAccepted)
    (fun _replay_to_epoch tail =>
      tail (digestMember -> epochDigestAccepted)
        (fun _epoch_to_digest digest_to_accept => digest_to_accept))

theorem ay_upco_checker_transcript
    (orderedReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUPCOCheckerTranscript orderedReplay checkerTranscript checkerAccepted ->
    orderedReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (orderedReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_upco_checker_accepted
    (orderedReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUPCOCheckerTranscript orderedReplay checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> checkerAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_upco_reconstruction_handle
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPCOReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    reconstructionHandle := by
  intro reconstruction
  exact ay_upco_conj_left reconstructionHandle
    (AyUPCOConj
      (AyUPCOMap emptyClause visibleUnsat)
      (AyUPCOMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_upco_visible_unsat_from_empty
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPCOReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClause -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_upco_original_unsat_from_visible
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPCOReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original => visible_to_original))

theorem ay_upco_fingerprint_agrees
    (orderedReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUPCOFingerprint orderedReplay fingerprintAgrees visibleUnsat ->
    orderedReplay ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (orderedReplay -> fingerprintAgrees)
    (fun replay_to_fingerprint _fingerprint_to_visible =>
      replay_to_fingerprint)

theorem ay_upco_visible_unsat_from_fingerprint
    (orderedReplay : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUPCOFingerprint orderedReplay fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _replay_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_upco_accepted_evidence
    (chunkOrderMap : Prop) (dependencyOrder : Prop)
    (orderedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPCOAcceptedReplay chunkOrderMap dependencyOrder orderedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPCOAcceptedEvidence chunkOrderMap dependencyOrder orderedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat := by
  intro accepted
  exact ay_upco_conj_left
    (AyUPCOAcceptedEvidence chunkOrderMap dependencyOrder orderedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_upco_accepted_original_unsat
    (chunkOrderMap : Prop) (dependencyOrder : Prop)
    (orderedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPCOAcceptedReplay chunkOrderMap dependencyOrder orderedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_upco_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUPCOPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_upco_disj_right noClaim originalUnsat unsat

theorem ay_upco_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUPCOPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_upco_disj_left noClaim originalUnsat no_claim

theorem ay_upco_accepted_chunk_order_publish_sound
    (chunkOrderMap : Prop) (dependencyOrder : Prop)
    (orderedReplay : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (stepMapEvidence : Prop)
    (stepMapAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUPCOAcceptedReplay chunkOrderMap dependencyOrder orderedReplay
      parentCoverage emptyClause stepMapEvidence stepMapAccepted epochMember
      digestMember epochDigestAccepted checkerTranscript checkerAccepted
      reconstructionHandle fingerprintAgrees visibleUnsat originalUnsat ->
    AyUPCOPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_upco_public_unsat_report noClaim originalUnsat
    (ay_upco_accepted_original_unsat chunkOrderMap dependencyOrder
      orderedReplay parentCoverage emptyClause stepMapEvidence stepMapAccepted
      epochMember digestMember epochDigestAccepted checkerTranscript
      checkerAccepted reconstructionHandle fingerprintAgrees visibleUnsat
      originalUnsat accepted)

theorem ay_upco_bad_order_no_claim
    (chunkPermutationDrift : Prop) (missingDependencyOrder : Prop)
    (uncheckedChunkOrdering : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPCOBadOrder chunkPermutationDrift missingDependencyOrder
      uncheckedChunkOrdering parentGap stepMapMismatch epochDrift
      digestMismatch checkerRejected noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_upco_conj_left noClaim recompute fail_closed)

theorem ay_upco_bad_order_recompute
    (chunkPermutationDrift : Prop) (missingDependencyOrder : Prop)
    (uncheckedChunkOrdering : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPCOBadOrder chunkPermutationDrift missingDependencyOrder
      uncheckedChunkOrdering parentGap stepMapMismatch epochDrift
      digestMismatch checkerRejected noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_upco_bad_order_public_no_claim
    (chunkPermutationDrift : Prop) (missingDependencyOrder : Prop)
    (uncheckedChunkOrdering : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPCOBadOrder chunkPermutationDrift missingDependencyOrder
      uncheckedChunkOrdering parentGap stepMapMismatch epochDrift
      digestMismatch checkerRejected noClaim recompute ->
    AyUPCOPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_upco_public_no_claim_report noClaim originalUnsat
    (ay_upco_bad_order_no_claim chunkPermutationDrift missingDependencyOrder
      uncheckedChunkOrdering parentGap stepMapMismatch epochDrift
      digestMismatch checkerRejected noClaim recompute bad)

theorem ay_upco_bad_order_cannot_publish
    (chunkPermutationDrift : Prop) (missingDependencyOrder : Prop)
    (uncheckedChunkOrdering : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPCOBadOrder chunkPermutationDrift missingDependencyOrder
      uncheckedChunkOrdering parentGap stepMapMismatch epochDrift
      digestMismatch checkerRejected noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_upco_bad_order_no_claim chunkPermutationDrift missingDependencyOrder
      uncheckedChunkOrdering parentGap stepMapMismatch epochDrift
      digestMismatch checkerRejected noClaim recompute bad)
    unsat

theorem ay_upco_chunk_permutation_drift_forces_no_claim
    (chunkPermutationDrift : Prop) (missingDependencyOrder : Prop)
    (uncheckedChunkOrdering : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    chunkPermutationDrift ->
    AyUPCOConj noClaim recompute ->
    AyUPCOBadOrder chunkPermutationDrift missingDependencyOrder
      uncheckedChunkOrdering parentGap stepMapMismatch epochDrift
      digestMismatch checkerRejected noClaim recompute := by
  intro drift
  intro fail_closed
  exact ay_upco_conj_intro
    (AyUPCOConj noClaim recompute)
    (AyUPCODisj chunkPermutationDrift
      (AyUPCODisj missingDependencyOrder
        (AyUPCODisj uncheckedChunkOrdering
          (AyUPCODisj parentGap
            (AyUPCODisj stepMapMismatch
              (AyUPCODisj epochDrift
                (AyUPCODisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_upco_disj_left chunkPermutationDrift
      (AyUPCODisj missingDependencyOrder
        (AyUPCODisj uncheckedChunkOrdering
          (AyUPCODisj parentGap
            (AyUPCODisj stepMapMismatch
              (AyUPCODisj epochDrift
                (AyUPCODisj digestMismatch checkerRejected))))))
      drift)

theorem ay_upco_missing_dependency_order_forces_no_claim
    (chunkPermutationDrift : Prop) (missingDependencyOrder : Prop)
    (uncheckedChunkOrdering : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    missingDependencyOrder ->
    AyUPCOConj noClaim recompute ->
    AyUPCOBadOrder chunkPermutationDrift missingDependencyOrder
      uncheckedChunkOrdering parentGap stepMapMismatch epochDrift
      digestMismatch checkerRejected noClaim recompute := by
  intro missing
  intro fail_closed
  exact ay_upco_conj_intro
    (AyUPCOConj noClaim recompute)
    (AyUPCODisj chunkPermutationDrift
      (AyUPCODisj missingDependencyOrder
        (AyUPCODisj uncheckedChunkOrdering
          (AyUPCODisj parentGap
            (AyUPCODisj stepMapMismatch
              (AyUPCODisj epochDrift
                (AyUPCODisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_upco_disj_right chunkPermutationDrift
      (AyUPCODisj missingDependencyOrder
        (AyUPCODisj uncheckedChunkOrdering
          (AyUPCODisj parentGap
            (AyUPCODisj stepMapMismatch
              (AyUPCODisj epochDrift
                (AyUPCODisj digestMismatch checkerRejected))))))
      (ay_upco_disj_left missingDependencyOrder
        (AyUPCODisj uncheckedChunkOrdering
          (AyUPCODisj parentGap
            (AyUPCODisj stepMapMismatch
              (AyUPCODisj epochDrift
                (AyUPCODisj digestMismatch checkerRejected)))))
        missing))

theorem ay_upco_unchecked_chunk_ordering_forces_no_claim
    (chunkPermutationDrift : Prop) (missingDependencyOrder : Prop)
    (uncheckedChunkOrdering : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) :
    uncheckedChunkOrdering ->
    AyUPCOConj noClaim recompute ->
    AyUPCOBadOrder chunkPermutationDrift missingDependencyOrder
      uncheckedChunkOrdering parentGap stepMapMismatch epochDrift
      digestMismatch checkerRejected noClaim recompute := by
  intro unchecked
  intro fail_closed
  exact ay_upco_conj_intro
    (AyUPCOConj noClaim recompute)
    (AyUPCODisj chunkPermutationDrift
      (AyUPCODisj missingDependencyOrder
        (AyUPCODisj uncheckedChunkOrdering
          (AyUPCODisj parentGap
            (AyUPCODisj stepMapMismatch
              (AyUPCODisj epochDrift
                (AyUPCODisj digestMismatch checkerRejected)))))))
    fail_closed
    (ay_upco_disj_right chunkPermutationDrift
      (AyUPCODisj missingDependencyOrder
        (AyUPCODisj uncheckedChunkOrdering
          (AyUPCODisj parentGap
            (AyUPCODisj stepMapMismatch
              (AyUPCODisj epochDrift
                (AyUPCODisj digestMismatch checkerRejected))))))
      (ay_upco_disj_right missingDependencyOrder
        (AyUPCODisj uncheckedChunkOrdering
          (AyUPCODisj parentGap
            (AyUPCODisj stepMapMismatch
              (AyUPCODisj epochDrift
                (AyUPCODisj digestMismatch checkerRejected)))))
        (ay_upco_disj_left uncheckedChunkOrdering
          (AyUPCODisj parentGap
            (AyUPCODisj stepMapMismatch
              (AyUPCODisj epochDrift
                (AyUPCODisj digestMismatch checkerRejected))))
          unchecked)))

theorem ay_upco_unchecked_chunk_ordering_cannot_publish
    (chunkPermutationDrift : Prop) (missingDependencyOrder : Prop)
    (uncheckedChunkOrdering : Prop) (parentGap : Prop)
    (stepMapMismatch : Prop) (epochDrift : Prop)
    (digestMismatch : Prop) (checkerRejected : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPCOBadOrder chunkPermutationDrift missingDependencyOrder
      uncheckedChunkOrdering parentGap stepMapMismatch epochDrift
      digestMismatch checkerRejected noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_upco_bad_order_cannot_publish chunkPermutationDrift
    missingDependencyOrder uncheckedChunkOrdering parentGap stepMapMismatch
    epochDrift digestMismatch checkerRejected noClaim recompute originalUnsat
    bad
