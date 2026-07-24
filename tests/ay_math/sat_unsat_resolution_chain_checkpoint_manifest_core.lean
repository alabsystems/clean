-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded resolution-chain checkpoint manifest soundness for ay sequential-main
-- SAT-COMP UNSAT validation. Propositions stand for checkpoint manifests,
-- clause-ID maps, parent coverage, root formula fingerprints, checker
-- transcripts, empty-clause reachability, reconstruction evidence, build
-- evidence, and fail-closed no-claim/recompute diagnostics.

def AyURCCCheckpointConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyURCCCheckpointDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyURCCCheckpointMap (source : Prop) (target : Prop) :=
  source -> target

def AyURCCCheckpointManifest
    (checkpointManifest : Prop) (clauseIdMap : Prop)
    (checkpointReplay : Prop) :=
  AyURCCCheckpointConj checkpointManifest
    (AyURCCCheckpointConj
      (AyURCCCheckpointMap checkpointManifest clauseIdMap)
      (AyURCCCheckpointMap clauseIdMap checkpointReplay))

def AyURCCCheckpointParentCoverage
    (checkpointReplay : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyURCCCheckpointConj
    (AyURCCCheckpointMap checkpointReplay parentCoverage)
    (AyURCCCheckpointMap parentCoverage emptyClauseReachable)

def AyURCCCheckpointFingerprint
    (checkpointReplay : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyURCCCheckpointConj
    (AyURCCCheckpointMap checkpointReplay rootFingerprint)
    (AyURCCCheckpointMap rootFingerprint fingerprintAccepted)

def AyURCCCheckpointTranscript
    (checkpointReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :=
  AyURCCCheckpointConj
    (AyURCCCheckpointMap checkpointReplay checkerTranscript)
    (AyURCCCheckpointMap checkerTranscript transcriptAccepted)

def AyURCCCheckpointBuild
    (checkpointReplay : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyURCCCheckpointConj
    (AyURCCCheckpointMap checkpointReplay buildEvidence)
    (AyURCCCheckpointMap buildEvidence buildAccepted)

def AyURCCCheckpointReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyURCCCheckpointConj reconstructionEvidence
    (AyURCCCheckpointConj
      (AyURCCCheckpointMap emptyClauseReachable visibleUnsat)
      (AyURCCCheckpointMap visibleUnsat originalUnsat))

def AyURCCCheckpointAcceptedEvidence
    (checkpointManifest : Prop) (clauseIdMap : Prop)
    (checkpointReplay : Prop) (parentCoverage : Prop)
    (rootFingerprint : Prop) (fingerprintAccepted : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyURCCCheckpointConj
    (AyURCCCheckpointManifest checkpointManifest clauseIdMap
      checkpointReplay)
    (AyURCCCheckpointConj
      (AyURCCCheckpointParentCoverage checkpointReplay parentCoverage
        emptyClauseReachable)
      (AyURCCCheckpointConj
        (AyURCCCheckpointFingerprint checkpointReplay rootFingerprint
          fingerprintAccepted)
        (AyURCCCheckpointConj
          (AyURCCCheckpointTranscript checkpointReplay checkerTranscript
            transcriptAccepted)
          (AyURCCCheckpointConj
            (AyURCCCheckpointBuild checkpointReplay buildEvidence
              buildAccepted)
            (AyURCCCheckpointReconstruction emptyClauseReachable
              reconstructionEvidence visibleUnsat originalUnsat)))))

def AyURCCCheckpointAcceptedReplay
    (checkpointManifest : Prop) (clauseIdMap : Prop)
    (checkpointReplay : Prop) (parentCoverage : Prop)
    (rootFingerprint : Prop) (fingerprintAccepted : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyURCCCheckpointConj
    (AyURCCCheckpointAcceptedEvidence checkpointManifest clauseIdMap
      checkpointReplay parentCoverage rootFingerprint fingerprintAccepted
      checkerTranscript transcriptAccepted emptyClauseReachable
      reconstructionEvidence buildEvidence buildAccepted visibleUnsat
      originalUnsat)
    originalUnsat

def AyURCCCheckpointBadReplay
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyURCCCheckpointConj
    (AyURCCCheckpointConj noClaim recompute)
    (AyURCCCheckpointDisj checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability
                buildDrift))))))

def AyURCCCheckpointPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyURCCCheckpointDisj noClaim originalUnsat

theorem ay_urcc_checkpoint_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyURCCCheckpointConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_urcc_checkpoint_conj_left
    (p : Prop) (q : Prop) :
    AyURCCCheckpointConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_urcc_checkpoint_disj_left
    (p : Prop) (q : Prop) :
    p -> AyURCCCheckpointDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_urcc_checkpoint_disj_right
    (p : Prop) (q : Prop) :
    q -> AyURCCCheckpointDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_urcc_checkpoint_manifest
    (checkpointManifest : Prop) (clauseIdMap : Prop)
    (checkpointReplay : Prop) :
    AyURCCCheckpointManifest checkpointManifest clauseIdMap
      checkpointReplay ->
    checkpointManifest := by
  intro manifest
  exact ay_urcc_checkpoint_conj_left checkpointManifest
    (AyURCCCheckpointConj
      (AyURCCCheckpointMap checkpointManifest clauseIdMap)
      (AyURCCCheckpointMap clauseIdMap checkpointReplay))
    manifest

theorem ay_urcc_checkpoint_clause_id_map
    (checkpointManifest : Prop) (clauseIdMap : Prop)
    (checkpointReplay : Prop) :
    AyURCCCheckpointManifest checkpointManifest clauseIdMap
      checkpointReplay ->
    clauseIdMap := by
  intro manifest
  exact manifest clauseIdMap
    (fun checkpoint tail =>
      tail clauseIdMap
        (fun checkpoint_to_id_map _id_map_to_replay =>
          checkpoint_to_id_map checkpoint))

theorem ay_urcc_checkpoint_replay
    (checkpointManifest : Prop) (clauseIdMap : Prop)
    (checkpointReplay : Prop) :
    AyURCCCheckpointManifest checkpointManifest clauseIdMap
      checkpointReplay ->
    checkpointReplay := by
  intro manifest
  exact manifest checkpointReplay
    (fun checkpoint tail =>
      tail checkpointReplay
        (fun checkpoint_to_id_map id_map_to_replay =>
          id_map_to_replay (checkpoint_to_id_map checkpoint)))

theorem ay_urcc_checkpoint_parent_coverage
    (checkpointReplay : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyURCCCheckpointParentCoverage checkpointReplay parentCoverage
      emptyClauseReachable ->
    checkpointReplay ->
    parentCoverage := by
  intro parents
  exact parents (checkpointReplay -> parentCoverage)
    (fun replay_to_parent _parent_to_empty => replay_to_parent)

theorem ay_urcc_checkpoint_empty_clause_reachable
    (checkpointReplay : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyURCCCheckpointParentCoverage checkpointReplay parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _replay_to_parent parent_to_empty => parent_to_empty)

theorem ay_urcc_checkpoint_root_fingerprint
    (checkpointReplay : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyURCCCheckpointFingerprint checkpointReplay rootFingerprint
      fingerprintAccepted ->
    checkpointReplay ->
    rootFingerprint := by
  intro fingerprint
  exact fingerprint (checkpointReplay -> rootFingerprint)
    (fun replay_to_fingerprint _fingerprint_to_accept =>
      replay_to_fingerprint)

theorem ay_urcc_checkpoint_fingerprint_accepted
    (checkpointReplay : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyURCCCheckpointFingerprint checkpointReplay rootFingerprint
      fingerprintAccepted ->
    rootFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (rootFingerprint -> fingerprintAccepted)
    (fun _replay_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_urcc_checkpoint_checker_transcript
    (checkpointReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyURCCCheckpointTranscript checkpointReplay checkerTranscript
      transcriptAccepted ->
    checkpointReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (checkpointReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_urcc_checkpoint_transcript_accepted
    (checkpointReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyURCCCheckpointTranscript checkpointReplay checkerTranscript
      transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> transcriptAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_urcc_checkpoint_build_evidence
    (checkpointReplay : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyURCCCheckpointBuild checkpointReplay buildEvidence buildAccepted ->
    checkpointReplay ->
    buildEvidence := by
  intro build
  exact build (checkpointReplay -> buildEvidence)
    (fun replay_to_build _build_to_accept => replay_to_build)

theorem ay_urcc_checkpoint_build_accepted
    (checkpointReplay : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyURCCCheckpointBuild checkpointReplay buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _replay_to_build build_to_accept => build_to_accept)

theorem ay_urcc_checkpoint_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCCCheckpointReconstruction emptyClauseReachable
      reconstructionEvidence visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_urcc_checkpoint_conj_left reconstructionEvidence
    (AyURCCCheckpointConj
      (AyURCCCheckpointMap emptyClauseReachable visibleUnsat)
      (AyURCCCheckpointMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_urcc_checkpoint_visible_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCCCheckpointReconstruction emptyClauseReachable
      reconstructionEvidence visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_urcc_checkpoint_original_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCCCheckpointReconstruction emptyClauseReachable
      reconstructionEvidence visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_urcc_checkpoint_accepted_evidence
    (checkpointManifest : Prop) (clauseIdMap : Prop)
    (checkpointReplay : Prop) (parentCoverage : Prop)
    (rootFingerprint : Prop) (fingerprintAccepted : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCCCheckpointAcceptedReplay checkpointManifest clauseIdMap
      checkpointReplay parentCoverage rootFingerprint fingerprintAccepted
      checkerTranscript transcriptAccepted emptyClauseReachable
      reconstructionEvidence buildEvidence buildAccepted visibleUnsat
      originalUnsat ->
    AyURCCCheckpointAcceptedEvidence checkpointManifest clauseIdMap
      checkpointReplay parentCoverage rootFingerprint fingerprintAccepted
      checkerTranscript transcriptAccepted emptyClauseReachable
      reconstructionEvidence buildEvidence buildAccepted visibleUnsat
      originalUnsat := by
  intro accepted
  exact accepted
    (AyURCCCheckpointAcceptedEvidence checkpointManifest clauseIdMap
      checkpointReplay parentCoverage rootFingerprint fingerprintAccepted
      checkerTranscript transcriptAccepted emptyClauseReachable
      reconstructionEvidence buildEvidence buildAccepted visibleUnsat
      originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_urcc_checkpoint_publish_sound
    (checkpointManifest : Prop) (clauseIdMap : Prop)
    (checkpointReplay : Prop) (parentCoverage : Prop)
    (rootFingerprint : Prop) (fingerprintAccepted : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyURCCCheckpointAcceptedReplay checkpointManifest clauseIdMap
      checkpointReplay parentCoverage rootFingerprint fingerprintAccepted
      checkerTranscript transcriptAccepted emptyClauseReachable
      reconstructionEvidence buildEvidence buildAccepted visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_urcc_checkpoint_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyURCCCheckpointPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_urcc_checkpoint_disj_right noClaim originalUnsat unsat

theorem ay_urcc_checkpoint_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyURCCCheckpointPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_urcc_checkpoint_disj_left noClaim originalUnsat no_claim

theorem ay_urcc_checkpoint_bad_no_claim
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyURCCCheckpointBadReplay checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_urcc_checkpoint_conj_left noClaim recompute fail_closed)

theorem ay_urcc_checkpoint_bad_recompute
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyURCCCheckpointBadReplay checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_urcc_checkpoint_bad_public_no_claim
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyURCCCheckpointBadReplay checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute ->
    AyURCCCheckpointPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_urcc_checkpoint_public_no_claim_report noClaim originalUnsat
    (ay_urcc_checkpoint_bad_no_claim checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute bad)

theorem ay_urcc_checkpoint_bad_cannot_bless_unsat
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    AyURCCCheckpointBadReplay checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_urcc_checkpoint_bad_no_claim checkpointDrift idMapMismatch
    missingParentCoverage staleFingerprint uncheckedTranscript
    missingEmptyReachability buildDrift noClaim recompute bad

theorem ay_urcc_checkpoint_drift_forces_no_claim
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    checkpointDrift ->
    noClaim ->
    recompute ->
    AyURCCCheckpointBadReplay checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute := by
  intro drift
  intro no_claim
  intro recheck
  exact ay_urcc_checkpoint_conj_intro
    (AyURCCCheckpointConj noClaim recompute)
    (AyURCCCheckpointDisj checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))))
    (ay_urcc_checkpoint_conj_intro noClaim recompute no_claim recheck)
    (ay_urcc_checkpoint_disj_left checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))))
      drift)

theorem ay_urcc_id_map_mismatch_forces_no_claim
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    idMapMismatch ->
    noClaim ->
    recompute ->
    AyURCCCheckpointBadReplay checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute := by
  intro mismatch
  intro no_claim
  intro recheck
  exact ay_urcc_checkpoint_conj_intro
    (AyURCCCheckpointConj noClaim recompute)
    (AyURCCCheckpointDisj checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))))
    (ay_urcc_checkpoint_conj_intro noClaim recompute no_claim recheck)
    (ay_urcc_checkpoint_disj_right checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))))
      (ay_urcc_checkpoint_disj_left idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))
        mismatch))

theorem ay_urcc_missing_parent_coverage_forces_no_claim
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    missingParentCoverage ->
    noClaim ->
    recompute ->
    AyURCCCheckpointBadReplay checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute := by
  intro missing
  intro no_claim
  intro recheck
  exact ay_urcc_checkpoint_conj_intro
    (AyURCCCheckpointConj noClaim recompute)
    (AyURCCCheckpointDisj checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))))
    (ay_urcc_checkpoint_conj_intro noClaim recompute no_claim recheck)
    (ay_urcc_checkpoint_disj_right checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))))
      (ay_urcc_checkpoint_disj_right idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))
        (ay_urcc_checkpoint_disj_left missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))
          missing)))

theorem ay_urcc_stale_fingerprint_forces_no_claim
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    staleFingerprint ->
    noClaim ->
    recompute ->
    AyURCCCheckpointBadReplay checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute := by
  intro stale
  intro no_claim
  intro recheck
  exact ay_urcc_checkpoint_conj_intro
    (AyURCCCheckpointConj noClaim recompute)
    (AyURCCCheckpointDisj checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))))
    (ay_urcc_checkpoint_conj_intro noClaim recompute no_claim recheck)
    (ay_urcc_checkpoint_disj_right checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))))
      (ay_urcc_checkpoint_disj_right idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))
        (ay_urcc_checkpoint_disj_right missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))
          (ay_urcc_checkpoint_disj_left staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))
            stale))))

theorem ay_urcc_unchecked_transcript_forces_no_claim
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    uncheckedTranscript ->
    noClaim ->
    recompute ->
    AyURCCCheckpointBadReplay checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute := by
  intro unchecked
  intro no_claim
  intro recheck
  exact ay_urcc_checkpoint_conj_intro
    (AyURCCCheckpointConj noClaim recompute)
    (AyURCCCheckpointDisj checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))))
    (ay_urcc_checkpoint_conj_intro noClaim recompute no_claim recheck)
    (ay_urcc_checkpoint_disj_right checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))))
      (ay_urcc_checkpoint_disj_right idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))
        (ay_urcc_checkpoint_disj_right missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))
          (ay_urcc_checkpoint_disj_right staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))
            (ay_urcc_checkpoint_disj_left uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)
              unchecked)))))

theorem ay_urcc_missing_empty_reachability_forces_no_claim
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    missingEmptyReachability ->
    noClaim ->
    recompute ->
    AyURCCCheckpointBadReplay checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute := by
  intro missing
  intro no_claim
  intro recheck
  exact ay_urcc_checkpoint_conj_intro
    (AyURCCCheckpointConj noClaim recompute)
    (AyURCCCheckpointDisj checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))))
    (ay_urcc_checkpoint_conj_intro noClaim recompute no_claim recheck)
    (ay_urcc_checkpoint_disj_right checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))))
      (ay_urcc_checkpoint_disj_right idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))
        (ay_urcc_checkpoint_disj_right missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))
          (ay_urcc_checkpoint_disj_right staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))
            (ay_urcc_checkpoint_disj_right uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)
              (ay_urcc_checkpoint_disj_left missingEmptyReachability
                buildDrift missing))))))

theorem ay_urcc_build_drift_forces_no_claim
    (checkpointDrift : Prop) (idMapMismatch : Prop)
    (missingParentCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (noClaim : Prop) (recompute : Prop) :
    buildDrift ->
    noClaim ->
    recompute ->
    AyURCCCheckpointBadReplay checkpointDrift idMapMismatch
      missingParentCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift noClaim recompute := by
  intro drift
  intro no_claim
  intro recheck
  exact ay_urcc_checkpoint_conj_intro
    (AyURCCCheckpointConj noClaim recompute)
    (AyURCCCheckpointDisj checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))))
    (ay_urcc_checkpoint_conj_intro noClaim recompute no_claim recheck)
    (ay_urcc_checkpoint_disj_right checkpointDrift
      (AyURCCCheckpointDisj idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))))
      (ay_urcc_checkpoint_disj_right idMapMismatch
        (AyURCCCheckpointDisj missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))))
        (ay_urcc_checkpoint_disj_right missingParentCoverage
          (AyURCCCheckpointDisj staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)))
          (ay_urcc_checkpoint_disj_right staleFingerprint
            (AyURCCCheckpointDisj uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift))
            (ay_urcc_checkpoint_disj_right uncheckedTranscript
              (AyURCCCheckpointDisj missingEmptyReachability buildDrift)
              (ay_urcc_checkpoint_disj_right missingEmptyReachability
                buildDrift drift))))))
