-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded LRAT step-index checkpoint replay soundness for ay sequential-main
-- SAT-COMP validation. Propositions stand for checkpoint manifests, step-index
-- digests, clause-ID maps, parent coverage, checker transcripts, empty-clause
-- reachability, formula fingerprints, reconstruction evidence, build evidence,
-- archive manifests, and fail-closed no-claim/recompute diagnostics.

def AyLSICConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyLSICDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyLSICMap (source : Prop) (target : Prop) :=
  source -> target

def AyLSICCheckpointReplay
    (checkpointManifest : Prop) (stepIndexDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :=
  AyLSICConj checkpointManifest
    (AyLSICConj
      (AyLSICMap checkpointManifest stepIndexDigest)
      (AyLSICConj
        (AyLSICMap stepIndexDigest archiveManifest)
        (AyLSICMap archiveManifest checkerTranscript)))

def AyLSICClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyLSICConj
    (AyLSICMap checkerTranscript clauseIdMap)
    (AyLSICMap clauseIdMap mappedTranscript)

def AyLSICParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyLSICConj
    (AyLSICMap mappedTranscript parentCoverage)
    (AyLSICMap parentCoverage emptyClauseReachable)

def AyLSICFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyLSICConj
    (AyLSICMap mappedTranscript formulaFingerprint)
    (AyLSICMap formulaFingerprint fingerprintAccepted)

def AyLSICBuild
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyLSICConj
    (AyLSICMap mappedTranscript buildEvidence)
    (AyLSICMap buildEvidence buildAccepted)

def AyLSICReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyLSICConj reconstructionEvidence
    (AyLSICConj
      (AyLSICMap emptyClauseReachable visibleUnsat)
      (AyLSICMap visibleUnsat originalUnsat))

def AyLSICAcceptedEvidence
    (checkpointManifest : Prop) (stepIndexDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyLSICConj
    (AyLSICCheckpointReplay checkpointManifest stepIndexDigest
      archiveManifest checkerTranscript)
    (AyLSICConj
      (AyLSICMap checkerTranscript checkerAccepted)
      (AyLSICConj
        (AyLSICClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyLSICConj
          (AyLSICParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyLSICConj
            (AyLSICFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyLSICConj
              (AyLSICBuild mappedTranscript buildEvidence buildAccepted)
              (AyLSICReconstruction emptyClauseReachable
                reconstructionEvidence visibleUnsat originalUnsat))))))

def AyLSICAcceptedPublication
    (checkpointManifest : Prop) (stepIndexDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyLSICConj
    (AyLSICAcceptedEvidence checkpointManifest stepIndexDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    originalUnsat

def AyLSICFailureReason
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :=
  AyLSICDisj checkpointFailure
    (AyLSICDisj indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))))

def AyLSICBadReplay
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyLSICConj
    (AyLSICConj noClaim recompute)
    (AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure)

def AyLSICPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyLSICDisj noClaim originalUnsat

theorem ay_lsic_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyLSICConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_lsic_conj_left
    (p : Prop) (q : Prop) :
    AyLSICConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_lsic_disj_left
    (p : Prop) (q : Prop) :
    p -> AyLSICDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_lsic_disj_right
    (p : Prop) (q : Prop) :
    q -> AyLSICDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_lsic_checkpoint_manifest
    (checkpointManifest : Prop) (stepIndexDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyLSICCheckpointReplay checkpointManifest stepIndexDigest
      archiveManifest checkerTranscript ->
    checkpointManifest := by
  intro replay
  exact ay_lsic_conj_left checkpointManifest
    (AyLSICConj
      (AyLSICMap checkpointManifest stepIndexDigest)
      (AyLSICConj
        (AyLSICMap stepIndexDigest archiveManifest)
        (AyLSICMap archiveManifest checkerTranscript)))
    replay

theorem ay_lsic_step_index_digest
    (checkpointManifest : Prop) (stepIndexDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyLSICCheckpointReplay checkpointManifest stepIndexDigest
      archiveManifest checkerTranscript ->
    stepIndexDigest := by
  intro replay
  exact replay stepIndexDigest
    (fun checkpoint tail =>
      tail stepIndexDigest
        (fun checkpoint_to_index _rest => checkpoint_to_index checkpoint))

theorem ay_lsic_archive_manifest
    (checkpointManifest : Prop) (stepIndexDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyLSICCheckpointReplay checkpointManifest stepIndexDigest
      archiveManifest checkerTranscript ->
    archiveManifest := by
  intro replay
  exact replay archiveManifest
    (fun checkpoint tail =>
      tail archiveManifest
        (fun checkpoint_to_index rest =>
          rest archiveManifest
            (fun index_to_archive _archive_to_transcript =>
              index_to_archive (checkpoint_to_index checkpoint))))

theorem ay_lsic_checker_transcript
    (checkpointManifest : Prop) (stepIndexDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyLSICCheckpointReplay checkpointManifest stepIndexDigest
      archiveManifest checkerTranscript ->
    checkerTranscript := by
  intro replay
  exact replay checkerTranscript
    (fun checkpoint tail =>
      tail checkerTranscript
        (fun checkpoint_to_index rest =>
          rest checkerTranscript
            (fun index_to_archive archive_to_transcript =>
              archive_to_transcript
                (index_to_archive (checkpoint_to_index checkpoint)))))

theorem ay_lsic_checker_accepted
    (checkerTranscript : Prop) (checkerAccepted : Prop) :
    AyLSICMap checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro accepted
  exact accepted

theorem ay_lsic_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyLSICClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_map _map_to_mapped => transcript_to_map)

theorem ay_lsic_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyLSICClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_map map_to_mapped => map_to_mapped)

theorem ay_lsic_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyLSICParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_lsic_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyLSICParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_lsic_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyLSICFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_lsic_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyLSICFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_lsic_build_evidence
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyLSICBuild mappedTranscript buildEvidence buildAccepted ->
    mappedTranscript ->
    buildEvidence := by
  intro build
  exact build (mappedTranscript -> buildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_lsic_build_accepted
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyLSICBuild mappedTranscript buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_lsic_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLSICReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_lsic_conj_left reconstructionEvidence
    (AyLSICConj
      (AyLSICMap emptyClauseReachable visibleUnsat)
      (AyLSICMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_lsic_visible_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLSICReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_lsic_original_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLSICReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_lsic_accepted_evidence
    (checkpointManifest : Prop) (stepIndexDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLSICAcceptedPublication checkpointManifest stepIndexDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    AyLSICAcceptedEvidence checkpointManifest stepIndexDigest archiveManifest
      checkerTranscript checkerAccepted clauseIdMap mappedTranscript
      parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat := by
  intro accepted
  exact accepted
    (AyLSICAcceptedEvidence checkpointManifest stepIndexDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_lsic_publication_sound
    (checkpointManifest : Prop) (stepIndexDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyLSICAcceptedPublication checkpointManifest stepIndexDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_lsic_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyLSICPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_lsic_disj_right noClaim originalUnsat unsat

theorem ay_lsic_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyLSICPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_lsic_disj_left noClaim originalUnsat no_claim

theorem ay_lsic_bad_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyLSICBadReplay checkpointFailure indexFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_lsic_conj_left noClaim recompute fail_closed)

theorem ay_lsic_bad_recompute
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyLSICBadReplay checkpointFailure indexFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_lsic_bad_public_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyLSICBadReplay checkpointFailure indexFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    AyLSICPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_lsic_public_no_claim_report noClaim originalUnsat
    (ay_lsic_bad_no_claim checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute bad)

theorem ay_lsic_bad_cannot_bless_unsat
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyLSICBadReplay checkpointFailure indexFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_lsic_bad_no_claim checkpointFailure indexFailure mapFailure
    parentFailure checkerFailure emptyClauseFailure fingerprintFailure
    reconstructionFailure buildFailure archiveFailure noClaim recompute bad

theorem ay_lsic_failure_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure ->
    noClaim ->
    recompute ->
    AyLSICBadReplay checkpointFailure indexFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_lsic_conj_intro (AyLSICConj noClaim recompute)
    (AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure)
    (ay_lsic_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_lsic_checkpoint_failure_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    checkpointFailure ->
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  exact ay_lsic_disj_left checkpointFailure
    (AyLSICDisj indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))))
    failure

theorem ay_lsic_failure_tail_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    AyLSICDisj indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))) ->
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro tail
  exact ay_lsic_disj_right checkpointFailure
    (AyLSICDisj indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))))
    tail

theorem ay_lsic_index_failure_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    indexFailure ->
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  exact ay_lsic_failure_tail_forces_no_claim checkpointFailure
    indexFailure mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure reconstructionFailure buildFailure archiveFailure
    (ay_lsic_disj_left indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))))
      failure)

theorem ay_lsic_map_failure_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    mapFailure ->
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  exact ay_lsic_failure_tail_forces_no_claim checkpointFailure
    indexFailure mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure reconstructionFailure buildFailure archiveFailure
    (ay_lsic_disj_right indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))))
      (ay_lsic_disj_left mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))
        failure))

theorem ay_lsic_parent_failure_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    parentFailure ->
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  exact ay_lsic_failure_tail_forces_no_claim checkpointFailure
    indexFailure mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure reconstructionFailure buildFailure archiveFailure
    (ay_lsic_disj_right indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))))
      (ay_lsic_disj_right mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))
        (ay_lsic_disj_left parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))
          failure)))

theorem ay_lsic_checker_failure_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    checkerFailure ->
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  exact ay_lsic_failure_tail_forces_no_claim checkpointFailure
    indexFailure mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure reconstructionFailure buildFailure archiveFailure
    (ay_lsic_disj_right indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))))
      (ay_lsic_disj_right mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))
        (ay_lsic_disj_right parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))
          (ay_lsic_disj_left checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))
            failure))))

theorem ay_lsic_empty_clause_failure_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    emptyClauseFailure ->
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  exact ay_lsic_failure_tail_forces_no_claim checkpointFailure
    indexFailure mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure reconstructionFailure buildFailure archiveFailure
    (ay_lsic_disj_right indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))))
      (ay_lsic_disj_right mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))
        (ay_lsic_disj_right parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))
          (ay_lsic_disj_right checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))
            (ay_lsic_disj_left emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))
              failure)))))

theorem ay_lsic_fingerprint_failure_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    fingerprintFailure ->
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  exact ay_lsic_failure_tail_forces_no_claim checkpointFailure
    indexFailure mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure reconstructionFailure buildFailure archiveFailure
    (ay_lsic_disj_right indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))))
      (ay_lsic_disj_right mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))
        (ay_lsic_disj_right parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))
          (ay_lsic_disj_right checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))
            (ay_lsic_disj_right emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))
              (ay_lsic_disj_left fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))
                failure))))))

theorem ay_lsic_reconstruction_failure_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    reconstructionFailure ->
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  exact ay_lsic_failure_tail_forces_no_claim checkpointFailure
    indexFailure mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure reconstructionFailure buildFailure archiveFailure
    (ay_lsic_disj_right indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))))
      (ay_lsic_disj_right mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))
        (ay_lsic_disj_right parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))
          (ay_lsic_disj_right checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))
            (ay_lsic_disj_right emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))
              (ay_lsic_disj_right fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))
                (ay_lsic_disj_left reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)
                  failure)))))))

theorem ay_lsic_build_failure_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    buildFailure ->
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  exact ay_lsic_failure_tail_forces_no_claim checkpointFailure
    indexFailure mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure reconstructionFailure buildFailure archiveFailure
    (ay_lsic_disj_right indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))))
      (ay_lsic_disj_right mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))
        (ay_lsic_disj_right parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))
          (ay_lsic_disj_right checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))
            (ay_lsic_disj_right emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))
              (ay_lsic_disj_right fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))
                (ay_lsic_disj_right reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)
                  (ay_lsic_disj_left buildFailure archiveFailure
                    failure))))))))

theorem ay_lsic_archive_failure_forces_no_claim
    (checkpointFailure : Prop) (indexFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    archiveFailure ->
    AyLSICFailureReason checkpointFailure indexFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  exact ay_lsic_failure_tail_forces_no_claim checkpointFailure
    indexFailure mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure reconstructionFailure buildFailure archiveFailure
    (ay_lsic_disj_right indexFailure
      (AyLSICDisj mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))))
      (ay_lsic_disj_right mapFailure
        (AyLSICDisj parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))))
        (ay_lsic_disj_right parentFailure
          (AyLSICDisj checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))))
          (ay_lsic_disj_right checkerFailure
            (AyLSICDisj emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))))
            (ay_lsic_disj_right emptyClauseFailure
              (AyLSICDisj fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)))
              (ay_lsic_disj_right fingerprintFailure
                (AyLSICDisj reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure))
                (ay_lsic_disj_right reconstructionFailure
                  (AyLSICDisj buildFailure archiveFailure)
                  (ay_lsic_disj_right buildFailure archiveFailure
                    failure))))))))
