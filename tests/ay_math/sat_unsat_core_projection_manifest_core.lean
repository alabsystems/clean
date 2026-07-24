-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT-core projection manifest soundness for ay sequential-main
-- SAT-COMP validation. Propositions stand for projection manifests,
-- clause-ID maps, original-clause parent coverage, formula fingerprints,
-- checker transcripts, empty-clause reachability, reconstruction evidence,
-- build evidence, and fail-closed no-claim/recompute diagnostics.

def AyUCPMConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCPMDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCPMMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCPMProjectionManifest
    (projectionManifest : Prop) (clauseIdMap : Prop)
    (projectedCore : Prop) :=
  AyUCPMConj projectionManifest
    (AyUCPMConj
      (AyUCPMMap projectionManifest clauseIdMap)
      (AyUCPMMap clauseIdMap projectedCore))

def AyUCPMParentCoverage
    (projectedCore : Prop) (originalClauseCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyUCPMConj
    (AyUCPMMap projectedCore originalClauseCoverage)
    (AyUCPMMap originalClauseCoverage emptyClauseReachable)

def AyUCPMFingerprint
    (projectedCore : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUCPMConj
    (AyUCPMMap projectedCore rootFingerprint)
    (AyUCPMMap rootFingerprint fingerprintAccepted)

def AyUCPMTranscript
    (projectedCore : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :=
  AyUCPMConj
    (AyUCPMMap projectedCore checkerTranscript)
    (AyUCPMMap checkerTranscript transcriptAccepted)

def AyUCPMBuild
    (projectedCore : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyUCPMConj
    (AyUCPMMap projectedCore buildEvidence)
    (AyUCPMMap buildEvidence buildAccepted)

def AyUCPMReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCPMConj reconstructionEvidence
    (AyUCPMConj
      (AyUCPMMap emptyClauseReachable visibleUnsat)
      (AyUCPMMap visibleUnsat originalUnsat))

def AyUCPMAcceptedEvidence
    (projectionManifest : Prop) (clauseIdMap : Prop)
    (projectedCore : Prop) (originalClauseCoverage : Prop)
    (rootFingerprint : Prop) (fingerprintAccepted : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCPMConj
    (AyUCPMProjectionManifest projectionManifest clauseIdMap projectedCore)
    (AyUCPMConj
      (AyUCPMParentCoverage projectedCore originalClauseCoverage
        emptyClauseReachable)
      (AyUCPMConj
        (AyUCPMFingerprint projectedCore rootFingerprint fingerprintAccepted)
        (AyUCPMConj
          (AyUCPMTranscript projectedCore checkerTranscript
            transcriptAccepted)
          (AyUCPMConj
            (AyUCPMBuild projectedCore buildEvidence buildAccepted)
            (AyUCPMReconstruction emptyClauseReachable
              reconstructionEvidence visibleUnsat originalUnsat)))))

def AyUCPMAcceptedProjection
    (projectionManifest : Prop) (clauseIdMap : Prop)
    (projectedCore : Prop) (originalClauseCoverage : Prop)
    (rootFingerprint : Prop) (fingerprintAccepted : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCPMConj
    (AyUCPMAcceptedEvidence projectionManifest clauseIdMap projectedCore
      originalClauseCoverage rootFingerprint fingerprintAccepted
      checkerTranscript transcriptAccepted emptyClauseReachable
      reconstructionEvidence buildEvidence buildAccepted visibleUnsat
      originalUnsat)
    originalUnsat

def AyUCPMFailureReason
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop) :=
  AyUCPMDisj projectionDrift
    (AyUCPMDisj idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))))

def AyUCPMBadProjection
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUCPMConj
    (AyUCPMConj noClaim recompute)
    (AyUCPMFailureReason projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap)

def AyUCPMPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCPMDisj noClaim originalUnsat

theorem ay_ucpm_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCPMConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucpm_conj_left
    (p : Prop) (q : Prop) :
    AyUCPMConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucpm_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCPMDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucpm_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCPMDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucpm_projection_manifest
    (projectionManifest : Prop) (clauseIdMap : Prop)
    (projectedCore : Prop) :
    AyUCPMProjectionManifest projectionManifest clauseIdMap projectedCore ->
    projectionManifest := by
  intro manifest
  exact ay_ucpm_conj_left projectionManifest
    (AyUCPMConj
      (AyUCPMMap projectionManifest clauseIdMap)
      (AyUCPMMap clauseIdMap projectedCore))
    manifest

theorem ay_ucpm_clause_id_map
    (projectionManifest : Prop) (clauseIdMap : Prop)
    (projectedCore : Prop) :
    AyUCPMProjectionManifest projectionManifest clauseIdMap projectedCore ->
    clauseIdMap := by
  intro manifest
  exact manifest clauseIdMap
    (fun projection tail =>
      tail clauseIdMap
        (fun projection_to_id_map _id_map_to_core =>
          projection_to_id_map projection))

theorem ay_ucpm_projected_core
    (projectionManifest : Prop) (clauseIdMap : Prop)
    (projectedCore : Prop) :
    AyUCPMProjectionManifest projectionManifest clauseIdMap projectedCore ->
    projectedCore := by
  intro manifest
  exact manifest projectedCore
    (fun projection tail =>
      tail projectedCore
        (fun projection_to_id_map id_map_to_core =>
          id_map_to_core (projection_to_id_map projection)))

theorem ay_ucpm_original_clause_coverage
    (projectedCore : Prop) (originalClauseCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUCPMParentCoverage projectedCore originalClauseCoverage
      emptyClauseReachable ->
    projectedCore ->
    originalClauseCoverage := by
  intro parents
  exact parents (projectedCore -> originalClauseCoverage)
    (fun core_to_coverage _coverage_to_empty => core_to_coverage)

theorem ay_ucpm_empty_clause_reachable
    (projectedCore : Prop) (originalClauseCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUCPMParentCoverage projectedCore originalClauseCoverage
      emptyClauseReachable ->
    originalClauseCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (originalClauseCoverage -> emptyClauseReachable)
    (fun _core_to_coverage coverage_to_empty => coverage_to_empty)

theorem ay_ucpm_root_fingerprint
    (projectedCore : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCPMFingerprint projectedCore rootFingerprint fingerprintAccepted ->
    projectedCore ->
    rootFingerprint := by
  intro fingerprint
  exact fingerprint (projectedCore -> rootFingerprint)
    (fun core_to_fingerprint _fingerprint_to_accept =>
      core_to_fingerprint)

theorem ay_ucpm_fingerprint_accepted
    (projectedCore : Prop) (rootFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCPMFingerprint projectedCore rootFingerprint fingerprintAccepted ->
    rootFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (rootFingerprint -> fingerprintAccepted)
    (fun _core_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_ucpm_checker_transcript
    (projectedCore : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUCPMTranscript projectedCore checkerTranscript transcriptAccepted ->
    projectedCore ->
    checkerTranscript := by
  intro transcript
  exact transcript (projectedCore -> checkerTranscript)
    (fun core_to_transcript _transcript_to_accept => core_to_transcript)

theorem ay_ucpm_transcript_accepted
    (projectedCore : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUCPMTranscript projectedCore checkerTranscript transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> transcriptAccepted)
    (fun _core_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_ucpm_build_evidence
    (projectedCore : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUCPMBuild projectedCore buildEvidence buildAccepted ->
    projectedCore ->
    buildEvidence := by
  intro build
  exact build (projectedCore -> buildEvidence)
    (fun core_to_build _build_to_accept => core_to_build)

theorem ay_ucpm_build_accepted
    (projectedCore : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUCPMBuild projectedCore buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _core_to_build build_to_accept => build_to_accept)

theorem ay_ucpm_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCPMReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_ucpm_conj_left reconstructionEvidence
    (AyUCPMConj
      (AyUCPMMap emptyClauseReachable visibleUnsat)
      (AyUCPMMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_ucpm_visible_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCPMReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_ucpm_original_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCPMReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_ucpm_accepted_evidence
    (projectionManifest : Prop) (clauseIdMap : Prop)
    (projectedCore : Prop) (originalClauseCoverage : Prop)
    (rootFingerprint : Prop) (fingerprintAccepted : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCPMAcceptedProjection projectionManifest clauseIdMap projectedCore
      originalClauseCoverage rootFingerprint fingerprintAccepted
      checkerTranscript transcriptAccepted emptyClauseReachable
      reconstructionEvidence buildEvidence buildAccepted visibleUnsat
      originalUnsat ->
    AyUCPMAcceptedEvidence projectionManifest clauseIdMap projectedCore
      originalClauseCoverage rootFingerprint fingerprintAccepted
      checkerTranscript transcriptAccepted emptyClauseReachable
      reconstructionEvidence buildEvidence buildAccepted visibleUnsat
      originalUnsat := by
  intro accepted
  exact accepted
    (AyUCPMAcceptedEvidence projectionManifest clauseIdMap projectedCore
      originalClauseCoverage rootFingerprint fingerprintAccepted
      checkerTranscript transcriptAccepted emptyClauseReachable
      reconstructionEvidence buildEvidence buildAccepted visibleUnsat
      originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_ucpm_projection_publish_sound
    (projectionManifest : Prop) (clauseIdMap : Prop)
    (projectedCore : Prop) (originalClauseCoverage : Prop)
    (rootFingerprint : Prop) (fingerprintAccepted : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCPMAcceptedProjection projectionManifest clauseIdMap projectedCore
      originalClauseCoverage rootFingerprint fingerprintAccepted
      checkerTranscript transcriptAccepted emptyClauseReachable
      reconstructionEvidence buildEvidence buildAccepted visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_ucpm_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUCPMPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucpm_disj_right noClaim originalUnsat unsat

theorem ay_ucpm_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUCPMPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucpm_disj_left noClaim originalUnsat no_claim

theorem ay_ucpm_bad_no_claim
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCPMBadProjection projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_ucpm_conj_left noClaim recompute fail_closed)

theorem ay_ucpm_bad_recompute
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCPMBadProjection projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_ucpm_bad_public_no_claim
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUCPMBadProjection projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap noClaim
      recompute ->
    AyUCPMPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucpm_public_no_claim_report noClaim originalUnsat
    (ay_ucpm_bad_no_claim projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap noClaim
      recompute bad)

theorem ay_ucpm_bad_cannot_bless_unsat
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCPMBadProjection projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap noClaim
      recompute ->
    noClaim := by
  intro bad
  exact ay_ucpm_bad_no_claim projectionDrift idMapMismatch
    missingOriginalCoverage staleFingerprint uncheckedTranscript
    missingEmptyReachability buildDrift reconstructionGap noClaim
    recompute bad

theorem ay_ucpm_failure_forces_no_claim
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCPMFailureReason projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap ->
    noClaim ->
    recompute ->
    AyUCPMBadProjection projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap noClaim
      recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_ucpm_conj_intro (AyUCPMConj noClaim recompute)
    (AyUCPMFailureReason projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap)
    (ay_ucpm_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_ucpm_projection_drift_forces_no_claim
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop) :
    projectionDrift ->
    AyUCPMFailureReason projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap := by
  intro drift
  exact ay_ucpm_disj_left projectionDrift
    (AyUCPMDisj idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))))
    drift

theorem ay_ucpm_id_map_mismatch_forces_no_claim
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop) :
    idMapMismatch ->
    AyUCPMFailureReason projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap := by
  intro mismatch
  exact ay_ucpm_disj_right projectionDrift
    (AyUCPMDisj idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))))
    (ay_ucpm_disj_left idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))))
      mismatch)

theorem ay_ucpm_missing_original_coverage_forces_no_claim
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop) :
    missingOriginalCoverage ->
    AyUCPMFailureReason projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap := by
  intro missing
  exact ay_ucpm_disj_right projectionDrift
    (AyUCPMDisj idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))))
    (ay_ucpm_disj_right idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))))
      (ay_ucpm_disj_left missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))
        missing))

theorem ay_ucpm_stale_fingerprint_forces_no_claim
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop) :
    staleFingerprint ->
    AyUCPMFailureReason projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap := by
  intro stale
  exact ay_ucpm_disj_right projectionDrift
    (AyUCPMDisj idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))))
    (ay_ucpm_disj_right idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))))
      (ay_ucpm_disj_right missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))
        (ay_ucpm_disj_left staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))
          stale)))

theorem ay_ucpm_unchecked_transcript_forces_no_claim
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop) :
    uncheckedTranscript ->
    AyUCPMFailureReason projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap := by
  intro unchecked
  exact ay_ucpm_disj_right projectionDrift
    (AyUCPMDisj idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))))
    (ay_ucpm_disj_right idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))))
      (ay_ucpm_disj_right missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))
        (ay_ucpm_disj_right staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))
          (ay_ucpm_disj_left uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))
            unchecked))))

theorem ay_ucpm_missing_empty_reachability_forces_no_claim
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop) :
    missingEmptyReachability ->
    AyUCPMFailureReason projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap := by
  intro missing
  exact ay_ucpm_disj_right projectionDrift
    (AyUCPMDisj idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))))
    (ay_ucpm_disj_right idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))))
      (ay_ucpm_disj_right missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))
        (ay_ucpm_disj_right staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))
          (ay_ucpm_disj_right uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))
            (ay_ucpm_disj_left missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)
              missing)))))

theorem ay_ucpm_build_drift_forces_no_claim
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop) :
    buildDrift ->
    AyUCPMFailureReason projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap := by
  intro drift
  exact ay_ucpm_disj_right projectionDrift
    (AyUCPMDisj idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))))
    (ay_ucpm_disj_right idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))))
      (ay_ucpm_disj_right missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))
        (ay_ucpm_disj_right staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))
          (ay_ucpm_disj_right uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))
            (ay_ucpm_disj_right missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)
              (ay_ucpm_disj_left buildDrift reconstructionGap drift))))))

theorem ay_ucpm_reconstruction_gap_forces_no_claim
    (projectionDrift : Prop) (idMapMismatch : Prop)
    (missingOriginalCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (missingEmptyReachability : Prop)
    (buildDrift : Prop) (reconstructionGap : Prop) :
    reconstructionGap ->
    AyUCPMFailureReason projectionDrift idMapMismatch
      missingOriginalCoverage staleFingerprint uncheckedTranscript
      missingEmptyReachability buildDrift reconstructionGap := by
  intro gap
  exact ay_ucpm_disj_right projectionDrift
    (AyUCPMDisj idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))))
    (ay_ucpm_disj_right idMapMismatch
      (AyUCPMDisj missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))))
      (ay_ucpm_disj_right missingOriginalCoverage
        (AyUCPMDisj staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))))
        (ay_ucpm_disj_right staleFingerprint
          (AyUCPMDisj uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)))
          (ay_ucpm_disj_right uncheckedTranscript
            (AyUCPMDisj missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap))
            (ay_ucpm_disj_right missingEmptyReachability
              (AyUCPMDisj buildDrift reconstructionGap)
              (ay_ucpm_disj_right buildDrift reconstructionGap gap))))))
