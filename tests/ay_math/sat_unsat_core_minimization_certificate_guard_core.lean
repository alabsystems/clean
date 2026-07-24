-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded minimized UNSAT-core certificate guard soundness for ay
-- sequential-main SAT-COMP validation. Propositions stand for core
-- minimization manifests, kept/deleted clause coverage, clause-ID maps,
-- parent coverage, checker transcripts, empty-clause reachability, formula
-- fingerprints, reconstruction evidence, build evidence, archive manifests,
-- and fail-closed no-claim/recompute diagnostics.

def AyUCMCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCMCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCMCMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCMCMinimizationManifest
    (coreMinimizationManifest : Prop) (keptDeletedCoverage : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :=
  AyUCMCConj coreMinimizationManifest
    (AyUCMCConj
      (AyUCMCMap coreMinimizationManifest keptDeletedCoverage)
      (AyUCMCConj
        (AyUCMCMap keptDeletedCoverage archiveManifest)
        (AyUCMCMap archiveManifest checkerTranscript)))

def AyUCMCClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyUCMCConj
    (AyUCMCMap checkerTranscript clauseIdMap)
    (AyUCMCMap clauseIdMap mappedTranscript)

def AyUCMCParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyUCMCConj
    (AyUCMCMap mappedTranscript parentCoverage)
    (AyUCMCMap parentCoverage emptyClauseReachable)

def AyUCMCFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUCMCConj
    (AyUCMCMap mappedTranscript formulaFingerprint)
    (AyUCMCMap formulaFingerprint fingerprintAccepted)

def AyUCMCBuild
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyUCMCConj
    (AyUCMCMap mappedTranscript buildEvidence)
    (AyUCMCMap buildEvidence buildAccepted)

def AyUCMCReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCMCConj reconstructionEvidence
    (AyUCMCConj
      (AyUCMCMap emptyClauseReachable visibleUnsat)
      (AyUCMCMap visibleUnsat originalUnsat))

def AyUCMCAcceptedEvidence
    (coreMinimizationManifest : Prop) (keptDeletedCoverage : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCMCConj
    (AyUCMCMinimizationManifest coreMinimizationManifest
      keptDeletedCoverage archiveManifest checkerTranscript)
    (AyUCMCConj
      (AyUCMCMap checkerTranscript checkerAccepted)
      (AyUCMCConj
        (AyUCMCClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyUCMCConj
          (AyUCMCParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyUCMCConj
            (AyUCMCFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyUCMCConj
              (AyUCMCBuild mappedTranscript buildEvidence buildAccepted)
              (AyUCMCReconstruction emptyClauseReachable
                reconstructionEvidence visibleUnsat originalUnsat))))))

def AyUCMCAcceptedPublication
    (coreMinimizationManifest : Prop) (keptDeletedCoverage : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCMCConj
    (AyUCMCAcceptedEvidence coreMinimizationManifest keptDeletedCoverage
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    originalUnsat

def AyUCMCFailureReason
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :=
  forall result : Prop,
    (manifestFailure -> result) ->
    (coverageFailure -> result) ->
    (mapFailure -> result) ->
    (parentFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (fingerprintFailure -> result) ->
    (reconstructionFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    result

def AyUCMCBadCertificate
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUCMCConj
    (AyUCMCConj noClaim recompute)
    (AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure)

def AyUCMCPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCMCDisj noClaim originalUnsat

theorem ay_ucmc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCMCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucmc_conj_left
    (p : Prop) (q : Prop) :
    AyUCMCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucmc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCMCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucmc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCMCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucmc_core_minimization_manifest
    (coreMinimizationManifest : Prop) (keptDeletedCoverage : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUCMCMinimizationManifest coreMinimizationManifest
      keptDeletedCoverage archiveManifest checkerTranscript ->
    coreMinimizationManifest := by
  intro manifest
  exact ay_ucmc_conj_left coreMinimizationManifest
    (AyUCMCConj
      (AyUCMCMap coreMinimizationManifest keptDeletedCoverage)
      (AyUCMCConj
        (AyUCMCMap keptDeletedCoverage archiveManifest)
        (AyUCMCMap archiveManifest checkerTranscript)))
    manifest

theorem ay_ucmc_kept_deleted_coverage
    (coreMinimizationManifest : Prop) (keptDeletedCoverage : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUCMCMinimizationManifest coreMinimizationManifest
      keptDeletedCoverage archiveManifest checkerTranscript ->
    keptDeletedCoverage := by
  intro manifest
  exact manifest keptDeletedCoverage
    (fun core_manifest tail =>
      tail keptDeletedCoverage
        (fun manifest_to_coverage _rest =>
          manifest_to_coverage core_manifest))

theorem ay_ucmc_archive_manifest
    (coreMinimizationManifest : Prop) (keptDeletedCoverage : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUCMCMinimizationManifest coreMinimizationManifest
      keptDeletedCoverage archiveManifest checkerTranscript ->
    archiveManifest := by
  intro manifest
  exact manifest archiveManifest
    (fun core_manifest tail =>
      tail archiveManifest
        (fun manifest_to_coverage rest =>
          rest archiveManifest
            (fun coverage_to_archive _archive_to_transcript =>
              coverage_to_archive (manifest_to_coverage core_manifest))))

theorem ay_ucmc_checker_transcript
    (coreMinimizationManifest : Prop) (keptDeletedCoverage : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUCMCMinimizationManifest coreMinimizationManifest
      keptDeletedCoverage archiveManifest checkerTranscript ->
    checkerTranscript := by
  intro manifest
  exact manifest checkerTranscript
    (fun core_manifest tail =>
      tail checkerTranscript
        (fun manifest_to_coverage rest =>
          rest checkerTranscript
            (fun coverage_to_archive archive_to_transcript =>
              archive_to_transcript
                (coverage_to_archive
                  (manifest_to_coverage core_manifest)))))

theorem ay_ucmc_checker_accepted
    (checkerTranscript : Prop) (checkerAccepted : Prop) :
    AyUCMCMap checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro accepted
  exact accepted

theorem ay_ucmc_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUCMCClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_map _map_to_mapped => transcript_to_map)

theorem ay_ucmc_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUCMCClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_map map_to_mapped => map_to_mapped)

theorem ay_ucmc_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUCMCParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_ucmc_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUCMCParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_ucmc_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCMCFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_ucmc_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCMCFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_ucmc_build_evidence
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUCMCBuild mappedTranscript buildEvidence buildAccepted ->
    mappedTranscript ->
    buildEvidence := by
  intro build
  exact build (mappedTranscript -> buildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_ucmc_build_accepted
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUCMCBuild mappedTranscript buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_ucmc_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMCReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_ucmc_conj_left reconstructionEvidence
    (AyUCMCConj
      (AyUCMCMap emptyClauseReachable visibleUnsat)
      (AyUCMCMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_ucmc_visible_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMCReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_ucmc_original_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMCReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_ucmc_accepted_evidence
    (coreMinimizationManifest : Prop) (keptDeletedCoverage : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMCAcceptedPublication coreMinimizationManifest
      keptDeletedCoverage archiveManifest checkerTranscript checkerAccepted
      clauseIdMap mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    AyUCMCAcceptedEvidence coreMinimizationManifest keptDeletedCoverage
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat := by
  intro accepted
  exact accepted
    (AyUCMCAcceptedEvidence coreMinimizationManifest keptDeletedCoverage
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_ucmc_publication_sound
    (coreMinimizationManifest : Prop) (keptDeletedCoverage : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCMCAcceptedPublication coreMinimizationManifest
      keptDeletedCoverage archiveManifest checkerTranscript checkerAccepted
      clauseIdMap mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_ucmc_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUCMCPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucmc_disj_right noClaim originalUnsat unsat

theorem ay_ucmc_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUCMCPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucmc_disj_left noClaim originalUnsat no_claim

theorem ay_ucmc_bad_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCMCBadCertificate manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_ucmc_conj_left noClaim recompute fail_closed)

theorem ay_ucmc_bad_recompute
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCMCBadCertificate manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_ucmc_bad_public_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUCMCBadCertificate manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    AyUCMCPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucmc_public_no_claim_report noClaim originalUnsat
    (ay_ucmc_bad_no_claim manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute bad)

theorem ay_ucmc_bad_cannot_bless_unsat
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCMCBadCertificate manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_ucmc_bad_no_claim manifestFailure coverageFailure mapFailure
    parentFailure checkerFailure emptyClauseFailure fingerprintFailure
    reconstructionFailure buildFailure archiveFailure noClaim recompute bad

theorem ay_ucmc_failure_forces_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure ->
    noClaim ->
    recompute ->
    AyUCMCBadCertificate manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_ucmc_conj_intro (AyUCMCConj noClaim recompute)
    (AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure)
    (ay_ucmc_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_ucmc_manifest_failure_forces_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    manifestFailure ->
    AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro manifest_to_result
  intro _coverage_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact manifest_to_result failure

theorem ay_ucmc_coverage_failure_forces_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    coverageFailure ->
    AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro coverage_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact coverage_to_result failure

theorem ay_ucmc_map_failure_forces_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    mapFailure ->
    AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _coverage_to_result
  intro map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact map_to_result failure

theorem ay_ucmc_parent_failure_forces_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    parentFailure ->
    AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _coverage_to_result
  intro _map_to_result
  intro parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact parent_to_result failure

theorem ay_ucmc_checker_failure_forces_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    checkerFailure ->
    AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _coverage_to_result
  intro _map_to_result
  intro _parent_to_result
  intro checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact checker_to_result failure

theorem ay_ucmc_empty_clause_failure_forces_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    emptyClauseFailure ->
    AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _coverage_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact empty_to_result failure

theorem ay_ucmc_fingerprint_failure_forces_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    fingerprintFailure ->
    AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _coverage_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact fingerprint_to_result failure

theorem ay_ucmc_reconstruction_failure_forces_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    reconstructionFailure ->
    AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _coverage_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact reconstruction_to_result failure

theorem ay_ucmc_build_failure_forces_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    buildFailure ->
    AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _coverage_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro build_to_result
  intro _archive_to_result
  exact build_to_result failure

theorem ay_ucmc_archive_failure_forces_no_claim
    (manifestFailure : Prop) (coverageFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    archiveFailure ->
    AyUCMCFailureReason manifestFailure coverageFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _coverage_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro archive_to_result
  exact archive_to_result failure
