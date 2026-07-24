-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded assumption-core projection guard soundness for ay sequential-main
-- SAT-COMP validation. Propositions stand for assumption manifests, projected
-- core digests, clause-ID maps, parent coverage, checker transcripts,
-- empty-clause reachability, formula fingerprints, reconstruction evidence,
-- build evidence, archive manifests, and fail-closed no-claim/recompute
-- diagnostics.

def AyUACPConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUACPDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUACPMap (source : Prop) (target : Prop) :=
  source -> target

def AyUACPAssumptionManifest
    (assumptionManifest : Prop) (projectedCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :=
  AyUACPConj assumptionManifest
    (AyUACPConj
      (AyUACPMap assumptionManifest projectedCoreDigest)
      (AyUACPConj
        (AyUACPMap projectedCoreDigest archiveManifest)
        (AyUACPMap archiveManifest checkerTranscript)))

def AyUACPClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyUACPConj
    (AyUACPMap checkerTranscript clauseIdMap)
    (AyUACPMap clauseIdMap mappedTranscript)

def AyUACPParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyUACPConj
    (AyUACPMap mappedTranscript parentCoverage)
    (AyUACPMap parentCoverage emptyClauseReachable)

def AyUACPFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUACPConj
    (AyUACPMap mappedTranscript formulaFingerprint)
    (AyUACPMap formulaFingerprint fingerprintAccepted)

def AyUACPBuild
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyUACPConj
    (AyUACPMap mappedTranscript buildEvidence)
    (AyUACPMap buildEvidence buildAccepted)

def AyUACPReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleAssumptionUnsat : Prop) (originalUnsatUnderAssumptions : Prop) :=
  AyUACPConj reconstructionEvidence
    (AyUACPConj
      (AyUACPMap emptyClauseReachable visibleAssumptionUnsat)
      (AyUACPMap visibleAssumptionUnsat originalUnsatUnderAssumptions))

def AyUACPAcceptedEvidence
    (assumptionManifest : Prop) (projectedCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleAssumptionUnsat : Prop)
    (originalUnsatUnderAssumptions : Prop) :=
  AyUACPConj
    (AyUACPAssumptionManifest assumptionManifest projectedCoreDigest
      archiveManifest checkerTranscript)
    (AyUACPConj
      (AyUACPMap checkerTranscript checkerAccepted)
      (AyUACPConj
        (AyUACPClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyUACPConj
          (AyUACPParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyUACPConj
            (AyUACPFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyUACPConj
              (AyUACPBuild mappedTranscript buildEvidence buildAccepted)
              (AyUACPReconstruction emptyClauseReachable
                reconstructionEvidence visibleAssumptionUnsat
                originalUnsatUnderAssumptions))))))

def AyUACPAcceptedPublication
    (assumptionManifest : Prop) (projectedCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleAssumptionUnsat : Prop)
    (originalUnsatUnderAssumptions : Prop) :=
  AyUACPConj
    (AyUACPAcceptedEvidence assumptionManifest projectedCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleAssumptionUnsat originalUnsatUnderAssumptions)
    originalUnsatUnderAssumptions

def AyUACPFailureReason
    (assumptionFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :=
  forall result : Prop,
    (assumptionFailure -> result) ->
    (coreFailure -> result) ->
    (mapFailure -> result) ->
    (parentFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (fingerprintFailure -> result) ->
    (reconstructionFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    result

def AyUACPBadProjection
    (assumptionFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUACPConj
    (AyUACPConj noClaim recompute)
    (AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure)

def AyUACPPublicReport
    (noClaim : Prop) (originalUnsatUnderAssumptions : Prop) :=
  AyUACPDisj noClaim originalUnsatUnderAssumptions

theorem ay_uacp_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUACPConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uacp_conj_left
    (p : Prop) (q : Prop) :
    AyUACPConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uacp_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUACPDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uacp_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUACPDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uacp_assumption_manifest
    (assumptionManifest : Prop) (projectedCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUACPAssumptionManifest assumptionManifest projectedCoreDigest
      archiveManifest checkerTranscript ->
    assumptionManifest := by
  intro manifest
  exact ay_uacp_conj_left assumptionManifest
    (AyUACPConj
      (AyUACPMap assumptionManifest projectedCoreDigest)
      (AyUACPConj
        (AyUACPMap projectedCoreDigest archiveManifest)
        (AyUACPMap archiveManifest checkerTranscript)))
    manifest

theorem ay_uacp_projected_core_digest
    (assumptionManifest : Prop) (projectedCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUACPAssumptionManifest assumptionManifest projectedCoreDigest
      archiveManifest checkerTranscript ->
    projectedCoreDigest := by
  intro manifest
  exact manifest projectedCoreDigest
    (fun assumption tail =>
      tail projectedCoreDigest
        (fun assumption_to_core _rest => assumption_to_core assumption))

theorem ay_uacp_archive_manifest
    (assumptionManifest : Prop) (projectedCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUACPAssumptionManifest assumptionManifest projectedCoreDigest
      archiveManifest checkerTranscript ->
    archiveManifest := by
  intro manifest
  exact manifest archiveManifest
    (fun assumption tail =>
      tail archiveManifest
        (fun assumption_to_core rest =>
          rest archiveManifest
            (fun core_to_archive _archive_to_transcript =>
              core_to_archive (assumption_to_core assumption))))

theorem ay_uacp_checker_transcript
    (assumptionManifest : Prop) (projectedCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUACPAssumptionManifest assumptionManifest projectedCoreDigest
      archiveManifest checkerTranscript ->
    checkerTranscript := by
  intro manifest
  exact manifest checkerTranscript
    (fun assumption tail =>
      tail checkerTranscript
        (fun assumption_to_core rest =>
          rest checkerTranscript
            (fun core_to_archive archive_to_transcript =>
              archive_to_transcript
                (core_to_archive (assumption_to_core assumption)))))

theorem ay_uacp_checker_accepted
    (checkerTranscript : Prop) (checkerAccepted : Prop) :
    AyUACPMap checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro accepted
  exact accepted

theorem ay_uacp_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUACPClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_map _map_to_mapped => transcript_to_map)

theorem ay_uacp_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUACPClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_map map_to_mapped => map_to_mapped)

theorem ay_uacp_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUACPParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_uacp_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUACPParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_uacp_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUACPFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_uacp_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUACPFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_uacp_build_evidence
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUACPBuild mappedTranscript buildEvidence buildAccepted ->
    mappedTranscript ->
    buildEvidence := by
  intro build
  exact build (mappedTranscript -> buildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_uacp_build_accepted
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUACPBuild mappedTranscript buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_uacp_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleAssumptionUnsat : Prop)
    (originalUnsatUnderAssumptions : Prop) :
    AyUACPReconstruction emptyClauseReachable reconstructionEvidence
      visibleAssumptionUnsat originalUnsatUnderAssumptions ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_uacp_conj_left reconstructionEvidence
    (AyUACPConj
      (AyUACPMap emptyClauseReachable visibleAssumptionUnsat)
      (AyUACPMap visibleAssumptionUnsat originalUnsatUnderAssumptions))
    reconstruction

theorem ay_uacp_visible_assumption_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleAssumptionUnsat : Prop)
    (originalUnsatUnderAssumptions : Prop) :
    AyUACPReconstruction emptyClauseReachable reconstructionEvidence
      visibleAssumptionUnsat originalUnsatUnderAssumptions ->
    emptyClauseReachable ->
    visibleAssumptionUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleAssumptionUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleAssumptionUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_uacp_original_unsat_under_assumptions
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleAssumptionUnsat : Prop)
    (originalUnsatUnderAssumptions : Prop) :
    AyUACPReconstruction emptyClauseReachable reconstructionEvidence
      visibleAssumptionUnsat originalUnsatUnderAssumptions ->
    visibleAssumptionUnsat ->
    originalUnsatUnderAssumptions := by
  intro reconstruction
  exact reconstruction (visibleAssumptionUnsat -> originalUnsatUnderAssumptions)
    (fun _handle tail =>
      tail (visibleAssumptionUnsat -> originalUnsatUnderAssumptions)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_uacp_accepted_evidence
    (assumptionManifest : Prop) (projectedCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleAssumptionUnsat : Prop)
    (originalUnsatUnderAssumptions : Prop) :
    AyUACPAcceptedPublication assumptionManifest projectedCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleAssumptionUnsat originalUnsatUnderAssumptions ->
    AyUACPAcceptedEvidence assumptionManifest projectedCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleAssumptionUnsat originalUnsatUnderAssumptions := by
  intro accepted
  exact accepted
    (AyUACPAcceptedEvidence assumptionManifest projectedCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleAssumptionUnsat originalUnsatUnderAssumptions)
    (fun evidence _unsat => evidence)

theorem ay_uacp_publication_sound
    (assumptionManifest : Prop) (projectedCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleAssumptionUnsat : Prop)
    (originalUnsatUnderAssumptions : Prop) :
    AyUACPAcceptedPublication assumptionManifest projectedCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleAssumptionUnsat originalUnsatUnderAssumptions ->
    originalUnsatUnderAssumptions := by
  intro accepted
  exact accepted originalUnsatUnderAssumptions
    (fun _evidence unsat => unsat)

theorem ay_uacp_public_unsat_report
    (noClaim : Prop) (originalUnsatUnderAssumptions : Prop) :
    originalUnsatUnderAssumptions ->
    AyUACPPublicReport noClaim originalUnsatUnderAssumptions := by
  intro unsat
  exact ay_uacp_disj_right noClaim originalUnsatUnderAssumptions unsat

theorem ay_uacp_public_no_claim_report
    (noClaim : Prop) (originalUnsatUnderAssumptions : Prop) :
    noClaim ->
    AyUACPPublicReport noClaim originalUnsatUnderAssumptions := by
  intro no_claim
  exact ay_uacp_disj_left noClaim originalUnsatUnderAssumptions no_claim

theorem ay_uacp_bad_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUACPBadProjection assumptionFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_uacp_conj_left noClaim recompute fail_closed)

theorem ay_uacp_bad_recompute
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUACPBadProjection assumptionFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_uacp_bad_public_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsatUnderAssumptions : Prop) :
    AyUACPBadProjection assumptionFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure noClaim recompute ->
    AyUACPPublicReport noClaim originalUnsatUnderAssumptions := by
  intro bad
  exact ay_uacp_public_no_claim_report noClaim
    originalUnsatUnderAssumptions
    (ay_uacp_bad_no_claim assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute bad)

theorem ay_uacp_bad_cannot_bless_unsat
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUACPBadProjection assumptionFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_uacp_bad_no_claim assumptionFailure coreFailure mapFailure
    parentFailure checkerFailure emptyClauseFailure fingerprintFailure
    reconstructionFailure buildFailure archiveFailure noClaim recompute bad

theorem ay_uacp_failure_forces_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure ->
    noClaim ->
    recompute ->
    AyUACPBadProjection assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_uacp_conj_intro (AyUACPConj noClaim recompute)
    (AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure)
    (ay_uacp_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_uacp_assumption_failure_forces_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    assumptionFailure ->
    AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro assumption_to_result
  intro _core_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact assumption_to_result failure

theorem ay_uacp_core_failure_forces_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    coreFailure ->
    AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _assumption_to_result
  intro core_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact core_to_result failure

theorem ay_uacp_map_failure_forces_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    mapFailure ->
    AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _assumption_to_result
  intro _core_to_result
  intro map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact map_to_result failure

theorem ay_uacp_parent_failure_forces_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    parentFailure ->
    AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _assumption_to_result
  intro _core_to_result
  intro _map_to_result
  intro parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact parent_to_result failure

theorem ay_uacp_checker_failure_forces_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    checkerFailure ->
    AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _assumption_to_result
  intro _core_to_result
  intro _map_to_result
  intro _parent_to_result
  intro checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact checker_to_result failure

theorem ay_uacp_empty_clause_failure_forces_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    emptyClauseFailure ->
    AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _assumption_to_result
  intro _core_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact empty_to_result failure

theorem ay_uacp_fingerprint_failure_forces_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    fingerprintFailure ->
    AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _assumption_to_result
  intro _core_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact fingerprint_to_result failure

theorem ay_uacp_reconstruction_failure_forces_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    reconstructionFailure ->
    AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _assumption_to_result
  intro _core_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact reconstruction_to_result failure

theorem ay_uacp_build_failure_forces_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    buildFailure ->
    AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _assumption_to_result
  intro _core_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro build_to_result
  intro _archive_to_result
  exact build_to_result failure

theorem ay_uacp_archive_failure_forces_no_claim
    (assumptionFailure : Prop) (coreFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    archiveFailure ->
    AyUACPFailureReason assumptionFailure coreFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _assumption_to_result
  intro _core_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro archive_to_result
  exact archive_to_result failure
