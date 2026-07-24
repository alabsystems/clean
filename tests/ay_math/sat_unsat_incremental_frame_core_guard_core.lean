-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded incremental frame-local UNSAT-core guard soundness for ay
-- sequential-main SAT-COMP validation. Propositions stand for frame manifests,
-- assumption/core digests, clause-ID maps, parent coverage, checker
-- transcripts, empty-clause reachability, formula fingerprints,
-- reconstruction evidence, build evidence, archive manifests, and fail-closed
-- no-claim/recompute diagnostics.

def AyUIFCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUIFCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUIFCMap (source : Prop) (target : Prop) :=
  source -> target

def AyUIFCFrameManifest
    (frameManifest : Prop) (assumptionCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :=
  AyUIFCConj frameManifest
    (AyUIFCConj
      (AyUIFCMap frameManifest assumptionCoreDigest)
      (AyUIFCConj
        (AyUIFCMap assumptionCoreDigest archiveManifest)
        (AyUIFCMap archiveManifest checkerTranscript)))

def AyUIFCClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyUIFCConj
    (AyUIFCMap checkerTranscript clauseIdMap)
    (AyUIFCMap clauseIdMap mappedTranscript)

def AyUIFCParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyUIFCConj
    (AyUIFCMap mappedTranscript parentCoverage)
    (AyUIFCMap parentCoverage emptyClauseReachable)

def AyUIFCFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUIFCConj
    (AyUIFCMap mappedTranscript formulaFingerprint)
    (AyUIFCMap formulaFingerprint fingerprintAccepted)

def AyUIFCBuild
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyUIFCConj
    (AyUIFCMap mappedTranscript buildEvidence)
    (AyUIFCMap buildEvidence buildAccepted)

def AyUIFCReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleFrameUnsat : Prop) (originalUnsatForFrame : Prop) :=
  AyUIFCConj reconstructionEvidence
    (AyUIFCConj
      (AyUIFCMap emptyClauseReachable visibleFrameUnsat)
      (AyUIFCMap visibleFrameUnsat originalUnsatForFrame))

def AyUIFCAcceptedEvidence
    (frameManifest : Prop) (assumptionCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleFrameUnsat : Prop) (originalUnsatForFrame : Prop) :=
  AyUIFCConj
    (AyUIFCFrameManifest frameManifest assumptionCoreDigest
      archiveManifest checkerTranscript)
    (AyUIFCConj
      (AyUIFCMap checkerTranscript checkerAccepted)
      (AyUIFCConj
        (AyUIFCClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyUIFCConj
          (AyUIFCParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyUIFCConj
            (AyUIFCFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyUIFCConj
              (AyUIFCBuild mappedTranscript buildEvidence buildAccepted)
              (AyUIFCReconstruction emptyClauseReachable
                reconstructionEvidence visibleFrameUnsat
                originalUnsatForFrame))))))

def AyUIFCAcceptedPublication
    (frameManifest : Prop) (assumptionCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleFrameUnsat : Prop) (originalUnsatForFrame : Prop) :=
  AyUIFCConj
    (AyUIFCAcceptedEvidence frameManifest assumptionCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleFrameUnsat originalUnsatForFrame)
    originalUnsatForFrame

def AyUIFCFailureReason
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :=
  forall result : Prop,
    (frameFailure -> result) ->
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

def AyUIFCBadFrame
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUIFCConj
    (AyUIFCConj noClaim recompute)
    (AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure)

def AyUIFCPublicReport (noClaim : Prop) (originalUnsatForFrame : Prop) :=
  AyUIFCDisj noClaim originalUnsatForFrame

theorem ay_uifc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUIFCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uifc_conj_left
    (p : Prop) (q : Prop) :
    AyUIFCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uifc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUIFCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uifc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUIFCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uifc_frame_manifest
    (frameManifest : Prop) (assumptionCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUIFCFrameManifest frameManifest assumptionCoreDigest
      archiveManifest checkerTranscript ->
    frameManifest := by
  intro manifest
  exact ay_uifc_conj_left frameManifest
    (AyUIFCConj
      (AyUIFCMap frameManifest assumptionCoreDigest)
      (AyUIFCConj
        (AyUIFCMap assumptionCoreDigest archiveManifest)
        (AyUIFCMap archiveManifest checkerTranscript)))
    manifest

theorem ay_uifc_assumption_core_digest
    (frameManifest : Prop) (assumptionCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUIFCFrameManifest frameManifest assumptionCoreDigest
      archiveManifest checkerTranscript ->
    assumptionCoreDigest := by
  intro manifest
  exact manifest assumptionCoreDigest
    (fun frame tail =>
      tail assumptionCoreDigest
        (fun frame_to_core _rest => frame_to_core frame))

theorem ay_uifc_archive_manifest
    (frameManifest : Prop) (assumptionCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUIFCFrameManifest frameManifest assumptionCoreDigest
      archiveManifest checkerTranscript ->
    archiveManifest := by
  intro manifest
  exact manifest archiveManifest
    (fun frame tail =>
      tail archiveManifest
        (fun frame_to_core rest =>
          rest archiveManifest
            (fun core_to_archive _archive_to_transcript =>
              core_to_archive (frame_to_core frame))))

theorem ay_uifc_checker_transcript
    (frameManifest : Prop) (assumptionCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUIFCFrameManifest frameManifest assumptionCoreDigest
      archiveManifest checkerTranscript ->
    checkerTranscript := by
  intro manifest
  exact manifest checkerTranscript
    (fun frame tail =>
      tail checkerTranscript
        (fun frame_to_core rest =>
          rest checkerTranscript
            (fun core_to_archive archive_to_transcript =>
              archive_to_transcript (core_to_archive (frame_to_core frame)))))

theorem ay_uifc_checker_accepted
    (checkerTranscript : Prop) (checkerAccepted : Prop) :
    AyUIFCMap checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro accepted
  exact accepted

theorem ay_uifc_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUIFCClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_map _map_to_mapped => transcript_to_map)

theorem ay_uifc_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUIFCClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_map map_to_mapped => map_to_mapped)

theorem ay_uifc_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUIFCParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_uifc_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUIFCParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_uifc_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUIFCFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_uifc_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUIFCFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_uifc_build_evidence
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUIFCBuild mappedTranscript buildEvidence buildAccepted ->
    mappedTranscript ->
    buildEvidence := by
  intro build
  exact build (mappedTranscript -> buildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_uifc_build_accepted
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUIFCBuild mappedTranscript buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_uifc_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleFrameUnsat : Prop) (originalUnsatForFrame : Prop) :
    AyUIFCReconstruction emptyClauseReachable reconstructionEvidence
      visibleFrameUnsat originalUnsatForFrame ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_uifc_conj_left reconstructionEvidence
    (AyUIFCConj
      (AyUIFCMap emptyClauseReachable visibleFrameUnsat)
      (AyUIFCMap visibleFrameUnsat originalUnsatForFrame))
    reconstruction

theorem ay_uifc_visible_frame_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleFrameUnsat : Prop) (originalUnsatForFrame : Prop) :
    AyUIFCReconstruction emptyClauseReachable reconstructionEvidence
      visibleFrameUnsat originalUnsatForFrame ->
    emptyClauseReachable ->
    visibleFrameUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleFrameUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleFrameUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_uifc_original_unsat_for_frame
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleFrameUnsat : Prop) (originalUnsatForFrame : Prop) :
    AyUIFCReconstruction emptyClauseReachable reconstructionEvidence
      visibleFrameUnsat originalUnsatForFrame ->
    visibleFrameUnsat ->
    originalUnsatForFrame := by
  intro reconstruction
  exact reconstruction (visibleFrameUnsat -> originalUnsatForFrame)
    (fun _handle tail =>
      tail (visibleFrameUnsat -> originalUnsatForFrame)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_uifc_accepted_evidence
    (frameManifest : Prop) (assumptionCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleFrameUnsat : Prop) (originalUnsatForFrame : Prop) :
    AyUIFCAcceptedPublication frameManifest assumptionCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleFrameUnsat originalUnsatForFrame ->
    AyUIFCAcceptedEvidence frameManifest assumptionCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleFrameUnsat originalUnsatForFrame := by
  intro accepted
  exact accepted
    (AyUIFCAcceptedEvidence frameManifest assumptionCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleFrameUnsat originalUnsatForFrame)
    (fun evidence _unsat => evidence)

theorem ay_uifc_publication_sound
    (frameManifest : Prop) (assumptionCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleFrameUnsat : Prop) (originalUnsatForFrame : Prop) :
    AyUIFCAcceptedPublication frameManifest assumptionCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleFrameUnsat originalUnsatForFrame ->
    originalUnsatForFrame := by
  intro accepted
  exact accepted originalUnsatForFrame (fun _evidence unsat => unsat)

theorem ay_uifc_public_unsat_report
    (noClaim : Prop) (originalUnsatForFrame : Prop) :
    originalUnsatForFrame ->
    AyUIFCPublicReport noClaim originalUnsatForFrame := by
  intro unsat
  exact ay_uifc_disj_right noClaim originalUnsatForFrame unsat

theorem ay_uifc_public_no_claim_report
    (noClaim : Prop) (originalUnsatForFrame : Prop) :
    noClaim ->
    AyUIFCPublicReport noClaim originalUnsatForFrame := by
  intro no_claim
  exact ay_uifc_disj_left noClaim originalUnsatForFrame no_claim

theorem ay_uifc_bad_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIFCBadFrame frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_uifc_conj_left noClaim recompute fail_closed)

theorem ay_uifc_bad_recompute
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIFCBadFrame frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_uifc_bad_public_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsatForFrame : Prop) :
    AyUIFCBadFrame frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure noClaim recompute ->
    AyUIFCPublicReport noClaim originalUnsatForFrame := by
  intro bad
  exact ay_uifc_public_no_claim_report noClaim originalUnsatForFrame
    (ay_uifc_bad_no_claim frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute bad)

theorem ay_uifc_bad_cannot_bless_unsat
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIFCBadFrame frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_uifc_bad_no_claim frameFailure coreFailure mapFailure
    parentFailure checkerFailure emptyClauseFailure fingerprintFailure
    reconstructionFailure buildFailure archiveFailure noClaim recompute bad

theorem ay_uifc_failure_forces_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure ->
    noClaim ->
    recompute ->
    AyUIFCBadFrame frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_uifc_conj_intro (AyUIFCConj noClaim recompute)
    (AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure)
    (ay_uifc_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_uifc_frame_failure_forces_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    frameFailure ->
    AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro frame_to_result
  intro _core_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact frame_to_result failure

theorem ay_uifc_core_failure_forces_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    coreFailure ->
    AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _frame_to_result
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

theorem ay_uifc_map_failure_forces_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    mapFailure ->
    AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _frame_to_result
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

theorem ay_uifc_parent_failure_forces_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    parentFailure ->
    AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _frame_to_result
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

theorem ay_uifc_checker_failure_forces_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    checkerFailure ->
    AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _frame_to_result
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

theorem ay_uifc_empty_clause_failure_forces_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    emptyClauseFailure ->
    AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _frame_to_result
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

theorem ay_uifc_fingerprint_failure_forces_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    fingerprintFailure ->
    AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _frame_to_result
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

theorem ay_uifc_reconstruction_failure_forces_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    reconstructionFailure ->
    AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _frame_to_result
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

theorem ay_uifc_build_failure_forces_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    buildFailure ->
    AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _frame_to_result
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

theorem ay_uifc_archive_failure_forces_no_claim
    (frameFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    archiveFailure ->
    AyUIFCFailureReason frameFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _frame_to_result
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
