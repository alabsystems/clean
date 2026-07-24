-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded popped-scope UNSAT-core guard soundness for ay incremental
-- solving. Propositions stand for pop-scope manifests, live-frame/core
-- digests, clause-ID maps, parent coverage, checker transcripts, empty-clause
-- reachability, formula fingerprints, reconstruction evidence, build evidence,
-- archive manifests, and fail-closed no-claim/recompute diagnostics.

def AyUPSCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPSCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPSCMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPSCPopScopeManifest
    (popScopeManifest : Prop) (liveFrameCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :=
  AyUPSCConj popScopeManifest
    (AyUPSCConj
      (AyUPSCMap popScopeManifest liveFrameCoreDigest)
      (AyUPSCConj
        (AyUPSCMap liveFrameCoreDigest archiveManifest)
        (AyUPSCMap archiveManifest checkerTranscript)))

def AyUPSCClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyUPSCConj
    (AyUPSCMap checkerTranscript clauseIdMap)
    (AyUPSCMap clauseIdMap mappedTranscript)

def AyUPSCParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyUPSCConj
    (AyUPSCMap mappedTranscript parentCoverage)
    (AyUPSCMap parentCoverage emptyClauseReachable)

def AyUPSCFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUPSCConj
    (AyUPSCMap mappedTranscript formulaFingerprint)
    (AyUPSCMap formulaFingerprint fingerprintAccepted)

def AyUPSCBuild
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyUPSCConj
    (AyUPSCMap mappedTranscript buildEvidence)
    (AyUPSCMap buildEvidence buildAccepted)

def AyUPSCReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleLiveFrameUnsat : Prop) (originalUnsatForLiveFrame : Prop) :=
  AyUPSCConj reconstructionEvidence
    (AyUPSCConj
      (AyUPSCMap emptyClauseReachable visibleLiveFrameUnsat)
      (AyUPSCMap visibleLiveFrameUnsat originalUnsatForLiveFrame))

def AyUPSCAcceptedEvidence
    (popScopeManifest : Prop) (liveFrameCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleLiveFrameUnsat : Prop) (originalUnsatForLiveFrame : Prop) :=
  AyUPSCConj
    (AyUPSCPopScopeManifest popScopeManifest liveFrameCoreDigest
      archiveManifest checkerTranscript)
    (AyUPSCConj
      (AyUPSCMap checkerTranscript checkerAccepted)
      (AyUPSCConj
        (AyUPSCClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyUPSCConj
          (AyUPSCParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyUPSCConj
            (AyUPSCFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyUPSCConj
              (AyUPSCBuild mappedTranscript buildEvidence buildAccepted)
              (AyUPSCReconstruction emptyClauseReachable
                reconstructionEvidence visibleLiveFrameUnsat
                originalUnsatForLiveFrame))))))

def AyUPSCAcceptedPublication
    (popScopeManifest : Prop) (liveFrameCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleLiveFrameUnsat : Prop) (originalUnsatForLiveFrame : Prop) :=
  AyUPSCConj
    (AyUPSCAcceptedEvidence popScopeManifest liveFrameCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleLiveFrameUnsat originalUnsatForLiveFrame)
    originalUnsatForLiveFrame

def AyUPSCFailureReason
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :=
  forall result : Prop,
    (scopeFailure -> result) ->
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

def AyUPSCBadPopScope
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUPSCConj
    (AyUPSCConj noClaim recompute)
    (AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure)

def AyUPSCPublicReport (noClaim : Prop) (originalUnsatForLiveFrame : Prop) :=
  AyUPSCDisj noClaim originalUnsatForLiveFrame

theorem ay_upsc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPSCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_upsc_conj_left
    (p : Prop) (q : Prop) :
    AyUPSCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_upsc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPSCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_upsc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPSCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_upsc_pop_scope_manifest
    (popScopeManifest : Prop) (liveFrameCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUPSCPopScopeManifest popScopeManifest liveFrameCoreDigest
      archiveManifest checkerTranscript ->
    popScopeManifest := by
  intro manifest
  exact ay_upsc_conj_left popScopeManifest
    (AyUPSCConj
      (AyUPSCMap popScopeManifest liveFrameCoreDigest)
      (AyUPSCConj
        (AyUPSCMap liveFrameCoreDigest archiveManifest)
        (AyUPSCMap archiveManifest checkerTranscript)))
    manifest

theorem ay_upsc_live_frame_core_digest
    (popScopeManifest : Prop) (liveFrameCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUPSCPopScopeManifest popScopeManifest liveFrameCoreDigest
      archiveManifest checkerTranscript ->
    liveFrameCoreDigest := by
  intro manifest
  exact manifest liveFrameCoreDigest
    (fun scope tail =>
      tail liveFrameCoreDigest
        (fun scope_to_core _rest => scope_to_core scope))

theorem ay_upsc_archive_manifest
    (popScopeManifest : Prop) (liveFrameCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUPSCPopScopeManifest popScopeManifest liveFrameCoreDigest
      archiveManifest checkerTranscript ->
    archiveManifest := by
  intro manifest
  exact manifest archiveManifest
    (fun scope tail =>
      tail archiveManifest
        (fun scope_to_core rest =>
          rest archiveManifest
            (fun core_to_archive _archive_to_transcript =>
              core_to_archive (scope_to_core scope))))

theorem ay_upsc_checker_transcript
    (popScopeManifest : Prop) (liveFrameCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyUPSCPopScopeManifest popScopeManifest liveFrameCoreDigest
      archiveManifest checkerTranscript ->
    checkerTranscript := by
  intro manifest
  exact manifest checkerTranscript
    (fun scope tail =>
      tail checkerTranscript
        (fun scope_to_core rest =>
          rest checkerTranscript
            (fun core_to_archive archive_to_transcript =>
              archive_to_transcript (core_to_archive (scope_to_core scope)))))

theorem ay_upsc_checker_accepted
    (checkerTranscript : Prop) (checkerAccepted : Prop) :
    AyUPSCMap checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro accepted
  exact accepted

theorem ay_upsc_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUPSCClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_map _map_to_mapped => transcript_to_map)

theorem ay_upsc_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyUPSCClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_map map_to_mapped => map_to_mapped)

theorem ay_upsc_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUPSCParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_upsc_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUPSCParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_upsc_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUPSCFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_upsc_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUPSCFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_upsc_build_evidence
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUPSCBuild mappedTranscript buildEvidence buildAccepted ->
    mappedTranscript ->
    buildEvidence := by
  intro build
  exact build (mappedTranscript -> buildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_upsc_build_accepted
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUPSCBuild mappedTranscript buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_upsc_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleLiveFrameUnsat : Prop) (originalUnsatForLiveFrame : Prop) :
    AyUPSCReconstruction emptyClauseReachable reconstructionEvidence
      visibleLiveFrameUnsat originalUnsatForLiveFrame ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_upsc_conj_left reconstructionEvidence
    (AyUPSCConj
      (AyUPSCMap emptyClauseReachable visibleLiveFrameUnsat)
      (AyUPSCMap visibleLiveFrameUnsat originalUnsatForLiveFrame))
    reconstruction

theorem ay_upsc_visible_live_frame_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleLiveFrameUnsat : Prop) (originalUnsatForLiveFrame : Prop) :
    AyUPSCReconstruction emptyClauseReachable reconstructionEvidence
      visibleLiveFrameUnsat originalUnsatForLiveFrame ->
    emptyClauseReachable ->
    visibleLiveFrameUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleLiveFrameUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleLiveFrameUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_upsc_original_unsat_for_live_frame
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleLiveFrameUnsat : Prop) (originalUnsatForLiveFrame : Prop) :
    AyUPSCReconstruction emptyClauseReachable reconstructionEvidence
      visibleLiveFrameUnsat originalUnsatForLiveFrame ->
    visibleLiveFrameUnsat ->
    originalUnsatForLiveFrame := by
  intro reconstruction
  exact reconstruction (visibleLiveFrameUnsat -> originalUnsatForLiveFrame)
    (fun _handle tail =>
      tail (visibleLiveFrameUnsat -> originalUnsatForLiveFrame)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_upsc_accepted_evidence
    (popScopeManifest : Prop) (liveFrameCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleLiveFrameUnsat : Prop) (originalUnsatForLiveFrame : Prop) :
    AyUPSCAcceptedPublication popScopeManifest liveFrameCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleLiveFrameUnsat originalUnsatForLiveFrame ->
    AyUPSCAcceptedEvidence popScopeManifest liveFrameCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleLiveFrameUnsat originalUnsatForLiveFrame := by
  intro accepted
  exact accepted
    (AyUPSCAcceptedEvidence popScopeManifest liveFrameCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleLiveFrameUnsat originalUnsatForLiveFrame)
    (fun evidence _unsat => evidence)

theorem ay_upsc_publication_sound
    (popScopeManifest : Prop) (liveFrameCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleLiveFrameUnsat : Prop) (originalUnsatForLiveFrame : Prop) :
    AyUPSCAcceptedPublication popScopeManifest liveFrameCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleLiveFrameUnsat originalUnsatForLiveFrame ->
    originalUnsatForLiveFrame := by
  intro accepted
  exact accepted originalUnsatForLiveFrame (fun _evidence unsat => unsat)

theorem ay_upsc_public_unsat_report
    (noClaim : Prop) (originalUnsatForLiveFrame : Prop) :
    originalUnsatForLiveFrame ->
    AyUPSCPublicReport noClaim originalUnsatForLiveFrame := by
  intro unsat
  exact ay_upsc_disj_right noClaim originalUnsatForLiveFrame unsat

theorem ay_upsc_public_no_claim_report
    (noClaim : Prop) (originalUnsatForLiveFrame : Prop) :
    noClaim ->
    AyUPSCPublicReport noClaim originalUnsatForLiveFrame := by
  intro no_claim
  exact ay_upsc_disj_left noClaim originalUnsatForLiveFrame no_claim

theorem ay_upsc_bad_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPSCBadPopScope scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_upsc_conj_left noClaim recompute fail_closed)

theorem ay_upsc_bad_recompute
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPSCBadPopScope scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_upsc_bad_public_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsatForLiveFrame : Prop) :
    AyUPSCBadPopScope scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    AyUPSCPublicReport noClaim originalUnsatForLiveFrame := by
  intro bad
  exact ay_upsc_public_no_claim_report noClaim originalUnsatForLiveFrame
    (ay_upsc_bad_no_claim scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute bad)

theorem ay_upsc_bad_cannot_bless_unsat
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPSCBadPopScope scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_upsc_bad_no_claim scopeFailure coreFailure mapFailure
    parentFailure checkerFailure emptyClauseFailure fingerprintFailure
    reconstructionFailure buildFailure archiveFailure noClaim recompute bad

theorem ay_upsc_failure_forces_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure ->
    noClaim ->
    recompute ->
    AyUPSCBadPopScope scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_upsc_conj_intro (AyUPSCConj noClaim recompute)
    (AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure)
    (ay_upsc_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_upsc_scope_failure_forces_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    scopeFailure ->
    AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro scope_to_result
  intro _core_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact scope_to_result failure

theorem ay_upsc_core_failure_forces_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    coreFailure ->
    AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _scope_to_result
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

theorem ay_upsc_map_failure_forces_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    mapFailure ->
    AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _scope_to_result
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

theorem ay_upsc_parent_failure_forces_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    parentFailure ->
    AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _scope_to_result
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

theorem ay_upsc_checker_failure_forces_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    checkerFailure ->
    AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _scope_to_result
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

theorem ay_upsc_empty_clause_failure_forces_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    emptyClauseFailure ->
    AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _scope_to_result
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

theorem ay_upsc_fingerprint_failure_forces_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    fingerprintFailure ->
    AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _scope_to_result
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

theorem ay_upsc_reconstruction_failure_forces_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    reconstructionFailure ->
    AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _scope_to_result
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

theorem ay_upsc_build_failure_forces_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    buildFailure ->
    AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _scope_to_result
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

theorem ay_upsc_archive_failure_forces_no_claim
    (scopeFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    archiveFailure ->
    AyUPSCFailureReason scopeFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure reconstructionFailure
      buildFailure archiveFailure := by
  intro failure
  intro result
  intro _scope_to_result
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
