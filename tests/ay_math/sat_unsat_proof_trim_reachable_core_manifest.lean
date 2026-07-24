-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded trimmed proof-core manifest soundness for ay sequential-main
-- SAT-COMP validation. Propositions stand for trim manifests, reachable-core
-- digests, clause-ID maps, parent coverage, checker transcripts, empty-clause
-- reachability, formula fingerprints, reconstruction evidence, build evidence,
-- archive manifests, and fail-closed no-claim/recompute diagnostics.

def AyPTRMConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyPTRMDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyPTRMMap (source : Prop) (target : Prop) :=
  source -> target

def AyPTRMTrimManifest
    (trimManifest : Prop) (reachableCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :=
  AyPTRMConj trimManifest
    (AyPTRMConj
      (AyPTRMMap trimManifest reachableCoreDigest)
      (AyPTRMConj
        (AyPTRMMap reachableCoreDigest archiveManifest)
        (AyPTRMMap archiveManifest checkerTranscript)))

def AyPTRMClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyPTRMConj
    (AyPTRMMap checkerTranscript clauseIdMap)
    (AyPTRMMap clauseIdMap mappedTranscript)

def AyPTRMParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyPTRMConj
    (AyPTRMMap mappedTranscript parentCoverage)
    (AyPTRMMap parentCoverage emptyClauseReachable)

def AyPTRMFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyPTRMConj
    (AyPTRMMap mappedTranscript formulaFingerprint)
    (AyPTRMMap formulaFingerprint fingerprintAccepted)

def AyPTRMBuild
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyPTRMConj
    (AyPTRMMap mappedTranscript buildEvidence)
    (AyPTRMMap buildEvidence buildAccepted)

def AyPTRMReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyPTRMConj reconstructionEvidence
    (AyPTRMConj
      (AyPTRMMap emptyClauseReachable visibleUnsat)
      (AyPTRMMap visibleUnsat originalUnsat))

def AyPTRMAcceptedEvidence
    (trimManifest : Prop) (reachableCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyPTRMConj
    (AyPTRMTrimManifest trimManifest reachableCoreDigest
      archiveManifest checkerTranscript)
    (AyPTRMConj
      (AyPTRMMap checkerTranscript checkerAccepted)
      (AyPTRMConj
        (AyPTRMClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyPTRMConj
          (AyPTRMParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyPTRMConj
            (AyPTRMFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyPTRMConj
              (AyPTRMBuild mappedTranscript buildEvidence buildAccepted)
              (AyPTRMReconstruction emptyClauseReachable
                reconstructionEvidence visibleUnsat originalUnsat))))))

def AyPTRMAcceptedPublication
    (trimManifest : Prop) (reachableCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyPTRMConj
    (AyPTRMAcceptedEvidence trimManifest reachableCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    originalUnsat

def AyPTRMFailureReason
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :=
  forall result : Prop,
    (trimFailure -> result) ->
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

def AyPTRMBadTrim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyPTRMConj
    (AyPTRMConj noClaim recompute)
    (AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure)

def AyPTRMPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyPTRMDisj noClaim originalUnsat

theorem ay_ptrm_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyPTRMConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ptrm_conj_left
    (p : Prop) (q : Prop) :
    AyPTRMConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ptrm_disj_left
    (p : Prop) (q : Prop) :
    p -> AyPTRMDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ptrm_disj_right
    (p : Prop) (q : Prop) :
    q -> AyPTRMDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ptrm_trim_manifest
    (trimManifest : Prop) (reachableCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyPTRMTrimManifest trimManifest reachableCoreDigest archiveManifest
      checkerTranscript ->
    trimManifest := by
  intro manifest
  exact ay_ptrm_conj_left trimManifest
    (AyPTRMConj
      (AyPTRMMap trimManifest reachableCoreDigest)
      (AyPTRMConj
        (AyPTRMMap reachableCoreDigest archiveManifest)
        (AyPTRMMap archiveManifest checkerTranscript)))
    manifest

theorem ay_ptrm_reachable_core_digest
    (trimManifest : Prop) (reachableCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyPTRMTrimManifest trimManifest reachableCoreDigest archiveManifest
      checkerTranscript ->
    reachableCoreDigest := by
  intro manifest
  exact manifest reachableCoreDigest
    (fun trim tail =>
      tail reachableCoreDigest
        (fun trim_to_core _rest => trim_to_core trim))

theorem ay_ptrm_archive_manifest
    (trimManifest : Prop) (reachableCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyPTRMTrimManifest trimManifest reachableCoreDigest archiveManifest
      checkerTranscript ->
    archiveManifest := by
  intro manifest
  exact manifest archiveManifest
    (fun trim tail =>
      tail archiveManifest
        (fun trim_to_core rest =>
          rest archiveManifest
            (fun core_to_archive _archive_to_transcript =>
              core_to_archive (trim_to_core trim))))

theorem ay_ptrm_checker_transcript
    (trimManifest : Prop) (reachableCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop) :
    AyPTRMTrimManifest trimManifest reachableCoreDigest archiveManifest
      checkerTranscript ->
    checkerTranscript := by
  intro manifest
  exact manifest checkerTranscript
    (fun trim tail =>
      tail checkerTranscript
        (fun trim_to_core rest =>
          rest checkerTranscript
            (fun core_to_archive archive_to_transcript =>
              archive_to_transcript (core_to_archive (trim_to_core trim)))))

theorem ay_ptrm_checker_accepted
    (checkerTranscript : Prop) (checkerAccepted : Prop) :
    AyPTRMMap checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro accepted
  exact accepted

theorem ay_ptrm_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyPTRMClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_map _map_to_mapped => transcript_to_map)

theorem ay_ptrm_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyPTRMClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_map map_to_mapped => map_to_mapped)

theorem ay_ptrm_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyPTRMParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_ptrm_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyPTRMParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_ptrm_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyPTRMFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_ptrm_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyPTRMFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_ptrm_build_evidence
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyPTRMBuild mappedTranscript buildEvidence buildAccepted ->
    mappedTranscript ->
    buildEvidence := by
  intro build
  exact build (mappedTranscript -> buildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_ptrm_build_accepted
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyPTRMBuild mappedTranscript buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_ptrm_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTRMReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_ptrm_conj_left reconstructionEvidence
    (AyPTRMConj
      (AyPTRMMap emptyClauseReachable visibleUnsat)
      (AyPTRMMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_ptrm_visible_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTRMReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_ptrm_original_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTRMReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_ptrm_accepted_evidence
    (trimManifest : Prop) (reachableCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTRMAcceptedPublication trimManifest reachableCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    AyPTRMAcceptedEvidence trimManifest reachableCoreDigest archiveManifest
      checkerTranscript checkerAccepted clauseIdMap mappedTranscript
      parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat := by
  intro accepted
  exact accepted
    (AyPTRMAcceptedEvidence trimManifest reachableCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_ptrm_publication_sound
    (trimManifest : Prop) (reachableCoreDigest : Prop)
    (archiveManifest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPTRMAcceptedPublication trimManifest reachableCoreDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted buildEvidence buildAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_ptrm_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyPTRMPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ptrm_disj_right noClaim originalUnsat unsat

theorem ay_ptrm_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyPTRMPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ptrm_disj_left noClaim originalUnsat no_claim

theorem ay_ptrm_bad_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPTRMBadTrim trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_ptrm_conj_left noClaim recompute fail_closed)

theorem ay_ptrm_bad_recompute
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPTRMBadTrim trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_ptrm_bad_public_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyPTRMBadTrim trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    AyPTRMPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ptrm_public_no_claim_report noClaim originalUnsat
    (ay_ptrm_bad_no_claim trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute bad)

theorem ay_ptrm_bad_cannot_bless_unsat
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPTRMBadTrim trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_ptrm_bad_no_claim trimFailure coreFailure mapFailure
    parentFailure checkerFailure emptyClauseFailure fingerprintFailure
    reconstructionFailure buildFailure archiveFailure noClaim recompute bad

theorem ay_ptrm_failure_forces_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure ->
    noClaim ->
    recompute ->
    AyPTRMBadTrim trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_ptrm_conj_intro (AyPTRMConj noClaim recompute)
    (AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure)
    (ay_ptrm_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_ptrm_trim_failure_forces_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    trimFailure ->
    AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro trim_to_result
  intro _core_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact trim_to_result failure

theorem ay_ptrm_core_failure_forces_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    coreFailure ->
    AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _trim_to_result
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

theorem ay_ptrm_map_failure_forces_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    mapFailure ->
    AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _trim_to_result
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

theorem ay_ptrm_parent_failure_forces_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    parentFailure ->
    AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _trim_to_result
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

theorem ay_ptrm_checker_failure_forces_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    checkerFailure ->
    AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _trim_to_result
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

theorem ay_ptrm_empty_clause_failure_forces_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    emptyClauseFailure ->
    AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _trim_to_result
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

theorem ay_ptrm_fingerprint_failure_forces_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    fingerprintFailure ->
    AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _trim_to_result
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

theorem ay_ptrm_reconstruction_failure_forces_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    reconstructionFailure ->
    AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _trim_to_result
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

theorem ay_ptrm_build_failure_forces_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    buildFailure ->
    AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _trim_to_result
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

theorem ay_ptrm_archive_failure_forces_no_claim
    (trimFailure : Prop) (coreFailure : Prop) (mapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    archiveFailure ->
    AyPTRMFailureReason trimFailure coreFailure mapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _trim_to_result
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
