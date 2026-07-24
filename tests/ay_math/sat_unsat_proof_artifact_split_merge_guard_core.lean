-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded split/merged proof-artifact guard soundness for ay sequential-main
-- SAT-COMP validation. Propositions stand for split manifests, merge
-- manifests, segment digests, clause-ID maps, parent coverage, checker
-- transcripts, empty-clause reachability, formula fingerprints,
-- reconstruction evidence, build evidence, archive manifests, and fail-closed
-- no-claim/recompute diagnostics.

def AyPASMConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyPASMDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyPASMMap (source : Prop) (target : Prop) :=
  source -> target

def AyPASMSplitMergeManifest
    (splitManifest : Prop) (mergeManifest : Prop)
    (segmentDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :=
  AyPASMConj splitManifest
    (AyPASMConj
      (AyPASMMap splitManifest mergeManifest)
      (AyPASMConj
        (AyPASMMap mergeManifest segmentDigest)
        (AyPASMConj
          (AyPASMMap segmentDigest archiveManifest)
          (AyPASMMap archiveManifest checkerTranscript))))

def AyPASMClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyPASMConj
    (AyPASMMap checkerTranscript clauseIdMap)
    (AyPASMMap clauseIdMap mappedTranscript)

def AyPASMParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyPASMConj
    (AyPASMMap mappedTranscript parentCoverage)
    (AyPASMMap parentCoverage emptyClauseReachable)

def AyPASMFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyPASMConj
    (AyPASMMap mappedTranscript formulaFingerprint)
    (AyPASMMap formulaFingerprint fingerprintAccepted)

def AyPASMBuild
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyPASMConj
    (AyPASMMap mappedTranscript buildEvidence)
    (AyPASMMap buildEvidence buildAccepted)

def AyPASMReconstruction
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyPASMConj reconstructionEvidence
    (AyPASMConj
      (AyPASMMap emptyClauseReachable visibleUnsat)
      (AyPASMMap visibleUnsat originalUnsat))

def AyPASMAcceptedEvidence
    (splitManifest : Prop) (mergeManifest : Prop)
    (segmentDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyPASMConj
    (AyPASMSplitMergeManifest splitManifest mergeManifest segmentDigest
      archiveManifest checkerTranscript)
    (AyPASMConj
      (AyPASMMap checkerTranscript checkerAccepted)
      (AyPASMConj
        (AyPASMClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyPASMConj
          (AyPASMParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyPASMConj
            (AyPASMFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyPASMConj
              (AyPASMBuild mappedTranscript buildEvidence buildAccepted)
              (AyPASMReconstruction emptyClauseReachable
                reconstructionEvidence visibleUnsat originalUnsat))))))

def AyPASMAcceptedPublication
    (splitManifest : Prop) (mergeManifest : Prop)
    (segmentDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyPASMConj
    (AyPASMAcceptedEvidence splitManifest mergeManifest segmentDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    originalUnsat

def AyPASMFailureReason
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :=
  forall result : Prop,
    (splitFailure -> result) ->
    (mergeFailure -> result) ->
    (segmentFailure -> result) ->
    (mapFailure -> result) ->
    (parentFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (fingerprintFailure -> result) ->
    (reconstructionFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    result

def AyPASMBadSplitMerge
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyPASMConj
    (AyPASMConj noClaim recompute)
    (AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure)

def AyPASMPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyPASMDisj noClaim originalUnsat

theorem ay_pasm_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyPASMConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_pasm_conj_left
    (p : Prop) (q : Prop) :
    AyPASMConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_pasm_disj_left
    (p : Prop) (q : Prop) :
    p -> AyPASMDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_pasm_disj_right
    (p : Prop) (q : Prop) :
    q -> AyPASMDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_pasm_split_manifest
    (splitManifest : Prop) (mergeManifest : Prop)
    (segmentDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyPASMSplitMergeManifest splitManifest mergeManifest segmentDigest
      archiveManifest checkerTranscript ->
    splitManifest := by
  intro manifest
  exact ay_pasm_conj_left splitManifest
    (AyPASMConj
      (AyPASMMap splitManifest mergeManifest)
      (AyPASMConj
        (AyPASMMap mergeManifest segmentDigest)
        (AyPASMConj
          (AyPASMMap segmentDigest archiveManifest)
          (AyPASMMap archiveManifest checkerTranscript))))
    manifest

theorem ay_pasm_merge_manifest
    (splitManifest : Prop) (mergeManifest : Prop)
    (segmentDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyPASMSplitMergeManifest splitManifest mergeManifest segmentDigest
      archiveManifest checkerTranscript ->
    mergeManifest := by
  intro manifest
  exact manifest mergeManifest
    (fun split tail =>
      tail mergeManifest
        (fun split_to_merge _rest => split_to_merge split))

theorem ay_pasm_segment_digest
    (splitManifest : Prop) (mergeManifest : Prop)
    (segmentDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyPASMSplitMergeManifest splitManifest mergeManifest segmentDigest
      archiveManifest checkerTranscript ->
    segmentDigest := by
  intro manifest
  exact manifest segmentDigest
    (fun split tail =>
      tail segmentDigest
        (fun split_to_merge rest =>
          rest segmentDigest
            (fun merge_to_segment _rest2 =>
              merge_to_segment (split_to_merge split))))

theorem ay_pasm_archive_manifest
    (splitManifest : Prop) (mergeManifest : Prop)
    (segmentDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyPASMSplitMergeManifest splitManifest mergeManifest segmentDigest
      archiveManifest checkerTranscript ->
    archiveManifest := by
  intro manifest
  exact manifest archiveManifest
    (fun split tail =>
      tail archiveManifest
        (fun split_to_merge rest =>
          rest archiveManifest
            (fun merge_to_segment rest2 =>
              rest2 archiveManifest
                (fun segment_to_archive _archive_to_transcript =>
                  segment_to_archive
                    (merge_to_segment (split_to_merge split))))))

theorem ay_pasm_checker_transcript
    (splitManifest : Prop) (mergeManifest : Prop)
    (segmentDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) :
    AyPASMSplitMergeManifest splitManifest mergeManifest segmentDigest
      archiveManifest checkerTranscript ->
    checkerTranscript := by
  intro manifest
  exact manifest checkerTranscript
    (fun split tail =>
      tail checkerTranscript
        (fun split_to_merge rest =>
          rest checkerTranscript
            (fun merge_to_segment rest2 =>
              rest2 checkerTranscript
                (fun segment_to_archive archive_to_transcript =>
                  archive_to_transcript
                    (segment_to_archive
                      (merge_to_segment (split_to_merge split)))))))

theorem ay_pasm_checker_accepted
    (checkerTranscript : Prop) (checkerAccepted : Prop) :
    AyPASMMap checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro accepted
  exact accepted

theorem ay_pasm_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyPASMClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_map _map_to_mapped => transcript_to_map)

theorem ay_pasm_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyPASMClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_map map_to_mapped => map_to_mapped)

theorem ay_pasm_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyPASMParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_pasm_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyPASMParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_pasm_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyPASMFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_pasm_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyPASMFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_pasm_build_evidence
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyPASMBuild mappedTranscript buildEvidence buildAccepted ->
    mappedTranscript ->
    buildEvidence := by
  intro build
  exact build (mappedTranscript -> buildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_pasm_build_accepted
    (mappedTranscript : Prop) (buildEvidence : Prop)
    (buildAccepted : Prop) :
    AyPASMBuild mappedTranscript buildEvidence buildAccepted ->
    buildEvidence ->
    buildAccepted := by
  intro build
  exact build (buildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_pasm_reconstruction_evidence
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPASMReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_pasm_conj_left reconstructionEvidence
    (AyPASMConj
      (AyPASMMap emptyClauseReachable visibleUnsat)
      (AyPASMMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_pasm_visible_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPASMReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClauseReachable -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_pasm_original_unsat
    (emptyClauseReachable : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPASMReconstruction emptyClauseReachable reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original =>
          visible_to_original))

theorem ay_pasm_accepted_evidence
    (splitManifest : Prop) (mergeManifest : Prop)
    (segmentDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPASMAcceptedPublication splitManifest mergeManifest segmentDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat ->
    AyPASMAcceptedEvidence splitManifest mergeManifest segmentDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat := by
  intro accepted
  exact accepted
    (AyPASMAcceptedEvidence splitManifest mergeManifest segmentDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_pasm_publication_sound
    (splitManifest : Prop) (mergeManifest : Prop)
    (segmentDigest : Prop) (archiveManifest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (buildEvidence : Prop) (buildAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPASMAcceptedPublication splitManifest mergeManifest segmentDigest
      archiveManifest checkerTranscript checkerAccepted clauseIdMap
      mappedTranscript parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted buildEvidence buildAccepted reconstructionEvidence
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_pasm_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyPASMPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_pasm_disj_right noClaim originalUnsat unsat

theorem ay_pasm_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyPASMPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_pasm_disj_left noClaim originalUnsat no_claim

theorem ay_pasm_bad_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPASMBadSplitMerge splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_pasm_conj_left noClaim recompute fail_closed)

theorem ay_pasm_bad_recompute
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPASMBadSplitMerge splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_pasm_bad_public_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyPASMBadSplitMerge splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    AyPASMPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_pasm_public_no_claim_report noClaim originalUnsat
    (ay_pasm_bad_no_claim splitFailure mergeFailure segmentFailure
      mapFailure parentFailure checkerFailure emptyClauseFailure
      fingerprintFailure reconstructionFailure buildFailure archiveFailure
      noClaim recompute bad)

theorem ay_pasm_bad_cannot_bless_unsat
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPASMBadSplitMerge splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_pasm_bad_no_claim splitFailure mergeFailure segmentFailure
    mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure reconstructionFailure buildFailure archiveFailure
    noClaim recompute bad

theorem ay_pasm_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure ->
    noClaim ->
    recompute ->
    AyPASMBadSplitMerge splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_pasm_conj_intro (AyPASMConj noClaim recompute)
    (AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure)
    (ay_pasm_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_pasm_split_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    splitFailure ->
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro split_to_result
  intro _merge_to_result
  intro _segment_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact split_to_result failure

theorem ay_pasm_merge_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    mergeFailure ->
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _split_to_result
  intro merge_to_result
  intro _segment_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact merge_to_result failure

theorem ay_pasm_segment_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    segmentFailure ->
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _split_to_result
  intro _merge_to_result
  intro segment_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact segment_to_result failure

theorem ay_pasm_map_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    mapFailure ->
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _split_to_result
  intro _merge_to_result
  intro _segment_to_result
  intro map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact map_to_result failure

theorem ay_pasm_parent_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    parentFailure ->
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _split_to_result
  intro _merge_to_result
  intro _segment_to_result
  intro _map_to_result
  intro parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact parent_to_result failure

theorem ay_pasm_checker_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    checkerFailure ->
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _split_to_result
  intro _merge_to_result
  intro _segment_to_result
  intro _map_to_result
  intro _parent_to_result
  intro checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact checker_to_result failure

theorem ay_pasm_empty_clause_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    emptyClauseFailure ->
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _split_to_result
  intro _merge_to_result
  intro _segment_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact empty_to_result failure

theorem ay_pasm_fingerprint_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    fingerprintFailure ->
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _split_to_result
  intro _merge_to_result
  intro _segment_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact fingerprint_to_result failure

theorem ay_pasm_reconstruction_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    reconstructionFailure ->
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _split_to_result
  intro _merge_to_result
  intro _segment_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro reconstruction_to_result
  intro _build_to_result
  intro _archive_to_result
  exact reconstruction_to_result failure

theorem ay_pasm_build_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    buildFailure ->
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _split_to_result
  intro _merge_to_result
  intro _segment_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro build_to_result
  intro _archive_to_result
  exact build_to_result failure

theorem ay_pasm_archive_failure_forces_no_claim
    (splitFailure : Prop) (mergeFailure : Prop) (segmentFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (reconstructionFailure : Prop) (buildFailure : Prop)
    (archiveFailure : Prop) :
    archiveFailure ->
    AyPASMFailureReason splitFailure mergeFailure segmentFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      reconstructionFailure buildFailure archiveFailure := by
  intro failure
  intro result
  intro _split_to_result
  intro _merge_to_result
  intro _segment_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _reconstruction_to_result
  intro _build_to_result
  intro archive_to_result
  exact archive_to_result failure
