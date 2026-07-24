-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded DRAT-to-LRAT translation replay guard soundness for ay
-- sequential-main SAT-COMP validation. Propositions stand for source DRAT
-- digests, LRAT translation manifests, clause-ID maps, parent coverage,
-- checker transcripts, empty-clause reachability, formula fingerprints,
-- solver build evidence, archive manifests, audit transcripts, and
-- fail-closed no-claim/recompute diagnostics.

def AyDLTGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyDLTGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyDLTGMap (source : Prop) (target : Prop) :=
  source -> target

def AyDLTGTranslationManifest
    (sourceDratDigest : Prop) (lratTranslationManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :=
  AyDLTGConj sourceDratDigest
    (AyDLTGConj
      (AyDLTGMap sourceDratDigest lratTranslationManifest)
      (AyDLTGConj
        (AyDLTGMap lratTranslationManifest archiveManifest)
        (AyDLTGConj
          (AyDLTGMap archiveManifest auditTranscript)
          (AyDLTGMap auditTranscript checkerTranscript))))

def AyDLTGClauseMap
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :=
  AyDLTGConj
    (AyDLTGMap checkerTranscript clauseIdMap)
    (AyDLTGMap clauseIdMap mappedTranscript)

def AyDLTGParentCoverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyDLTGConj
    (AyDLTGMap mappedTranscript parentCoverage)
    (AyDLTGMap parentCoverage emptyClauseReachable)

def AyDLTGFingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyDLTGConj
    (AyDLTGMap mappedTranscript formulaFingerprint)
    (AyDLTGMap formulaFingerprint fingerprintAccepted)

def AyDLTGBuild
    (mappedTranscript : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyDLTGConj
    (AyDLTGMap mappedTranscript solverBuildEvidence)
    (AyDLTGMap solverBuildEvidence buildAccepted)

def AyDLTGReconstruction
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyDLTGConj
    (AyDLTGMap emptyClauseReachable visibleUnsat)
    (AyDLTGMap visibleUnsat originalUnsat)

def AyDLTGAcceptedEvidence
    (sourceDratDigest : Prop) (lratTranslationManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyDLTGConj
    (AyDLTGTranslationManifest sourceDratDigest lratTranslationManifest
      archiveManifest auditTranscript checkerTranscript)
    (AyDLTGConj
      (AyDLTGMap checkerTranscript checkerAccepted)
      (AyDLTGConj
        (AyDLTGClauseMap checkerTranscript clauseIdMap mappedTranscript)
        (AyDLTGConj
          (AyDLTGParentCoverage mappedTranscript parentCoverage
            emptyClauseReachable)
          (AyDLTGConj
            (AyDLTGFingerprint mappedTranscript formulaFingerprint
              fingerprintAccepted)
            (AyDLTGConj
              (AyDLTGBuild mappedTranscript solverBuildEvidence
                buildAccepted)
              (AyDLTGReconstruction emptyClauseReachable visibleUnsat
                originalUnsat))))))

def AyDLTGAcceptedPublication
    (sourceDratDigest : Prop) (lratTranslationManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyDLTGConj
    (AyDLTGAcceptedEvidence sourceDratDigest lratTranslationManifest
      archiveManifest auditTranscript checkerTranscript checkerAccepted
      clauseIdMap mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted visibleUnsat originalUnsat)
    originalUnsat

def AyDLTGFailureReason
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) :=
  forall result : Prop,
    (dratDigestFailure -> result) ->
    (translationFailure -> result) ->
    (mapFailure -> result) ->
    (parentFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (fingerprintFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    (auditFailure -> result) ->
    result

def AyDLTGBadTranslation
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyDLTGConj
    (AyDLTGConj noClaim recompute)
    (AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure)

def AyDLTGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyDLTGDisj noClaim originalUnsat

theorem ay_dltg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyDLTGConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_dltg_conj_left
    (p : Prop) (q : Prop) :
    AyDLTGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_dltg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyDLTGDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_dltg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyDLTGDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_dltg_source_drat_digest
    (sourceDratDigest : Prop) (lratTranslationManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :
    AyDLTGTranslationManifest sourceDratDigest lratTranslationManifest
      archiveManifest auditTranscript checkerTranscript ->
    sourceDratDigest := by
  intro manifest
  exact ay_dltg_conj_left sourceDratDigest
    (AyDLTGConj
      (AyDLTGMap sourceDratDigest lratTranslationManifest)
      (AyDLTGConj
        (AyDLTGMap lratTranslationManifest archiveManifest)
        (AyDLTGConj
          (AyDLTGMap archiveManifest auditTranscript)
          (AyDLTGMap auditTranscript checkerTranscript))))
    manifest

theorem ay_dltg_lrat_translation_manifest
    (sourceDratDigest : Prop) (lratTranslationManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :
    AyDLTGTranslationManifest sourceDratDigest lratTranslationManifest
      archiveManifest auditTranscript checkerTranscript ->
    lratTranslationManifest := by
  intro manifest
  exact manifest lratTranslationManifest
    (fun drat tail =>
      tail lratTranslationManifest
        (fun drat_to_lrat _rest => drat_to_lrat drat))

theorem ay_dltg_archive_manifest
    (sourceDratDigest : Prop) (lratTranslationManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :
    AyDLTGTranslationManifest sourceDratDigest lratTranslationManifest
      archiveManifest auditTranscript checkerTranscript ->
    archiveManifest := by
  intro manifest
  exact manifest archiveManifest
    (fun drat tail =>
      tail archiveManifest
        (fun drat_to_lrat rest =>
          rest archiveManifest
            (fun lrat_to_archive _rest2 =>
              lrat_to_archive (drat_to_lrat drat))))

theorem ay_dltg_audit_transcript
    (sourceDratDigest : Prop) (lratTranslationManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :
    AyDLTGTranslationManifest sourceDratDigest lratTranslationManifest
      archiveManifest auditTranscript checkerTranscript ->
    auditTranscript := by
  intro manifest
  exact manifest auditTranscript
    (fun drat tail =>
      tail auditTranscript
        (fun drat_to_lrat rest =>
          rest auditTranscript
            (fun lrat_to_archive rest2 =>
              rest2 auditTranscript
                (fun archive_to_audit _audit_to_checker =>
                  archive_to_audit (lrat_to_archive (drat_to_lrat drat))))))

theorem ay_dltg_checker_transcript
    (sourceDratDigest : Prop) (lratTranslationManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :
    AyDLTGTranslationManifest sourceDratDigest lratTranslationManifest
      archiveManifest auditTranscript checkerTranscript ->
    checkerTranscript := by
  intro manifest
  exact manifest checkerTranscript
    (fun drat tail =>
      tail checkerTranscript
        (fun drat_to_lrat rest =>
          rest checkerTranscript
            (fun lrat_to_archive rest2 =>
              rest2 checkerTranscript
                (fun archive_to_audit audit_to_checker =>
                  audit_to_checker
                    (archive_to_audit (lrat_to_archive
                      (drat_to_lrat drat)))))))

theorem ay_dltg_checker_accepted
    (checkerTranscript : Prop) (checkerAccepted : Prop) :
    AyDLTGMap checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro accepted
  exact accepted

theorem ay_dltg_clause_id_map
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyDLTGClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    checkerTranscript ->
    clauseIdMap := by
  intro clause_map
  exact clause_map (checkerTranscript -> clauseIdMap)
    (fun transcript_to_map _map_to_mapped => transcript_to_map)

theorem ay_dltg_mapped_transcript
    (checkerTranscript : Prop) (clauseIdMap : Prop)
    (mappedTranscript : Prop) :
    AyDLTGClauseMap checkerTranscript clauseIdMap mappedTranscript ->
    clauseIdMap ->
    mappedTranscript := by
  intro clause_map
  exact clause_map (clauseIdMap -> mappedTranscript)
    (fun _transcript_to_map map_to_mapped => map_to_mapped)

theorem ay_dltg_parent_coverage
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyDLTGParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    mappedTranscript ->
    parentCoverage := by
  intro parents
  exact parents (mappedTranscript -> parentCoverage)
    (fun mapped_to_parent _parent_to_empty => mapped_to_parent)

theorem ay_dltg_empty_clause_reachable
    (mappedTranscript : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyDLTGParentCoverage mappedTranscript parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _mapped_to_parent parent_to_empty => parent_to_empty)

theorem ay_dltg_formula_fingerprint
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyDLTGFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    mappedTranscript ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (mappedTranscript -> formulaFingerprint)
    (fun mapped_to_fingerprint _fingerprint_to_accept =>
      mapped_to_fingerprint)

theorem ay_dltg_fingerprint_accepted
    (mappedTranscript : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyDLTGFingerprint mappedTranscript formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _mapped_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_dltg_solver_build_evidence
    (mappedTranscript : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) :
    AyDLTGBuild mappedTranscript solverBuildEvidence buildAccepted ->
    mappedTranscript ->
    solverBuildEvidence := by
  intro build
  exact build (mappedTranscript -> solverBuildEvidence)
    (fun mapped_to_build _build_to_accept => mapped_to_build)

theorem ay_dltg_build_accepted
    (mappedTranscript : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) :
    AyDLTGBuild mappedTranscript solverBuildEvidence buildAccepted ->
    solverBuildEvidence ->
    buildAccepted := by
  intro build
  exact build (solverBuildEvidence -> buildAccepted)
    (fun _mapped_to_build build_to_accept => build_to_accept)

theorem ay_dltg_visible_unsat
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyDLTGReconstruction emptyClauseReachable visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_dltg_original_unsat
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyDLTGReconstruction emptyClauseReachable visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_dltg_accepted_evidence
    (sourceDratDigest : Prop) (lratTranslationManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyDLTGAcceptedPublication sourceDratDigest lratTranslationManifest
      archiveManifest auditTranscript checkerTranscript checkerAccepted
      clauseIdMap mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted visibleUnsat originalUnsat ->
    AyDLTGAcceptedEvidence sourceDratDigest lratTranslationManifest
      archiveManifest auditTranscript checkerTranscript checkerAccepted
      clauseIdMap mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted visibleUnsat originalUnsat := by
  intro accepted
  exact accepted
    (AyDLTGAcceptedEvidence sourceDratDigest lratTranslationManifest
      archiveManifest auditTranscript checkerTranscript checkerAccepted
      clauseIdMap mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted visibleUnsat originalUnsat)
    (fun evidence _unsat => evidence)

theorem ay_dltg_publication_sound
    (sourceDratDigest : Prop) (lratTranslationManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (clauseIdMap : Prop) (mappedTranscript : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyDLTGAcceptedPublication sourceDratDigest lratTranslationManifest
      archiveManifest auditTranscript checkerTranscript checkerAccepted
      clauseIdMap mappedTranscript parentCoverage emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_dltg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyDLTGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_dltg_disj_right noClaim originalUnsat unsat

theorem ay_dltg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyDLTGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_dltg_disj_left noClaim originalUnsat no_claim

theorem ay_dltg_bad_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyDLTGBadTranslation dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_dltg_conj_left noClaim recompute fail_closed)

theorem ay_dltg_bad_recompute
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyDLTGBadTranslation dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_dltg_failed_translation_cannot_bless_unsat
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyDLTGBadTranslation dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_dltg_bad_no_claim dratDigestFailure translationFailure
    mapFailure parentFailure checkerFailure emptyClauseFailure
    fingerprintFailure buildFailure archiveFailure auditFailure noClaim
    recompute bad

theorem ay_dltg_failure_forces_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure ->
    noClaim ->
    recompute ->
    AyDLTGBadTranslation dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_dltg_conj_intro (AyDLTGConj noClaim recompute)
    (AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure)
    (ay_dltg_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_dltg_drat_digest_failure_forces_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop) :
    dratDigestFailure ->
    AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure := by
  intro failure
  intro result
  intro drat_to_result
  intro _translation_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  exact drat_to_result failure

theorem ay_dltg_translation_failure_forces_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop) :
    translationFailure ->
    AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure := by
  intro failure
  intro result
  intro _drat_to_result
  intro translation_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  exact translation_to_result failure

theorem ay_dltg_map_failure_forces_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop) :
    mapFailure ->
    AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure := by
  intro failure
  intro result
  intro _drat_to_result
  intro _translation_to_result
  intro map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  exact map_to_result failure

theorem ay_dltg_parent_failure_forces_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop) :
    parentFailure ->
    AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure := by
  intro failure
  intro result
  intro _drat_to_result
  intro _translation_to_result
  intro _map_to_result
  intro parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  exact parent_to_result failure

theorem ay_dltg_checker_failure_forces_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop) :
    checkerFailure ->
    AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure := by
  intro failure
  intro result
  intro _drat_to_result
  intro _translation_to_result
  intro _map_to_result
  intro _parent_to_result
  intro checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  exact checker_to_result failure

theorem ay_dltg_empty_clause_failure_forces_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop) :
    emptyClauseFailure ->
    AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure := by
  intro failure
  intro result
  intro _drat_to_result
  intro _translation_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  exact empty_to_result failure

theorem ay_dltg_fingerprint_failure_forces_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop) :
    fingerprintFailure ->
    AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure := by
  intro failure
  intro result
  intro _drat_to_result
  intro _translation_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  exact fingerprint_to_result failure

theorem ay_dltg_build_failure_forces_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop) :
    buildFailure ->
    AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure := by
  intro failure
  intro result
  intro _drat_to_result
  intro _translation_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro build_to_result
  intro _archive_to_result
  intro _audit_to_result
  exact build_to_result failure

theorem ay_dltg_archive_failure_forces_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop) :
    archiveFailure ->
    AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure := by
  intro failure
  intro result
  intro _drat_to_result
  intro _translation_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro archive_to_result
  intro _audit_to_result
  exact archive_to_result failure

theorem ay_dltg_audit_failure_forces_no_claim
    (dratDigestFailure : Prop) (translationFailure : Prop)
    (mapFailure : Prop) (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop) :
    auditFailure ->
    AyDLTGFailureReason dratDigestFailure translationFailure mapFailure
      parentFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure archiveFailure auditFailure := by
  intro failure
  intro result
  intro _drat_to_result
  intro _translation_to_result
  intro _map_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro audit_to_result
  exact audit_to_result failure
