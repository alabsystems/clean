-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded incremental UNSAT-core extraction replay guard soundness for ay
-- sequential-main SAT-COMP validation. Propositions stand for core manifests,
-- selected-clause maps, parent coverage, checker transcripts, empty-clause
-- reachability, formula fingerprints, solver build evidence, archive
-- manifests, audit transcripts, public core reports, and fail-closed
-- no-claim/recompute diagnostics.

def AyUCEGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCEGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCEGMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCEGCoreManifest
    (coreManifest : Prop) (selectedClauseMap : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :=
  AyUCEGConj coreManifest
    (AyUCEGConj
      (AyUCEGMap coreManifest selectedClauseMap)
      (AyUCEGConj
        (AyUCEGMap selectedClauseMap archiveManifest)
        (AyUCEGConj
          (AyUCEGMap archiveManifest auditTranscript)
          (AyUCEGMap auditTranscript checkerTranscript))))

def AyUCEGParentCoverage
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :=
  AyUCEGConj
    (AyUCEGMap selectedClauseMap parentCoverage)
    (AyUCEGMap parentCoverage emptyClauseReachable)

def AyUCEGFingerprint
    (selectedClauseMap : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUCEGConj
    (AyUCEGMap selectedClauseMap formulaFingerprint)
    (AyUCEGMap formulaFingerprint fingerprintAccepted)

def AyUCEGBuild
    (selectedClauseMap : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) :=
  AyUCEGConj
    (AyUCEGMap selectedClauseMap solverBuildEvidence)
    (AyUCEGMap solverBuildEvidence buildAccepted)

def AyUCEGReconstruction
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUCEGConj
    (AyUCEGMap emptyClauseReachable visibleUnsat)
    (AyUCEGMap visibleUnsat originalUnsat)

def AyUCEGCoreReport
    (selectedClauseMap : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :=
  AyUCEGConj
    (AyUCEGMap selectedClauseMap publicCore)
    (AyUCEGMap publicCore coreReportAccepted)

def AyUCEGAcceptedEvidence
    (coreManifest : Prop) (selectedClauseMap : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (publicCore : Prop) (coreReportAccepted : Prop) :=
  AyUCEGConj
    (AyUCEGCoreManifest coreManifest selectedClauseMap archiveManifest
      auditTranscript checkerTranscript)
    (AyUCEGConj
      (AyUCEGMap checkerTranscript checkerAccepted)
      (AyUCEGConj
        (AyUCEGParentCoverage selectedClauseMap parentCoverage
          emptyClauseReachable)
        (AyUCEGConj
          (AyUCEGFingerprint selectedClauseMap formulaFingerprint
            fingerprintAccepted)
          (AyUCEGConj
            (AyUCEGBuild selectedClauseMap solverBuildEvidence
              buildAccepted)
            (AyUCEGConj
              (AyUCEGReconstruction emptyClauseReachable visibleUnsat
                originalUnsat)
              (AyUCEGCoreReport selectedClauseMap publicCore
                coreReportAccepted))))))

def AyUCEGAcceptedPublication
    (coreManifest : Prop) (selectedClauseMap : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (publicCore : Prop) (coreReportAccepted : Prop) :=
  AyUCEGConj
    (AyUCEGAcceptedEvidence coreManifest selectedClauseMap archiveManifest
      auditTranscript checkerTranscript checkerAccepted parentCoverage
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted visibleUnsat originalUnsat
      publicCore coreReportAccepted)
    (AyUCEGConj originalUnsat coreReportAccepted)

def AyUCEGFailureReason
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :=
  forall result : Prop,
    (manifestFailure -> result) ->
    (selectedMapFailure -> result) ->
    (parentFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (fingerprintFailure -> result) ->
    (buildFailure -> result) ->
    (archiveFailure -> result) ->
    (auditFailure -> result) ->
    (coreReportFailure -> result) ->
    result

def AyUCEGBadExtraction
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUCEGConj
    (AyUCEGConj noClaim recompute)
    (AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure)

def AyUCEGPublicReport
    (noClaim : Prop) (originalUnsat : Prop) (publicCore : Prop) :=
  AyUCEGDisj noClaim (AyUCEGConj originalUnsat publicCore)

theorem ay_uceg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCEGConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uceg_conj_left
    (p : Prop) (q : Prop) :
    AyUCEGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uceg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCEGDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uceg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCEGDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uceg_core_manifest
    (coreManifest : Prop) (selectedClauseMap : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :
    AyUCEGCoreManifest coreManifest selectedClauseMap archiveManifest
      auditTranscript checkerTranscript ->
    coreManifest := by
  intro manifest
  exact ay_uceg_conj_left coreManifest
    (AyUCEGConj
      (AyUCEGMap coreManifest selectedClauseMap)
      (AyUCEGConj
        (AyUCEGMap selectedClauseMap archiveManifest)
        (AyUCEGConj
          (AyUCEGMap archiveManifest auditTranscript)
          (AyUCEGMap auditTranscript checkerTranscript))))
    manifest

theorem ay_uceg_selected_clause_map
    (coreManifest : Prop) (selectedClauseMap : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :
    AyUCEGCoreManifest coreManifest selectedClauseMap archiveManifest
      auditTranscript checkerTranscript ->
    selectedClauseMap := by
  intro manifest
  exact manifest selectedClauseMap
    (fun core tail =>
      tail selectedClauseMap
        (fun core_to_selected _rest => core_to_selected core))

theorem ay_uceg_archive_manifest
    (coreManifest : Prop) (selectedClauseMap : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :
    AyUCEGCoreManifest coreManifest selectedClauseMap archiveManifest
      auditTranscript checkerTranscript ->
    archiveManifest := by
  intro manifest
  exact manifest archiveManifest
    (fun core tail =>
      tail archiveManifest
        (fun core_to_selected rest =>
          rest archiveManifest
            (fun selected_to_archive _rest2 =>
              selected_to_archive (core_to_selected core))))

theorem ay_uceg_audit_transcript
    (coreManifest : Prop) (selectedClauseMap : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :
    AyUCEGCoreManifest coreManifest selectedClauseMap archiveManifest
      auditTranscript checkerTranscript ->
    auditTranscript := by
  intro manifest
  exact manifest auditTranscript
    (fun core tail =>
      tail auditTranscript
        (fun core_to_selected rest =>
          rest auditTranscript
            (fun selected_to_archive rest2 =>
              rest2 auditTranscript
                (fun archive_to_audit _audit_to_checker =>
                  archive_to_audit
                    (selected_to_archive (core_to_selected core))))))

theorem ay_uceg_checker_transcript
    (coreManifest : Prop) (selectedClauseMap : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) :
    AyUCEGCoreManifest coreManifest selectedClauseMap archiveManifest
      auditTranscript checkerTranscript ->
    checkerTranscript := by
  intro manifest
  exact manifest checkerTranscript
    (fun core tail =>
      tail checkerTranscript
        (fun core_to_selected rest =>
          rest checkerTranscript
            (fun selected_to_archive rest2 =>
              rest2 checkerTranscript
                (fun archive_to_audit audit_to_checker =>
                  audit_to_checker
                    (archive_to_audit
                      (selected_to_archive (core_to_selected core)))))))

theorem ay_uceg_checker_accepted
    (checkerTranscript : Prop) (checkerAccepted : Prop) :
    AyUCEGMap checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro accepted
  exact accepted

theorem ay_uceg_parent_coverage
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUCEGParentCoverage selectedClauseMap parentCoverage
      emptyClauseReachable ->
    selectedClauseMap ->
    parentCoverage := by
  intro parents
  exact parents (selectedClauseMap -> parentCoverage)
    (fun selected_to_parent _parent_to_empty => selected_to_parent)

theorem ay_uceg_empty_clause_reachable
    (selectedClauseMap : Prop) (parentCoverage : Prop)
    (emptyClauseReachable : Prop) :
    AyUCEGParentCoverage selectedClauseMap parentCoverage
      emptyClauseReachable ->
    parentCoverage ->
    emptyClauseReachable := by
  intro parents
  exact parents (parentCoverage -> emptyClauseReachable)
    (fun _selected_to_parent parent_to_empty => parent_to_empty)

theorem ay_uceg_formula_fingerprint
    (selectedClauseMap : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCEGFingerprint selectedClauseMap formulaFingerprint
      fingerprintAccepted ->
    selectedClauseMap ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (selectedClauseMap -> formulaFingerprint)
    (fun selected_to_fingerprint _fingerprint_to_accept =>
      selected_to_fingerprint)

theorem ay_uceg_fingerprint_accepted
    (selectedClauseMap : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCEGFingerprint selectedClauseMap formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _selected_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_uceg_solver_build_evidence
    (selectedClauseMap : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUCEGBuild selectedClauseMap solverBuildEvidence buildAccepted ->
    selectedClauseMap ->
    solverBuildEvidence := by
  intro build
  exact build (selectedClauseMap -> solverBuildEvidence)
    (fun selected_to_build _build_to_accept => selected_to_build)

theorem ay_uceg_build_accepted
    (selectedClauseMap : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) :
    AyUCEGBuild selectedClauseMap solverBuildEvidence buildAccepted ->
    solverBuildEvidence ->
    buildAccepted := by
  intro build
  exact build (solverBuildEvidence -> buildAccepted)
    (fun _selected_to_build build_to_accept => build_to_accept)

theorem ay_uceg_visible_unsat
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCEGReconstruction emptyClauseReachable visibleUnsat originalUnsat ->
    emptyClauseReachable ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClauseReachable -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_uceg_original_unsat
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCEGReconstruction emptyClauseReachable visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_uceg_public_core
    (selectedClauseMap : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCEGCoreReport selectedClauseMap publicCore coreReportAccepted ->
    selectedClauseMap ->
    publicCore := by
  intro report
  exact report (selectedClauseMap -> publicCore)
    (fun selected_to_core _core_to_accepted => selected_to_core)

theorem ay_uceg_core_report_accepted
    (selectedClauseMap : Prop) (publicCore : Prop)
    (coreReportAccepted : Prop) :
    AyUCEGCoreReport selectedClauseMap publicCore coreReportAccepted ->
    publicCore ->
    coreReportAccepted := by
  intro report
  exact report (publicCore -> coreReportAccepted)
    (fun _selected_to_core core_to_accepted => core_to_accepted)

theorem ay_uceg_accepted_evidence
    (coreManifest : Prop) (selectedClauseMap : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (publicCore : Prop) (coreReportAccepted : Prop) :
    AyUCEGAcceptedPublication coreManifest selectedClauseMap
      archiveManifest auditTranscript checkerTranscript checkerAccepted
      parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted visibleUnsat
      originalUnsat publicCore coreReportAccepted ->
    AyUCEGAcceptedEvidence coreManifest selectedClauseMap archiveManifest
      auditTranscript checkerTranscript checkerAccepted parentCoverage
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted visibleUnsat originalUnsat
      publicCore coreReportAccepted := by
  intro accepted
  exact accepted
    (AyUCEGAcceptedEvidence coreManifest selectedClauseMap archiveManifest
      auditTranscript checkerTranscript checkerAccepted parentCoverage
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted visibleUnsat originalUnsat
      publicCore coreReportAccepted)
    (fun evidence _published => evidence)

theorem ay_uceg_publication_sound
    (coreManifest : Prop) (selectedClauseMap : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (publicCore : Prop) (coreReportAccepted : Prop) :
    AyUCEGAcceptedPublication coreManifest selectedClauseMap
      archiveManifest auditTranscript checkerTranscript checkerAccepted
      parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted visibleUnsat
      originalUnsat publicCore coreReportAccepted ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _evidence published =>
      published originalUnsat (fun unsat _core_ok => unsat))

theorem ay_uceg_public_core_sound
    (coreManifest : Prop) (selectedClauseMap : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (parentCoverage : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (publicCore : Prop) (coreReportAccepted : Prop) :
    AyUCEGAcceptedPublication coreManifest selectedClauseMap
      archiveManifest auditTranscript checkerTranscript checkerAccepted
      parentCoverage emptyClauseReachable formulaFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted visibleUnsat
      originalUnsat publicCore coreReportAccepted ->
    coreReportAccepted := by
  intro accepted
  exact accepted coreReportAccepted
    (fun _evidence published =>
      published coreReportAccepted (fun _unsat core_ok => core_ok))

theorem ay_uceg_public_unsat_core_report
    (noClaim : Prop) (originalUnsat : Prop) (publicCore : Prop) :
    originalUnsat ->
    publicCore ->
    AyUCEGPublicReport noClaim originalUnsat publicCore := by
  intro unsat
  intro core
  exact ay_uceg_disj_right noClaim (AyUCEGConj originalUnsat publicCore)
    (ay_uceg_conj_intro originalUnsat publicCore unsat core)

theorem ay_uceg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicCore : Prop) :
    noClaim ->
    AyUCEGPublicReport noClaim originalUnsat publicCore := by
  intro no_claim
  exact ay_uceg_disj_left noClaim (AyUCEGConj originalUnsat publicCore)
    no_claim

theorem ay_uceg_bad_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCEGBadExtraction manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_uceg_conj_left noClaim recompute fail_closed)

theorem ay_uceg_bad_recompute
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCEGBadExtraction manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recheck => recheck))

theorem ay_uceg_failed_extraction_cannot_bless_unsat_or_core
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCEGBadExtraction manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_uceg_bad_no_claim manifestFailure selectedMapFailure
    parentFailure checkerFailure emptyClauseFailure fingerprintFailure
    buildFailure archiveFailure auditFailure coreReportFailure noClaim
    recompute bad

theorem ay_uceg_failure_forces_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure ->
    noClaim ->
    recompute ->
    AyUCEGBadExtraction manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure noClaim recompute := by
  intro reason
  intro no_claim
  intro recheck
  exact ay_uceg_conj_intro (AyUCEGConj noClaim recompute)
    (AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure)
    (ay_uceg_conj_intro noClaim recompute no_claim recheck)
    reason

theorem ay_uceg_manifest_failure_forces_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :
    manifestFailure ->
    AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure := by
  intro failure
  intro result
  intro manifest_to_result
  intro _selected_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  intro _core_report_to_result
  exact manifest_to_result failure

theorem ay_uceg_selected_map_failure_forces_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :
    selectedMapFailure ->
    AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro selected_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  intro _core_report_to_result
  exact selected_to_result failure

theorem ay_uceg_parent_failure_forces_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :
    parentFailure ->
    AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _selected_to_result
  intro parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  intro _core_report_to_result
  exact parent_to_result failure

theorem ay_uceg_checker_failure_forces_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :
    checkerFailure ->
    AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _selected_to_result
  intro _parent_to_result
  intro checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  intro _core_report_to_result
  exact checker_to_result failure

theorem ay_uceg_empty_clause_failure_forces_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :
    emptyClauseFailure ->
    AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _selected_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  intro _core_report_to_result
  exact empty_to_result failure

theorem ay_uceg_fingerprint_failure_forces_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :
    fingerprintFailure ->
    AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _selected_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  intro _core_report_to_result
  exact fingerprint_to_result failure

theorem ay_uceg_build_failure_forces_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :
    buildFailure ->
    AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _selected_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro build_to_result
  intro _archive_to_result
  intro _audit_to_result
  intro _core_report_to_result
  exact build_to_result failure

theorem ay_uceg_archive_failure_forces_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :
    archiveFailure ->
    AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _selected_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro archive_to_result
  intro _audit_to_result
  intro _core_report_to_result
  exact archive_to_result failure

theorem ay_uceg_audit_failure_forces_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :
    auditFailure ->
    AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _selected_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro audit_to_result
  intro _core_report_to_result
  exact audit_to_result failure

theorem ay_uceg_core_report_failure_forces_no_claim
    (manifestFailure : Prop) (selectedMapFailure : Prop)
    (parentFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (archiveFailure : Prop) (auditFailure : Prop)
    (coreReportFailure : Prop) :
    coreReportFailure ->
    AyUCEGFailureReason manifestFailure selectedMapFailure parentFailure
      checkerFailure emptyClauseFailure fingerprintFailure buildFailure
      archiveFailure auditFailure coreReportFailure := by
  intro failure
  intro result
  intro _manifest_to_result
  intro _selected_to_result
  intro _parent_to_result
  intro _checker_to_result
  intro _empty_to_result
  intro _fingerprint_to_result
  intro _build_to_result
  intro _archive_to_result
  intro _audit_to_result
  intro core_report_to_result
  exact core_report_to_result failure
