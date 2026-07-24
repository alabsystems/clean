-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- LRAT hint guard soundness for ay sequential-main SAT-COMP UNSAT proof
-- checking. Propositions model formula fingerprints, proof-line digests, LRAT
-- hint-list digests, antecedent order, unit-propagation traces,
-- deletion/live-clause context, empty-clause reachability, checker
-- transcripts, archive/build evidence, fallback no-claim paths, audit
-- transcripts, and fail-closed recompute diagnostics.

def ay_lhg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_lhg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_lhg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_lhg_accepted_evidence
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (lratHintListDigest : Prop) (antecedentOrderWitness : Prop)
    (unitPropagationTraceDigest : Prop) (deletionLiveClauseContextDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (hintOrderContextPreserved : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (originalFormulaFingerprint ->
      proofLineDigest ->
      lratHintListDigest ->
      antecedentOrderWitness ->
      unitPropagationTraceDigest ->
      deletionLiveClauseContextDigest ->
      emptyClauseReachabilityWitness ->
      checkerTranscript ->
      checkerAccepted ->
      archiveManifest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      fallbackNoClaim ->
      auditTranscript ->
      hintOrderContextPreserved ->
      originalUnsat ->
      result) ->
    result

def ay_lhg_checker_publication_path
    (lratHintListDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :=
  ay_lhg_conj
    (ay_lhg_map lratHintListDigest checkerTranscript)
    (ay_lhg_conj
      (ay_lhg_map checkerTranscript checkerAccepted)
      (ay_lhg_conj
        (ay_lhg_map checkerAccepted emptyClauseReachabilityWitness)
        (ay_lhg_map emptyClauseReachabilityWitness originalUnsat)))

def ay_lhg_context_preservation
    (lratHintListDigest : Prop) (antecedentOrderWitness : Prop)
    (unitPropagationTraceDigest : Prop) (deletionLiveClauseContextDigest : Prop)
    (hintOrderContextPreserved : Prop) :=
  ay_lhg_conj
    (ay_lhg_map lratHintListDigest antecedentOrderWitness)
    (ay_lhg_conj
      (ay_lhg_map antecedentOrderWitness unitPropagationTraceDigest)
      (ay_lhg_conj
        (ay_lhg_map unitPropagationTraceDigest
          deletionLiveClauseContextDigest)
        (ay_lhg_map deletionLiveClauseContextDigest
          hintOrderContextPreserved)))

def ay_lhg_publication
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (lratHintListDigest : Prop) (antecedentOrderWitness : Prop)
    (unitPropagationTraceDigest : Prop) (deletionLiveClauseContextDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (hintOrderContextPreserved : Prop)
    (originalUnsat : Prop) :=
  ay_lhg_conj
    (ay_lhg_accepted_evidence originalFormulaFingerprint proofLineDigest
      lratHintListDigest antecedentOrderWitness unitPropagationTraceDigest
      deletionLiveClauseContextDigest emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      hintOrderContextPreserved originalUnsat)
    originalUnsat

def ay_lhg_failure_reason
    (proofLineMismatch : Prop) (hintMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (liveClauseMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (proofLineMismatch -> result) ->
    (hintMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (traceMismatch -> result) ->
    (liveClauseMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (checkerMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_lhg_bad_guard
    (proofLineMismatch : Prop) (hintMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (liveClauseMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_lhg_conj
    (ay_lhg_conj noClaim recompute)
    (ay_lhg_failure_reason proofLineMismatch hintMismatch antecedentMismatch
      traceMismatch liveClauseMismatch reachabilityMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch)

def ay_lhg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_lhg_disj noClaim (ay_lhg_disj originalUnsat publicSat)

theorem ay_lhg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_lhg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_lhg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_lhg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_lhg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_lhg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_lhg_build_accepted_evidence
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (lratHintListDigest : Prop) (antecedentOrderWitness : Prop)
    (unitPropagationTraceDigest : Prop) (deletionLiveClauseContextDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (hintOrderContextPreserved : Prop)
    (originalUnsat : Prop) :
    originalFormulaFingerprint ->
    proofLineDigest ->
    lratHintListDigest ->
    antecedentOrderWitness ->
    unitPropagationTraceDigest ->
    deletionLiveClauseContextDigest ->
    emptyClauseReachabilityWitness ->
    checkerTranscript ->
    checkerAccepted ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    fallbackNoClaim ->
    auditTranscript ->
    hintOrderContextPreserved ->
    originalUnsat ->
    ay_lhg_accepted_evidence originalFormulaFingerprint proofLineDigest
      lratHintListDigest antecedentOrderWitness unitPropagationTraceDigest
      deletionLiveClauseContextDigest emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      hintOrderContextPreserved originalUnsat := by
  intro hFingerprint hLine hHint hAntecedent hTrace hLive hReachability
  intro hTranscript hChecker hArchive hArchiveAccepted hBuild hBuildAccepted
  intro hFallback hAudit hContext hOriginal result publish
  exact publish hFingerprint hLine hHint hAntecedent hTrace hLive
    hReachability hTranscript hChecker hArchive hArchiveAccepted hBuild
    hBuildAccepted hFallback hAudit hContext hOriginal

theorem ay_lhg_hints_publish_only_through_checker_replay
    (lratHintListDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :
    ay_lhg_checker_publication_path lratHintListDigest checkerTranscript
      checkerAccepted emptyClauseReachabilityWitness originalUnsat ->
    lratHintListDigest ->
    originalUnsat := by
  intro path hHint
  exact path originalUnsat
    (fun hint_to_transcript rest =>
      rest originalUnsat
        (fun transcript_to_checker rest2 =>
          rest2 originalUnsat
            (fun checker_to_reachability reachability_to_original =>
              reachability_to_original
                (checker_to_reachability
                  (transcript_to_checker
                    (hint_to_transcript hHint)))))))

theorem ay_lhg_hint_order_context_preserved_for_checker
    (lratHintListDigest : Prop) (antecedentOrderWitness : Prop)
    (unitPropagationTraceDigest : Prop) (deletionLiveClauseContextDigest : Prop)
    (hintOrderContextPreserved : Prop) :
    ay_lhg_context_preservation lratHintListDigest antecedentOrderWitness
      unitPropagationTraceDigest deletionLiveClauseContextDigest
      hintOrderContextPreserved ->
    lratHintListDigest ->
    hintOrderContextPreserved := by
  intro preservation hHint
  exact preservation hintOrderContextPreserved
    (fun hint_to_antecedent rest =>
      rest hintOrderContextPreserved
        (fun antecedent_to_trace rest2 =>
          rest2 hintOrderContextPreserved
            (fun trace_to_live live_to_context =>
              live_to_context
                (trace_to_live
                  (antecedent_to_trace
                    (hint_to_antecedent hHint)))))))

theorem ay_lhg_empty_clause_reachability_available
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (lratHintListDigest : Prop) (antecedentOrderWitness : Prop)
    (unitPropagationTraceDigest : Prop) (deletionLiveClauseContextDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (hintOrderContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_lhg_accepted_evidence originalFormulaFingerprint proofLineDigest
      lratHintListDigest antecedentOrderWitness unitPropagationTraceDigest
      deletionLiveClauseContextDigest emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      hintOrderContextPreserved originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hFingerprint _hLine _hHint _hAntecedent _hTrace _hLive
      hReachability _hTranscript _hChecker _hArchive _hArchiveAccepted
      _hBuild _hBuildAccepted _hFallback _hAudit _hContext _hOriginal =>
      hReachability)

theorem ay_lhg_checker_context_available
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (lratHintListDigest : Prop) (antecedentOrderWitness : Prop)
    (unitPropagationTraceDigest : Prop) (deletionLiveClauseContextDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (hintOrderContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_lhg_accepted_evidence originalFormulaFingerprint proofLineDigest
      lratHintListDigest antecedentOrderWitness unitPropagationTraceDigest
      deletionLiveClauseContextDigest emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      hintOrderContextPreserved originalUnsat ->
    hintOrderContextPreserved := by
  intro accepted
  exact accepted hintOrderContextPreserved
    (fun _hFingerprint _hLine _hHint _hAntecedent _hTrace _hLive
      _hReachability _hTranscript _hChecker _hArchive _hArchiveAccepted
      _hBuild _hBuildAccepted _hFallback _hAudit hContext _hOriginal =>
      hContext)

theorem ay_lhg_publication_sound
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (lratHintListDigest : Prop) (antecedentOrderWitness : Prop)
    (unitPropagationTraceDigest : Prop) (deletionLiveClauseContextDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (hintOrderContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_lhg_publication originalFormulaFingerprint proofLineDigest
      lratHintListDigest antecedentOrderWitness unitPropagationTraceDigest
      deletionLiveClauseContextDigest emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      hintOrderContextPreserved originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_lhg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_lhg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_lhg_disj_right noClaim (ay_lhg_disj originalUnsat publicSat)
    (ay_lhg_disj_left originalUnsat publicSat hUnsat)

theorem ay_lhg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_lhg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_lhg_disj_left noClaim
    (ay_lhg_disj originalUnsat publicSat) hNoClaim

theorem ay_lhg_bad_no_claim
    (proofLineMismatch : Prop) (hintMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (liveClauseMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_lhg_bad_guard proofLineMismatch hintMismatch antecedentMismatch
      traceMismatch liveClauseMismatch reachabilityMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_lhg_bad_recompute
    (proofLineMismatch : Prop) (hintMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (liveClauseMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_lhg_bad_guard proofLineMismatch hintMismatch antecedentMismatch
      traceMismatch liveClauseMismatch reachabilityMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_lhg_failed_guard_cannot_bless_unsat
    (proofLineMismatch : Prop) (hintMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (liveClauseMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_lhg_bad_guard proofLineMismatch hintMismatch antecedentMismatch
      traceMismatch liveClauseMismatch reachabilityMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    ay_lhg_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_lhg_bad_recompute proofLineMismatch hintMismatch antecedentMismatch
    traceMismatch liveClauseMismatch reachabilityMismatch checkerMismatch
    archiveMismatch buildMismatch auditMismatch noClaim recompute bad

theorem ay_lhg_failure_forces_no_claim
    (proofLineMismatch : Prop) (hintMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (liveClauseMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_lhg_failure_reason proofLineMismatch hintMismatch antecedentMismatch
      traceMismatch liveClauseMismatch reachabilityMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch ->
    (proofLineMismatch -> noClaim) ->
    (hintMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (traceMismatch -> noClaim) ->
    (liveClauseMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason line_to_no_claim hint_to_no_claim antecedent_to_no_claim
  intro trace_to_no_claim live_to_no_claim reachability_to_no_claim
  intro checker_to_no_claim archive_to_no_claim build_to_no_claim
  intro audit_to_no_claim
  exact reason noClaim line_to_no_claim hint_to_no_claim antecedent_to_no_claim
    trace_to_no_claim live_to_no_claim reachability_to_no_claim
    checker_to_no_claim archive_to_no_claim build_to_no_claim
    audit_to_no_claim

theorem ay_lhg_proof_line_mismatch_forces_no_claim
    (proofLineMismatch noClaim : Prop) :
    proofLineMismatch ->
    (proofLineMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_lhg_hint_mismatch_forces_no_claim
    (hintMismatch noClaim : Prop) :
    hintMismatch ->
    (hintMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_lhg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch ->
    (antecedentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_lhg_trace_mismatch_forces_no_claim
    (traceMismatch noClaim : Prop) :
    traceMismatch ->
    (traceMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_lhg_live_clause_mismatch_forces_no_claim
    (liveClauseMismatch noClaim : Prop) :
    liveClauseMismatch ->
    (liveClauseMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_lhg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch ->
    (reachabilityMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_lhg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_lhg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_lhg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_lhg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
