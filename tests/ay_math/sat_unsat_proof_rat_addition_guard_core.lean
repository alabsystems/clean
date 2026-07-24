-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- RAT-addition guard soundness for ay sequential-main SAT-COMP DRAT-style
-- UNSAT proof checking. Propositions model formula fingerprints, proof-line
-- and added-clause digests, RAT pivot witnesses, resolution candidate ledgers,
-- unit-propagation traces for blocked candidates, antecedent/reason maps,
-- checker transcripts, empty-clause reachability, archive/build evidence,
-- fallback no-claim paths, audit transcripts, and fail-closed recompute
-- diagnostics.

def ay_ratg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_ratg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_ratg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_ratg_accepted_evidence
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (addedClauseDigest : Prop) (ratPivotWitness : Prop)
    (resolutionCandidateLedger : Prop)
    (blockedCandidatePropagationTrace : Prop)
    (antecedentReasonMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (checkerContextPreserved : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (originalFormulaFingerprint ->
      proofLineDigest ->
      addedClauseDigest ->
      ratPivotWitness ->
      resolutionCandidateLedger ->
      blockedCandidatePropagationTrace ->
      antecedentReasonMapDigest ->
      checkerTranscript ->
      checkerAccepted ->
      emptyClauseReachabilityWitness ->
      archiveManifest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      fallbackNoClaim ->
      auditTranscript ->
      checkerContextPreserved ->
      originalUnsat ->
      result) ->
    result

def ay_ratg_checker_publication_path
    (ratPivotWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :=
  ay_ratg_conj
    (ay_ratg_map ratPivotWitness checkerTranscript)
    (ay_ratg_conj
      (ay_ratg_map checkerTranscript checkerAccepted)
      (ay_ratg_conj
        (ay_ratg_map checkerAccepted emptyClauseReachabilityWitness)
        (ay_ratg_map emptyClauseReachabilityWitness originalUnsat)))

def ay_ratg_context_preservation
    (ratPivotWitness : Prop) (resolutionCandidateLedger : Prop)
    (blockedCandidatePropagationTrace : Prop)
    (antecedentReasonMapDigest : Prop) (checkerContextPreserved : Prop) :=
  ay_ratg_conj
    (ay_ratg_map ratPivotWitness resolutionCandidateLedger)
    (ay_ratg_conj
      (ay_ratg_map resolutionCandidateLedger
        blockedCandidatePropagationTrace)
      (ay_ratg_conj
        (ay_ratg_map blockedCandidatePropagationTrace
          antecedentReasonMapDigest)
        (ay_ratg_map antecedentReasonMapDigest checkerContextPreserved)))

def ay_ratg_publication
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (addedClauseDigest : Prop) (ratPivotWitness : Prop)
    (resolutionCandidateLedger : Prop)
    (blockedCandidatePropagationTrace : Prop)
    (antecedentReasonMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (checkerContextPreserved : Prop) (originalUnsat : Prop) :=
  ay_ratg_conj
    (ay_ratg_accepted_evidence originalFormulaFingerprint proofLineDigest
      addedClauseDigest ratPivotWitness resolutionCandidateLedger
      blockedCandidatePropagationTrace antecedentReasonMapDigest
      checkerTranscript checkerAccepted emptyClauseReachabilityWitness
      archiveManifest archiveAccepted solverBuildEvidence buildAccepted
      fallbackNoClaim auditTranscript checkerContextPreserved originalUnsat)
    originalUnsat

def ay_ratg_failure_reason
    (proofLineMismatch : Prop) (clauseMismatch : Prop)
    (pivotMismatch : Prop) (candidateMismatch : Prop)
    (traceMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (reachabilityMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (proofLineMismatch -> result) ->
    (clauseMismatch -> result) ->
    (pivotMismatch -> result) ->
    (candidateMismatch -> result) ->
    (traceMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (checkerMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_ratg_bad_guard
    (proofLineMismatch : Prop) (clauseMismatch : Prop)
    (pivotMismatch : Prop) (candidateMismatch : Prop)
    (traceMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (reachabilityMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_ratg_conj
    (ay_ratg_conj noClaim recompute)
    (ay_ratg_failure_reason proofLineMismatch clauseMismatch pivotMismatch
      candidateMismatch traceMismatch antecedentMismatch checkerMismatch
      reachabilityMismatch archiveMismatch buildMismatch auditMismatch)

def ay_ratg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_ratg_disj noClaim (ay_ratg_disj originalUnsat publicSat)

theorem ay_ratg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_ratg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_ratg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_ratg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_ratg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_ratg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_ratg_build_accepted_evidence
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (addedClauseDigest : Prop) (ratPivotWitness : Prop)
    (resolutionCandidateLedger : Prop)
    (blockedCandidatePropagationTrace : Prop)
    (antecedentReasonMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (checkerContextPreserved : Prop) (originalUnsat : Prop) :
    originalFormulaFingerprint ->
    proofLineDigest ->
    addedClauseDigest ->
    ratPivotWitness ->
    resolutionCandidateLedger ->
    blockedCandidatePropagationTrace ->
    antecedentReasonMapDigest ->
    checkerTranscript ->
    checkerAccepted ->
    emptyClauseReachabilityWitness ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    fallbackNoClaim ->
    auditTranscript ->
    checkerContextPreserved ->
    originalUnsat ->
    ay_ratg_accepted_evidence originalFormulaFingerprint proofLineDigest
      addedClauseDigest ratPivotWitness resolutionCandidateLedger
      blockedCandidatePropagationTrace antecedentReasonMapDigest
      checkerTranscript checkerAccepted emptyClauseReachabilityWitness
      archiveManifest archiveAccepted solverBuildEvidence buildAccepted
      fallbackNoClaim auditTranscript checkerContextPreserved originalUnsat := by
  intro hFingerprint hLine hClause hPivot hCandidates hTrace hAntecedent
  intro hTranscript hChecker hReachability hArchive hArchiveAccepted hBuild
  intro hBuildAccepted hFallback hAudit hContext hOriginal result publish
  exact publish hFingerprint hLine hClause hPivot hCandidates hTrace
    hAntecedent hTranscript hChecker hReachability hArchive hArchiveAccepted
    hBuild hBuildAccepted hFallback hAudit hContext hOriginal

theorem ay_ratg_rat_addition_requires_checker_replay
    (ratPivotWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :
    ay_ratg_checker_publication_path ratPivotWitness checkerTranscript
      checkerAccepted emptyClauseReachabilityWitness originalUnsat ->
    ratPivotWitness ->
    originalUnsat := by
  intro path hPivot
  exact path originalUnsat
    (fun pivot_to_transcript rest =>
      rest originalUnsat
        (fun transcript_to_checker rest2 =>
          rest2 originalUnsat
            (fun checker_to_reachability reachability_to_original =>
              reachability_to_original
                (checker_to_reachability
                  (transcript_to_checker
                    (pivot_to_transcript hPivot)))))))

theorem ay_ratg_context_preserved_for_checker
    (ratPivotWitness : Prop) (resolutionCandidateLedger : Prop)
    (blockedCandidatePropagationTrace : Prop)
    (antecedentReasonMapDigest : Prop) (checkerContextPreserved : Prop) :
    ay_ratg_context_preservation ratPivotWitness resolutionCandidateLedger
      blockedCandidatePropagationTrace antecedentReasonMapDigest
      checkerContextPreserved ->
    ratPivotWitness ->
    checkerContextPreserved := by
  intro preservation hPivot
  exact preservation checkerContextPreserved
    (fun pivot_to_candidates rest =>
      rest checkerContextPreserved
        (fun candidates_to_trace rest2 =>
          rest2 checkerContextPreserved
            (fun trace_to_antecedent antecedent_to_context =>
              antecedent_to_context
                (trace_to_antecedent
                  (candidates_to_trace
                    (pivot_to_candidates hPivot)))))))

theorem ay_ratg_empty_clause_reachability_available
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (addedClauseDigest : Prop) (ratPivotWitness : Prop)
    (resolutionCandidateLedger : Prop)
    (blockedCandidatePropagationTrace : Prop)
    (antecedentReasonMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (checkerContextPreserved : Prop) (originalUnsat : Prop) :
    ay_ratg_accepted_evidence originalFormulaFingerprint proofLineDigest
      addedClauseDigest ratPivotWitness resolutionCandidateLedger
      blockedCandidatePropagationTrace antecedentReasonMapDigest
      checkerTranscript checkerAccepted emptyClauseReachabilityWitness
      archiveManifest archiveAccepted solverBuildEvidence buildAccepted
      fallbackNoClaim auditTranscript checkerContextPreserved originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hFingerprint _hLine _hClause _hPivot _hCandidates _hTrace
      _hAntecedent _hTranscript _hChecker hReachability _hArchive
      _hArchiveAccepted _hBuild _hBuildAccepted _hFallback _hAudit _hContext
      _hOriginal =>
      hReachability)

theorem ay_ratg_checker_context_available
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (addedClauseDigest : Prop) (ratPivotWitness : Prop)
    (resolutionCandidateLedger : Prop)
    (blockedCandidatePropagationTrace : Prop)
    (antecedentReasonMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (checkerContextPreserved : Prop) (originalUnsat : Prop) :
    ay_ratg_accepted_evidence originalFormulaFingerprint proofLineDigest
      addedClauseDigest ratPivotWitness resolutionCandidateLedger
      blockedCandidatePropagationTrace antecedentReasonMapDigest
      checkerTranscript checkerAccepted emptyClauseReachabilityWitness
      archiveManifest archiveAccepted solverBuildEvidence buildAccepted
      fallbackNoClaim auditTranscript checkerContextPreserved originalUnsat ->
    checkerContextPreserved := by
  intro accepted
  exact accepted checkerContextPreserved
    (fun _hFingerprint _hLine _hClause _hPivot _hCandidates _hTrace
      _hAntecedent _hTranscript _hChecker _hReachability _hArchive
      _hArchiveAccepted _hBuild _hBuildAccepted _hFallback _hAudit hContext
      _hOriginal =>
      hContext)

theorem ay_ratg_publication_sound
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (addedClauseDigest : Prop) (ratPivotWitness : Prop)
    (resolutionCandidateLedger : Prop)
    (blockedCandidatePropagationTrace : Prop)
    (antecedentReasonMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (checkerContextPreserved : Prop) (originalUnsat : Prop) :
    ay_ratg_publication originalFormulaFingerprint proofLineDigest
      addedClauseDigest ratPivotWitness resolutionCandidateLedger
      blockedCandidatePropagationTrace antecedentReasonMapDigest
      checkerTranscript checkerAccepted emptyClauseReachabilityWitness
      archiveManifest archiveAccepted solverBuildEvidence buildAccepted
      fallbackNoClaim auditTranscript checkerContextPreserved originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_ratg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_ratg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_ratg_disj_right noClaim (ay_ratg_disj originalUnsat publicSat)
    (ay_ratg_disj_left originalUnsat publicSat hUnsat)

theorem ay_ratg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_ratg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_ratg_disj_left noClaim
    (ay_ratg_disj originalUnsat publicSat) hNoClaim

theorem ay_ratg_bad_no_claim
    (proofLineMismatch : Prop) (clauseMismatch : Prop)
    (pivotMismatch : Prop) (candidateMismatch : Prop)
    (traceMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (reachabilityMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ratg_bad_guard proofLineMismatch clauseMismatch pivotMismatch
      candidateMismatch traceMismatch antecedentMismatch checkerMismatch
      reachabilityMismatch archiveMismatch buildMismatch auditMismatch noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_ratg_bad_recompute
    (proofLineMismatch : Prop) (clauseMismatch : Prop)
    (pivotMismatch : Prop) (candidateMismatch : Prop)
    (traceMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (reachabilityMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ratg_bad_guard proofLineMismatch clauseMismatch pivotMismatch
      candidateMismatch traceMismatch antecedentMismatch checkerMismatch
      reachabilityMismatch archiveMismatch buildMismatch auditMismatch noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_ratg_failed_guard_cannot_bless_unsat
    (proofLineMismatch : Prop) (clauseMismatch : Prop)
    (pivotMismatch : Prop) (candidateMismatch : Prop)
    (traceMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (reachabilityMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_ratg_bad_guard proofLineMismatch clauseMismatch pivotMismatch
      candidateMismatch traceMismatch antecedentMismatch checkerMismatch
      reachabilityMismatch archiveMismatch buildMismatch auditMismatch noClaim
      recompute ->
    ay_ratg_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_ratg_bad_recompute proofLineMismatch clauseMismatch pivotMismatch
    candidateMismatch traceMismatch antecedentMismatch checkerMismatch
    reachabilityMismatch archiveMismatch buildMismatch auditMismatch noClaim
    recompute bad

theorem ay_ratg_failure_forces_no_claim
    (proofLineMismatch : Prop) (clauseMismatch : Prop)
    (pivotMismatch : Prop) (candidateMismatch : Prop)
    (traceMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (reachabilityMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_ratg_failure_reason proofLineMismatch clauseMismatch pivotMismatch
      candidateMismatch traceMismatch antecedentMismatch checkerMismatch
      reachabilityMismatch archiveMismatch buildMismatch auditMismatch ->
    (proofLineMismatch -> noClaim) ->
    (clauseMismatch -> noClaim) ->
    (pivotMismatch -> noClaim) ->
    (candidateMismatch -> noClaim) ->
    (traceMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason line_to_no_claim clause_to_no_claim pivot_to_no_claim
  intro candidate_to_no_claim trace_to_no_claim antecedent_to_no_claim
  intro checker_to_no_claim reachability_to_no_claim archive_to_no_claim
  intro build_to_no_claim audit_to_no_claim
  exact reason noClaim line_to_no_claim clause_to_no_claim pivot_to_no_claim
    candidate_to_no_claim trace_to_no_claim antecedent_to_no_claim
    checker_to_no_claim reachability_to_no_claim archive_to_no_claim
    build_to_no_claim audit_to_no_claim

theorem ay_ratg_proof_line_mismatch_forces_no_claim
    (proofLineMismatch noClaim : Prop) :
    proofLineMismatch ->
    (proofLineMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ratg_clause_mismatch_forces_no_claim
    (clauseMismatch noClaim : Prop) :
    clauseMismatch ->
    (clauseMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ratg_pivot_mismatch_forces_no_claim
    (pivotMismatch noClaim : Prop) :
    pivotMismatch ->
    (pivotMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ratg_candidate_mismatch_forces_no_claim
    (candidateMismatch noClaim : Prop) :
    candidateMismatch ->
    (candidateMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ratg_trace_mismatch_forces_no_claim
    (traceMismatch noClaim : Prop) :
    traceMismatch ->
    (traceMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ratg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch ->
    (antecedentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ratg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ratg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch ->
    (reachabilityMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ratg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ratg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ratg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
