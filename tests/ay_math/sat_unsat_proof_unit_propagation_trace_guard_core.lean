-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Unit-propagation trace guard soundness for ay sequential-main SAT-COMP
-- RUP/LRAT-style UNSAT proof checking. Propositions model formula
-- fingerprints, proof-line digests, propagation trace digests, assignment
-- trails, watched-literal state, antecedent/reason maps, conflict or
-- empty-clause witnesses, checker transcripts, archive/build evidence,
-- fallback no-claim paths, audit transcripts, and fail-closed recompute
-- diagnostics.

def ay_uptg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_uptg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_uptg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_uptg_accepted_evidence
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (unitPropagationTraceDigest : Prop) (assignmentTrailDigest : Prop)
    (watchedLiteralStateDigest : Prop) (antecedentReasonMapDigest : Prop)
    (conflictEmptyClauseWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (checkerContextPreserved : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (originalFormulaFingerprint ->
      proofLineDigest ->
      unitPropagationTraceDigest ->
      assignmentTrailDigest ->
      watchedLiteralStateDigest ->
      antecedentReasonMapDigest ->
      conflictEmptyClauseWitness ->
      checkerTranscript ->
      checkerAccepted ->
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

def ay_uptg_trace_checker_path
    (unitPropagationTraceDigest : Prop)
    (conflictEmptyClauseWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (originalUnsat : Prop) :=
  ay_uptg_conj
    (ay_uptg_map unitPropagationTraceDigest conflictEmptyClauseWitness)
    (ay_uptg_conj
      (ay_uptg_map conflictEmptyClauseWitness checkerTranscript)
      (ay_uptg_conj
        (ay_uptg_map checkerTranscript checkerAccepted)
        (ay_uptg_map checkerAccepted originalUnsat)))

def ay_uptg_context_preservation
    (unitPropagationTraceDigest : Prop) (assignmentTrailDigest : Prop)
    (watchedLiteralStateDigest : Prop) (antecedentReasonMapDigest : Prop)
    (checkerContextPreserved : Prop) :=
  ay_uptg_conj
    (ay_uptg_map unitPropagationTraceDigest assignmentTrailDigest)
    (ay_uptg_conj
      (ay_uptg_map assignmentTrailDigest watchedLiteralStateDigest)
      (ay_uptg_conj
        (ay_uptg_map watchedLiteralStateDigest antecedentReasonMapDigest)
        (ay_uptg_map antecedentReasonMapDigest checkerContextPreserved)))

def ay_uptg_publication
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (unitPropagationTraceDigest : Prop) (assignmentTrailDigest : Prop)
    (watchedLiteralStateDigest : Prop) (antecedentReasonMapDigest : Prop)
    (conflictEmptyClauseWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (checkerContextPreserved : Prop)
    (originalUnsat : Prop) :=
  ay_uptg_conj
    (ay_uptg_accepted_evidence originalFormulaFingerprint proofLineDigest
      unitPropagationTraceDigest assignmentTrailDigest watchedLiteralStateDigest
      antecedentReasonMapDigest conflictEmptyClauseWitness checkerTranscript
      checkerAccepted archiveManifest archiveAccepted solverBuildEvidence
      buildAccepted fallbackNoClaim auditTranscript checkerContextPreserved
      originalUnsat)
    originalUnsat

def ay_uptg_failure_reason
    (proofLineMismatch : Prop) (traceMismatch : Prop)
    (trailMismatch : Prop) (watchMismatch : Prop)
    (antecedentMismatch : Prop) (conflictMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (proofLineMismatch -> result) ->
    (traceMismatch -> result) ->
    (trailMismatch -> result) ->
    (watchMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (conflictMismatch -> result) ->
    (checkerMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_uptg_bad_guard
    (proofLineMismatch : Prop) (traceMismatch : Prop)
    (trailMismatch : Prop) (watchMismatch : Prop)
    (antecedentMismatch : Prop) (conflictMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_uptg_conj
    (ay_uptg_conj noClaim recompute)
    (ay_uptg_failure_reason proofLineMismatch traceMismatch trailMismatch
      watchMismatch antecedentMismatch conflictMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch)

def ay_uptg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_uptg_disj noClaim (ay_uptg_disj originalUnsat publicSat)

theorem ay_uptg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_uptg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_uptg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_uptg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_uptg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_uptg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_uptg_build_accepted_evidence
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (unitPropagationTraceDigest : Prop) (assignmentTrailDigest : Prop)
    (watchedLiteralStateDigest : Prop) (antecedentReasonMapDigest : Prop)
    (conflictEmptyClauseWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (checkerContextPreserved : Prop)
    (originalUnsat : Prop) :
    originalFormulaFingerprint ->
    proofLineDigest ->
    unitPropagationTraceDigest ->
    assignmentTrailDigest ->
    watchedLiteralStateDigest ->
    antecedentReasonMapDigest ->
    conflictEmptyClauseWitness ->
    checkerTranscript ->
    checkerAccepted ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    fallbackNoClaim ->
    auditTranscript ->
    checkerContextPreserved ->
    originalUnsat ->
    ay_uptg_accepted_evidence originalFormulaFingerprint proofLineDigest
      unitPropagationTraceDigest assignmentTrailDigest watchedLiteralStateDigest
      antecedentReasonMapDigest conflictEmptyClauseWitness checkerTranscript
      checkerAccepted archiveManifest archiveAccepted solverBuildEvidence
      buildAccepted fallbackNoClaim auditTranscript checkerContextPreserved
      originalUnsat := by
  intro hFingerprint hLine hTrace hTrail hWatch hAntecedent hConflict
  intro hTranscript hChecker hArchive hArchiveAccepted hBuild hBuildAccepted
  intro hFallback hAudit hContext hOriginal result publish
  exact publish hFingerprint hLine hTrace hTrail hWatch hAntecedent hConflict
    hTranscript hChecker hArchive hArchiveAccepted hBuild hBuildAccepted
    hFallback hAudit hContext hOriginal

theorem ay_uptg_trace_replay_required_for_publication
    (unitPropagationTraceDigest : Prop)
    (conflictEmptyClauseWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (originalUnsat : Prop) :
    ay_uptg_trace_checker_path unitPropagationTraceDigest
      conflictEmptyClauseWitness checkerTranscript checkerAccepted
      originalUnsat ->
    unitPropagationTraceDigest ->
    originalUnsat := by
  intro path hTrace
  exact path originalUnsat
    (fun trace_to_conflict rest =>
      rest originalUnsat
        (fun conflict_to_transcript rest2 =>
          rest2 originalUnsat
            (fun transcript_to_checker checker_to_original =>
              checker_to_original
                (transcript_to_checker
                  (conflict_to_transcript
                    (trace_to_conflict hTrace)))))))

theorem ay_uptg_trace_context_preserved_for_checker
    (unitPropagationTraceDigest : Prop) (assignmentTrailDigest : Prop)
    (watchedLiteralStateDigest : Prop) (antecedentReasonMapDigest : Prop)
    (checkerContextPreserved : Prop) :
    ay_uptg_context_preservation unitPropagationTraceDigest
      assignmentTrailDigest watchedLiteralStateDigest antecedentReasonMapDigest
      checkerContextPreserved ->
    unitPropagationTraceDigest ->
    checkerContextPreserved := by
  intro preservation hTrace
  exact preservation checkerContextPreserved
    (fun trace_to_trail rest =>
      rest checkerContextPreserved
        (fun trail_to_watch rest2 =>
          rest2 checkerContextPreserved
            (fun watch_to_antecedent antecedent_to_context =>
              antecedent_to_context
                (watch_to_antecedent
                  (trail_to_watch
                    (trace_to_trail hTrace)))))))

theorem ay_uptg_conflict_witness_available
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (unitPropagationTraceDigest : Prop) (assignmentTrailDigest : Prop)
    (watchedLiteralStateDigest : Prop) (antecedentReasonMapDigest : Prop)
    (conflictEmptyClauseWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (checkerContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_uptg_accepted_evidence originalFormulaFingerprint proofLineDigest
      unitPropagationTraceDigest assignmentTrailDigest watchedLiteralStateDigest
      antecedentReasonMapDigest conflictEmptyClauseWitness checkerTranscript
      checkerAccepted archiveManifest archiveAccepted solverBuildEvidence
      buildAccepted fallbackNoClaim auditTranscript checkerContextPreserved
      originalUnsat ->
    conflictEmptyClauseWitness := by
  intro accepted
  exact accepted conflictEmptyClauseWitness
    (fun _hFingerprint _hLine _hTrace _hTrail _hWatch _hAntecedent hConflict
      _hTranscript _hChecker _hArchive _hArchiveAccepted _hBuild
      _hBuildAccepted _hFallback _hAudit _hContext _hOriginal =>
      hConflict)

theorem ay_uptg_checker_context_available
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (unitPropagationTraceDigest : Prop) (assignmentTrailDigest : Prop)
    (watchedLiteralStateDigest : Prop) (antecedentReasonMapDigest : Prop)
    (conflictEmptyClauseWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (checkerContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_uptg_accepted_evidence originalFormulaFingerprint proofLineDigest
      unitPropagationTraceDigest assignmentTrailDigest watchedLiteralStateDigest
      antecedentReasonMapDigest conflictEmptyClauseWitness checkerTranscript
      checkerAccepted archiveManifest archiveAccepted solverBuildEvidence
      buildAccepted fallbackNoClaim auditTranscript checkerContextPreserved
      originalUnsat ->
    checkerContextPreserved := by
  intro accepted
  exact accepted checkerContextPreserved
    (fun _hFingerprint _hLine _hTrace _hTrail _hWatch _hAntecedent _hConflict
      _hTranscript _hChecker _hArchive _hArchiveAccepted _hBuild
      _hBuildAccepted _hFallback _hAudit hContext _hOriginal =>
      hContext)

theorem ay_uptg_publication_sound
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (unitPropagationTraceDigest : Prop) (assignmentTrailDigest : Prop)
    (watchedLiteralStateDigest : Prop) (antecedentReasonMapDigest : Prop)
    (conflictEmptyClauseWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (checkerContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_uptg_publication originalFormulaFingerprint proofLineDigest
      unitPropagationTraceDigest assignmentTrailDigest watchedLiteralStateDigest
      antecedentReasonMapDigest conflictEmptyClauseWitness checkerTranscript
      checkerAccepted archiveManifest archiveAccepted solverBuildEvidence
      buildAccepted fallbackNoClaim auditTranscript checkerContextPreserved
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_uptg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_uptg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_uptg_disj_right noClaim (ay_uptg_disj originalUnsat publicSat)
    (ay_uptg_disj_left originalUnsat publicSat hUnsat)

theorem ay_uptg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_uptg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_uptg_disj_left noClaim
    (ay_uptg_disj originalUnsat publicSat) hNoClaim

theorem ay_uptg_bad_no_claim
    (proofLineMismatch : Prop) (traceMismatch : Prop)
    (trailMismatch : Prop) (watchMismatch : Prop)
    (antecedentMismatch : Prop) (conflictMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uptg_bad_guard proofLineMismatch traceMismatch trailMismatch
      watchMismatch antecedentMismatch conflictMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_uptg_bad_recompute
    (proofLineMismatch : Prop) (traceMismatch : Prop)
    (trailMismatch : Prop) (watchMismatch : Prop)
    (antecedentMismatch : Prop) (conflictMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uptg_bad_guard proofLineMismatch traceMismatch trailMismatch
      watchMismatch antecedentMismatch conflictMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_uptg_failed_guard_cannot_bless_unsat
    (proofLineMismatch : Prop) (traceMismatch : Prop)
    (trailMismatch : Prop) (watchMismatch : Prop)
    (antecedentMismatch : Prop) (conflictMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_uptg_bad_guard proofLineMismatch traceMismatch trailMismatch
      watchMismatch antecedentMismatch conflictMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    ay_uptg_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_uptg_bad_recompute proofLineMismatch traceMismatch trailMismatch
    watchMismatch antecedentMismatch conflictMismatch checkerMismatch
    archiveMismatch buildMismatch auditMismatch noClaim recompute bad

theorem ay_uptg_failure_forces_no_claim
    (proofLineMismatch : Prop) (traceMismatch : Prop)
    (trailMismatch : Prop) (watchMismatch : Prop)
    (antecedentMismatch : Prop) (conflictMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_uptg_failure_reason proofLineMismatch traceMismatch trailMismatch
      watchMismatch antecedentMismatch conflictMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch ->
    (proofLineMismatch -> noClaim) ->
    (traceMismatch -> noClaim) ->
    (trailMismatch -> noClaim) ->
    (watchMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (conflictMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason line_to_no_claim trace_to_no_claim trail_to_no_claim
  intro watch_to_no_claim antecedent_to_no_claim conflict_to_no_claim
  intro checker_to_no_claim archive_to_no_claim build_to_no_claim
  intro audit_to_no_claim
  exact reason noClaim line_to_no_claim trace_to_no_claim trail_to_no_claim
    watch_to_no_claim antecedent_to_no_claim conflict_to_no_claim
    checker_to_no_claim archive_to_no_claim build_to_no_claim
    audit_to_no_claim

theorem ay_uptg_proof_line_mismatch_forces_no_claim
    (proofLineMismatch noClaim : Prop) :
    proofLineMismatch ->
    (proofLineMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uptg_trace_mismatch_forces_no_claim
    (traceMismatch noClaim : Prop) :
    traceMismatch ->
    (traceMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uptg_trail_mismatch_forces_no_claim
    (trailMismatch noClaim : Prop) :
    trailMismatch ->
    (trailMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uptg_watch_mismatch_forces_no_claim
    (watchMismatch noClaim : Prop) :
    watchMismatch ->
    (watchMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uptg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch ->
    (antecedentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uptg_conflict_mismatch_forces_no_claim
    (conflictMismatch noClaim : Prop) :
    conflictMismatch ->
    (conflictMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uptg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uptg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uptg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uptg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
