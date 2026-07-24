-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- UNSAT proof-core trimming guard soundness for ay sequential-main SAT-COMP
-- certificates. Propositions model formula fingerprints, raw and trimmed
-- proof digests, dependency graphs, empty-clause reachability, retained-line
-- ledgers, line-renumbering and antecedent maps, checker replay transcripts,
-- archives, build evidence, fallback no-claim paths, audit transcripts, and
-- fail-closed recompute diagnostics.

def ay_ctg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_ctg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_ctg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_ctg_accepted_evidence
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (trimmedProofDigest : Prop) (dependencyGraphDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (retainedLineLedger : Prop)
    (lineRenumberingMapDigest : Prop) (antecedentMapDigest : Prop)
    (checkerReplayTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (antecedentContextPreserved : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (originalFormulaFingerprint ->
      rawProofDigest ->
      trimmedProofDigest ->
      dependencyGraphDigest ->
      emptyClauseReachabilityWitness ->
      retainedLineLedger ->
      lineRenumberingMapDigest ->
      antecedentMapDigest ->
      checkerReplayTranscript ->
      checkerAccepted ->
      archiveManifest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      fallbackNoClaim ->
      auditTranscript ->
      antecedentContextPreserved ->
      originalUnsat ->
      result) ->
    result

def ay_ctg_trimmed_checker_path
    (trimmedProofDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerReplayTranscript : Prop) (checkerAccepted : Prop)
    (originalUnsat : Prop) :=
  ay_ctg_conj
    (ay_ctg_map trimmedProofDigest emptyClauseReachabilityWitness)
    (ay_ctg_conj
      (ay_ctg_map emptyClauseReachabilityWitness checkerReplayTranscript)
      (ay_ctg_conj
        (ay_ctg_map checkerReplayTranscript checkerAccepted)
        (ay_ctg_map checkerAccepted originalUnsat)))

def ay_ctg_context_preservation
    (dependencyGraphDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (retainedLineLedger : Prop) (lineRenumberingMapDigest : Prop)
    (antecedentMapDigest : Prop) (antecedentContextPreserved : Prop) :=
  ay_ctg_conj
    (ay_ctg_map dependencyGraphDigest emptyClauseReachabilityWitness)
    (ay_ctg_conj
      (ay_ctg_map emptyClauseReachabilityWitness retainedLineLedger)
      (ay_ctg_conj
        (ay_ctg_map retainedLineLedger lineRenumberingMapDigest)
        (ay_ctg_conj
          (ay_ctg_map lineRenumberingMapDigest antecedentMapDigest)
          (ay_ctg_map antecedentMapDigest antecedentContextPreserved))))

def ay_ctg_publication
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (trimmedProofDigest : Prop) (dependencyGraphDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (retainedLineLedger : Prop)
    (lineRenumberingMapDigest : Prop) (antecedentMapDigest : Prop)
    (checkerReplayTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (antecedentContextPreserved : Prop) (originalUnsat : Prop) :=
  ay_ctg_conj
    (ay_ctg_accepted_evidence originalFormulaFingerprint rawProofDigest
      trimmedProofDigest dependencyGraphDigest emptyClauseReachabilityWitness
      retainedLineLedger lineRenumberingMapDigest antecedentMapDigest
      checkerReplayTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      antecedentContextPreserved originalUnsat)
    originalUnsat

def ay_ctg_failure_reason
    (rawMismatch : Prop) (trimmedMismatch : Prop)
    (dependencyMismatch : Prop) (reachabilityMismatch : Prop)
    (retainedLineMismatch : Prop) (renumberingMismatch : Prop)
    (antecedentMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (rawMismatch -> result) ->
    (trimmedMismatch -> result) ->
    (dependencyMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (retainedLineMismatch -> result) ->
    (renumberingMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (checkerMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_ctg_bad_guard
    (rawMismatch : Prop) (trimmedMismatch : Prop)
    (dependencyMismatch : Prop) (reachabilityMismatch : Prop)
    (retainedLineMismatch : Prop) (renumberingMismatch : Prop)
    (antecedentMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_ctg_conj
    (ay_ctg_conj noClaim recompute)
    (ay_ctg_failure_reason rawMismatch trimmedMismatch dependencyMismatch
      reachabilityMismatch retainedLineMismatch renumberingMismatch
      antecedentMismatch checkerMismatch archiveMismatch buildMismatch
      auditMismatch)

def ay_ctg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_ctg_disj noClaim (ay_ctg_disj originalUnsat publicSat)

theorem ay_ctg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_ctg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_ctg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_ctg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_ctg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_ctg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_ctg_build_accepted_evidence
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (trimmedProofDigest : Prop) (dependencyGraphDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (retainedLineLedger : Prop)
    (lineRenumberingMapDigest : Prop) (antecedentMapDigest : Prop)
    (checkerReplayTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (antecedentContextPreserved : Prop) (originalUnsat : Prop) :
    originalFormulaFingerprint ->
    rawProofDigest ->
    trimmedProofDigest ->
    dependencyGraphDigest ->
    emptyClauseReachabilityWitness ->
    retainedLineLedger ->
    lineRenumberingMapDigest ->
    antecedentMapDigest ->
    checkerReplayTranscript ->
    checkerAccepted ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    fallbackNoClaim ->
    auditTranscript ->
    antecedentContextPreserved ->
    originalUnsat ->
    ay_ctg_accepted_evidence originalFormulaFingerprint rawProofDigest
      trimmedProofDigest dependencyGraphDigest emptyClauseReachabilityWitness
      retainedLineLedger lineRenumberingMapDigest antecedentMapDigest
      checkerReplayTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      antecedentContextPreserved originalUnsat := by
  intro hFingerprint hRaw hTrimmed hDependency hReachability hRetained
  intro hRenumbering hAntecedent hTranscript hChecker hArchive
  intro hArchiveAccepted hBuild hBuildAccepted hFallback hAudit hContext
  intro hOriginal result publish
  exact publish hFingerprint hRaw hTrimmed hDependency hReachability
    hRetained hRenumbering hAntecedent hTranscript hChecker hArchive
    hArchiveAccepted hBuild hBuildAccepted hFallback hAudit hContext
    hOriginal

theorem ay_ctg_trimmed_publication_requires_checker_replay
    (trimmedProofDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerReplayTranscript : Prop) (checkerAccepted : Prop)
    (originalUnsat : Prop) :
    ay_ctg_trimmed_checker_path trimmedProofDigest
      emptyClauseReachabilityWitness checkerReplayTranscript checkerAccepted
      originalUnsat ->
    trimmedProofDigest ->
    originalUnsat := by
  intro path hTrimmed
  exact path originalUnsat
    (fun trimmed_to_reachability rest =>
      rest originalUnsat
        (fun reachability_to_transcript rest2 =>
          rest2 originalUnsat
            (fun transcript_to_checker checker_to_original =>
              checker_to_original
                (transcript_to_checker
                  (reachability_to_transcript
                    (trimmed_to_reachability hTrimmed)))))))

theorem ay_ctg_reachability_renumbering_preserve_antecedents
    (dependencyGraphDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (retainedLineLedger : Prop) (lineRenumberingMapDigest : Prop)
    (antecedentMapDigest : Prop) (antecedentContextPreserved : Prop) :
    ay_ctg_context_preservation dependencyGraphDigest
      emptyClauseReachabilityWitness retainedLineLedger
      lineRenumberingMapDigest antecedentMapDigest
      antecedentContextPreserved ->
    dependencyGraphDigest ->
    antecedentContextPreserved := by
  intro preservation hDependency
  exact preservation antecedentContextPreserved
    (fun dependency_to_reachability rest =>
      rest antecedentContextPreserved
        (fun reachability_to_retained rest2 =>
          rest2 antecedentContextPreserved
            (fun retained_to_renumbering rest3 =>
              rest3 antecedentContextPreserved
                (fun renumbering_to_antecedent antecedent_to_context =>
                  antecedent_to_context
                    (renumbering_to_antecedent
                      (retained_to_renumbering
                        (reachability_to_retained
                          (dependency_to_reachability hDependency)))))))))

theorem ay_ctg_checker_replay_transcript
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (trimmedProofDigest : Prop) (dependencyGraphDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (retainedLineLedger : Prop)
    (lineRenumberingMapDigest : Prop) (antecedentMapDigest : Prop)
    (checkerReplayTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (antecedentContextPreserved : Prop) (originalUnsat : Prop) :
    ay_ctg_accepted_evidence originalFormulaFingerprint rawProofDigest
      trimmedProofDigest dependencyGraphDigest emptyClauseReachabilityWitness
      retainedLineLedger lineRenumberingMapDigest antecedentMapDigest
      checkerReplayTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      antecedentContextPreserved originalUnsat ->
    checkerReplayTranscript := by
  intro accepted
  exact accepted checkerReplayTranscript
    (fun _hFingerprint _hRaw _hTrimmed _hDependency _hReachability
      _hRetained _hRenumbering _hAntecedent hTranscript _hChecker _hArchive
      _hArchiveAccepted _hBuild _hBuildAccepted _hFallback _hAudit
      _hContext _hOriginal =>
      hTranscript)

theorem ay_ctg_antecedent_context_preserved
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (trimmedProofDigest : Prop) (dependencyGraphDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (retainedLineLedger : Prop)
    (lineRenumberingMapDigest : Prop) (antecedentMapDigest : Prop)
    (checkerReplayTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (antecedentContextPreserved : Prop) (originalUnsat : Prop) :
    ay_ctg_accepted_evidence originalFormulaFingerprint rawProofDigest
      trimmedProofDigest dependencyGraphDigest emptyClauseReachabilityWitness
      retainedLineLedger lineRenumberingMapDigest antecedentMapDigest
      checkerReplayTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      antecedentContextPreserved originalUnsat ->
    antecedentContextPreserved := by
  intro accepted
  exact accepted antecedentContextPreserved
    (fun _hFingerprint _hRaw _hTrimmed _hDependency _hReachability
      _hRetained _hRenumbering _hAntecedent _hTranscript _hChecker _hArchive
      _hArchiveAccepted _hBuild _hBuildAccepted _hFallback _hAudit hContext
      _hOriginal =>
      hContext)

theorem ay_ctg_publication_sound
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (trimmedProofDigest : Prop) (dependencyGraphDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (retainedLineLedger : Prop)
    (lineRenumberingMapDigest : Prop) (antecedentMapDigest : Prop)
    (checkerReplayTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (antecedentContextPreserved : Prop) (originalUnsat : Prop) :
    ay_ctg_publication originalFormulaFingerprint rawProofDigest
      trimmedProofDigest dependencyGraphDigest emptyClauseReachabilityWitness
      retainedLineLedger lineRenumberingMapDigest antecedentMapDigest
      checkerReplayTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      antecedentContextPreserved originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_ctg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_ctg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_ctg_disj_right noClaim (ay_ctg_disj originalUnsat publicSat)
    (ay_ctg_disj_left originalUnsat publicSat hUnsat)

theorem ay_ctg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_ctg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_ctg_disj_left noClaim
    (ay_ctg_disj originalUnsat publicSat) hNoClaim

theorem ay_ctg_bad_no_claim
    (rawMismatch : Prop) (trimmedMismatch : Prop)
    (dependencyMismatch : Prop) (reachabilityMismatch : Prop)
    (retainedLineMismatch : Prop) (renumberingMismatch : Prop)
    (antecedentMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ctg_bad_guard rawMismatch trimmedMismatch dependencyMismatch
      reachabilityMismatch retainedLineMismatch renumberingMismatch
      antecedentMismatch checkerMismatch archiveMismatch buildMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_ctg_bad_recompute
    (rawMismatch : Prop) (trimmedMismatch : Prop)
    (dependencyMismatch : Prop) (reachabilityMismatch : Prop)
    (retainedLineMismatch : Prop) (renumberingMismatch : Prop)
    (antecedentMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ctg_bad_guard rawMismatch trimmedMismatch dependencyMismatch
      reachabilityMismatch retainedLineMismatch renumberingMismatch
      antecedentMismatch checkerMismatch archiveMismatch buildMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_ctg_failed_guard_cannot_bless_unsat
    (rawMismatch : Prop) (trimmedMismatch : Prop)
    (dependencyMismatch : Prop) (reachabilityMismatch : Prop)
    (retainedLineMismatch : Prop) (renumberingMismatch : Prop)
    (antecedentMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_ctg_bad_guard rawMismatch trimmedMismatch dependencyMismatch
      reachabilityMismatch retainedLineMismatch renumberingMismatch
      antecedentMismatch checkerMismatch archiveMismatch buildMismatch
      auditMismatch noClaim recompute ->
    ay_ctg_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_ctg_bad_recompute rawMismatch trimmedMismatch dependencyMismatch
    reachabilityMismatch retainedLineMismatch renumberingMismatch
    antecedentMismatch checkerMismatch archiveMismatch buildMismatch
    auditMismatch noClaim recompute bad

theorem ay_ctg_failure_forces_no_claim
    (rawMismatch : Prop) (trimmedMismatch : Prop)
    (dependencyMismatch : Prop) (reachabilityMismatch : Prop)
    (retainedLineMismatch : Prop) (renumberingMismatch : Prop)
    (antecedentMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_ctg_failure_reason rawMismatch trimmedMismatch dependencyMismatch
      reachabilityMismatch retainedLineMismatch renumberingMismatch
      antecedentMismatch checkerMismatch archiveMismatch buildMismatch
      auditMismatch ->
    (rawMismatch -> noClaim) ->
    (trimmedMismatch -> noClaim) ->
    (dependencyMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (retainedLineMismatch -> noClaim) ->
    (renumberingMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason raw_to_no_claim trimmed_to_no_claim dependency_to_no_claim
  intro reachability_to_no_claim retained_to_no_claim renumbering_to_no_claim
  intro antecedent_to_no_claim checker_to_no_claim archive_to_no_claim
  intro build_to_no_claim audit_to_no_claim
  exact reason noClaim raw_to_no_claim trimmed_to_no_claim
    dependency_to_no_claim reachability_to_no_claim retained_to_no_claim
    renumbering_to_no_claim antecedent_to_no_claim checker_to_no_claim
    archive_to_no_claim build_to_no_claim audit_to_no_claim

theorem ay_ctg_raw_mismatch_forces_no_claim
    (rawMismatch noClaim : Prop) :
    rawMismatch ->
    (rawMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ctg_trimmed_mismatch_forces_no_claim
    (trimmedMismatch noClaim : Prop) :
    trimmedMismatch ->
    (trimmedMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ctg_dependency_mismatch_forces_no_claim
    (dependencyMismatch noClaim : Prop) :
    dependencyMismatch ->
    (dependencyMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ctg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch ->
    (reachabilityMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ctg_retained_line_mismatch_forces_no_claim
    (retainedLineMismatch noClaim : Prop) :
    retainedLineMismatch ->
    (retainedLineMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ctg_renumbering_mismatch_forces_no_claim
    (renumberingMismatch noClaim : Prop) :
    renumberingMismatch ->
    (renumberingMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ctg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch ->
    (antecedentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ctg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ctg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ctg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ctg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
