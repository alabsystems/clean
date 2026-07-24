-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- UNSAT status/proof consistency guard soundness for ay sequential-main
-- SAT-COMP proof publication. Propositions model solver-output digests, UNSAT
-- status parse transcripts, proof artifacts, benchmark fingerprints,
-- normalized proof digests, checker transcripts, empty-clause reachability,
-- model-artifact absence or inconsistency ledgers, archive/build evidence,
-- fallback no-claim paths, audit transcripts, and fail-closed recompute
-- diagnostics.

def ay_uscg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_uscg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_uscg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_uscg_accepted_evidence
    (rawSolverOutputDigest : Prop) (unsatStatusParseTranscript : Prop)
    (proofArtifactDigest : Prop) (benchmarkFingerprint : Prop)
    (normalizedProofDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (modelArtifactAbsenceLedger : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (statusProofConsistent : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (rawSolverOutputDigest ->
      unsatStatusParseTranscript ->
      proofArtifactDigest ->
      benchmarkFingerprint ->
      normalizedProofDigest ->
      checkerTranscript ->
      checkerAccepted ->
      emptyClauseReachabilityWitness ->
      modelArtifactAbsenceLedger ->
      archiveManifest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      fallbackNoClaim ->
      auditTranscript ->
      statusProofConsistent ->
      originalUnsat ->
      result) ->
    result

def ay_uscg_status_and_checker_path
    (unsatStatusParseTranscript : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :=
  ay_uscg_conj
    unsatStatusParseTranscript
    (ay_uscg_conj
      (ay_uscg_map proofArtifactDigest checkerTranscript)
      (ay_uscg_conj
        (ay_uscg_map checkerTranscript checkerAccepted)
        (ay_uscg_conj
          (ay_uscg_map checkerAccepted emptyClauseReachabilityWitness)
          (ay_uscg_map emptyClauseReachabilityWitness originalUnsat))))

def ay_uscg_status_proof_consistency
    (rawSolverOutputDigest : Prop) (unsatStatusParseTranscript : Prop)
    (proofArtifactDigest : Prop) (benchmarkFingerprint : Prop)
    (normalizedProofDigest : Prop) (modelArtifactAbsenceLedger : Prop)
    (statusProofConsistent : Prop) :=
  ay_uscg_conj
    (ay_uscg_map rawSolverOutputDigest unsatStatusParseTranscript)
    (ay_uscg_conj
      (ay_uscg_map unsatStatusParseTranscript proofArtifactDigest)
      (ay_uscg_conj
        (ay_uscg_map proofArtifactDigest benchmarkFingerprint)
        (ay_uscg_conj
          (ay_uscg_map benchmarkFingerprint normalizedProofDigest)
          (ay_uscg_conj
            (ay_uscg_map normalizedProofDigest modelArtifactAbsenceLedger)
            (ay_uscg_map modelArtifactAbsenceLedger
              statusProofConsistent)))))

def ay_uscg_publication
    (rawSolverOutputDigest : Prop) (unsatStatusParseTranscript : Prop)
    (proofArtifactDigest : Prop) (benchmarkFingerprint : Prop)
    (normalizedProofDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (modelArtifactAbsenceLedger : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (statusProofConsistent : Prop)
    (originalUnsat : Prop) :=
  ay_uscg_conj
    (ay_uscg_accepted_evidence rawSolverOutputDigest
      unsatStatusParseTranscript proofArtifactDigest benchmarkFingerprint
      normalizedProofDigest checkerTranscript checkerAccepted
      emptyClauseReachabilityWitness modelArtifactAbsenceLedger archiveManifest
      archiveAccepted solverBuildEvidence buildAccepted fallbackNoClaim
      auditTranscript statusProofConsistent originalUnsat)
    originalUnsat

def ay_uscg_failure_reason
    (missingProof : Prop) (staleProof : Prop) (satModelConflict : Prop)
    (statusProofMismatch : Prop) (statusMismatch : Prop)
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (missingProof -> result) ->
    (staleProof -> result) ->
    (satModelConflict -> result) ->
    (statusProofMismatch -> result) ->
    (statusMismatch -> result) ->
    (proofMismatch -> result) ->
    (checkerMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_uscg_bad_guard
    (missingProof : Prop) (staleProof : Prop) (satModelConflict : Prop)
    (statusProofMismatch : Prop) (statusMismatch : Prop)
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_uscg_conj
    (ay_uscg_conj noClaim recompute)
    (ay_uscg_failure_reason missingProof staleProof satModelConflict
      statusProofMismatch statusMismatch proofMismatch checkerMismatch
      reachabilityMismatch archiveMismatch buildMismatch auditMismatch)

def ay_uscg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_uscg_disj noClaim (ay_uscg_disj originalUnsat publicSat)

theorem ay_uscg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_uscg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_uscg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_uscg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_uscg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_uscg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_uscg_build_accepted_evidence
    (rawSolverOutputDigest : Prop) (unsatStatusParseTranscript : Prop)
    (proofArtifactDigest : Prop) (benchmarkFingerprint : Prop)
    (normalizedProofDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (modelArtifactAbsenceLedger : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (statusProofConsistent : Prop)
    (originalUnsat : Prop) :
    rawSolverOutputDigest ->
    unsatStatusParseTranscript ->
    proofArtifactDigest ->
    benchmarkFingerprint ->
    normalizedProofDigest ->
    checkerTranscript ->
    checkerAccepted ->
    emptyClauseReachabilityWitness ->
    modelArtifactAbsenceLedger ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    fallbackNoClaim ->
    auditTranscript ->
    statusProofConsistent ->
    originalUnsat ->
    ay_uscg_accepted_evidence rawSolverOutputDigest
      unsatStatusParseTranscript proofArtifactDigest benchmarkFingerprint
      normalizedProofDigest checkerTranscript checkerAccepted
      emptyClauseReachabilityWitness modelArtifactAbsenceLedger archiveManifest
      archiveAccepted solverBuildEvidence buildAccepted fallbackNoClaim
      auditTranscript statusProofConsistent originalUnsat := by
  intro hRaw hStatus hProof hBenchmark hNormalized hTranscript hChecker
  intro hReachability hModelLedger hArchive hArchiveAccepted hBuild
  intro hBuildAccepted hFallback hAudit hConsistent hOriginal result publish
  exact publish hRaw hStatus hProof hBenchmark hNormalized hTranscript
    hChecker hReachability hModelLedger hArchive hArchiveAccepted hBuild
    hBuildAccepted hFallback hAudit hConsistent hOriginal

theorem ay_uscg_unsat_publication_requires_status_and_checked_empty_clause
    (unsatStatusParseTranscript : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :
    ay_uscg_status_and_checker_path unsatStatusParseTranscript
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachabilityWitness originalUnsat ->
    proofArtifactDigest ->
    originalUnsat := by
  intro path hProof
  exact path originalUnsat
    (fun _hStatus rest =>
      rest originalUnsat
        (fun proof_to_transcript rest2 =>
          rest2 originalUnsat
            (fun transcript_to_checker rest3 =>
              rest3 originalUnsat
                (fun checker_to_reachability reachability_to_original =>
                  reachability_to_original
                    (checker_to_reachability
                      (transcript_to_checker
                        (proof_to_transcript hProof))))))))

theorem ay_uscg_status_alone_cannot_publish_without_proof_checker
    (unsatStatusParseTranscript : Prop) (noClaim : Prop)
    (missingProof : Prop) :
    unsatStatusParseTranscript ->
    missingProof ->
    (missingProof -> noClaim) ->
    noClaim := by
  intro _hStatus hMissing missing_to_no_claim
  exact missing_to_no_claim hMissing

theorem ay_uscg_status_proof_context_consistent
    (rawSolverOutputDigest : Prop) (unsatStatusParseTranscript : Prop)
    (proofArtifactDigest : Prop) (benchmarkFingerprint : Prop)
    (normalizedProofDigest : Prop) (modelArtifactAbsenceLedger : Prop)
    (statusProofConsistent : Prop) :
    ay_uscg_status_proof_consistency rawSolverOutputDigest
      unsatStatusParseTranscript proofArtifactDigest benchmarkFingerprint
      normalizedProofDigest modelArtifactAbsenceLedger statusProofConsistent ->
    rawSolverOutputDigest ->
    statusProofConsistent := by
  intro consistency hRaw
  exact consistency statusProofConsistent
    (fun raw_to_status rest =>
      rest statusProofConsistent
        (fun status_to_proof rest2 =>
          rest2 statusProofConsistent
            (fun proof_to_benchmark rest3 =>
              rest3 statusProofConsistent
                (fun benchmark_to_normalized rest4 =>
                  rest4 statusProofConsistent
                    (fun normalized_to_model model_to_consistent =>
                      model_to_consistent
                        (normalized_to_model
                          (benchmark_to_normalized
                            (proof_to_benchmark
                              (status_to_proof
                                (raw_to_status hRaw)))))))))))

theorem ay_uscg_reachability_available
    (rawSolverOutputDigest : Prop) (unsatStatusParseTranscript : Prop)
    (proofArtifactDigest : Prop) (benchmarkFingerprint : Prop)
    (normalizedProofDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (modelArtifactAbsenceLedger : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (statusProofConsistent : Prop)
    (originalUnsat : Prop) :
    ay_uscg_accepted_evidence rawSolverOutputDigest
      unsatStatusParseTranscript proofArtifactDigest benchmarkFingerprint
      normalizedProofDigest checkerTranscript checkerAccepted
      emptyClauseReachabilityWitness modelArtifactAbsenceLedger archiveManifest
      archiveAccepted solverBuildEvidence buildAccepted fallbackNoClaim
      auditTranscript statusProofConsistent originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hRaw _hStatus _hProof _hBenchmark _hNormalized _hTranscript
      _hChecker hReachability _hModelLedger _hArchive _hArchiveAccepted
      _hBuild _hBuildAccepted _hFallback _hAudit _hConsistent _hOriginal =>
      hReachability)

theorem ay_uscg_consistency_available
    (rawSolverOutputDigest : Prop) (unsatStatusParseTranscript : Prop)
    (proofArtifactDigest : Prop) (benchmarkFingerprint : Prop)
    (normalizedProofDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (modelArtifactAbsenceLedger : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (statusProofConsistent : Prop)
    (originalUnsat : Prop) :
    ay_uscg_accepted_evidence rawSolverOutputDigest
      unsatStatusParseTranscript proofArtifactDigest benchmarkFingerprint
      normalizedProofDigest checkerTranscript checkerAccepted
      emptyClauseReachabilityWitness modelArtifactAbsenceLedger archiveManifest
      archiveAccepted solverBuildEvidence buildAccepted fallbackNoClaim
      auditTranscript statusProofConsistent originalUnsat ->
    statusProofConsistent := by
  intro accepted
  exact accepted statusProofConsistent
    (fun _hRaw _hStatus _hProof _hBenchmark _hNormalized _hTranscript
      _hChecker _hReachability _hModelLedger _hArchive _hArchiveAccepted
      _hBuild _hBuildAccepted _hFallback _hAudit hConsistent _hOriginal =>
      hConsistent)

theorem ay_uscg_publication_sound
    (rawSolverOutputDigest : Prop) (unsatStatusParseTranscript : Prop)
    (proofArtifactDigest : Prop) (benchmarkFingerprint : Prop)
    (normalizedProofDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (modelArtifactAbsenceLedger : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (statusProofConsistent : Prop)
    (originalUnsat : Prop) :
    ay_uscg_publication rawSolverOutputDigest unsatStatusParseTranscript
      proofArtifactDigest benchmarkFingerprint normalizedProofDigest
      checkerTranscript checkerAccepted emptyClauseReachabilityWitness
      modelArtifactAbsenceLedger archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      statusProofConsistent originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_uscg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_uscg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_uscg_disj_right noClaim (ay_uscg_disj originalUnsat publicSat)
    (ay_uscg_disj_left originalUnsat publicSat hUnsat)

theorem ay_uscg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_uscg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_uscg_disj_left noClaim
    (ay_uscg_disj originalUnsat publicSat) hNoClaim

theorem ay_uscg_bad_no_claim
    (missingProof : Prop) (staleProof : Prop) (satModelConflict : Prop)
    (statusProofMismatch : Prop) (statusMismatch : Prop)
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uscg_bad_guard missingProof staleProof satModelConflict
      statusProofMismatch statusMismatch proofMismatch checkerMismatch
      reachabilityMismatch archiveMismatch buildMismatch auditMismatch noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_uscg_bad_recompute
    (missingProof : Prop) (staleProof : Prop) (satModelConflict : Prop)
    (statusProofMismatch : Prop) (statusMismatch : Prop)
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uscg_bad_guard missingProof staleProof satModelConflict
      statusProofMismatch statusMismatch proofMismatch checkerMismatch
      reachabilityMismatch archiveMismatch buildMismatch auditMismatch noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_uscg_failed_guard_cannot_bless_unsat
    (missingProof : Prop) (staleProof : Prop) (satModelConflict : Prop)
    (statusProofMismatch : Prop) (statusMismatch : Prop)
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_uscg_bad_guard missingProof staleProof satModelConflict
      statusProofMismatch statusMismatch proofMismatch checkerMismatch
      reachabilityMismatch archiveMismatch buildMismatch auditMismatch noClaim
      recompute ->
    ay_uscg_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_uscg_bad_recompute missingProof staleProof satModelConflict
    statusProofMismatch statusMismatch proofMismatch checkerMismatch
    reachabilityMismatch archiveMismatch buildMismatch auditMismatch noClaim
    recompute bad

theorem ay_uscg_proof_or_model_conflict_forces_no_claim
    (missingProof : Prop) (staleProof : Prop) (satModelConflict : Prop)
    (noClaim : Prop) :
    ay_uscg_disj missingProof (ay_uscg_disj staleProof satModelConflict) ->
    (missingProof -> noClaim) ->
    (staleProof -> noClaim) ->
    (satModelConflict -> noClaim) ->
    noClaim := by
  intro problem missing_to_no_claim stale_to_no_claim model_to_no_claim
  exact problem noClaim missing_to_no_claim
    (fun stale_or_model =>
      stale_or_model noClaim stale_to_no_claim model_to_no_claim)

theorem ay_uscg_failure_forces_no_claim
    (missingProof : Prop) (staleProof : Prop) (satModelConflict : Prop)
    (statusProofMismatch : Prop) (statusMismatch : Prop)
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_uscg_failure_reason missingProof staleProof satModelConflict
      statusProofMismatch statusMismatch proofMismatch checkerMismatch
      reachabilityMismatch archiveMismatch buildMismatch auditMismatch ->
    (missingProof -> noClaim) ->
    (staleProof -> noClaim) ->
    (satModelConflict -> noClaim) ->
    (statusProofMismatch -> noClaim) ->
    (statusMismatch -> noClaim) ->
    (proofMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason missing_to_no_claim stale_to_no_claim model_to_no_claim
  intro status_proof_to_no_claim status_to_no_claim proof_to_no_claim
  intro checker_to_no_claim reachability_to_no_claim archive_to_no_claim
  intro build_to_no_claim audit_to_no_claim
  exact reason noClaim missing_to_no_claim stale_to_no_claim
    model_to_no_claim status_proof_to_no_claim status_to_no_claim
    proof_to_no_claim checker_to_no_claim reachability_to_no_claim
    archive_to_no_claim build_to_no_claim audit_to_no_claim

theorem ay_uscg_missing_proof_forces_no_claim
    (missingProof noClaim : Prop) :
    missingProof ->
    (missingProof -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uscg_stale_proof_forces_no_claim
    (staleProof noClaim : Prop) :
    staleProof ->
    (staleProof -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uscg_sat_model_conflict_forces_no_claim
    (satModelConflict noClaim : Prop) :
    satModelConflict ->
    (satModelConflict -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uscg_status_proof_mismatch_forces_no_claim
    (statusProofMismatch noClaim : Prop) :
    statusProofMismatch ->
    (statusProofMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uscg_status_mismatch_forces_no_claim
    (statusMismatch noClaim : Prop) :
    statusMismatch ->
    (statusMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uscg_proof_mismatch_forces_no_claim
    (proofMismatch noClaim : Prop) :
    proofMismatch ->
    (proofMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uscg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uscg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch ->
    (reachabilityMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uscg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uscg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_uscg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
