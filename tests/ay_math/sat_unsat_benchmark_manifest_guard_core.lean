-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT benchmark-manifest guard soundness for ay sequential-main
-- SAT-COMP publication. Propositions stand for benchmark manifests, formula
-- fingerprints, proof artifact digests, checker transcripts, empty-clause
-- reachability, solver build evidence, submission manifests, archive
-- manifests, audit transcripts, and fail-closed no-claim/recompute
-- diagnostics.

def AyUBMGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUBMGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUBMGMap (source : Prop) (target : Prop) :=
  source -> target

def AyUBMGAcceptedEvidence
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (benchmarkManifest ->
      formulaFingerprint ->
      fingerprintAccepted ->
      proofArtifactDigest ->
      checkerTranscript ->
      checkerAccepted ->
      emptyClauseReachable ->
      solverBuildEvidence ->
      buildAccepted ->
      submissionManifest ->
      archiveManifest ->
      auditTranscript ->
      visibleUnsat ->
      originalUnsat ->
      result) ->
    result

def AyUBMGBenchmarkCertificate
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (proofArtifactDigest : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop) :=
  AyUBMGConj benchmarkManifest
    (AyUBMGConj formulaFingerprint
      (AyUBMGConj proofArtifactDigest
        (AyUBMGConj submissionManifest
          (AyUBMGConj archiveManifest auditTranscript))))

def AyUBMGReplayGuard
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (submissionManifest : Prop) :=
  AyUBMGConj
    (AyUBMGMap benchmarkManifest formulaFingerprint)
    (AyUBMGConj
      (AyUBMGMap formulaFingerprint proofArtifactDigest)
      (AyUBMGConj
        (AyUBMGMap proofArtifactDigest submissionManifest)
        (AyUBMGConj
          (AyUBMGMap submissionManifest emptyClauseReachable)
          (AyUBMGMap checkerTranscript checkerAccepted))))

def AyUBMGPublication
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUBMGConj
    (AyUBMGAcceptedEvidence benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript
      checkerAccepted emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat)
    originalUnsat

def AyUBMGFailureReason
    (benchmarkFailure : Prop) (fingerprintFailure : Prop)
    (proofFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (buildFailure : Prop)
    (submissionFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) :=
  forall result : Prop,
    (benchmarkFailure -> result) ->
    (fingerprintFailure -> result) ->
    (proofFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (buildFailure -> result) ->
    (submissionFailure -> result) ->
    (archiveFailure -> result) ->
    (auditFailure -> result) ->
    result

def AyUBMGBadBenchmarkAgreement
    (benchmarkFailure : Prop) (fingerprintFailure : Prop)
    (proofFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (buildFailure : Prop)
    (submissionFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUBMGConj
    (AyUBMGConj noClaim recompute)
    (AyUBMGFailureReason benchmarkFailure fingerprintFailure proofFailure
      checkerFailure emptyClauseFailure buildFailure submissionFailure
      archiveFailure auditFailure)

def AyUBMGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUBMGDisj noClaim originalUnsat

theorem ay_ubmg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUBMGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_ubmg_conj_left
    (p : Prop) (q : Prop) :
    AyUBMGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ubmg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUBMGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_ubmg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUBMGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_ubmg_accepted_evidence
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    benchmarkManifest ->
    formulaFingerprint ->
    fingerprintAccepted ->
    proofArtifactDigest ->
    checkerTranscript ->
    checkerAccepted ->
    emptyClauseReachable ->
    solverBuildEvidence ->
    buildAccepted ->
    submissionManifest ->
    archiveManifest ->
    auditTranscript ->
    visibleUnsat ->
    originalUnsat ->
    AyUBMGAcceptedEvidence benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript
      checkerAccepted emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat := by
  intro hBenchmark hFingerprint hFingerprintAccepted hProof hTranscript
  intro hChecker hEmpty hBuild hBuildAccepted hSubmission hArchive hAudit
  intro hVisible hOriginal result publish
  exact publish hBenchmark hFingerprint hFingerprintAccepted hProof
    hTranscript hChecker hEmpty hBuild hBuildAccepted hSubmission hArchive
    hAudit hVisible hOriginal

theorem ay_ubmg_benchmark_manifest
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBMGAcceptedEvidence benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript
      checkerAccepted emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    benchmarkManifest := by
  intro accepted
  exact accepted benchmarkManifest
    (fun hBenchmark _hFingerprint _hFingerprintAccepted _hProof _hTranscript
      _hChecker _hEmpty _hBuild _hBuildAccepted _hSubmission _hArchive _hAudit
      _hVisible _hOriginal => hBenchmark)

theorem ay_ubmg_formula_fingerprint
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBMGAcceptedEvidence benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript
      checkerAccepted emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    formulaFingerprint := by
  intro accepted
  exact accepted formulaFingerprint
    (fun _hBenchmark hFingerprint _hFingerprintAccepted _hProof _hTranscript
      _hChecker _hEmpty _hBuild _hBuildAccepted _hSubmission _hArchive _hAudit
      _hVisible _hOriginal => hFingerprint)

theorem ay_ubmg_fingerprint_accepted
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBMGAcceptedEvidence benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript
      checkerAccepted emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    fingerprintAccepted := by
  intro accepted
  exact accepted fingerprintAccepted
    (fun _hBenchmark _hFingerprint hFingerprintAccepted _hProof _hTranscript
      _hChecker _hEmpty _hBuild _hBuildAccepted _hSubmission _hArchive _hAudit
      _hVisible _hOriginal => hFingerprintAccepted)

theorem ay_ubmg_proof_artifact_digest
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBMGAcceptedEvidence benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript
      checkerAccepted emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    proofArtifactDigest := by
  intro accepted
  exact accepted proofArtifactDigest
    (fun _hBenchmark _hFingerprint _hFingerprintAccepted hProof _hTranscript
      _hChecker _hEmpty _hBuild _hBuildAccepted _hSubmission _hArchive _hAudit
      _hVisible _hOriginal => hProof)

theorem ay_ubmg_checker_transcript
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBMGAcceptedEvidence benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript
      checkerAccepted emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hBenchmark _hFingerprint _hFingerprintAccepted _hProof hTranscript
      _hChecker _hEmpty _hBuild _hBuildAccepted _hSubmission _hArchive _hAudit
      _hVisible _hOriginal => hTranscript)

theorem ay_ubmg_checker_accepted
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBMGAcceptedEvidence benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript
      checkerAccepted emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hBenchmark _hFingerprint _hFingerprintAccepted _hProof _hTranscript
      hChecker _hEmpty _hBuild _hBuildAccepted _hSubmission _hArchive _hAudit
      _hVisible _hOriginal => hChecker)

theorem ay_ubmg_empty_clause_reachable
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBMGAcceptedEvidence benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript
      checkerAccepted emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hBenchmark _hFingerprint _hFingerprintAccepted _hProof _hTranscript
      _hChecker hEmpty _hBuild _hBuildAccepted _hSubmission _hArchive _hAudit
      _hVisible _hOriginal => hEmpty)

theorem ay_ubmg_submission_manifest
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBMGAcceptedEvidence benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript
      checkerAccepted emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    submissionManifest := by
  intro accepted
  exact accepted submissionManifest
    (fun _hBenchmark _hFingerprint _hFingerprintAccepted _hProof _hTranscript
      _hChecker _hEmpty _hBuild _hBuildAccepted hSubmission _hArchive _hAudit
      _hVisible _hOriginal => hSubmission)

theorem ay_ubmg_original_unsat
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBMGAcceptedEvidence benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript
      checkerAccepted emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hBenchmark _hFingerprint _hFingerprintAccepted _hProof _hTranscript
      _hChecker _hEmpty _hBuild _hBuildAccepted _hSubmission _hArchive _hAudit
      _hVisible hOriginal => hOriginal)

theorem ay_ubmg_publication_sound
    (benchmarkManifest : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (proofArtifactDigest : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (submissionManifest : Prop)
    (archiveManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBMGPublication benchmarkManifest formulaFingerprint
      fingerprintAccepted proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable solverBuildEvidence buildAccepted
      submissionManifest archiveManifest auditTranscript visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted unsat => unsat)

theorem ay_ubmg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUBMGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ubmg_disj_right noClaim originalUnsat unsat

theorem ay_ubmg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUBMGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ubmg_disj_left noClaim originalUnsat no_claim

theorem ay_ubmg_bad_no_claim
    (benchmarkFailure : Prop) (fingerprintFailure : Prop)
    (proofFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (buildFailure : Prop)
    (submissionFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUBMGBadBenchmarkAgreement benchmarkFailure fingerprintFailure
      proofFailure checkerFailure emptyClauseFailure buildFailure
      submissionFailure archiveFailure auditFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_ubmg_bad_recompute
    (benchmarkFailure : Prop) (fingerprintFailure : Prop)
    (proofFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (buildFailure : Prop)
    (submissionFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUBMGBadBenchmarkAgreement benchmarkFailure fingerprintFailure
      proofFailure checkerFailure emptyClauseFailure buildFailure
      submissionFailure archiveFailure auditFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_ubmg_failed_benchmark_agreement_cannot_bless_unsat
    (benchmarkFailure : Prop) (fingerprintFailure : Prop)
    (proofFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (buildFailure : Prop)
    (submissionFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUBMGBadBenchmarkAgreement benchmarkFailure fingerprintFailure
      proofFailure checkerFailure emptyClauseFailure buildFailure
      submissionFailure archiveFailure auditFailure noClaim recompute ->
    AyUBMGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ubmg_public_no_claim_report noClaim originalUnsat
    (ay_ubmg_bad_no_claim benchmarkFailure fingerprintFailure proofFailure
      checkerFailure emptyClauseFailure buildFailure submissionFailure
      archiveFailure auditFailure noClaim recompute bad)

theorem ay_ubmg_failure_forces_no_claim
    (benchmarkFailure : Prop) (fingerprintFailure : Prop)
    (proofFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (buildFailure : Prop)
    (submissionFailure : Prop) (archiveFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUBMGBadBenchmarkAgreement benchmarkFailure fingerprintFailure
      proofFailure checkerFailure emptyClauseFailure buildFailure
      submissionFailure archiveFailure auditFailure noClaim recompute ->
    AyUBMGConj noClaim recompute := by
  intro bad
  exact ay_ubmg_conj_intro noClaim recompute
    (ay_ubmg_bad_no_claim benchmarkFailure fingerprintFailure proofFailure
      checkerFailure emptyClauseFailure buildFailure submissionFailure
      archiveFailure auditFailure noClaim recompute bad)
    (ay_ubmg_bad_recompute benchmarkFailure fingerprintFailure proofFailure
      checkerFailure emptyClauseFailure buildFailure submissionFailure
      archiveFailure auditFailure noClaim recompute bad)

theorem ay_ubmg_benchmark_failure_forces_no_claim
    (benchmarkFailure : Prop) (noClaim : Prop) :
    benchmarkFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ubmg_fingerprint_failure_forces_no_claim
    (fingerprintFailure : Prop) (noClaim : Prop) :
    fingerprintFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ubmg_proof_failure_forces_no_claim
    (proofFailure : Prop) (noClaim : Prop) :
    proofFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ubmg_checker_failure_forces_no_claim
    (checkerFailure : Prop) (noClaim : Prop) :
    checkerFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ubmg_empty_clause_failure_forces_no_claim
    (emptyClauseFailure : Prop) (noClaim : Prop) :
    emptyClauseFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ubmg_build_failure_forces_no_claim
    (buildFailure : Prop) (noClaim : Prop) :
    buildFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ubmg_submission_failure_forces_no_claim
    (submissionFailure : Prop) (noClaim : Prop) :
    submissionFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ubmg_archive_failure_forces_no_claim
    (archiveFailure : Prop) (noClaim : Prop) :
    archiveFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_ubmg_audit_failure_forces_no_claim
    (auditFailure : Prop) (noClaim : Prop) :
    auditFailure -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
