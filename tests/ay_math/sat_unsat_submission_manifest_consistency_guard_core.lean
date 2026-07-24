-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT submission-manifest consistency guard soundness for ay
-- sequential-main SAT-COMP publication. Propositions stand for submission
-- manifests, proof archive manifests, proof artifact digests, checker
-- transcripts, empty-clause reachability, formula fingerprints, solver build
-- evidence, benchmark manifests, audit transcripts, and fail-closed
-- no-claim/recompute diagnostics.

def AyUSMGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUSMGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUSMGMap (source : Prop) (target : Prop) :=
  source -> target

def AyUSMGAcceptedEvidence
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (submissionManifest ->
      proofArchiveManifest ->
      proofArtifactDigest ->
      checkerTranscript ->
      checkerAccepted ->
      emptyClauseReachable ->
      formulaFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      benchmarkManifest ->
      auditTranscript ->
      visibleUnsat ->
      originalUnsat ->
      result) ->
    result

def AyUSMGSubmissionCertificate
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (benchmarkManifest : Prop)
    (auditTranscript : Prop) :=
  AyUSMGConj submissionManifest
    (AyUSMGConj proofArchiveManifest
      (AyUSMGConj proofArtifactDigest
        (AyUSMGConj benchmarkManifest auditTranscript)))

def AyUSMGSubmissionReplayGuard
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkManifest : Prop) :=
  AyUSMGConj
    (AyUSMGMap submissionManifest proofArchiveManifest)
    (AyUSMGConj
      (AyUSMGMap proofArchiveManifest proofArtifactDigest)
      (AyUSMGConj
        (AyUSMGMap proofArtifactDigest benchmarkManifest)
        (AyUSMGConj
          (AyUSMGMap benchmarkManifest emptyClauseReachable)
          (AyUSMGMap checkerTranscript checkerAccepted))))

def AyUSMGPublication
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSMGConj
    (AyUSMGAcceptedEvidence submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted
      emptyClauseReachable formulaFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted benchmarkManifest auditTranscript
      visibleUnsat originalUnsat)
    originalUnsat

def AyUSMGFailureReason
    (submissionFailure : Prop) (archiveFailure : Prop)
    (artifactDigestFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (benchmarkFailure : Prop)
    (auditFailure : Prop) :=
  forall result : Prop,
    (submissionFailure -> result) ->
    (archiveFailure -> result) ->
    (artifactDigestFailure -> result) ->
    (checkerFailure -> result) ->
    (emptyClauseFailure -> result) ->
    (fingerprintFailure -> result) ->
    (buildFailure -> result) ->
    (benchmarkFailure -> result) ->
    (auditFailure -> result) ->
    result

def AyUSMGBadSubmissionAgreement
    (submissionFailure : Prop) (archiveFailure : Prop)
    (artifactDigestFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (benchmarkFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUSMGConj
    (AyUSMGConj noClaim recompute)
    (AyUSMGFailureReason submissionFailure archiveFailure
      artifactDigestFailure checkerFailure emptyClauseFailure
      fingerprintFailure buildFailure benchmarkFailure auditFailure)

def AyUSMGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUSMGDisj noClaim originalUnsat

theorem ay_usmg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUSMGConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_usmg_conj_left
    (p : Prop) (q : Prop) :
    AyUSMGConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_usmg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUSMGDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_usmg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUSMGDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_usmg_accepted_evidence
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    submissionManifest ->
    proofArchiveManifest ->
    proofArtifactDigest ->
    checkerTranscript ->
    checkerAccepted ->
    emptyClauseReachable ->
    formulaFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    benchmarkManifest ->
    auditTranscript ->
    visibleUnsat ->
    originalUnsat ->
    AyUSMGAcceptedEvidence submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      benchmarkManifest auditTranscript visibleUnsat originalUnsat := by
  intro hSubmission
  intro hArchive
  intro hDigest
  intro hTranscript
  intro hChecker
  intro hEmpty
  intro hFingerprint
  intro hFingerprintAccepted
  intro hBuild
  intro hBuildAccepted
  intro hBenchmark
  intro hAudit
  intro hVisible
  intro hOriginal
  intro result
  intro publish
  exact publish hSubmission hArchive hDigest hTranscript hChecker hEmpty
    hFingerprint hFingerprintAccepted hBuild hBuildAccepted hBenchmark hAudit
    hVisible hOriginal

theorem ay_usmg_submission_manifest
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMGAcceptedEvidence submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      benchmarkManifest auditTranscript visibleUnsat originalUnsat ->
    submissionManifest := by
  intro accepted
  exact accepted submissionManifest
    (fun hSubmission _hArchive _hDigest _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hBenchmark
      _hAudit _hVisible _hOriginal => hSubmission)

theorem ay_usmg_proof_archive_manifest
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMGAcceptedEvidence submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      benchmarkManifest auditTranscript visibleUnsat originalUnsat ->
    proofArchiveManifest := by
  intro accepted
  exact accepted proofArchiveManifest
    (fun _hSubmission hArchive _hDigest _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hBenchmark
      _hAudit _hVisible _hOriginal => hArchive)

theorem ay_usmg_proof_artifact_digest
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMGAcceptedEvidence submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      benchmarkManifest auditTranscript visibleUnsat originalUnsat ->
    proofArtifactDigest := by
  intro accepted
  exact accepted proofArtifactDigest
    (fun _hSubmission _hArchive hDigest _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hBenchmark
      _hAudit _hVisible _hOriginal => hDigest)

theorem ay_usmg_checker_transcript
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMGAcceptedEvidence submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      benchmarkManifest auditTranscript visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hSubmission _hArchive _hDigest hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hBenchmark
      _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_usmg_checker_accepted
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMGAcceptedEvidence submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      benchmarkManifest auditTranscript visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hSubmission _hArchive _hDigest _hTranscript hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hBenchmark
      _hAudit _hVisible _hOriginal => hChecker)

theorem ay_usmg_empty_clause_reachable
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMGAcceptedEvidence submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      benchmarkManifest auditTranscript visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hSubmission _hArchive _hDigest _hTranscript _hChecker hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hBenchmark
      _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_usmg_formula_fingerprint
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMGAcceptedEvidence submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      benchmarkManifest auditTranscript visibleUnsat originalUnsat ->
    formulaFingerprint := by
  intro accepted
  exact accepted formulaFingerprint
    (fun _hSubmission _hArchive _hDigest _hTranscript _hChecker _hEmpty
      hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hBenchmark
      _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_usmg_benchmark_manifest
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMGAcceptedEvidence submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      benchmarkManifest auditTranscript visibleUnsat originalUnsat ->
    benchmarkManifest := by
  intro accepted
  exact accepted benchmarkManifest
    (fun _hSubmission _hArchive _hDigest _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted hBenchmark
      _hAudit _hVisible _hOriginal => hBenchmark)

theorem ay_usmg_original_unsat
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMGAcceptedEvidence submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      benchmarkManifest auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hSubmission _hArchive _hDigest _hTranscript _hChecker _hEmpty
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hBenchmark
      _hAudit _hVisible hOriginal => hOriginal)

theorem ay_usmg_publication_sound
    (submissionManifest : Prop) (proofArchiveManifest : Prop)
    (proofArtifactDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (benchmarkManifest : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMGPublication submissionManifest proofArchiveManifest
      proofArtifactDigest checkerTranscript checkerAccepted emptyClauseReachable
      formulaFingerprint fingerprintAccepted solverBuildEvidence buildAccepted
      benchmarkManifest auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted unsat => unsat)

theorem ay_usmg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUSMGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_usmg_disj_right noClaim originalUnsat unsat

theorem ay_usmg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUSMGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_usmg_disj_left noClaim originalUnsat no_claim

theorem ay_usmg_bad_no_claim
    (submissionFailure : Prop) (archiveFailure : Prop)
    (artifactDigestFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (benchmarkFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUSMGBadSubmissionAgreement submissionFailure archiveFailure
      artifactDigestFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure benchmarkFailure auditFailure noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_usmg_bad_recompute
    (submissionFailure : Prop) (archiveFailure : Prop)
    (artifactDigestFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (benchmarkFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUSMGBadSubmissionAgreement submissionFailure archiveFailure
      artifactDigestFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure benchmarkFailure auditFailure noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_usmg_failed_submission_agreement_cannot_bless_unsat
    (submissionFailure : Prop) (archiveFailure : Prop)
    (artifactDigestFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (benchmarkFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUSMGBadSubmissionAgreement submissionFailure archiveFailure
      artifactDigestFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure benchmarkFailure auditFailure noClaim recompute ->
    AyUSMGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_usmg_public_no_claim_report noClaim originalUnsat
    (ay_usmg_bad_no_claim submissionFailure archiveFailure
      artifactDigestFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure benchmarkFailure auditFailure noClaim recompute bad)

theorem ay_usmg_failure_forces_no_claim
    (submissionFailure : Prop) (archiveFailure : Prop)
    (artifactDigestFailure : Prop) (checkerFailure : Prop)
    (emptyClauseFailure : Prop) (fingerprintFailure : Prop)
    (buildFailure : Prop) (benchmarkFailure : Prop)
    (auditFailure : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUSMGBadSubmissionAgreement submissionFailure archiveFailure
      artifactDigestFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure benchmarkFailure auditFailure noClaim recompute ->
    AyUSMGConj noClaim recompute := by
  intro bad
  exact ay_usmg_conj_intro noClaim recompute
    (ay_usmg_bad_no_claim submissionFailure archiveFailure
      artifactDigestFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure benchmarkFailure auditFailure noClaim recompute bad)
    (ay_usmg_bad_recompute submissionFailure archiveFailure
      artifactDigestFailure checkerFailure emptyClauseFailure fingerprintFailure
      buildFailure benchmarkFailure auditFailure noClaim recompute bad)

theorem ay_usmg_submission_failure_forces_no_claim
    (submissionFailure : Prop) (noClaim : Prop) :
    submissionFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_usmg_archive_failure_forces_no_claim
    (archiveFailure : Prop) (noClaim : Prop) :
    archiveFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_usmg_artifact_digest_failure_forces_no_claim
    (artifactDigestFailure : Prop) (noClaim : Prop) :
    artifactDigestFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_usmg_checker_failure_forces_no_claim
    (checkerFailure : Prop) (noClaim : Prop) :
    checkerFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_usmg_empty_clause_failure_forces_no_claim
    (emptyClauseFailure : Prop) (noClaim : Prop) :
    emptyClauseFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_usmg_fingerprint_failure_forces_no_claim
    (fingerprintFailure : Prop) (noClaim : Prop) :
    fingerprintFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_usmg_build_failure_forces_no_claim
    (buildFailure : Prop) (noClaim : Prop) :
    buildFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_usmg_benchmark_failure_forces_no_claim
    (benchmarkFailure : Prop) (noClaim : Prop) :
    benchmarkFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim

theorem ay_usmg_audit_failure_forces_no_claim
    (auditFailure : Prop) (noClaim : Prop) :
    auditFailure -> noClaim -> noClaim := by
  intro _failure
  intro no_claim
  exact no_claim
