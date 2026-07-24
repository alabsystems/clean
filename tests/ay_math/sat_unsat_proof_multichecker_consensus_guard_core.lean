-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Multi-checker consensus guard soundness for ay sequential-main SAT-COMP
-- UNSAT proof publication. Propositions stand for proof digests, primary and
-- independent checker transcripts, checker-version manifests, parsed-step
-- agreement ledgers, empty-clause reachability agreement, benchmark
-- fingerprints, build/archive evidence, fallback no-claim paths, audit
-- transcripts, and fail-closed recompute diagnostics.

def ay_mcgg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_mcgg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_mcgg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_mcgg_accepted_evidence
    (proofDigest : Prop) (primaryCheckerTranscript : Prop)
    (independentCheckerTranscript : Prop) (checkerVersionManifest : Prop)
    (parsedStepAgreementLedger : Prop)
    (emptyClauseReachabilityAgreement : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofDigest ->
      primaryCheckerTranscript ->
      independentCheckerTranscript ->
      checkerVersionManifest ->
      parsedStepAgreementLedger ->
      emptyClauseReachabilityAgreement ->
      benchmarkFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      archiveManifest ->
      fallbackNoClaim ->
      auditTranscript ->
      originalUnsat ->
      result) ->
    result

def ay_mcgg_consensus_composition
    (proofDigest : Prop) (primaryCheckerTranscript : Prop)
    (independentCheckerTranscript : Prop) (checkerVersionManifest : Prop)
    (parsedStepAgreementLedger : Prop)
    (emptyClauseReachabilityAgreement : Prop) (originalUnsat : Prop) :=
  ay_mcgg_conj
    (ay_mcgg_map proofDigest primaryCheckerTranscript)
    (ay_mcgg_conj
      (ay_mcgg_map primaryCheckerTranscript independentCheckerTranscript)
      (ay_mcgg_conj
        (ay_mcgg_map independentCheckerTranscript checkerVersionManifest)
        (ay_mcgg_conj
          (ay_mcgg_map checkerVersionManifest parsedStepAgreementLedger)
          (ay_mcgg_conj
            (ay_mcgg_map parsedStepAgreementLedger
              emptyClauseReachabilityAgreement)
            (ay_mcgg_map emptyClauseReachabilityAgreement originalUnsat))))))

def ay_mcgg_publication
    (proofDigest : Prop) (primaryCheckerTranscript : Prop)
    (independentCheckerTranscript : Prop) (checkerVersionManifest : Prop)
    (parsedStepAgreementLedger : Prop)
    (emptyClauseReachabilityAgreement : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  ay_mcgg_conj
    (ay_mcgg_accepted_evidence proofDigest primaryCheckerTranscript
      independentCheckerTranscript checkerVersionManifest
      parsedStepAgreementLedger emptyClauseReachabilityAgreement
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat)
    originalUnsat

def ay_mcgg_failure_reason
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (versionMismatch : Prop) (agreementMismatch : Prop)
    (reachabilityMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (checkerMismatch -> result) ->
    (versionMismatch -> result) ->
    (agreementMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_mcgg_bad_guard
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (versionMismatch : Prop) (agreementMismatch : Prop)
    (reachabilityMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_mcgg_conj
    (ay_mcgg_conj noClaim recompute)
    (ay_mcgg_failure_reason digestMismatch checkerMismatch versionMismatch
      agreementMismatch reachabilityMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch)

def ay_mcgg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_mcgg_disj noClaim (ay_mcgg_disj originalUnsat publicSat)

theorem ay_mcgg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_mcgg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_mcgg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_mcgg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_mcgg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_mcgg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_mcgg_build_accepted_evidence
    (proofDigest : Prop) (primaryCheckerTranscript : Prop)
    (independentCheckerTranscript : Prop) (checkerVersionManifest : Prop)
    (parsedStepAgreementLedger : Prop)
    (emptyClauseReachabilityAgreement : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    proofDigest ->
    primaryCheckerTranscript ->
    independentCheckerTranscript ->
    checkerVersionManifest ->
    parsedStepAgreementLedger ->
    emptyClauseReachabilityAgreement ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    fallbackNoClaim ->
    auditTranscript ->
    originalUnsat ->
    ay_mcgg_accepted_evidence proofDigest primaryCheckerTranscript
      independentCheckerTranscript checkerVersionManifest
      parsedStepAgreementLedger emptyClauseReachabilityAgreement
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat := by
  intro hDigest hPrimary hIndependent hVersion hAgreement hReachability
  intro hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
  intro hFallback hAudit hOriginal result publish
  exact publish hDigest hPrimary hIndependent hVersion hAgreement
    hReachability hFingerprint hFingerprintAccepted hBuild hBuildAccepted
    hArchive hFallback hAudit hOriginal

theorem ay_mcgg_empty_clause_reachability_agreement
    (proofDigest : Prop) (primaryCheckerTranscript : Prop)
    (independentCheckerTranscript : Prop) (checkerVersionManifest : Prop)
    (parsedStepAgreementLedger : Prop)
    (emptyClauseReachabilityAgreement : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_mcgg_accepted_evidence proofDigest primaryCheckerTranscript
      independentCheckerTranscript checkerVersionManifest
      parsedStepAgreementLedger emptyClauseReachabilityAgreement
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    emptyClauseReachabilityAgreement := by
  intro accepted
  exact accepted emptyClauseReachabilityAgreement
    (fun _hDigest _hPrimary _hIndependent _hVersion _hAgreement hReachability
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit _hOriginal =>
      hReachability)

theorem ay_mcgg_original_unsat
    (proofDigest : Prop) (primaryCheckerTranscript : Prop)
    (independentCheckerTranscript : Prop) (checkerVersionManifest : Prop)
    (parsedStepAgreementLedger : Prop)
    (emptyClauseReachabilityAgreement : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_mcgg_accepted_evidence proofDigest primaryCheckerTranscript
      independentCheckerTranscript checkerVersionManifest
      parsedStepAgreementLedger emptyClauseReachabilityAgreement
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hPrimary _hIndependent _hVersion _hAgreement _hReachability
      _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive
      _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_mcgg_consensus_composes_to_original
    (proofDigest : Prop) (primaryCheckerTranscript : Prop)
    (independentCheckerTranscript : Prop) (checkerVersionManifest : Prop)
    (parsedStepAgreementLedger : Prop)
    (emptyClauseReachabilityAgreement : Prop) (originalUnsat : Prop) :
    ay_mcgg_consensus_composition proofDigest primaryCheckerTranscript
      independentCheckerTranscript checkerVersionManifest
      parsedStepAgreementLedger emptyClauseReachabilityAgreement
      originalUnsat ->
    proofDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_primary rest =>
      rest originalUnsat
        (fun primary_to_independent rest2 =>
          rest2 originalUnsat
            (fun independent_to_version rest3 =>
              rest3 originalUnsat
                (fun version_to_agreement rest4 =>
                  rest4 originalUnsat
                    (fun agreement_to_reachability reachability_to_original =>
                      reachability_to_original
                        (agreement_to_reachability
                          (version_to_agreement
                            (independent_to_version
                              (primary_to_independent
                                (digest_to_primary hDigest)))))))))))

theorem ay_mcgg_publication_sound
    (proofDigest : Prop) (primaryCheckerTranscript : Prop)
    (independentCheckerTranscript : Prop) (checkerVersionManifest : Prop)
    (parsedStepAgreementLedger : Prop)
    (emptyClauseReachabilityAgreement : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_mcgg_publication proofDigest primaryCheckerTranscript
      independentCheckerTranscript checkerVersionManifest
      parsedStepAgreementLedger emptyClauseReachabilityAgreement
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_mcgg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_mcgg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_mcgg_disj_right noClaim (ay_mcgg_disj originalUnsat publicSat)
    (ay_mcgg_disj_left originalUnsat publicSat hOriginal)

theorem ay_mcgg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_mcgg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_mcgg_disj_left noClaim (ay_mcgg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_mcgg_bad_no_claim
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (versionMismatch : Prop) (agreementMismatch : Prop)
    (reachabilityMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_mcgg_bad_guard digestMismatch checkerMismatch versionMismatch
      agreementMismatch reachabilityMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_mcgg_bad_recompute
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (versionMismatch : Prop) (agreementMismatch : Prop)
    (reachabilityMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_mcgg_bad_guard digestMismatch checkerMismatch versionMismatch
      agreementMismatch reachabilityMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_mcgg_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (versionMismatch : Prop) (agreementMismatch : Prop)
    (reachabilityMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_mcgg_bad_guard digestMismatch checkerMismatch versionMismatch
      agreementMismatch reachabilityMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_mcgg_disj noClaim originalUnsat := by
  intro bad
  exact ay_mcgg_disj_left noClaim originalUnsat
    (ay_mcgg_bad_no_claim digestMismatch checkerMismatch versionMismatch
      agreementMismatch reachabilityMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_mcgg_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (versionMismatch : Prop) (agreementMismatch : Prop)
    (reachabilityMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_mcgg_bad_guard digestMismatch checkerMismatch versionMismatch
      agreementMismatch reachabilityMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_mcgg_disj noClaim publicSat := by
  intro bad
  exact ay_mcgg_disj_left noClaim publicSat
    (ay_mcgg_bad_no_claim digestMismatch checkerMismatch versionMismatch
      agreementMismatch reachabilityMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_mcgg_failure_forces_no_claim
    (digestMismatch : Prop) (checkerMismatch : Prop)
    (versionMismatch : Prop) (agreementMismatch : Prop)
    (reachabilityMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_mcgg_failure_reason digestMismatch checkerMismatch versionMismatch
      agreementMismatch reachabilityMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch ->
    (digestMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (versionMismatch -> noClaim) ->
    (agreementMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure digest_to_no_claim checker_to_no_claim version_to_no_claim
  intro agreement_to_no_claim reachability_to_no_claim
  intro fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
  intro audit_to_no_claim
  exact failure noClaim digest_to_no_claim checker_to_no_claim
    version_to_no_claim agreement_to_no_claim reachability_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_mcgg_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_mcgg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_mcgg_version_mismatch_forces_no_claim
    (versionMismatch noClaim : Prop) :
    versionMismatch -> (versionMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_mcgg_agreement_mismatch_forces_no_claim
    (agreementMismatch noClaim : Prop) :
    agreementMismatch -> (agreementMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_mcgg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch -> (reachabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_mcgg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_mcgg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_mcgg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_mcgg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
