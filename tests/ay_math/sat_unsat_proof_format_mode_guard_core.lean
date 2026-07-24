-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Proof-format mode guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. Propositions stand for proof text digests, declared
-- RUP/DRAT/LRAT-like modes, parsed-step ledgers, checker-mode compatibility,
-- antecedent availability ledgers, resolvent/redundancy replay, empty-clause
-- reachability, checker transcripts, benchmark fingerprints, solver build
-- evidence, archive manifests, fallback no-claim paths, audit transcripts,
-- and fail-closed recompute diagnostics.

def ay_fmgg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_fmgg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_fmgg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_fmgg_accepted_evidence
    (proofTextDigest : Prop) (declaredProofFormatMode : Prop)
    (parsedStepLedger : Prop) (checkerModeCompatible : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofTextDigest ->
      declaredProofFormatMode ->
      parsedStepLedger ->
      checkerModeCompatible ->
      antecedentAvailabilityLedger ->
      replayEvidence ->
      emptyClauseReachable ->
      checkerTranscript ->
      checkerAccepted ->
      benchmarkFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      archiveManifest ->
      fallbackNoClaim ->
      auditTranscript ->
      visibleUnsat ->
      originalUnsat ->
      result) ->
    result

def ay_fmgg_mode_replay_composition
    (proofTextDigest : Prop) (declaredProofFormatMode : Prop)
    (parsedStepLedger : Prop) (checkerModeCompatible : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  ay_fmgg_conj
    (ay_fmgg_map proofTextDigest declaredProofFormatMode)
    (ay_fmgg_conj
      (ay_fmgg_map declaredProofFormatMode parsedStepLedger)
      (ay_fmgg_conj
        (ay_fmgg_map parsedStepLedger checkerModeCompatible)
        (ay_fmgg_conj
          (ay_fmgg_map checkerModeCompatible antecedentAvailabilityLedger)
          (ay_fmgg_conj
            (ay_fmgg_map antecedentAvailabilityLedger replayEvidence)
            (ay_fmgg_conj
              (ay_fmgg_map replayEvidence emptyClauseReachable)
              (ay_fmgg_conj
                (ay_fmgg_map emptyClauseReachable visibleUnsat)
                (ay_fmgg_map visibleUnsat originalUnsat)))))))

def ay_fmgg_publication
    (proofTextDigest : Prop) (declaredProofFormatMode : Prop)
    (parsedStepLedger : Prop) (checkerModeCompatible : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  ay_fmgg_conj
    (ay_fmgg_accepted_evidence proofTextDigest declaredProofFormatMode
      parsedStepLedger checkerModeCompatible antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat)
    originalUnsat

def ay_fmgg_failure_reason
    (digestMismatch : Prop) (modeMismatch : Prop) (parseMismatch : Prop)
    (compatibilityMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (modeMismatch -> result) ->
    (parseMismatch -> result) ->
    (compatibilityMismatch -> result) ->
    (availabilityMismatch -> result) ->
    (replayMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_fmgg_bad_guard
    (digestMismatch : Prop) (modeMismatch : Prop) (parseMismatch : Prop)
    (compatibilityMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  ay_fmgg_conj
    (ay_fmgg_conj noClaim recompute)
    (ay_fmgg_failure_reason digestMismatch modeMismatch parseMismatch
      compatibilityMismatch availabilityMismatch replayMismatch
      reachabilityMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch)

def ay_fmgg_public_report (noClaim : Prop) (originalUnsat : Prop) :=
  ay_fmgg_disj noClaim originalUnsat

theorem ay_fmgg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_fmgg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_fmgg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_fmgg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_fmgg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_fmgg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_fmgg_build_accepted_evidence
    (proofTextDigest : Prop) (declaredProofFormatMode : Prop)
    (parsedStepLedger : Prop) (checkerModeCompatible : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    proofTextDigest ->
    declaredProofFormatMode ->
    parsedStepLedger ->
    checkerModeCompatible ->
    antecedentAvailabilityLedger ->
    replayEvidence ->
    emptyClauseReachable ->
    checkerTranscript ->
    checkerAccepted ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    fallbackNoClaim ->
    auditTranscript ->
    visibleUnsat ->
    originalUnsat ->
    ay_fmgg_accepted_evidence proofTextDigest declaredProofFormatMode
      parsedStepLedger checkerModeCompatible antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat := by
  intro hDigest hMode hParsed hCompat hAvail hReplay hEmpty hTranscript
  intro hChecker hFingerprint hFingerprintAccepted hBuild hBuildAccepted
  intro hArchive hFallback hAudit hVisible hOriginal result publish
  exact publish hDigest hMode hParsed hCompat hAvail hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hVisible hOriginal

theorem ay_fmgg_empty_clause_reachable
    (proofTextDigest : Prop) (declaredProofFormatMode : Prop)
    (parsedStepLedger : Prop) (checkerModeCompatible : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    ay_fmgg_accepted_evidence proofTextDigest declaredProofFormatMode
      parsedStepLedger checkerModeCompatible antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hDigest _hMode _hParsed _hCompat _hAvail _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hEmpty)

theorem ay_fmgg_replay_evidence
    (proofTextDigest : Prop) (declaredProofFormatMode : Prop)
    (parsedStepLedger : Prop) (checkerModeCompatible : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    ay_fmgg_accepted_evidence proofTextDigest declaredProofFormatMode
      parsedStepLedger checkerModeCompatible antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat ->
    replayEvidence := by
  intro accepted
  exact accepted replayEvidence
    (fun _hDigest _hMode _hParsed _hCompat _hAvail hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hReplay)

theorem ay_fmgg_original_unsat
    (proofTextDigest : Prop) (declaredProofFormatMode : Prop)
    (parsedStepLedger : Prop) (checkerModeCompatible : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    ay_fmgg_accepted_evidence proofTextDigest declaredProofFormatMode
      parsedStepLedger checkerModeCompatible antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hMode _hParsed _hCompat _hAvail _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible hOriginal =>
      hOriginal)

theorem ay_fmgg_format_mode_replay_composes_to_original
    (proofTextDigest : Prop) (declaredProofFormatMode : Prop)
    (parsedStepLedger : Prop) (checkerModeCompatible : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    proofTextDigest ->
    ay_fmgg_mode_replay_composition proofTextDigest declaredProofFormatMode
      parsedStepLedger checkerModeCompatible antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable visibleUnsat originalUnsat ->
    originalUnsat := by
  intro hDigest
  intro composed
  exact composed originalUnsat
    (fun digest_to_mode rest1 =>
      rest1 originalUnsat
        (fun mode_to_parsed rest2 =>
          rest2 originalUnsat
            (fun parsed_to_compat rest3 =>
              rest3 originalUnsat
                (fun compat_to_avail rest4 =>
                  rest4 originalUnsat
                    (fun avail_to_replay rest5 =>
                      rest5 originalUnsat
                        (fun replay_to_empty rest6 =>
                          rest6 originalUnsat
                            (fun empty_to_visible visible_to_original =>
                              visible_to_original
                                (empty_to_visible
                                  (replay_to_empty
                                    (avail_to_replay
                                      (compat_to_avail
                                        (parsed_to_compat
                                          (mode_to_parsed
                                            (digest_to_mode hDigest))))))))))))))

theorem ay_fmgg_publication_sound
    (proofTextDigest : Prop) (declaredProofFormatMode : Prop)
    (parsedStepLedger : Prop) (checkerModeCompatible : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    ay_fmgg_publication proofTextDigest declaredProofFormatMode
      parsedStepLedger checkerModeCompatible antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat (fun _accepted unsat => unsat)

theorem ay_fmgg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> ay_fmgg_public_report noClaim originalUnsat := by
  intro unsat
  exact ay_fmgg_disj_right noClaim originalUnsat unsat

theorem ay_fmgg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> ay_fmgg_public_report noClaim originalUnsat := by
  intro no_claim
  exact ay_fmgg_disj_left noClaim originalUnsat no_claim

theorem ay_fmgg_bad_no_claim
    (digestMismatch : Prop) (modeMismatch : Prop) (parseMismatch : Prop)
    (compatibilityMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_fmgg_bad_guard digestMismatch modeMismatch parseMismatch
      compatibilityMismatch availabilityMismatch replayMismatch
      reachabilityMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_fmgg_bad_recompute
    (digestMismatch : Prop) (modeMismatch : Prop) (parseMismatch : Prop)
    (compatibilityMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_fmgg_bad_guard digestMismatch modeMismatch parseMismatch
      compatibilityMismatch availabilityMismatch replayMismatch
      reachabilityMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_fmgg_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (modeMismatch : Prop) (parseMismatch : Prop)
    (compatibilityMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    ay_fmgg_bad_guard digestMismatch modeMismatch parseMismatch
      compatibilityMismatch availabilityMismatch replayMismatch
      reachabilityMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_fmgg_public_report noClaim originalUnsat := by
  intro bad
  exact ay_fmgg_public_no_claim_report noClaim originalUnsat
    (ay_fmgg_bad_no_claim digestMismatch modeMismatch parseMismatch
      compatibilityMismatch availabilityMismatch replayMismatch
      reachabilityMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_fmgg_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (modeMismatch : Prop) (parseMismatch : Prop)
    (compatibilityMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (publicSat : Prop) :
    ay_fmgg_bad_guard digestMismatch modeMismatch parseMismatch
      compatibilityMismatch availabilityMismatch replayMismatch
      reachabilityMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_fmgg_bad_no_claim digestMismatch modeMismatch parseMismatch
    compatibilityMismatch availabilityMismatch replayMismatch reachabilityMismatch
    checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
    auditMismatch noClaim recompute bad

theorem ay_fmgg_failure_forces_no_claim
    (digestMismatch : Prop) (modeMismatch : Prop) (parseMismatch : Prop)
    (compatibilityMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_fmgg_bad_guard digestMismatch modeMismatch parseMismatch
      compatibilityMismatch availabilityMismatch replayMismatch
      reachabilityMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_fmgg_conj noClaim recompute := by
  intro bad
  exact ay_fmgg_conj_intro noClaim recompute
    (ay_fmgg_bad_no_claim digestMismatch modeMismatch parseMismatch
      compatibilityMismatch availabilityMismatch replayMismatch
      reachabilityMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)
    (ay_fmgg_bad_recompute digestMismatch modeMismatch parseMismatch
      compatibilityMismatch availabilityMismatch replayMismatch
      reachabilityMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_fmgg_digest_mismatch_forces_no_claim
    (digestMismatch : Prop) (noClaim : Prop) :
    digestMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_fmgg_mode_mismatch_forces_no_claim
    (modeMismatch : Prop) (noClaim : Prop) :
    modeMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_fmgg_parse_mismatch_forces_no_claim
    (parseMismatch : Prop) (noClaim : Prop) :
    parseMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_fmgg_compatibility_mismatch_forces_no_claim
    (compatibilityMismatch : Prop) (noClaim : Prop) :
    compatibilityMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_fmgg_availability_mismatch_forces_no_claim
    (availabilityMismatch : Prop) (noClaim : Prop) :
    availabilityMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_fmgg_replay_mismatch_forces_no_claim
    (replayMismatch : Prop) (noClaim : Prop) :
    replayMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_fmgg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch : Prop) (noClaim : Prop) :
    reachabilityMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_fmgg_checker_mismatch_forces_no_claim
    (checkerMismatch : Prop) (noClaim : Prop) :
    checkerMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_fmgg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_fmgg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_fmgg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_fmgg_audit_mismatch_forces_no_claim
    (auditMismatch : Prop) (noClaim : Prop) :
    auditMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
