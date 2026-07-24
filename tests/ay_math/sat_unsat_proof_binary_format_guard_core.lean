-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Binary proof-format guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. Propositions stand for binary proof digests, decoding
-- version manifests, decoded-step ledgers, antecedent availability,
-- resolvent/redundancy replay, original-formula empty-clause reachability,
-- checker transcripts, benchmark fingerprints, build/archive evidence,
-- fallback no-claim paths, audit transcripts, and fail-closed recompute
-- diagnostics.

def ay_bfgg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_bfgg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_bfgg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_bfgg_accepted_evidence
    (binaryProofDigest : Prop) (decodingVersionManifest : Prop)
    (decodedStepLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (replayEvidence : Prop) (originalEmptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (binaryProofDigest ->
      decodingVersionManifest ->
      decodedStepLedger ->
      antecedentAvailabilityLedger ->
      replayEvidence ->
      originalEmptyClauseReachable ->
      checkerTranscript ->
      checkerAccepted ->
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

def ay_bfgg_binary_replay_composition
    (binaryProofDigest : Prop) (decodingVersionManifest : Prop)
    (decodedStepLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (replayEvidence : Prop) (originalEmptyClauseReachable : Prop)
    (originalUnsat : Prop) :=
  ay_bfgg_conj
    (ay_bfgg_map binaryProofDigest decodingVersionManifest)
    (ay_bfgg_conj
      (ay_bfgg_map decodingVersionManifest decodedStepLedger)
      (ay_bfgg_conj
        (ay_bfgg_map decodedStepLedger antecedentAvailabilityLedger)
        (ay_bfgg_conj
          (ay_bfgg_map antecedentAvailabilityLedger replayEvidence)
          (ay_bfgg_conj
            (ay_bfgg_map replayEvidence originalEmptyClauseReachable)
            (ay_bfgg_map originalEmptyClauseReachable originalUnsat))))))

def ay_bfgg_publication
    (binaryProofDigest : Prop) (decodingVersionManifest : Prop)
    (decodedStepLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (replayEvidence : Prop) (originalEmptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  ay_bfgg_conj
    (ay_bfgg_accepted_evidence binaryProofDigest decodingVersionManifest
      decodedStepLedger antecedentAvailabilityLedger replayEvidence
      originalEmptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat)
    originalUnsat

def ay_bfgg_failure_reason
    (digestMismatch : Prop) (versionMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (versionMismatch -> result) ->
    (decodeMismatch -> result) ->
    (availabilityMismatch -> result) ->
    (replayMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_bfgg_bad_guard
    (digestMismatch : Prop) (versionMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_bfgg_conj
    (ay_bfgg_conj noClaim recompute)
    (ay_bfgg_failure_reason digestMismatch versionMismatch decodeMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch)

def ay_bfgg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_bfgg_disj noClaim (ay_bfgg_disj originalUnsat publicSat)

theorem ay_bfgg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_bfgg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_bfgg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_bfgg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_bfgg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_bfgg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_bfgg_build_accepted_evidence
    (binaryProofDigest : Prop) (decodingVersionManifest : Prop)
    (decodedStepLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (replayEvidence : Prop) (originalEmptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    binaryProofDigest ->
    decodingVersionManifest ->
    decodedStepLedger ->
    antecedentAvailabilityLedger ->
    replayEvidence ->
    originalEmptyClauseReachable ->
    checkerTranscript ->
    checkerAccepted ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    fallbackNoClaim ->
    auditTranscript ->
    originalUnsat ->
    ay_bfgg_accepted_evidence binaryProofDigest decodingVersionManifest
      decodedStepLedger antecedentAvailabilityLedger replayEvidence
      originalEmptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat := by
  intro hDigest hVersion hDecoded hAvail hReplay hEmpty hTranscript
  intro hChecker hFingerprint hFingerprintAccepted hBuild hBuildAccepted
  intro hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hVersion hDecoded hAvail hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_bfgg_original_empty_clause_reachable
    (binaryProofDigest : Prop) (decodingVersionManifest : Prop)
    (decodedStepLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (replayEvidence : Prop) (originalEmptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_bfgg_accepted_evidence binaryProofDigest decodingVersionManifest
      decodedStepLedger antecedentAvailabilityLedger replayEvidence
      originalEmptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalEmptyClauseReachable := by
  intro accepted
  exact accepted originalEmptyClauseReachable
    (fun _hDigest _hVersion _hDecoded _hAvail _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_bfgg_original_unsat
    (binaryProofDigest : Prop) (decodingVersionManifest : Prop)
    (decodedStepLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (replayEvidence : Prop) (originalEmptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_bfgg_accepted_evidence binaryProofDigest decodingVersionManifest
      decodedStepLedger antecedentAvailabilityLedger replayEvidence
      originalEmptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hVersion _hDecoded _hAvail _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_bfgg_binary_replay_composes_to_original
    (binaryProofDigest : Prop) (decodingVersionManifest : Prop)
    (decodedStepLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (replayEvidence : Prop) (originalEmptyClauseReachable : Prop)
    (originalUnsat : Prop) :
    ay_bfgg_binary_replay_composition binaryProofDigest
      decodingVersionManifest decodedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable originalUnsat ->
    binaryProofDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_version rest =>
      rest originalUnsat
        (fun version_to_decoded rest2 =>
          rest2 originalUnsat
            (fun decoded_to_availability rest3 =>
              rest3 originalUnsat
                (fun availability_to_replay rest4 =>
                  rest4 originalUnsat
                    (fun replay_to_empty empty_to_original =>
                      empty_to_original
                        (replay_to_empty
                          (availability_to_replay
                            (decoded_to_availability
                              (version_to_decoded
                                (digest_to_version hDigest)))))))))))

theorem ay_bfgg_publication_sound
    (binaryProofDigest : Prop) (decodingVersionManifest : Prop)
    (decodedStepLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (replayEvidence : Prop) (originalEmptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_bfgg_publication binaryProofDigest decodingVersionManifest
      decodedStepLedger antecedentAvailabilityLedger replayEvidence
      originalEmptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_bfgg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_bfgg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_bfgg_disj_right noClaim (ay_bfgg_disj originalUnsat publicSat)
    (ay_bfgg_disj_left originalUnsat publicSat hOriginal)

theorem ay_bfgg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_bfgg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_bfgg_disj_left noClaim (ay_bfgg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_bfgg_bad_no_claim
    (digestMismatch : Prop) (versionMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_bfgg_bad_guard digestMismatch versionMismatch decodeMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_bfgg_bad_recompute
    (digestMismatch : Prop) (versionMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_bfgg_bad_guard digestMismatch versionMismatch decodeMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_bfgg_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (versionMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_bfgg_bad_guard digestMismatch versionMismatch decodeMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    ay_bfgg_disj noClaim originalUnsat := by
  intro bad
  exact ay_bfgg_disj_left noClaim originalUnsat
    (ay_bfgg_bad_no_claim digestMismatch versionMismatch decodeMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute bad)

theorem ay_bfgg_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (versionMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_bfgg_bad_guard digestMismatch versionMismatch decodeMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    ay_bfgg_disj noClaim publicSat := by
  intro bad
  exact ay_bfgg_disj_left noClaim publicSat
    (ay_bfgg_bad_no_claim digestMismatch versionMismatch decodeMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute bad)

theorem ay_bfgg_failure_forces_no_claim
    (digestMismatch : Prop) (versionMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_bfgg_failure_reason digestMismatch versionMismatch decodeMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch ->
    (digestMismatch -> noClaim) ->
    (versionMismatch -> noClaim) ->
    (decodeMismatch -> noClaim) ->
    (availabilityMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure digest_to_no_claim version_to_no_claim decode_to_no_claim
  intro availability_to_no_claim replay_to_no_claim reachability_to_no_claim
  intro checker_to_no_claim fingerprint_to_no_claim build_to_no_claim
  intro archive_to_no_claim audit_to_no_claim
  exact failure noClaim digest_to_no_claim version_to_no_claim
    decode_to_no_claim availability_to_no_claim replay_to_no_claim
    reachability_to_no_claim checker_to_no_claim fingerprint_to_no_claim
    build_to_no_claim archive_to_no_claim audit_to_no_claim

theorem ay_bfgg_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_bfgg_version_mismatch_forces_no_claim
    (versionMismatch noClaim : Prop) :
    versionMismatch -> (versionMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_bfgg_decode_mismatch_forces_no_claim
    (decodeMismatch noClaim : Prop) :
    decodeMismatch -> (decodeMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_bfgg_availability_mismatch_forces_no_claim
    (availabilityMismatch noClaim : Prop) :
    availabilityMismatch -> (availabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_bfgg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_bfgg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch -> (reachabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_bfgg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_bfgg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_bfgg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_bfgg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_bfgg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
