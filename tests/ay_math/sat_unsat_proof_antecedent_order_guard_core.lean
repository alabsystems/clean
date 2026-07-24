-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Antecedent-order guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. Propositions stand for proof digests, parsed-step
-- ledgers, antecedent order manifests, commutation/replay witnesses,
-- antecedent availability, resolvent/redundancy replay, empty-clause
-- reachability, checker transcripts, benchmark fingerprints, build/archive
-- evidence, fallback no-claim paths, audit transcripts, and fail-closed
-- recompute diagnostics.

def ay_aogg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_aogg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_aogg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_aogg_accepted_evidence
    (proofDigest : Prop) (parsedStepLedger : Prop)
    (antecedentOrderManifest : Prop) (commutationReplayWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofDigest ->
      parsedStepLedger ->
      antecedentOrderManifest ->
      commutationReplayWitness ->
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
      originalUnsat ->
      result) ->
    result

def ay_aogg_order_replay_composition
    (proofDigest : Prop) (parsedStepLedger : Prop)
    (antecedentOrderManifest : Prop) (commutationReplayWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (originalUnsat : Prop) :=
  ay_aogg_conj
    (ay_aogg_map proofDigest parsedStepLedger)
    (ay_aogg_conj
      (ay_aogg_map parsedStepLedger antecedentOrderManifest)
      (ay_aogg_conj
        (ay_aogg_map antecedentOrderManifest commutationReplayWitness)
        (ay_aogg_conj
          (ay_aogg_map commutationReplayWitness antecedentAvailabilityLedger)
          (ay_aogg_conj
            (ay_aogg_map antecedentAvailabilityLedger replayEvidence)
            (ay_aogg_conj
              (ay_aogg_map replayEvidence emptyClauseReachable)
              (ay_aogg_map emptyClauseReachable originalUnsat)))))))

def ay_aogg_publication
    (proofDigest : Prop) (parsedStepLedger : Prop)
    (antecedentOrderManifest : Prop) (commutationReplayWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  ay_aogg_conj
    (ay_aogg_accepted_evidence proofDigest parsedStepLedger
      antecedentOrderManifest commutationReplayWitness
      antecedentAvailabilityLedger replayEvidence emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackNoClaim auditTranscript originalUnsat)
    originalUnsat

def ay_aogg_failure_reason
    (digestMismatch : Prop) (parseMismatch : Prop) (orderMismatch : Prop)
    (commutationMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (parseMismatch -> result) ->
    (orderMismatch -> result) ->
    (commutationMismatch -> result) ->
    (availabilityMismatch -> result) ->
    (replayMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_aogg_bad_guard
    (digestMismatch : Prop) (parseMismatch : Prop) (orderMismatch : Prop)
    (commutationMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_aogg_conj
    (ay_aogg_conj noClaim recompute)
    (ay_aogg_failure_reason digestMismatch parseMismatch orderMismatch
      commutationMismatch availabilityMismatch replayMismatch
      reachabilityMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch)

def ay_aogg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_aogg_disj noClaim (ay_aogg_disj originalUnsat publicSat)

theorem ay_aogg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_aogg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_aogg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_aogg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_aogg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_aogg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_aogg_build_accepted_evidence
    (proofDigest : Prop) (parsedStepLedger : Prop)
    (antecedentOrderManifest : Prop) (commutationReplayWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    proofDigest ->
    parsedStepLedger ->
    antecedentOrderManifest ->
    commutationReplayWitness ->
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
    originalUnsat ->
    ay_aogg_accepted_evidence proofDigest parsedStepLedger
      antecedentOrderManifest commutationReplayWitness
      antecedentAvailabilityLedger replayEvidence emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackNoClaim auditTranscript originalUnsat := by
  intro hDigest hParsed hOrder hCommutation hAvail hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hParsed hOrder hCommutation hAvail hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_aogg_empty_clause_reachable
    (proofDigest : Prop) (parsedStepLedger : Prop)
    (antecedentOrderManifest : Prop) (commutationReplayWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_aogg_accepted_evidence proofDigest parsedStepLedger
      antecedentOrderManifest commutationReplayWitness
      antecedentAvailabilityLedger replayEvidence emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackNoClaim auditTranscript originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hDigest _hParsed _hOrder _hCommutation _hAvail _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_aogg_original_unsat
    (proofDigest : Prop) (parsedStepLedger : Prop)
    (antecedentOrderManifest : Prop) (commutationReplayWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_aogg_accepted_evidence proofDigest parsedStepLedger
      antecedentOrderManifest commutationReplayWitness
      antecedentAvailabilityLedger replayEvidence emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackNoClaim auditTranscript originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hParsed _hOrder _hCommutation _hAvail _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_aogg_order_replay_composes_to_original
    (proofDigest : Prop) (parsedStepLedger : Prop)
    (antecedentOrderManifest : Prop) (commutationReplayWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (originalUnsat : Prop) :
    ay_aogg_order_replay_composition proofDigest parsedStepLedger
      antecedentOrderManifest commutationReplayWitness
      antecedentAvailabilityLedger replayEvidence emptyClauseReachable
      originalUnsat ->
    proofDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_parsed rest =>
      rest originalUnsat
        (fun parsed_to_order rest2 =>
          rest2 originalUnsat
            (fun order_to_commutation rest3 =>
              rest3 originalUnsat
                (fun commutation_to_availability rest4 =>
                  rest4 originalUnsat
                    (fun availability_to_replay rest5 =>
                      rest5 originalUnsat
                        (fun replay_to_empty empty_to_original =>
                          empty_to_original
                            (replay_to_empty
                              (availability_to_replay
                                (commutation_to_availability
                                  (order_to_commutation
                                    (parsed_to_order
                                      (digest_to_parsed hDigest))))))))))))

theorem ay_aogg_publication_sound
    (proofDigest : Prop) (parsedStepLedger : Prop)
    (antecedentOrderManifest : Prop) (commutationReplayWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_aogg_publication proofDigest parsedStepLedger antecedentOrderManifest
      commutationReplayWitness antecedentAvailabilityLedger replayEvidence
      emptyClauseReachable checkerTranscript checkerAccepted benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackNoClaim auditTranscript originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_aogg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_aogg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_aogg_disj_right noClaim (ay_aogg_disj originalUnsat publicSat)
    (ay_aogg_disj_left originalUnsat publicSat hOriginal)

theorem ay_aogg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_aogg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_aogg_disj_left noClaim (ay_aogg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_aogg_bad_no_claim
    (digestMismatch : Prop) (parseMismatch : Prop) (orderMismatch : Prop)
    (commutationMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_aogg_bad_guard digestMismatch parseMismatch orderMismatch
      commutationMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_aogg_bad_recompute
    (digestMismatch : Prop) (parseMismatch : Prop) (orderMismatch : Prop)
    (commutationMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_aogg_bad_guard digestMismatch parseMismatch orderMismatch
      commutationMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_aogg_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (parseMismatch : Prop) (orderMismatch : Prop)
    (commutationMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_aogg_bad_guard digestMismatch parseMismatch orderMismatch
      commutationMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_aogg_disj noClaim originalUnsat := by
  intro bad
  exact ay_aogg_disj_left noClaim originalUnsat
    (ay_aogg_bad_no_claim digestMismatch parseMismatch orderMismatch
      commutationMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_aogg_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (parseMismatch : Prop) (orderMismatch : Prop)
    (commutationMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_aogg_bad_guard digestMismatch parseMismatch orderMismatch
      commutationMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_aogg_disj noClaim publicSat := by
  intro bad
  exact ay_aogg_disj_left noClaim publicSat
    (ay_aogg_bad_no_claim digestMismatch parseMismatch orderMismatch
      commutationMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_aogg_failure_forces_no_claim
    (digestMismatch : Prop) (parseMismatch : Prop) (orderMismatch : Prop)
    (commutationMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_aogg_failure_reason digestMismatch parseMismatch orderMismatch
      commutationMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch ->
    (digestMismatch -> noClaim) ->
    (parseMismatch -> noClaim) ->
    (orderMismatch -> noClaim) ->
    (commutationMismatch -> noClaim) ->
    (availabilityMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure digest_to_no_claim parse_to_no_claim order_to_no_claim
  intro commutation_to_no_claim availability_to_no_claim replay_to_no_claim
  intro reachability_to_no_claim checker_to_no_claim fingerprint_to_no_claim
  intro build_to_no_claim archive_to_no_claim audit_to_no_claim
  exact failure noClaim digest_to_no_claim parse_to_no_claim
    order_to_no_claim commutation_to_no_claim availability_to_no_claim
    replay_to_no_claim reachability_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_aogg_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_aogg_parse_mismatch_forces_no_claim
    (parseMismatch noClaim : Prop) :
    parseMismatch -> (parseMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_aogg_order_mismatch_forces_no_claim
    (orderMismatch noClaim : Prop) :
    orderMismatch -> (orderMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_aogg_commutation_mismatch_forces_no_claim
    (commutationMismatch noClaim : Prop) :
    commutationMismatch -> (commutationMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_aogg_availability_mismatch_forces_no_claim
    (availabilityMismatch noClaim : Prop) :
    availabilityMismatch -> (availabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_aogg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_aogg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch -> (reachabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_aogg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_aogg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_aogg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_aogg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_aogg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
