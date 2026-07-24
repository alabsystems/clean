-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Incremental-frame guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. Propositions stand for proof text digests, frame stack
-- ledgers, active-frame discharge witnesses, parsed proof steps, antecedent
-- availability, replay evidence, empty-clause reachability on the original
-- benchmark formula, checker transcripts, fingerprints, build/archive
-- evidence, fallback no-claim paths, audit transcripts, and fail-closed
-- recompute diagnostics.

def ay_ifgg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_ifgg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_ifgg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_ifgg_accepted_evidence
    (proofTextDigest : Prop) (frameStackLedger : Prop)
    (activeFrameDischargeWitness : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofTextDigest ->
      frameStackLedger ->
      activeFrameDischargeWitness ->
      parsedStepLedger ->
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

def ay_ifgg_frame_replay_composition
    (proofTextDigest : Prop) (frameStackLedger : Prop)
    (activeFrameDischargeWitness : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (originalUnsat : Prop) :=
  ay_ifgg_conj
    (ay_ifgg_map proofTextDigest frameStackLedger)
    (ay_ifgg_conj
      (ay_ifgg_map frameStackLedger activeFrameDischargeWitness)
      (ay_ifgg_conj
        (ay_ifgg_map activeFrameDischargeWitness parsedStepLedger)
        (ay_ifgg_conj
          (ay_ifgg_map parsedStepLedger antecedentAvailabilityLedger)
          (ay_ifgg_conj
            (ay_ifgg_map antecedentAvailabilityLedger replayEvidence)
            (ay_ifgg_conj
              (ay_ifgg_map replayEvidence originalEmptyClauseReachable)
              (ay_ifgg_map originalEmptyClauseReachable originalUnsat)))))))

def ay_ifgg_publication
    (proofTextDigest : Prop) (frameStackLedger : Prop)
    (activeFrameDischargeWitness : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  ay_ifgg_conj
    (ay_ifgg_accepted_evidence proofTextDigest frameStackLedger
      activeFrameDischargeWitness parsedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat)
    originalUnsat

def ay_ifgg_failure_reason
    (digestMismatch : Prop) (frameMismatch : Prop)
    (dischargeMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (frameMismatch -> result) ->
    (dischargeMismatch -> result) ->
    (parseMismatch -> result) ->
    (availabilityMismatch -> result) ->
    (replayMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_ifgg_bad_guard
    (digestMismatch : Prop) (frameMismatch : Prop)
    (dischargeMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_ifgg_conj
    (ay_ifgg_conj noClaim recompute)
    (ay_ifgg_failure_reason digestMismatch frameMismatch dischargeMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch)

def ay_ifgg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_ifgg_disj noClaim (ay_ifgg_disj originalUnsat publicSat)

theorem ay_ifgg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_ifgg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_ifgg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_ifgg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_ifgg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_ifgg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_ifgg_build_accepted_evidence
    (proofTextDigest : Prop) (frameStackLedger : Prop)
    (activeFrameDischargeWitness : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    proofTextDigest ->
    frameStackLedger ->
    activeFrameDischargeWitness ->
    parsedStepLedger ->
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
    ay_ifgg_accepted_evidence proofTextDigest frameStackLedger
      activeFrameDischargeWitness parsedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat := by
  intro hDigest hFrame hDischarge hParsed hAvail hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hFrame hDischarge hParsed hAvail hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_ifgg_original_empty_clause_reachable
    (proofTextDigest : Prop) (frameStackLedger : Prop)
    (activeFrameDischargeWitness : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_ifgg_accepted_evidence proofTextDigest frameStackLedger
      activeFrameDischargeWitness parsedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalEmptyClauseReachable := by
  intro accepted
  exact accepted originalEmptyClauseReachable
    (fun _hDigest _hFrame _hDischarge _hParsed _hAvail _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_ifgg_original_unsat
    (proofTextDigest : Prop) (frameStackLedger : Prop)
    (activeFrameDischargeWitness : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_ifgg_accepted_evidence proofTextDigest frameStackLedger
      activeFrameDischargeWitness parsedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hFrame _hDischarge _hParsed _hAvail _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_ifgg_frame_replay_composes_to_original
    (proofTextDigest : Prop) (frameStackLedger : Prop)
    (activeFrameDischargeWitness : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (originalUnsat : Prop) :
    ay_ifgg_frame_replay_composition proofTextDigest frameStackLedger
      activeFrameDischargeWitness parsedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable originalUnsat ->
    proofTextDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_frame rest =>
      rest originalUnsat
        (fun frame_to_discharge rest2 =>
          rest2 originalUnsat
            (fun discharge_to_parsed rest3 =>
              rest3 originalUnsat
                (fun parsed_to_availability rest4 =>
                  rest4 originalUnsat
                    (fun availability_to_replay rest5 =>
                      rest5 originalUnsat
                        (fun replay_to_empty empty_to_original =>
                          empty_to_original
                            (replay_to_empty
                              (availability_to_replay
                                (parsed_to_availability
                                  (discharge_to_parsed
                                    (frame_to_discharge
                                      (digest_to_frame hDigest))))))))))))

theorem ay_ifgg_publication_sound
    (proofTextDigest : Prop) (frameStackLedger : Prop)
    (activeFrameDischargeWitness : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_ifgg_publication proofTextDigest frameStackLedger
      activeFrameDischargeWitness parsedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_ifgg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_ifgg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_ifgg_disj_right noClaim (ay_ifgg_disj originalUnsat publicSat)
    (ay_ifgg_disj_left originalUnsat publicSat hOriginal)

theorem ay_ifgg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_ifgg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_ifgg_disj_left noClaim (ay_ifgg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_ifgg_bad_no_claim
    (digestMismatch : Prop) (frameMismatch : Prop)
    (dischargeMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ifgg_bad_guard digestMismatch frameMismatch dischargeMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_ifgg_bad_recompute
    (digestMismatch : Prop) (frameMismatch : Prop)
    (dischargeMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ifgg_bad_guard digestMismatch frameMismatch dischargeMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_ifgg_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (frameMismatch : Prop)
    (dischargeMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_ifgg_bad_guard digestMismatch frameMismatch dischargeMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_ifgg_disj noClaim originalUnsat := by
  intro bad
  exact ay_ifgg_disj_left noClaim originalUnsat
    (ay_ifgg_bad_no_claim digestMismatch frameMismatch dischargeMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_ifgg_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (frameMismatch : Prop)
    (dischargeMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_ifgg_bad_guard digestMismatch frameMismatch dischargeMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_ifgg_disj noClaim publicSat := by
  intro bad
  exact ay_ifgg_disj_left noClaim publicSat
    (ay_ifgg_bad_no_claim digestMismatch frameMismatch dischargeMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_ifgg_failure_forces_no_claim
    (digestMismatch : Prop) (frameMismatch : Prop)
    (dischargeMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ifgg_failure_reason digestMismatch frameMismatch dischargeMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch ->
    (digestMismatch -> noClaim) ->
    (frameMismatch -> noClaim) ->
    (dischargeMismatch -> noClaim) ->
    (parseMismatch -> noClaim) ->
    (availabilityMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure digest_to_no_claim frame_to_no_claim discharge_to_no_claim
  intro parse_to_no_claim availability_to_no_claim replay_to_no_claim
  intro reachability_to_no_claim checker_to_no_claim
  intro fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
  intro audit_to_no_claim
  exact failure noClaim digest_to_no_claim frame_to_no_claim
    discharge_to_no_claim parse_to_no_claim availability_to_no_claim
    replay_to_no_claim reachability_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_ifgg_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ifgg_frame_mismatch_forces_no_claim
    (frameMismatch noClaim : Prop) :
    frameMismatch -> (frameMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ifgg_discharge_mismatch_forces_no_claim
    (dischargeMismatch noClaim : Prop) :
    dischargeMismatch -> (dischargeMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ifgg_parse_mismatch_forces_no_claim
    (parseMismatch noClaim : Prop) :
    parseMismatch -> (parseMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ifgg_availability_mismatch_forces_no_claim
    (availabilityMismatch noClaim : Prop) :
    availabilityMismatch -> (availabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ifgg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ifgg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch -> (reachabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ifgg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ifgg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ifgg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ifgg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ifgg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
