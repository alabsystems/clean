-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Unit-propagation replay guard soundness for ay sequential-main SAT-COMP
-- UNSAT proof publication. Propositions stand for proof digests, parsed proof
-- ledgers, unit queue schedules, antecedent availability, propagation traces,
-- empty-clause reachability witnesses, checker transcripts, benchmark
-- fingerprints, build/archive evidence, fallback no-claim paths, audit
-- transcripts, and fail-closed recompute diagnostics.

def ay_uprg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_uprg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_uprg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_uprg_accepted_evidence
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (unitQueueSchedule : Prop) (antecedentAvailabilityLedger : Prop)
    (propagationTrace : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofDigest ->
      parsedProofLedger ->
      unitQueueSchedule ->
      antecedentAvailabilityLedger ->
      propagationTrace ->
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

def ay_uprg_propagation_replay_composition
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (unitQueueSchedule : Prop) (antecedentAvailabilityLedger : Prop)
    (propagationTrace : Prop) (emptyClauseReachable : Prop)
    (originalUnsat : Prop) :=
  ay_uprg_conj
    (ay_uprg_map proofDigest parsedProofLedger)
    (ay_uprg_conj
      (ay_uprg_map parsedProofLedger unitQueueSchedule)
      (ay_uprg_conj
        (ay_uprg_map unitQueueSchedule antecedentAvailabilityLedger)
        (ay_uprg_conj
          (ay_uprg_map antecedentAvailabilityLedger propagationTrace)
          (ay_uprg_conj
            (ay_uprg_map propagationTrace emptyClauseReachable)
            (ay_uprg_map emptyClauseReachable originalUnsat))))))

def ay_uprg_publication
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (unitQueueSchedule : Prop) (antecedentAvailabilityLedger : Prop)
    (propagationTrace : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  ay_uprg_conj
    (ay_uprg_accepted_evidence proofDigest parsedProofLedger
      unitQueueSchedule antecedentAvailabilityLedger propagationTrace
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat)
    originalUnsat

def ay_uprg_failure_reason
    (parseMismatch : Prop) (queueMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (parseMismatch -> result) ->
    (queueMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (traceMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_uprg_bad_guard
    (parseMismatch : Prop) (queueMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_uprg_conj
    (ay_uprg_conj noClaim recompute)
    (ay_uprg_failure_reason parseMismatch queueMismatch antecedentMismatch
      traceMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch)

def ay_uprg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_uprg_disj noClaim (ay_uprg_disj originalUnsat publicSat)

theorem ay_uprg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_uprg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_uprg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_uprg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_uprg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_uprg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_uprg_build_accepted_evidence
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (unitQueueSchedule : Prop) (antecedentAvailabilityLedger : Prop)
    (propagationTrace : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    proofDigest ->
    parsedProofLedger ->
    unitQueueSchedule ->
    antecedentAvailabilityLedger ->
    propagationTrace ->
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
    ay_uprg_accepted_evidence proofDigest parsedProofLedger
      unitQueueSchedule antecedentAvailabilityLedger propagationTrace
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat := by
  intro hDigest hParsed hQueue hAntecedent hTrace hEmpty hTranscript
  intro hChecker hFingerprint hFingerprintAccepted hBuild hBuildAccepted
  intro hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hParsed hQueue hAntecedent hTrace hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_uprg_empty_clause_reachable
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (unitQueueSchedule : Prop) (antecedentAvailabilityLedger : Prop)
    (propagationTrace : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_uprg_accepted_evidence proofDigest parsedProofLedger
      unitQueueSchedule antecedentAvailabilityLedger propagationTrace
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hDigest _hParsed _hQueue _hAntecedent _hTrace hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_uprg_original_unsat
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (unitQueueSchedule : Prop) (antecedentAvailabilityLedger : Prop)
    (propagationTrace : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_uprg_accepted_evidence proofDigest parsedProofLedger
      unitQueueSchedule antecedentAvailabilityLedger propagationTrace
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hParsed _hQueue _hAntecedent _hTrace _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_uprg_propagation_replay_composes_to_original
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (unitQueueSchedule : Prop) (antecedentAvailabilityLedger : Prop)
    (propagationTrace : Prop) (emptyClauseReachable : Prop)
    (originalUnsat : Prop) :
    ay_uprg_propagation_replay_composition proofDigest parsedProofLedger
      unitQueueSchedule antecedentAvailabilityLedger propagationTrace
      emptyClauseReachable originalUnsat ->
    proofDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_parsed rest =>
      rest originalUnsat
        (fun parsed_to_queue rest2 =>
          rest2 originalUnsat
            (fun queue_to_antecedent rest3 =>
              rest3 originalUnsat
                (fun antecedent_to_trace rest4 =>
                  rest4 originalUnsat
                    (fun trace_to_empty empty_to_original =>
                      empty_to_original
                        (trace_to_empty
                          (antecedent_to_trace
                            (queue_to_antecedent
                              (parsed_to_queue
                                (digest_to_parsed hDigest)))))))))))

theorem ay_uprg_publication_sound
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (unitQueueSchedule : Prop) (antecedentAvailabilityLedger : Prop)
    (propagationTrace : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_uprg_publication proofDigest parsedProofLedger unitQueueSchedule
      antecedentAvailabilityLedger propagationTrace emptyClauseReachable
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_uprg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_uprg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_uprg_disj_right noClaim (ay_uprg_disj originalUnsat publicSat)
    (ay_uprg_disj_left originalUnsat publicSat hOriginal)

theorem ay_uprg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_uprg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_uprg_disj_left noClaim (ay_uprg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_uprg_bad_no_claim
    (parseMismatch : Prop) (queueMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uprg_bad_guard parseMismatch queueMismatch antecedentMismatch
      traceMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_uprg_bad_recompute
    (parseMismatch : Prop) (queueMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uprg_bad_guard parseMismatch queueMismatch antecedentMismatch
      traceMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_uprg_failed_guard_cannot_bless_unsat
    (parseMismatch : Prop) (queueMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_uprg_bad_guard parseMismatch queueMismatch antecedentMismatch
      traceMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_uprg_disj noClaim originalUnsat := by
  intro bad
  exact ay_uprg_disj_left noClaim originalUnsat
    (ay_uprg_bad_no_claim parseMismatch queueMismatch antecedentMismatch
      traceMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_uprg_failed_guard_cannot_create_public_sat
    (parseMismatch : Prop) (queueMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_uprg_bad_guard parseMismatch queueMismatch antecedentMismatch
      traceMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_uprg_disj noClaim publicSat := by
  intro bad
  exact ay_uprg_disj_left noClaim publicSat
    (ay_uprg_bad_no_claim parseMismatch queueMismatch antecedentMismatch
      traceMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_uprg_failure_forces_no_claim
    (parseMismatch : Prop) (queueMismatch : Prop)
    (antecedentMismatch : Prop) (traceMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uprg_failure_reason parseMismatch queueMismatch antecedentMismatch
      traceMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch ->
    (parseMismatch -> noClaim) ->
    (queueMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (traceMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure parse_to_no_claim queue_to_no_claim antecedent_to_no_claim
  intro trace_to_no_claim checker_to_no_claim fingerprint_to_no_claim
  intro build_to_no_claim archive_to_no_claim audit_to_no_claim
  exact failure noClaim parse_to_no_claim queue_to_no_claim
    antecedent_to_no_claim trace_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_uprg_parse_mismatch_forces_no_claim
    (parseMismatch noClaim : Prop) :
    parseMismatch -> (parseMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uprg_queue_mismatch_forces_no_claim
    (queueMismatch noClaim : Prop) :
    queueMismatch -> (queueMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uprg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch -> (antecedentMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uprg_trace_mismatch_forces_no_claim
    (traceMismatch noClaim : Prop) :
    traceMismatch -> (traceMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uprg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uprg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uprg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uprg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uprg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
