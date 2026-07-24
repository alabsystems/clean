-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Proof replay memory-budget guard soundness for ay sequential-main SAT-COMP
-- UNSAT proof publication. Propositions stand for proof text digests, replay
-- memory-limit manifests, allocation ledgers, spill/chunk policies,
-- antecedent availability, resolvent/redundancy replay, empty-clause
-- reachability, checker transcripts, benchmark fingerprints, build/archive
-- evidence, fallback no-claim paths, audit transcripts, and fail-closed
-- recompute diagnostics.

def ay_rmbg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_rmbg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_rmbg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_rmbg_accepted_evidence
    (proofTextDigest : Prop) (memoryLimitManifest : Prop)
    (allocationLedger : Prop) (spillChunkPolicyWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofTextDigest ->
      memoryLimitManifest ->
      allocationLedger ->
      spillChunkPolicyWitness ->
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

def ay_rmbg_memory_replay_composition
    (proofTextDigest : Prop) (memoryLimitManifest : Prop)
    (allocationLedger : Prop) (spillChunkPolicyWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (originalUnsat : Prop) :=
  ay_rmbg_conj
    (ay_rmbg_map proofTextDigest memoryLimitManifest)
    (ay_rmbg_conj
      (ay_rmbg_map memoryLimitManifest allocationLedger)
      (ay_rmbg_conj
        (ay_rmbg_map allocationLedger spillChunkPolicyWitness)
        (ay_rmbg_conj
          (ay_rmbg_map spillChunkPolicyWitness antecedentAvailabilityLedger)
          (ay_rmbg_conj
            (ay_rmbg_map antecedentAvailabilityLedger replayEvidence)
            (ay_rmbg_conj
              (ay_rmbg_map replayEvidence emptyClauseReachable)
              (ay_rmbg_map emptyClauseReachable originalUnsat)))))))

def ay_rmbg_publication
    (proofTextDigest : Prop) (memoryLimitManifest : Prop)
    (allocationLedger : Prop) (spillChunkPolicyWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  ay_rmbg_conj
    (ay_rmbg_accepted_evidence proofTextDigest memoryLimitManifest
      allocationLedger spillChunkPolicyWitness antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat)
    originalUnsat

def ay_rmbg_failure_reason
    (digestMismatch : Prop) (memoryMismatch : Prop)
    (allocationMismatch : Prop) (spillMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (memoryMismatch -> result) ->
    (allocationMismatch -> result) ->
    (spillMismatch -> result) ->
    (availabilityMismatch -> result) ->
    (replayMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_rmbg_bad_guard
    (digestMismatch : Prop) (memoryMismatch : Prop)
    (allocationMismatch : Prop) (spillMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_rmbg_conj
    (ay_rmbg_conj noClaim recompute)
    (ay_rmbg_failure_reason digestMismatch memoryMismatch allocationMismatch
      spillMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch)

def ay_rmbg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_rmbg_disj noClaim (ay_rmbg_disj originalUnsat publicSat)

theorem ay_rmbg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_rmbg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_rmbg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_rmbg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_rmbg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_rmbg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_rmbg_build_accepted_evidence
    (proofTextDigest : Prop) (memoryLimitManifest : Prop)
    (allocationLedger : Prop) (spillChunkPolicyWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    proofTextDigest ->
    memoryLimitManifest ->
    allocationLedger ->
    spillChunkPolicyWitness ->
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
    ay_rmbg_accepted_evidence proofTextDigest memoryLimitManifest
      allocationLedger spillChunkPolicyWitness antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat := by
  intro hDigest hMemory hAllocation hSpill hAvail hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hMemory hAllocation hSpill hAvail hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_rmbg_empty_clause_reachable
    (proofTextDigest : Prop) (memoryLimitManifest : Prop)
    (allocationLedger : Prop) (spillChunkPolicyWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_rmbg_accepted_evidence proofTextDigest memoryLimitManifest
      allocationLedger spillChunkPolicyWitness antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hDigest _hMemory _hAllocation _hSpill _hAvail _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_rmbg_original_unsat
    (proofTextDigest : Prop) (memoryLimitManifest : Prop)
    (allocationLedger : Prop) (spillChunkPolicyWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_rmbg_accepted_evidence proofTextDigest memoryLimitManifest
      allocationLedger spillChunkPolicyWitness antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hMemory _hAllocation _hSpill _hAvail _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_rmbg_memory_replay_composes_to_original
    (proofTextDigest : Prop) (memoryLimitManifest : Prop)
    (allocationLedger : Prop) (spillChunkPolicyWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (originalUnsat : Prop) :
    ay_rmbg_memory_replay_composition proofTextDigest memoryLimitManifest
      allocationLedger spillChunkPolicyWitness antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable originalUnsat ->
    proofTextDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_memory rest =>
      rest originalUnsat
        (fun memory_to_allocation rest2 =>
          rest2 originalUnsat
            (fun allocation_to_spill rest3 =>
              rest3 originalUnsat
                (fun spill_to_availability rest4 =>
                  rest4 originalUnsat
                    (fun availability_to_replay rest5 =>
                      rest5 originalUnsat
                        (fun replay_to_empty empty_to_original =>
                          empty_to_original
                            (replay_to_empty
                              (availability_to_replay
                                (spill_to_availability
                                  (allocation_to_spill
                                    (memory_to_allocation
                                      (digest_to_memory hDigest))))))))))))

theorem ay_rmbg_publication_sound
    (proofTextDigest : Prop) (memoryLimitManifest : Prop)
    (allocationLedger : Prop) (spillChunkPolicyWitness : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_rmbg_publication proofTextDigest memoryLimitManifest allocationLedger
      spillChunkPolicyWitness antecedentAvailabilityLedger replayEvidence
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_rmbg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_rmbg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_rmbg_disj_right noClaim (ay_rmbg_disj originalUnsat publicSat)
    (ay_rmbg_disj_left originalUnsat publicSat hOriginal)

theorem ay_rmbg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_rmbg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_rmbg_disj_left noClaim (ay_rmbg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_rmbg_bad_no_claim
    (digestMismatch : Prop) (memoryMismatch : Prop)
    (allocationMismatch : Prop) (spillMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_rmbg_bad_guard digestMismatch memoryMismatch allocationMismatch
      spillMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_rmbg_bad_recompute
    (digestMismatch : Prop) (memoryMismatch : Prop)
    (allocationMismatch : Prop) (spillMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_rmbg_bad_guard digestMismatch memoryMismatch allocationMismatch
      spillMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_rmbg_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (memoryMismatch : Prop)
    (allocationMismatch : Prop) (spillMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_rmbg_bad_guard digestMismatch memoryMismatch allocationMismatch
      spillMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_rmbg_disj noClaim originalUnsat := by
  intro bad
  exact ay_rmbg_disj_left noClaim originalUnsat
    (ay_rmbg_bad_no_claim digestMismatch memoryMismatch allocationMismatch
      spillMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_rmbg_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (memoryMismatch : Prop)
    (allocationMismatch : Prop) (spillMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_rmbg_bad_guard digestMismatch memoryMismatch allocationMismatch
      spillMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_rmbg_disj noClaim publicSat := by
  intro bad
  exact ay_rmbg_disj_left noClaim publicSat
    (ay_rmbg_bad_no_claim digestMismatch memoryMismatch allocationMismatch
      spillMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_rmbg_failure_forces_no_claim
    (digestMismatch : Prop) (memoryMismatch : Prop)
    (allocationMismatch : Prop) (spillMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_rmbg_failure_reason digestMismatch memoryMismatch allocationMismatch
      spillMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch ->
    (digestMismatch -> noClaim) ->
    (memoryMismatch -> noClaim) ->
    (allocationMismatch -> noClaim) ->
    (spillMismatch -> noClaim) ->
    (availabilityMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure digest_to_no_claim memory_to_no_claim allocation_to_no_claim
  intro spill_to_no_claim availability_to_no_claim replay_to_no_claim
  intro reachability_to_no_claim checker_to_no_claim fingerprint_to_no_claim
  intro build_to_no_claim archive_to_no_claim audit_to_no_claim
  exact failure noClaim digest_to_no_claim memory_to_no_claim
    allocation_to_no_claim spill_to_no_claim availability_to_no_claim
    replay_to_no_claim reachability_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_rmbg_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rmbg_memory_mismatch_forces_no_claim
    (memoryMismatch noClaim : Prop) :
    memoryMismatch -> (memoryMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rmbg_allocation_mismatch_forces_no_claim
    (allocationMismatch noClaim : Prop) :
    allocationMismatch -> (allocationMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rmbg_spill_mismatch_forces_no_claim
    (spillMismatch noClaim : Prop) :
    spillMismatch -> (spillMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rmbg_availability_mismatch_forces_no_claim
    (availabilityMismatch noClaim : Prop) :
    availabilityMismatch -> (availabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rmbg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rmbg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch -> (reachabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rmbg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rmbg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rmbg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rmbg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rmbg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
