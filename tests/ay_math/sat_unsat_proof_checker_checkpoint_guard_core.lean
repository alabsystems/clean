-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Proof-checker checkpoint guard soundness for ay sequential-main SAT-COMP
-- UNSAT proof publication. Propositions stand for proof text digests, checker
-- checkpoint digests, parsed-step prefix ledgers, antecedent availability,
-- resume replay witnesses, empty-clause reachability, checker transcripts,
-- benchmark fingerprints, build/archive evidence, fallback no-claim paths,
-- audit transcripts, and fail-closed recompute diagnostics.

def ay_cckg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_cckg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_cckg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_cckg_accepted_evidence
    (proofTextDigest : Prop) (checkpointDigest : Prop)
    (parsedStepPrefixLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (resumeReplayWitness : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofTextDigest ->
      checkpointDigest ->
      parsedStepPrefixLedger ->
      antecedentAvailabilityLedger ->
      resumeReplayWitness ->
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

def ay_cckg_checkpoint_replay_composition
    (proofTextDigest : Prop) (checkpointDigest : Prop)
    (parsedStepPrefixLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (resumeReplayWitness : Prop) (emptyClauseReachable : Prop)
    (originalUnsat : Prop) :=
  ay_cckg_conj
    (ay_cckg_map proofTextDigest checkpointDigest)
    (ay_cckg_conj
      (ay_cckg_map checkpointDigest parsedStepPrefixLedger)
      (ay_cckg_conj
        (ay_cckg_map parsedStepPrefixLedger antecedentAvailabilityLedger)
        (ay_cckg_conj
          (ay_cckg_map antecedentAvailabilityLedger resumeReplayWitness)
          (ay_cckg_conj
            (ay_cckg_map resumeReplayWitness emptyClauseReachable)
            (ay_cckg_map emptyClauseReachable originalUnsat))))))

def ay_cckg_publication
    (proofTextDigest : Prop) (checkpointDigest : Prop)
    (parsedStepPrefixLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (resumeReplayWitness : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  ay_cckg_conj
    (ay_cckg_accepted_evidence proofTextDigest checkpointDigest
      parsedStepPrefixLedger antecedentAvailabilityLedger resumeReplayWitness
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat)
    originalUnsat

def ay_cckg_failure_reason
    (digestMismatch : Prop) (checkpointMismatch : Prop)
    (prefixMismatch : Prop) (availabilityMismatch : Prop)
    (resumeMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (checkpointMismatch -> result) ->
    (prefixMismatch -> result) ->
    (availabilityMismatch -> result) ->
    (resumeMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_cckg_bad_guard
    (digestMismatch : Prop) (checkpointMismatch : Prop)
    (prefixMismatch : Prop) (availabilityMismatch : Prop)
    (resumeMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_cckg_conj
    (ay_cckg_conj noClaim recompute)
    (ay_cckg_failure_reason digestMismatch checkpointMismatch prefixMismatch
      availabilityMismatch resumeMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch)

def ay_cckg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_cckg_disj noClaim (ay_cckg_disj originalUnsat publicSat)

theorem ay_cckg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_cckg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_cckg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_cckg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_cckg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_cckg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_cckg_build_accepted_evidence
    (proofTextDigest : Prop) (checkpointDigest : Prop)
    (parsedStepPrefixLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (resumeReplayWitness : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    proofTextDigest ->
    checkpointDigest ->
    parsedStepPrefixLedger ->
    antecedentAvailabilityLedger ->
    resumeReplayWitness ->
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
    ay_cckg_accepted_evidence proofTextDigest checkpointDigest
      parsedStepPrefixLedger antecedentAvailabilityLedger resumeReplayWitness
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat := by
  intro hDigest hCheckpoint hPrefix hAvail hResume hEmpty hTranscript
  intro hChecker hFingerprint hFingerprintAccepted hBuild hBuildAccepted
  intro hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hCheckpoint hPrefix hAvail hResume hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_cckg_empty_clause_reachable
    (proofTextDigest : Prop) (checkpointDigest : Prop)
    (parsedStepPrefixLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (resumeReplayWitness : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_cckg_accepted_evidence proofTextDigest checkpointDigest
      parsedStepPrefixLedger antecedentAvailabilityLedger resumeReplayWitness
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hDigest _hCheckpoint _hPrefix _hAvail _hResume hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_cckg_original_unsat
    (proofTextDigest : Prop) (checkpointDigest : Prop)
    (parsedStepPrefixLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (resumeReplayWitness : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_cckg_accepted_evidence proofTextDigest checkpointDigest
      parsedStepPrefixLedger antecedentAvailabilityLedger resumeReplayWitness
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hCheckpoint _hPrefix _hAvail _hResume _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_cckg_checkpoint_replay_composes_to_original
    (proofTextDigest : Prop) (checkpointDigest : Prop)
    (parsedStepPrefixLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (resumeReplayWitness : Prop) (emptyClauseReachable : Prop)
    (originalUnsat : Prop) :
    ay_cckg_checkpoint_replay_composition proofTextDigest checkpointDigest
      parsedStepPrefixLedger antecedentAvailabilityLedger resumeReplayWitness
      emptyClauseReachable originalUnsat ->
    proofTextDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_checkpoint rest =>
      rest originalUnsat
        (fun checkpoint_to_prefix rest2 =>
          rest2 originalUnsat
            (fun prefix_to_availability rest3 =>
              rest3 originalUnsat
                (fun availability_to_resume rest4 =>
                  rest4 originalUnsat
                    (fun resume_to_empty empty_to_original =>
                      empty_to_original
                        (resume_to_empty
                          (availability_to_resume
                            (prefix_to_availability
                              (checkpoint_to_prefix
                                (digest_to_checkpoint hDigest)))))))))))

theorem ay_cckg_publication_sound
    (proofTextDigest : Prop) (checkpointDigest : Prop)
    (parsedStepPrefixLedger : Prop) (antecedentAvailabilityLedger : Prop)
    (resumeReplayWitness : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_cckg_publication proofTextDigest checkpointDigest
      parsedStepPrefixLedger antecedentAvailabilityLedger resumeReplayWitness
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_cckg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_cckg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_cckg_disj_right noClaim (ay_cckg_disj originalUnsat publicSat)
    (ay_cckg_disj_left originalUnsat publicSat hOriginal)

theorem ay_cckg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_cckg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_cckg_disj_left noClaim (ay_cckg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_cckg_bad_no_claim
    (digestMismatch : Prop) (checkpointMismatch : Prop)
    (prefixMismatch : Prop) (availabilityMismatch : Prop)
    (resumeMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_cckg_bad_guard digestMismatch checkpointMismatch prefixMismatch
      availabilityMismatch resumeMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_cckg_bad_recompute
    (digestMismatch : Prop) (checkpointMismatch : Prop)
    (prefixMismatch : Prop) (availabilityMismatch : Prop)
    (resumeMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_cckg_bad_guard digestMismatch checkpointMismatch prefixMismatch
      availabilityMismatch resumeMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_cckg_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (checkpointMismatch : Prop)
    (prefixMismatch : Prop) (availabilityMismatch : Prop)
    (resumeMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_cckg_bad_guard digestMismatch checkpointMismatch prefixMismatch
      availabilityMismatch resumeMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    ay_cckg_disj noClaim originalUnsat := by
  intro bad
  exact ay_cckg_disj_left noClaim originalUnsat
    (ay_cckg_bad_no_claim digestMismatch checkpointMismatch prefixMismatch
      availabilityMismatch resumeMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute bad)

theorem ay_cckg_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (checkpointMismatch : Prop)
    (prefixMismatch : Prop) (availabilityMismatch : Prop)
    (resumeMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_cckg_bad_guard digestMismatch checkpointMismatch prefixMismatch
      availabilityMismatch resumeMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    ay_cckg_disj noClaim publicSat := by
  intro bad
  exact ay_cckg_disj_left noClaim publicSat
    (ay_cckg_bad_no_claim digestMismatch checkpointMismatch prefixMismatch
      availabilityMismatch resumeMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute bad)

theorem ay_cckg_failure_forces_no_claim
    (digestMismatch : Prop) (checkpointMismatch : Prop)
    (prefixMismatch : Prop) (availabilityMismatch : Prop)
    (resumeMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_cckg_failure_reason digestMismatch checkpointMismatch prefixMismatch
      availabilityMismatch resumeMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch ->
    (digestMismatch -> noClaim) ->
    (checkpointMismatch -> noClaim) ->
    (prefixMismatch -> noClaim) ->
    (availabilityMismatch -> noClaim) ->
    (resumeMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure digest_to_no_claim checkpoint_to_no_claim prefix_to_no_claim
  intro availability_to_no_claim resume_to_no_claim reachability_to_no_claim
  intro checker_to_no_claim fingerprint_to_no_claim build_to_no_claim
  intro archive_to_no_claim audit_to_no_claim
  exact failure noClaim digest_to_no_claim checkpoint_to_no_claim
    prefix_to_no_claim availability_to_no_claim resume_to_no_claim
    reachability_to_no_claim checker_to_no_claim fingerprint_to_no_claim
    build_to_no_claim archive_to_no_claim audit_to_no_claim

theorem ay_cckg_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cckg_checkpoint_mismatch_forces_no_claim
    (checkpointMismatch noClaim : Prop) :
    checkpointMismatch -> (checkpointMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cckg_prefix_mismatch_forces_no_claim
    (prefixMismatch noClaim : Prop) :
    prefixMismatch -> (prefixMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cckg_availability_mismatch_forces_no_claim
    (availabilityMismatch noClaim : Prop) :
    availabilityMismatch -> (availabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cckg_resume_mismatch_forces_no_claim
    (resumeMismatch noClaim : Prop) :
    resumeMismatch -> (resumeMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cckg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch -> (reachabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cckg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cckg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cckg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cckg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cckg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
