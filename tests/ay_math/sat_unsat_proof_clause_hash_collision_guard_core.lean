-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-hash collision guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. Propositions stand for proof digests, clause hash
-- manifests, collision-resolution ledgers, parsed-step ledgers, antecedent
-- availability, resolvent/redundancy replay, empty-clause reachability,
-- checker transcripts, benchmark fingerprints, build/archive evidence,
-- fallback no-claim paths, audit transcripts, and fail-closed recompute
-- diagnostics.

def ay_chcg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_chcg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_chcg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_chcg_accepted_evidence
    (proofDigest : Prop) (clauseHashManifest : Prop)
    (collisionResolutionLedger : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofDigest ->
      clauseHashManifest ->
      collisionResolutionLedger ->
      parsedStepLedger ->
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

def ay_chcg_collision_replay_composition
    (proofDigest : Prop) (clauseHashManifest : Prop)
    (collisionResolutionLedger : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (originalUnsat : Prop) :=
  ay_chcg_conj
    (ay_chcg_map proofDigest clauseHashManifest)
    (ay_chcg_conj
      (ay_chcg_map clauseHashManifest collisionResolutionLedger)
      (ay_chcg_conj
        (ay_chcg_map collisionResolutionLedger parsedStepLedger)
        (ay_chcg_conj
          (ay_chcg_map parsedStepLedger antecedentAvailabilityLedger)
          (ay_chcg_conj
            (ay_chcg_map antecedentAvailabilityLedger replayEvidence)
            (ay_chcg_conj
              (ay_chcg_map replayEvidence emptyClauseReachable)
              (ay_chcg_map emptyClauseReachable originalUnsat)))))))

def ay_chcg_publication
    (proofDigest : Prop) (clauseHashManifest : Prop)
    (collisionResolutionLedger : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  ay_chcg_conj
    (ay_chcg_accepted_evidence proofDigest clauseHashManifest
      collisionResolutionLedger parsedStepLedger antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat)
    originalUnsat

def ay_chcg_failure_reason
    (digestMismatch : Prop) (hashMismatch : Prop)
    (collisionMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (hashMismatch -> result) ->
    (collisionMismatch -> result) ->
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

def ay_chcg_bad_guard
    (digestMismatch : Prop) (hashMismatch : Prop)
    (collisionMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_chcg_conj
    (ay_chcg_conj noClaim recompute)
    (ay_chcg_failure_reason digestMismatch hashMismatch collisionMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch)

def ay_chcg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_chcg_disj noClaim (ay_chcg_disj originalUnsat publicSat)

theorem ay_chcg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_chcg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_chcg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_chcg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_chcg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_chcg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_chcg_build_accepted_evidence
    (proofDigest : Prop) (clauseHashManifest : Prop)
    (collisionResolutionLedger : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    proofDigest ->
    clauseHashManifest ->
    collisionResolutionLedger ->
    parsedStepLedger ->
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
    ay_chcg_accepted_evidence proofDigest clauseHashManifest
      collisionResolutionLedger parsedStepLedger antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat := by
  intro hDigest hHash hCollision hParsed hAvail hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hHash hCollision hParsed hAvail hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_chcg_empty_clause_reachable
    (proofDigest : Prop) (clauseHashManifest : Prop)
    (collisionResolutionLedger : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_chcg_accepted_evidence proofDigest clauseHashManifest
      collisionResolutionLedger parsedStepLedger antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hDigest _hHash _hCollision _hParsed _hAvail _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_chcg_original_unsat
    (proofDigest : Prop) (clauseHashManifest : Prop)
    (collisionResolutionLedger : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_chcg_accepted_evidence proofDigest clauseHashManifest
      collisionResolutionLedger parsedStepLedger antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hHash _hCollision _hParsed _hAvail _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_chcg_collision_replay_composes_to_original
    (proofDigest : Prop) (clauseHashManifest : Prop)
    (collisionResolutionLedger : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (originalUnsat : Prop) :
    ay_chcg_collision_replay_composition proofDigest clauseHashManifest
      collisionResolutionLedger parsedStepLedger antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable originalUnsat ->
    proofDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_hash rest =>
      rest originalUnsat
        (fun hash_to_collision rest2 =>
          rest2 originalUnsat
            (fun collision_to_parsed rest3 =>
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
                                  (collision_to_parsed
                                    (hash_to_collision
                                      (digest_to_hash hDigest))))))))))))

theorem ay_chcg_publication_sound
    (proofDigest : Prop) (clauseHashManifest : Prop)
    (collisionResolutionLedger : Prop) (parsedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_chcg_publication proofDigest clauseHashManifest
      collisionResolutionLedger parsedStepLedger antecedentAvailabilityLedger
      replayEvidence emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_chcg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_chcg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_chcg_disj_right noClaim (ay_chcg_disj originalUnsat publicSat)
    (ay_chcg_disj_left originalUnsat publicSat hOriginal)

theorem ay_chcg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_chcg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_chcg_disj_left noClaim (ay_chcg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_chcg_bad_no_claim
    (digestMismatch : Prop) (hashMismatch : Prop)
    (collisionMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_chcg_bad_guard digestMismatch hashMismatch collisionMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_chcg_bad_recompute
    (digestMismatch : Prop) (hashMismatch : Prop)
    (collisionMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_chcg_bad_guard digestMismatch hashMismatch collisionMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_chcg_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (hashMismatch : Prop)
    (collisionMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_chcg_bad_guard digestMismatch hashMismatch collisionMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_chcg_disj noClaim originalUnsat := by
  intro bad
  exact ay_chcg_disj_left noClaim originalUnsat
    (ay_chcg_bad_no_claim digestMismatch hashMismatch collisionMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_chcg_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (hashMismatch : Prop)
    (collisionMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_chcg_bad_guard digestMismatch hashMismatch collisionMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_chcg_disj noClaim publicSat := by
  intro bad
  exact ay_chcg_disj_left noClaim publicSat
    (ay_chcg_bad_no_claim digestMismatch hashMismatch collisionMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_chcg_failure_forces_no_claim
    (digestMismatch : Prop) (hashMismatch : Prop)
    (collisionMismatch : Prop) (parseMismatch : Prop)
    (availabilityMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_chcg_failure_reason digestMismatch hashMismatch collisionMismatch
      parseMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch ->
    (digestMismatch -> noClaim) ->
    (hashMismatch -> noClaim) ->
    (collisionMismatch -> noClaim) ->
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
  intro failure digest_to_no_claim hash_to_no_claim collision_to_no_claim
  intro parse_to_no_claim availability_to_no_claim replay_to_no_claim
  intro reachability_to_no_claim checker_to_no_claim fingerprint_to_no_claim
  intro build_to_no_claim archive_to_no_claim audit_to_no_claim
  exact failure noClaim digest_to_no_claim hash_to_no_claim
    collision_to_no_claim parse_to_no_claim availability_to_no_claim
    replay_to_no_claim reachability_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_chcg_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_chcg_hash_mismatch_forces_no_claim
    (hashMismatch noClaim : Prop) :
    hashMismatch -> (hashMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_chcg_collision_mismatch_forces_no_claim
    (collisionMismatch noClaim : Prop) :
    collisionMismatch -> (collisionMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_chcg_parse_mismatch_forces_no_claim
    (parseMismatch noClaim : Prop) :
    parseMismatch -> (parseMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_chcg_availability_mismatch_forces_no_claim
    (availabilityMismatch noClaim : Prop) :
    availabilityMismatch -> (availabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_chcg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_chcg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch -> (reachabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_chcg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_chcg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_chcg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_chcg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_chcg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
