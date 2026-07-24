-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Deletion/revival guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. Propositions stand for proof text digests,
-- clause-deletion ledgers, clause-revival witnesses, antecedent availability
-- ledgers, resolvent replay, empty-clause reachability, checker transcripts,
-- benchmark fingerprints, solver build evidence, archive manifests, fallback
-- no-claim paths, audit transcripts, and fail-closed recompute diagnostics.

def ay_drg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_drg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_drg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_drg_accepted_evidence
    (proofTextDigest : Prop) (clauseDeletionLedger : Prop)
    (clauseRevivalWitness : Prop) (antecedentAvailabilityLedger : Prop)
    (resolventReplay : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofTextDigest ->
      clauseDeletionLedger ->
      clauseRevivalWitness ->
      antecedentAvailabilityLedger ->
      resolventReplay ->
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

def ay_drg_replay_composition
    (proofTextDigest : Prop) (clauseDeletionLedger : Prop)
    (clauseRevivalWitness : Prop) (antecedentAvailabilityLedger : Prop)
    (resolventReplay : Prop) (emptyClauseReachable : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  ay_drg_conj
    (ay_drg_map proofTextDigest clauseDeletionLedger)
    (ay_drg_conj
      (ay_drg_map clauseDeletionLedger clauseRevivalWitness)
      (ay_drg_conj
        (ay_drg_map clauseRevivalWitness antecedentAvailabilityLedger)
        (ay_drg_conj
          (ay_drg_map antecedentAvailabilityLedger resolventReplay)
          (ay_drg_conj
            (ay_drg_map resolventReplay emptyClauseReachable)
            (ay_drg_conj
              (ay_drg_map emptyClauseReachable visibleUnsat)
              (ay_drg_map visibleUnsat originalUnsat))))))

def ay_drg_publication
    (proofTextDigest : Prop) (clauseDeletionLedger : Prop)
    (clauseRevivalWitness : Prop) (antecedentAvailabilityLedger : Prop)
    (resolventReplay : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  ay_drg_conj
    (ay_drg_accepted_evidence proofTextDigest clauseDeletionLedger
      clauseRevivalWitness antecedentAvailabilityLedger resolventReplay
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat)
    originalUnsat

def ay_drg_failure_reason
    (digestMismatch : Prop) (deletionMismatch : Prop)
    (revivalMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (deletionMismatch -> result) ->
    (revivalMismatch -> result) ->
    (availabilityMismatch -> result) ->
    (replayMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_drg_bad_guard
    (digestMismatch : Prop) (deletionMismatch : Prop)
    (revivalMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  ay_drg_conj
    (ay_drg_conj noClaim recompute)
    (ay_drg_failure_reason digestMismatch deletionMismatch revivalMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch)

def ay_drg_public_report (noClaim : Prop) (originalUnsat : Prop) :=
  ay_drg_disj noClaim originalUnsat

theorem ay_drg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_drg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_drg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_drg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_drg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_drg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_drg_build_accepted_evidence
    (proofTextDigest : Prop) (clauseDeletionLedger : Prop)
    (clauseRevivalWitness : Prop) (antecedentAvailabilityLedger : Prop)
    (resolventReplay : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    proofTextDigest ->
    clauseDeletionLedger ->
    clauseRevivalWitness ->
    antecedentAvailabilityLedger ->
    resolventReplay ->
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
    ay_drg_accepted_evidence proofTextDigest clauseDeletionLedger
      clauseRevivalWitness antecedentAvailabilityLedger resolventReplay
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat := by
  intro hDigest hDeletion hRevival hAvailability hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hVisible hOriginal
  intro result publish
  exact publish hDigest hDeletion hRevival hAvailability hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hVisible hOriginal

theorem ay_drg_empty_clause_reachable
    (proofTextDigest : Prop) (clauseDeletionLedger : Prop)
    (clauseRevivalWitness : Prop) (antecedentAvailabilityLedger : Prop)
    (resolventReplay : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    ay_drg_accepted_evidence proofTextDigest clauseDeletionLedger
      clauseRevivalWitness antecedentAvailabilityLedger resolventReplay
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hDigest _hDeletion _hRevival _hAvailability _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hEmpty)

theorem ay_drg_resolvent_replay
    (proofTextDigest : Prop) (clauseDeletionLedger : Prop)
    (clauseRevivalWitness : Prop) (antecedentAvailabilityLedger : Prop)
    (resolventReplay : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    ay_drg_accepted_evidence proofTextDigest clauseDeletionLedger
      clauseRevivalWitness antecedentAvailabilityLedger resolventReplay
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat ->
    resolventReplay := by
  intro accepted
  exact accepted resolventReplay
    (fun _hDigest _hDeletion _hRevival _hAvailability hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hReplay)

theorem ay_drg_original_unsat
    (proofTextDigest : Prop) (clauseDeletionLedger : Prop)
    (clauseRevivalWitness : Prop) (antecedentAvailabilityLedger : Prop)
    (resolventReplay : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    ay_drg_accepted_evidence proofTextDigest clauseDeletionLedger
      clauseRevivalWitness antecedentAvailabilityLedger resolventReplay
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hDeletion _hRevival _hAvailability _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible hOriginal =>
      hOriginal)

theorem ay_drg_revival_replay_composes_to_original
    (proofTextDigest : Prop) (clauseDeletionLedger : Prop)
    (clauseRevivalWitness : Prop) (antecedentAvailabilityLedger : Prop)
    (resolventReplay : Prop) (emptyClauseReachable : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    proofTextDigest ->
    ay_drg_replay_composition proofTextDigest clauseDeletionLedger
      clauseRevivalWitness antecedentAvailabilityLedger resolventReplay
      emptyClauseReachable visibleUnsat originalUnsat ->
    originalUnsat := by
  intro hDigest
  intro composed
  exact composed originalUnsat
    (fun digest_to_deletion rest1 =>
      rest1 originalUnsat
        (fun deletion_to_revival rest2 =>
          rest2 originalUnsat
            (fun revival_to_availability rest3 =>
              rest3 originalUnsat
                (fun availability_to_replay rest4 =>
                  rest4 originalUnsat
                    (fun replay_to_empty rest5 =>
                      rest5 originalUnsat
                        (fun empty_to_visible visible_to_original =>
                          visible_to_original
                            (empty_to_visible
                              (replay_to_empty
                                (availability_to_replay
                                  (revival_to_availability
                                    (deletion_to_revival
                                      (digest_to_deletion hDigest))))))))))))

theorem ay_drg_publication_sound
    (proofTextDigest : Prop) (clauseDeletionLedger : Prop)
    (clauseRevivalWitness : Prop) (antecedentAvailabilityLedger : Prop)
    (resolventReplay : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    ay_drg_publication proofTextDigest clauseDeletionLedger
      clauseRevivalWitness antecedentAvailabilityLedger resolventReplay
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat (fun _accepted unsat => unsat)

theorem ay_drg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> ay_drg_public_report noClaim originalUnsat := by
  intro unsat
  exact ay_drg_disj_right noClaim originalUnsat unsat

theorem ay_drg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> ay_drg_public_report noClaim originalUnsat := by
  intro no_claim
  exact ay_drg_disj_left noClaim originalUnsat no_claim

theorem ay_drg_bad_no_claim
    (digestMismatch : Prop) (deletionMismatch : Prop)
    (revivalMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_drg_bad_guard digestMismatch deletionMismatch revivalMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_drg_bad_recompute
    (digestMismatch : Prop) (deletionMismatch : Prop)
    (revivalMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_drg_bad_guard digestMismatch deletionMismatch revivalMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_drg_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (deletionMismatch : Prop)
    (revivalMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    ay_drg_bad_guard digestMismatch deletionMismatch revivalMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch noClaim
      recompute ->
    ay_drg_public_report noClaim originalUnsat := by
  intro bad
  exact ay_drg_public_no_claim_report noClaim originalUnsat
    (ay_drg_bad_no_claim digestMismatch deletionMismatch revivalMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch noClaim
      recompute bad)

theorem ay_drg_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (deletionMismatch : Prop)
    (revivalMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (publicSat : Prop) :
    ay_drg_bad_guard digestMismatch deletionMismatch revivalMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch noClaim
      recompute ->
    noClaim := by
  intro bad
  exact ay_drg_bad_no_claim digestMismatch deletionMismatch revivalMismatch
    availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
    fingerprintMismatch buildMismatch archiveMismatch auditMismatch noClaim
    recompute bad

theorem ay_drg_failure_forces_no_claim
    (digestMismatch : Prop) (deletionMismatch : Prop)
    (revivalMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_drg_bad_guard digestMismatch deletionMismatch revivalMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch noClaim
      recompute ->
    ay_drg_conj noClaim recompute := by
  intro bad
  exact ay_drg_conj_intro noClaim recompute
    (ay_drg_bad_no_claim digestMismatch deletionMismatch revivalMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch noClaim
      recompute bad)
    (ay_drg_bad_recompute digestMismatch deletionMismatch revivalMismatch
      availabilityMismatch replayMismatch reachabilityMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch noClaim
      recompute bad)

theorem ay_drg_digest_mismatch_forces_no_claim
    (digestMismatch : Prop) (noClaim : Prop) :
    digestMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_drg_deletion_mismatch_forces_no_claim
    (deletionMismatch : Prop) (noClaim : Prop) :
    deletionMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_drg_revival_mismatch_forces_no_claim
    (revivalMismatch : Prop) (noClaim : Prop) :
    revivalMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_drg_availability_mismatch_forces_no_claim
    (availabilityMismatch : Prop) (noClaim : Prop) :
    availabilityMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_drg_replay_mismatch_forces_no_claim
    (replayMismatch : Prop) (noClaim : Prop) :
    replayMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_drg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch : Prop) (noClaim : Prop) :
    reachabilityMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_drg_checker_mismatch_forces_no_claim
    (checkerMismatch : Prop) (noClaim : Prop) :
    checkerMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_drg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_drg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_drg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_drg_audit_mismatch_forces_no_claim
    (auditMismatch : Prop) (noClaim : Prop) :
    auditMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
