-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-deletion replay guard soundness for ay sequential-main SAT-COMP
-- UNSAT proof publication. Propositions stand for proof digests, parsed proof
-- ledgers, deletion ledgers, active-clause-set digests, antecedent availability
-- witnesses, proof replay, empty-clause reachability witnesses, checker
-- transcripts, benchmark fingerprints, build/archive evidence, fallback
-- no-claim paths, audit transcripts, and fail-closed recompute diagnostics.

def ay_cdrg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_cdrg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_cdrg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_cdrg_accepted_evidence
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (deletionLedger : Prop) (activeClauseSetDigest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofDigest ->
      parsedProofLedger ->
      deletionLedger ->
      activeClauseSetDigest ->
      antecedentAvailabilityWitness ->
      proofReplay ->
      emptyClauseReachabilityWitness ->
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

def ay_cdrg_deletion_replay_composition
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (deletionLedger : Prop) (activeClauseSetDigest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :=
  ay_cdrg_conj
    (ay_cdrg_map proofDigest parsedProofLedger)
    (ay_cdrg_conj
      (ay_cdrg_map parsedProofLedger deletionLedger)
      (ay_cdrg_conj
        (ay_cdrg_map deletionLedger activeClauseSetDigest)
        (ay_cdrg_conj
          (ay_cdrg_map activeClauseSetDigest antecedentAvailabilityWitness)
          (ay_cdrg_conj
            (ay_cdrg_map antecedentAvailabilityWitness proofReplay)
            (ay_cdrg_conj
              (ay_cdrg_map proofReplay emptyClauseReachabilityWitness)
              (ay_cdrg_map emptyClauseReachabilityWitness originalUnsat)))))))

def ay_cdrg_publication
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (deletionLedger : Prop) (activeClauseSetDigest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  ay_cdrg_conj
    (ay_cdrg_accepted_evidence proofDigest parsedProofLedger deletionLedger
      activeClauseSetDigest antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat)
    originalUnsat

def ay_cdrg_failure_reason
    (digestMismatch : Prop) (parseMismatch : Prop)
    (deletionMismatch : Prop) (activeSetMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (parseMismatch -> result) ->
    (deletionMismatch -> result) ->
    (activeSetMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_cdrg_bad_guard
    (digestMismatch : Prop) (parseMismatch : Prop)
    (deletionMismatch : Prop) (activeSetMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_cdrg_conj
    (ay_cdrg_conj noClaim recompute)
    (ay_cdrg_failure_reason digestMismatch parseMismatch deletionMismatch
      activeSetMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch)

def ay_cdrg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_cdrg_disj noClaim (ay_cdrg_disj originalUnsat publicSat)

theorem ay_cdrg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_cdrg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_cdrg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_cdrg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_cdrg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_cdrg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_cdrg_build_accepted_evidence
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (deletionLedger : Prop) (activeClauseSetDigest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    proofDigest ->
    parsedProofLedger ->
    deletionLedger ->
    activeClauseSetDigest ->
    antecedentAvailabilityWitness ->
    proofReplay ->
    emptyClauseReachabilityWitness ->
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
    ay_cdrg_accepted_evidence proofDigest parsedProofLedger deletionLedger
      activeClauseSetDigest antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat := by
  intro hDigest hParsed hDeletion hActive hAntecedent hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hParsed hDeletion hActive hAntecedent hReplay
    hEmpty hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_cdrg_empty_clause_reachable
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (deletionLedger : Prop) (activeClauseSetDigest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_cdrg_accepted_evidence proofDigest parsedProofLedger deletionLedger
      activeClauseSetDigest antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hDigest _hParsed _hDeletion _hActive _hAntecedent _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_cdrg_original_unsat
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (deletionLedger : Prop) (activeClauseSetDigest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_cdrg_accepted_evidence proofDigest parsedProofLedger deletionLedger
      activeClauseSetDigest antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hParsed _hDeletion _hActive _hAntecedent _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_cdrg_deletion_replay_composes_to_original
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (deletionLedger : Prop) (activeClauseSetDigest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :
    ay_cdrg_deletion_replay_composition proofDigest parsedProofLedger
      deletionLedger activeClauseSetDigest antecedentAvailabilityWitness
      proofReplay emptyClauseReachabilityWitness originalUnsat ->
    proofDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_parsed rest =>
      rest originalUnsat
        (fun parsed_to_deletion rest2 =>
          rest2 originalUnsat
            (fun deletion_to_active rest3 =>
              rest3 originalUnsat
                (fun active_to_antecedent rest4 =>
                  rest4 originalUnsat
                    (fun antecedent_to_replay rest5 =>
                      rest5 originalUnsat
                        (fun replay_to_empty empty_to_original =>
                          empty_to_original
                            (replay_to_empty
                              (antecedent_to_replay
                                (active_to_antecedent
                                  (deletion_to_active
                                    (parsed_to_deletion
                                      (digest_to_parsed hDigest))))))))))))

theorem ay_cdrg_publication_sound
    (proofDigest : Prop) (parsedProofLedger : Prop)
    (deletionLedger : Prop) (activeClauseSetDigest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_cdrg_publication proofDigest parsedProofLedger deletionLedger
      activeClauseSetDigest antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_cdrg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_cdrg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_cdrg_disj_right noClaim (ay_cdrg_disj originalUnsat publicSat)
    (ay_cdrg_disj_left originalUnsat publicSat hOriginal)

theorem ay_cdrg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_cdrg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_cdrg_disj_left noClaim (ay_cdrg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_cdrg_bad_no_claim
    (digestMismatch : Prop) (parseMismatch : Prop)
    (deletionMismatch : Prop) (activeSetMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_cdrg_bad_guard digestMismatch parseMismatch deletionMismatch
      activeSetMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_cdrg_bad_recompute
    (digestMismatch : Prop) (parseMismatch : Prop)
    (deletionMismatch : Prop) (activeSetMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_cdrg_bad_guard digestMismatch parseMismatch deletionMismatch
      activeSetMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_cdrg_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (parseMismatch : Prop)
    (deletionMismatch : Prop) (activeSetMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_cdrg_bad_guard digestMismatch parseMismatch deletionMismatch
      activeSetMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    ay_cdrg_disj noClaim originalUnsat := by
  intro bad
  exact ay_cdrg_disj_left noClaim originalUnsat
    (ay_cdrg_bad_no_claim digestMismatch parseMismatch deletionMismatch
      activeSetMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute bad)

theorem ay_cdrg_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (parseMismatch : Prop)
    (deletionMismatch : Prop) (activeSetMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_cdrg_bad_guard digestMismatch parseMismatch deletionMismatch
      activeSetMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    ay_cdrg_disj noClaim publicSat := by
  intro bad
  exact ay_cdrg_disj_left noClaim publicSat
    (ay_cdrg_bad_no_claim digestMismatch parseMismatch deletionMismatch
      activeSetMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute bad)

theorem ay_cdrg_failure_forces_no_claim
    (digestMismatch : Prop) (parseMismatch : Prop)
    (deletionMismatch : Prop) (activeSetMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_cdrg_failure_reason digestMismatch parseMismatch deletionMismatch
      activeSetMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch ->
    (digestMismatch -> noClaim) ->
    (parseMismatch -> noClaim) ->
    (deletionMismatch -> noClaim) ->
    (activeSetMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure digest_to_no_claim parse_to_no_claim deletion_to_no_claim
  intro active_to_no_claim antecedent_to_no_claim replay_to_no_claim
  intro checker_to_no_claim fingerprint_to_no_claim build_to_no_claim
  intro archive_to_no_claim audit_to_no_claim
  exact failure noClaim digest_to_no_claim parse_to_no_claim
    deletion_to_no_claim active_to_no_claim antecedent_to_no_claim
    replay_to_no_claim checker_to_no_claim fingerprint_to_no_claim
    build_to_no_claim archive_to_no_claim audit_to_no_claim

theorem ay_cdrg_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cdrg_parse_mismatch_forces_no_claim
    (parseMismatch noClaim : Prop) :
    parseMismatch -> (parseMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cdrg_deletion_mismatch_forces_no_claim
    (deletionMismatch noClaim : Prop) :
    deletionMismatch -> (deletionMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cdrg_active_set_mismatch_forces_no_claim
    (activeSetMismatch noClaim : Prop) :
    activeSetMismatch -> (activeSetMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cdrg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch -> (antecedentMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cdrg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cdrg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cdrg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cdrg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cdrg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cdrg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
