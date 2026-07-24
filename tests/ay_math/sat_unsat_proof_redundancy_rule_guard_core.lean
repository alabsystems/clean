-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Redundancy-rule guard soundness for ay sequential-main SAT-COMP UNSAT proof
-- publication. Propositions stand for proof digests, rule manifests, parsed
-- ledgers, redundancy witnesses, antecedent availability, replay evidence,
-- empty-clause reachability, checker transcripts, benchmark fingerprints,
-- build/archive evidence, fallback no-claim paths, audit transcripts, and
-- fail-closed recompute diagnostics.

def ay_rrug_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_rrug_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_rrug_map (source : Prop) (target : Prop) :=
  source -> target

def ay_rrug_accepted_evidence
    (proofDigest : Prop) (ruleManifest : Prop) (parsedLedger : Prop)
    (redundancyWitness : Prop) (antecedentAvailability : Prop)
    (replayEvidence : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofDigest ->
      ruleManifest ->
      parsedLedger ->
      redundancyWitness ->
      antecedentAvailability ->
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

def ay_rrug_rule_replay_composition
    (proofDigest : Prop) (ruleManifest : Prop) (parsedLedger : Prop)
    (redundancyWitness : Prop) (antecedentAvailability : Prop)
    (replayEvidence : Prop) (emptyClauseReachable : Prop)
    (originalUnsat : Prop) :=
  ay_rrug_conj
    (ay_rrug_map proofDigest ruleManifest)
    (ay_rrug_conj
      (ay_rrug_map ruleManifest parsedLedger)
      (ay_rrug_conj
        (ay_rrug_map parsedLedger redundancyWitness)
        (ay_rrug_conj
          (ay_rrug_map redundancyWitness antecedentAvailability)
          (ay_rrug_conj
            (ay_rrug_map antecedentAvailability replayEvidence)
            (ay_rrug_conj
              (ay_rrug_map replayEvidence emptyClauseReachable)
              (ay_rrug_map emptyClauseReachable originalUnsat)))))))

def ay_rrug_publication
    (proofDigest : Prop) (ruleManifest : Prop) (parsedLedger : Prop)
    (redundancyWitness : Prop) (antecedentAvailability : Prop)
    (replayEvidence : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  ay_rrug_conj
    (ay_rrug_accepted_evidence proofDigest ruleManifest parsedLedger
      redundancyWitness antecedentAvailability replayEvidence
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat)
    originalUnsat

def ay_rrug_failure_reason
    (digestMismatch : Prop) (parseMismatch : Prop) (ruleMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (parseMismatch -> result) ->
    (ruleMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_rrug_bad_guard
    (digestMismatch : Prop) (parseMismatch : Prop) (ruleMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_rrug_conj
    (ay_rrug_conj noClaim recompute)
    (ay_rrug_failure_reason digestMismatch parseMismatch ruleMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch)

def ay_rrug_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_rrug_disj noClaim (ay_rrug_disj originalUnsat publicSat)

theorem ay_rrug_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_rrug_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_rrug_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_rrug_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_rrug_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_rrug_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_rrug_build_accepted_evidence
    (proofDigest : Prop) (ruleManifest : Prop) (parsedLedger : Prop)
    (redundancyWitness : Prop) (antecedentAvailability : Prop)
    (replayEvidence : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    proofDigest ->
    ruleManifest ->
    parsedLedger ->
    redundancyWitness ->
    antecedentAvailability ->
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
    ay_rrug_accepted_evidence proofDigest ruleManifest parsedLedger
      redundancyWitness antecedentAvailability replayEvidence
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat := by
  intro hDigest hRule hParsed hRedundant hAntecedent hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hRule hParsed hRedundant hAntecedent hReplay
    hEmpty hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_rrug_empty_clause_reachable
    (proofDigest : Prop) (ruleManifest : Prop) (parsedLedger : Prop)
    (redundancyWitness : Prop) (antecedentAvailability : Prop)
    (replayEvidence : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_rrug_accepted_evidence proofDigest ruleManifest parsedLedger
      redundancyWitness antecedentAvailability replayEvidence
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hDigest _hRule _hParsed _hRedundant _hAntecedent _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_rrug_original_unsat
    (proofDigest : Prop) (ruleManifest : Prop) (parsedLedger : Prop)
    (redundancyWitness : Prop) (antecedentAvailability : Prop)
    (replayEvidence : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_rrug_accepted_evidence proofDigest ruleManifest parsedLedger
      redundancyWitness antecedentAvailability replayEvidence
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hRule _hParsed _hRedundant _hAntecedent _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_rrug_rule_replay_composes_to_original
    (proofDigest : Prop) (ruleManifest : Prop) (parsedLedger : Prop)
    (redundancyWitness : Prop) (antecedentAvailability : Prop)
    (replayEvidence : Prop) (emptyClauseReachable : Prop)
    (originalUnsat : Prop) :
    ay_rrug_rule_replay_composition proofDigest ruleManifest parsedLedger
      redundancyWitness antecedentAvailability replayEvidence
      emptyClauseReachable originalUnsat ->
    proofDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_rule rest =>
      rest originalUnsat
        (fun rule_to_parsed rest2 =>
          rest2 originalUnsat
            (fun parsed_to_redundant rest3 =>
              rest3 originalUnsat
                (fun redundant_to_antecedent rest4 =>
                  rest4 originalUnsat
                    (fun antecedent_to_replay rest5 =>
                      rest5 originalUnsat
                        (fun replay_to_empty empty_to_original =>
                          empty_to_original
                            (replay_to_empty
                              (antecedent_to_replay
                                (redundant_to_antecedent
                                  (parsed_to_redundant
                                    (rule_to_parsed
                                      (digest_to_rule hDigest))))))))))))

theorem ay_rrug_publication_sound
    (proofDigest : Prop) (ruleManifest : Prop) (parsedLedger : Prop)
    (redundancyWitness : Prop) (antecedentAvailability : Prop)
    (replayEvidence : Prop) (emptyClauseReachable : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_rrug_publication proofDigest ruleManifest parsedLedger
      redundancyWitness antecedentAvailability replayEvidence
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_rrug_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_rrug_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_rrug_disj_right noClaim (ay_rrug_disj originalUnsat publicSat)
    (ay_rrug_disj_left originalUnsat publicSat hOriginal)

theorem ay_rrug_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_rrug_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_rrug_disj_left noClaim (ay_rrug_disj originalUnsat publicSat)
    hNoClaim

theorem ay_rrug_bad_no_claim
    (digestMismatch : Prop) (parseMismatch : Prop) (ruleMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_rrug_bad_guard digestMismatch parseMismatch ruleMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_rrug_bad_recompute
    (digestMismatch : Prop) (parseMismatch : Prop) (ruleMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_rrug_bad_guard digestMismatch parseMismatch ruleMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_rrug_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (parseMismatch : Prop) (ruleMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_rrug_bad_guard digestMismatch parseMismatch ruleMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_rrug_disj noClaim originalUnsat := by
  intro bad
  exact ay_rrug_disj_left noClaim originalUnsat
    (ay_rrug_bad_no_claim digestMismatch parseMismatch ruleMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_rrug_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (parseMismatch : Prop) (ruleMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_rrug_bad_guard digestMismatch parseMismatch ruleMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_rrug_disj noClaim publicSat := by
  intro bad
  exact ay_rrug_disj_left noClaim publicSat
    (ay_rrug_bad_no_claim digestMismatch parseMismatch ruleMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_rrug_failure_forces_no_claim
    (digestMismatch : Prop) (parseMismatch : Prop) (ruleMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_rrug_failure_reason digestMismatch parseMismatch ruleMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch ->
    (digestMismatch -> noClaim) ->
    (parseMismatch -> noClaim) ->
    (ruleMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure digest_to_no_claim parse_to_no_claim rule_to_no_claim
  intro antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
  intro fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
  intro audit_to_no_claim
  exact failure noClaim digest_to_no_claim parse_to_no_claim
    rule_to_no_claim antecedent_to_no_claim replay_to_no_claim
    checker_to_no_claim fingerprint_to_no_claim build_to_no_claim
    archive_to_no_claim audit_to_no_claim

theorem ay_rrug_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rrug_parse_mismatch_forces_no_claim
    (parseMismatch noClaim : Prop) :
    parseMismatch -> (parseMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rrug_rule_mismatch_forces_no_claim
    (ruleMismatch noClaim : Prop) :
    ruleMismatch -> (ruleMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rrug_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch -> (antecedentMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rrug_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rrug_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rrug_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rrug_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rrug_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_rrug_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
